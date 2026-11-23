#!/usr/bin/env python3
"""Adversarial ownership and schema checks for the legacy AxisEngine API."""
from __future__ import annotations

import argparse
import copy
from pathlib import Path

import axis as AX


def need(condition, message):
    if not condition:
        raise AssertionError(message)


def snapshot(engine):
    return copy.deepcopy((engine.rows, engine.raw_rows, engine.dc, engine.cnt,
        engine.live, engine.measure, engine.pairs_computed, engine.pairs_released,
        engine.remeasured, engine.axes_decl, engine._domains, engine.result(), engine.table()))


def fixture(model):
    nested = {"slot": [0]}
    # The configuration and declaration deliberately share a mutable object.
    return model.Table("boundary", (model.Axis("a", (0, 1, 2, 3, False, None, "z",
        [0], nested, {"slot": [1]})),), ("p", "q"),
        (model.Row({"a": nested}, {"p": {"seen": [0]}, "q": [0]}),),
        (model.Edge(("p", "q"), 1),))


def row(model, value=1):
    return model.Row({"a": value}, {"p": {"seen": [1]}, "q": [1]})


def refused(engine, operation, label):
    before = snapshot(engine)
    try:
        operation()
    except AX.NotAJoin:
        pass
    else:
        raise AssertionError("malformed operation accepted: " + label)
    need(snapshot(engine) == before, "refusal changed retained state: " + label)


def check_ownership(model, solver):
    supplied = fixture(model)
    engine = AX.AxisEngine(model, supplied)
    before = snapshot(engine)
    supplied.contract[0].configuration["a"]["slot"].append(9)
    supplied.contract[0].behavior["p"]["seen"].append(9)
    supplied.contract[0].behavior["q"].clear()
    supplied.contract[0].configuration["extra"] = 1
    need(snapshot(engine) == before, "constructor retained caller-owned declarations or rows")

    new = row(model, {"slot": [1]})
    engine.join([new])
    before = snapshot(engine)
    new.configuration["a"]["slot"].append(7)
    new.behavior["p"]["seen"].append(7)
    new.behavior.clear()
    need(snapshot(engine) == before, "join retained a caller-owned row")

    exported = engine.table()
    exported.contract[0].configuration["a"]["slot"].append(5)
    exported.contract[0].behavior["p"]["seen"].append(5)
    exported.contract[1].configuration.clear()
    exported.axes[0].values[-1]["slot"].append(5)
    need(snapshot(engine) == before, "table() exported mutable retained data")
    refused(engine, lambda: engine.join([row(model, {"slot": [1, 5]})]),
            "mutated exported domain must not enlarge admission")
    need(engine.result() == solver.solve(engine.table()), "ownership checks left cache/table disagreement")

    # A producer may reuse or mutate a previously yielded Row while the rest
    # of its batch is still being read. Staging must own each yielded value.
    engine = AX.AxisEngine(model, fixture(model))
    first = row(model, 1)
    second = row(model, 2)

    def batch():
        yield first
        first.configuration["a"] = 3
        first.behavior["p"]["seen"].append(12)
        yield second

    engine.join(batch())
    need(engine.table().contract[1].configuration["a"] == 1,
         "staged row changed while its generator advanced")
    need(engine.result() == solver.solve(engine.table()), "generator mutation changed cached meaning")
    return 5


def check_join_validation(model, solver):
    good_behavior = {"p": 0, "q": 0}
    cycle = []
    cycle.append(cycle)

    class NameLike:
        def __init__(self, name):
            self.name = name

        def __hash__(self):
            return hash(self.name)

        def __eq__(self, other):
            return self.name == other

    bad = [
        ("missing axis", model.Row({}, good_behavior)),
        ("unknown axis", model.Row({"a": 2, "other": 0}, good_behavior)),
        ("non-object configuration", model.Row([], good_behavior)),
        ("non-string axis key", model.Row({1: 2}, good_behavior)),
        ("string-equal non-string axis key", model.Row({NameLike("a"): 2}, good_behavior)),
        ("value outside domain", model.Row({"a": 99}, good_behavior)),
        ("missing component", model.Row({"a": 2}, {"p": 0})),
        ("unknown component", model.Row({"a": 2}, {"p": 0, "q": 0, "other": 0})),
        ("non-object behavior", model.Row({"a": 2}, [])),
        ("non-string component key", model.Row({"a": 2}, {"p": 0, 0: 0})),
        ("string-equal non-string component key", model.Row({"a": 2}, {NameLike("p"): 0, "q": 0})),
        ("NaN behavior", model.Row({"a": 2}, {"p": float("nan"), "q": 0})),
        ("infinite behavior", model.Row({"a": 2}, {"p": float("inf"), "q": 0})),
        ("nested non-JSON behavior", model.Row({"a": 2}, {"p": [set()], "q": 0})),
        ("tuple behavior", model.Row({"a": 2}, {"p": (0, 1), "q": 0})),
        ("bytes behavior", model.Row({"a": 2}, {"p": b"0", "q": 0})),
        ("non-string JSON key", model.Row({"a": 2}, {"p": {1: "value"}, "q": 0})),
        ("cyclic behavior", model.Row({"a": 2}, {"p": cycle, "q": 0})),
        ("not a Row", {"configuration": {"a": 2}, "behavior": good_behavior}),
    ]
    for label, invalid in bad:
        engine = AX.AxisEngine(model, fixture(model))
        refused(engine, lambda invalid=invalid: engine.join([row(model), invalid]), label)
        refused(engine, lambda invalid=invalid: engine._encode(invalid), "direct _encode: " + label)
        engine.join([row(model)])
        need(engine.result() == solver.solve(engine.table()), "valid retry failed after " + label)

    engine = AX.AxisEngine(model, fixture(model))
    original = engine.table().contract[0]
    refused(engine, lambda: engine.join([row(model), original]), "existing duplicate")
    changed = model.Row(copy.deepcopy(original.configuration), {"p": 9, "q": 9})
    refused(engine, lambda: engine.join([row(model), changed]), "existing behavior replacement")
    refused(engine, lambda: engine.join([row(model), row(model)]), "duplicate inside batch")
    refused(engine, lambda: engine.join(None), "non-iterable join")

    # Python equality considers False == 0; finite JSON domains must not.
    numeric = model.Table("typed", (model.Axis("a", (0, 1)),), ("p", "q"), (),
                          (model.Edge(("p", "q"), 1),))
    engine = AX.AxisEngine(model, numeric)
    refused(engine, lambda: engine.join([row(model, False)]), "boolean is not numeric zero")
    engine.join([row(model, 0), row(model, 1)])
    need(engine.result() == solver.solve(engine.table()), "typed domain retry failed")
    return 2 * len(bad) + 5


def check_withdrawal_validation(model, solver):
    invalid = [({}, "missing axis"), ({"a": 0, "extra": 1}, "unknown axis"),
               ([], "non-object configuration"), ({"a": 99}, "outside domain"),
               ({"a": 2}, "absent in-domain configuration"),
               ({"a": float("nan")}, "NaN configuration")]
    for value, label in invalid:
        engine = AX.AxisEngine(model, fixture(model))
        engine.join([row(model)])
        first = copy.deepcopy(engine.table().contract[0].configuration)
        refused(engine, lambda value=value: engine.withdraw([first, value]), label)
        engine.withdraw([first])
        need(engine.result() == solver.solve(engine.table()), "valid withdrawal retry failed: " + label)
    engine = AX.AxisEngine(model, fixture(model))
    first = copy.deepcopy(engine.table().contract[0].configuration)
    refused(engine, lambda: engine.withdraw([first, first]), "duplicate withdrawal")
    refused(engine, lambda: engine.withdraw(None), "non-iterable withdrawal")
    return len(invalid) + 2


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("solver_dir", nargs="?", default=str(Path(__file__).resolve().parent.parent))
    args = parser.parse_args()
    model, solver = AX.load_solver(args.solver_dir)
    checks = check_ownership(model, solver)
    checks += check_join_validation(model, solver)
    checks += check_withdrawal_validation(model, solver)
    print(f"AXIS BOUNDARY PASS: {checks} ownership/schema controls; rejected batches atomic; "
          "retained input and table exports detached; valid retries agree with solver")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
