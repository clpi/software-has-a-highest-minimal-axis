#!/usr/bin/env python3
"""Incremental finite HMA witnesses with reconstructible checkpoints.

Events have contiguous sequence numbers and a schema epoch. The event stream
may be append-only, but the active rows, witness support, and selected answer
are revision-sensitive. This materializer retains no event history or row-pair
records. A checkpoint retains the active input and replay boundary, and its
derived caches are reconstructed on restoration.

The implementation is checked against the imported Lean definitions by the
gate. It is not a proof of this Python program. Checkpoint parsing establishes
well-formedness, not the truth of an untrusted historical claim; independently
validated checkpoint/outcome bytes are the replay boundary.
"""

from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path
import sys
from typing import Any, Iterable

import solve


COUNTERS = (
    "pair_evaluations", "pair_additions", "pair_removals",
    "exact_cells_changed", "support_threshold_changes", "cone_visits",
    "live_cells_changed", "full_rebuilds",
)


def zero_counters() -> dict[str, int]:
    return {key: 0 for key in COUNTERS}


def row_key(row: dict[str, Any]) -> tuple[tuple[int, Any], ...]:
    return tuple(solve.scalar_key(value) for value in row["axes"])


def behavior_key(row: dict[str, Any]) -> tuple[tuple[int, Any], ...]:
    return tuple(solve.scalar_key(value) for value in row["behavior"])


def supersets(mask: int, axes: int) -> Iterable[int]:
    """Enumerate each superset once: exactly 2 ** (axes - popcount(mask))."""
    free = ((1 << axes) - 1) ^ mask
    extra = free
    while True:
        yield mask | extra
        if extra == 0:
            break
        extra = (extra - 1) & free


def natural(value: Any, label: str, *, positive: bool = False) -> int:
    solve.require(type(value) is int and value >= int(positive),
                  f"{label}: expected {'positive' if positive else 'nonnegative'} integer")
    return value


class Incremental:
    """Active rows plus exact-mask multiplicities and their subset closure.

    ``exact[(D,b)]`` counts distinct unordered active row pairs witnessing
    component b with exact changed-axis set D. ``support[S][b]`` counts the
    occupied exact supports D contained in S. The live bit is support > 0.
    Only an exact support's transition between zero and positive changes its
    superset cone. Multiple derivations are retained as multiplicities, so a
    withdrawal cannot erase an independently supported live conclusion.

    Event row vectors use the canonical sorted columns in ``instance()``.
    Public methods return copies; caller mutations cannot alter active state.
    """

    def __init__(self, instance: Any):
        data = solve.normalize(instance)
        self._data = data
        self._rows: dict[tuple, dict[str, Any]] = {}
        self._exact: dict[tuple[int, int], int] = {}
        self._support = [[0] * len(data["components"])
                         for _ in range(1 << len(data["axes"]))]
        self._live = [0] * len(self._support)
        self.next_seq = 1
        self.epoch = 0
        self._cumulative = zero_counters()
        self._reconstruction = zero_counters()
        metrics = self._change_rows(data["contract"])
        metrics["full_rebuilds"] = 1
        self._accumulate(metrics)
        self._last = metrics

    def _accumulate(self, metrics: dict[str, int]) -> None:
        for key in COUNTERS:
            self._cumulative[key] += metrics[key]

    def _pair(self, left: tuple[tuple, tuple], right: tuple[tuple, tuple], sign: int,
              delta: dict[tuple[int, int], int], metrics: dict[str, int]) -> None:
        metrics["pair_evaluations"] += 1
        metrics["pair_additions" if sign > 0 else "pair_removals"] += 1
        changed = sum(1 << i for i, (a, b) in enumerate(zip(left[0], right[0])) if a != b)
        for component, (a, b) in enumerate(zip(left[1], right[1])):
            if a != b:
                key = (changed, component)
                delta[key] = delta.get(key, 0) + sign

    def _change_rows(self, rows: list[dict[str, Any]]) -> dict[str, int]:
        """Commit a prevalidated row transition without revisiting retained pairs.

        Every possible rejection is checked before the first state mutation.
        Net support deltas are accumulated before updating the closure, avoiding
        transient support loss within a behavior-replacement transaction.
        """
        final = {row_key(row): row for row in rows}
        unchanged = [row for key, row in self._rows.items()
                     if key in final and behavior_key(row) == behavior_key(final[key])]
        removed = [row for key, row in self._rows.items()
                   if key not in final or behavior_key(row) != behavior_key(final[key])]
        added = [row for key, row in final.items()
                 if key not in self._rows or behavior_key(row) != behavior_key(self._rows[key])]
        # Sorted row order makes both accounting and traversal reproducible.
        unchanged.sort(key=row_key)
        removed.sort(key=row_key)
        added.sort(key=row_key)
        metrics = zero_counters()
        delta: dict[tuple[int, int], int] = {}
        # Precompute injective typed identities once per row, rather than
        # reparsing scalar types for every pair. These are temporary comparison
        # keys, not a retained pair history or a second behavior semantics.
        retained_keys = [(row_key(row), behavior_key(row)) for row in unchanged]
        for changed, sign in ((removed, -1), (added, 1)):
            changed_keys = [(row_key(row), behavior_key(row)) for row in changed]
            for index, row in enumerate(changed_keys):
                for other in retained_keys:
                    self._pair(row, other, sign, delta, metrics)
                for other in changed_keys[index + 1:]:
                    self._pair(row, other, sign, delta, metrics)

        exact_changes: dict[tuple[int, int], int] = {}
        closure_delta: dict[tuple[int, int], int] = {}
        for key, difference in sorted(delta.items()):
            if difference == 0:
                continue
            old = self._exact.get(key, 0)
            new = old + difference
            solve.require(new >= 0, "internal witness multiplicity underflow")
            exact_changes[key] = new
            metrics["exact_cells_changed"] += 1
            if bool(old) == bool(new):
                continue
            metrics["support_threshold_changes"] += 1
            change = 1 if new else -1
            mask, component = key
            for superset in supersets(mask, len(self._data["axes"])):
                metrics["cone_visits"] += 1
                cell = (superset, component)
                closure_delta[cell] = closure_delta.get(cell, 0) + change

        support_changes: dict[tuple[int, int], int] = {}
        for (mask, component), difference in closure_delta.items():
            if difference == 0:
                continue
            old = self._support[mask][component]
            new = old + difference
            solve.require(new >= 0, "internal subset support underflow")
            support_changes[(mask, component)] = new
            metrics["live_cells_changed"] += int(bool(old) != bool(new))

        for key, new in exact_changes.items():
            if new:
                self._exact[key] = new
            else:
                self._exact.pop(key)
        for (mask, component), new in support_changes.items():
            self._support[mask][component] = new
            if new:
                self._live[mask] |= 1 << component
            else:
                self._live[mask] &= ~(1 << component)
        self._rows = final
        return metrics

    def instance(self) -> dict[str, Any]:
        return copy.deepcopy(self._data)

    def observe(self) -> dict[str, Any]:
        """Pure complete observation; pair search is never performed here."""
        return solve.result_from_live_masks(self._data, self._live)

    def diagnostics(self) -> dict[str, Any]:
        return {
            "next_seq": self.next_seq,
            "epoch": self.epoch,
            "last": dict(self._last),
            "cumulative": dict(self._cumulative),
            "reconstruction": dict(self._reconstruction),
            "storage": {
                "active_rows": len(self._rows),
                "active_pairs": len(self._rows) * (len(self._rows) - 1) // 2,
                "retained_pair_records": 0,
                "retained_events": 0,
                "exact_support_cells": len(self._exact),
                "subset_table_slots": len(self._live),
                "subset_support_cells": len(self._live) * len(self._data["components"]),
            },
            "observation": {
                "subsets_rendered": len(self._live),
                "edge_subset_checks": len(self._live) * len(self._data["hyperedges"]),
                "minimal_neighbor_upper_bound": (
                    len(self._data["axes"]) * len(self._live) // 2),
            },
        }

    def apply(self, event: Any) -> dict[str, Any]:
        solve.require(type(event) is dict, "event: expected an object")
        op = event.get("op")
        payloads = {"append": "rows", "remove": "axes", "replace": "rows",
                    "edges": "hyperedges", "rebase": "instance"}
        solve.require(type(op) is str and op in payloads, "event: unsupported operation")
        payload = payloads[op]
        solve.fields(event, {"seq", "epoch", "op", payload}, "event")
        seq = natural(event["seq"], "event.seq", positive=True)
        epoch = natural(event["epoch"], "event.epoch")
        solve.require(seq == self.next_seq, "event: stale, duplicate, or noncontiguous sequence")
        solve.require(epoch == self.epoch, "event: schema epoch mismatch")

        if op == "rebase":
            replacement = Incremental(event["instance"])
            metrics = replacement._last
            # A new schema is a declared full reconstruction. No old positional
            # mask or support is reused across this boundary.
            self._data = replacement._data
            self._rows = replacement._rows
            self._exact = replacement._exact
            self._support = replacement._support
            self._live = replacement._live
            self.epoch += 1
        else:
            candidate = self.instance()
            if op in {"append", "replace"}:
                incoming = solve.sequence(event["rows"], "event.rows")
                # Normalize incoming vectors alone to reject duplicate keys,
                # invalid domains, unknown fields, and inconsistent types.
                table = self.instance()
                table["contract"] = incoming
                normalized = solve.normalize(table)["contract"]
                if op == "append":
                    solve.require(all(row_key(row) not in self._rows for row in normalized),
                                  "append: configuration already active")
                    candidate["contract"].extend(normalized)
                else:
                    solve.require(all(row_key(row) in self._rows for row in normalized),
                                  "replace: configuration is not active")
                    replacements = {row_key(row): row for row in normalized}
                    candidate["contract"] = [replacements.get(row_key(row), row)
                                             for row in candidate["contract"]]
            elif op == "remove":
                vectors = solve.sequence(event["axes"], "event.axes")
                keys = []
                for vector in vectors:
                    solve.sequence(vector, "event.axes vector")
                    solve.require(len(vector) == len(candidate["axes"]),
                                  "remove: incomplete configuration")
                    keys.append(tuple(solve.scalar_key(value) for value in vector))
                solve.require(len(set(keys)) == len(keys), "remove: duplicate configuration")
                solve.require(all(key in self._rows for key in keys),
                              "remove: configuration is not active")
                remove = set(keys)
                candidate["contract"] = [row for row in candidate["contract"]
                                         if row_key(row) not in remove]
            else:
                candidate["hyperedges"] = event["hyperedges"]
            candidate = solve.normalize(candidate)
            metrics = self._change_rows(candidate["contract"])
            self._data = candidate

        self._accumulate(metrics)
        self._last = dict(metrics)
        self.next_seq += 1
        return {"seq": seq, "op": op, "epoch": self.epoch,
                "next_seq": self.next_seq, "work": dict(metrics),
                "cumulative": dict(self._cumulative)}

    def append_rows(self, rows: Any) -> dict[str, Any]:
        return self.apply({"seq": self.next_seq, "epoch": self.epoch,
                           "op": "append", "rows": rows})

    def remove_rows(self, axes: Any) -> dict[str, Any]:
        return self.apply({"seq": self.next_seq, "epoch": self.epoch,
                           "op": "remove", "axes": axes})

    def replace_rows(self, rows: Any) -> dict[str, Any]:
        return self.apply({"seq": self.next_seq, "epoch": self.epoch,
                           "op": "replace", "rows": rows})

    def set_edges(self, hyperedges: Any) -> dict[str, Any]:
        return self.apply({"seq": self.next_seq, "epoch": self.epoch,
                           "op": "edges", "hyperedges": hyperedges})

    def rebase(self, instance: Any) -> dict[str, Any]:
        return self.apply({"seq": self.next_seq, "epoch": self.epoch,
                           "op": "rebase", "instance": instance})

    def checkpoint(self) -> dict[str, Any]:
        """Compact replay boundary, containing neither events nor derived caches."""
        return {"schema": 1, "kind": "hma-incremental-checkpoint",
                "next_seq": self.next_seq, "epoch": self.epoch,
                "instance": self.instance(), "cumulative": dict(self._cumulative)}

    @classmethod
    def restore(cls, checkpoint: Any) -> "Incremental":
        solve.fields(checkpoint, {"schema", "kind", "next_seq", "epoch", "instance", "cumulative"},
                     "checkpoint")
        solve.require(type(checkpoint["schema"]) is int and checkpoint["schema"] == 1,
                      "checkpoint: unsupported schema")
        solve.require(checkpoint["kind"] == "hma-incremental-checkpoint",
                      "checkpoint: unexpected kind")
        next_seq = natural(checkpoint["next_seq"], "checkpoint.next_seq", positive=True)
        epoch = natural(checkpoint["epoch"], "checkpoint.epoch")
        solve.require(epoch < next_seq, "checkpoint: impossible schema epoch")
        solve.fields(checkpoint["cumulative"], set(COUNTERS), "checkpoint.cumulative")
        cumulative = {key: natural(checkpoint["cumulative"][key], "checkpoint.cumulative." + key)
                      for key in COUNTERS}
        solve.require(cumulative["pair_evaluations"] == cumulative["pair_additions"] + cumulative["pair_removals"],
                      "checkpoint: inconsistent pair accounting")
        solve.require(cumulative["full_rebuilds"] == epoch + 1,
                      "checkpoint: inconsistent reconstruction accounting")
        instance = cls(checkpoint["instance"])
        instance._reconstruction = dict(instance._last)
        instance._last = zero_counters()
        instance._cumulative = cumulative
        instance.next_seq = next_seq
        instance.epoch = epoch
        return instance


def replay(initial: Any, events: Any) -> tuple[Incremental, list[dict[str, Any]]]:
    """Return replayed state and a complete observation at every suffix prefix."""
    solve.require(type(initial) is dict, "initial: expected instance or checkpoint")
    state = (Incremental.restore(initial) if initial.get("kind") == "hma-incremental-checkpoint"
             else Incremental(initial))
    observations = [{"next_seq": state.next_seq, "epoch": state.epoch,
                     "result": state.observe()}]
    for event in solve.sequence(events, "events"):
        receipt = state.apply(event)
        observations.append({"receipt": receipt, "result": state.observe()})
    return state, observations


def run_campaign(campaign: Any) -> dict[str, Any]:
    solve.fields(campaign, {"schema", "initial", "events"}, "campaign")
    solve.require(type(campaign["schema"]) is int and campaign["schema"] == 1,
                  "campaign: unsupported schema")
    state, observations = replay(campaign["initial"], campaign["events"])
    return {"schema": 1, "observations": observations, "checkpoint": state.checkpoint(),
            "diagnostics": state.diagnostics()}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("campaign", help="schema 1 JSON with initial instance/checkpoint and events")
    args = parser.parse_args()
    try:
        data = json.loads(Path(args.campaign).read_text(encoding="utf-8"),
                          object_pairs_hook=solve.unique_object,
                          parse_constant=solve.reject_constant)
        output = run_campaign(data)
        sys.stdout.buffer.write(solve.dumps(output).encode("utf-8"))
    except (solve.InvalidInstance, OSError, ValueError) as error:
        print(f"Rejected: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
