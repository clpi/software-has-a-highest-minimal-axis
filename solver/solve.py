#!/usr/bin/env python3
"""Deterministic finite-table implementation of SPEC.md sections 2--4 and 7.

The implementation is checked against Hma.lean by the separate validation gate.
It is not a proof of this Python program. JSON values are typed finite labels:
null, booleans, integers, and strings; in particular false and 0 stay distinct.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


class InvalidInstance(ValueError):
    """The input does not denote an unambiguous instance in the table format."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise InvalidInstance(message)


def text(value: Any, where: str, *, nonempty: bool = False) -> str:
    require(type(value) is str, f"{where}: expected a string")
    require(not nonempty or bool(value), f"{where}: empty names are not allowed")
    try:
        value.encode("utf-8", errors="strict")
    except UnicodeEncodeError as error:
        raise InvalidInstance(f"{where}: invalid Unicode surrogate") from error
    return value


def scalar_key(value: Any) -> tuple[int, Any]:
    """An injective, totally ordered representation of allowed JSON scalars."""
    if value is None:
        return (0, 0)
    if type(value) is bool:
        return (1, int(value))
    if type(value) is int:
        return (2, value)
    if type(value) is str:
        return (3, text(value, "scalar"))
    raise InvalidInstance("finite values must be null, boolean, integer, or string")


def fields(value: Any, expected: set[str], where: str) -> dict[str, Any]:
    require(type(value) is dict, f"{where}: expected an object")
    require(set(value) == expected, f"{where}: expected fields {sorted(expected)}")
    return value


def sequence(value: Any, where: str) -> list[Any]:
    require(type(value) is list, f"{where}: expected a list")
    return value


def unique_names(values: Any, where: str) -> list[str]:
    names = [text(v, where, nonempty=True) for v in sequence(values, where)]
    require(len(set(names)) == len(names), f"{where}: duplicate name")
    return names


def normalize(data: Any) -> dict[str, Any]:
    """Validate and canonicalize a table without changing any scalar identity.

    Axes, components, edge members, and the edge family denote sets. Duplicate
    declarations are rejected rather than allowed to change Lean list counts.
    Contract configurations must be unique, making the behavior table a function.
    """
    fields(data, {"schema", "name", "axes", "components", "contract", "hyperedges"}, "instance")
    require(type(data["schema"]) is int and data["schema"] == 1, "unsupported schema")
    name = text(data["name"], "name", nonempty=True)
    axes = sequence(data["axes"], "axes")
    names: list[str] = []
    domains: list[list[Any]] = []
    domain_keys: list[set[tuple[int, Any]]] = []
    for i, axis in enumerate(axes):
        fields(axis, {"name", "values"}, f"axes[{i}]")
        names.append(text(axis["name"], f"axes[{i}].name", nonempty=True))
        values = sequence(axis["values"], f"axes[{i}].values")
        keys = [scalar_key(v) for v in values]
        require(len(set(keys)) == len(keys), f"axes[{i}]: duplicate finite value")
        domains.append(sorted(values, key=scalar_key))
        domain_keys.append(set(keys))
    require(len(set(names)) == len(names), "axes: duplicate name")
    comps = unique_names(data["components"], "components")
    axis_order = sorted(range(len(names)), key=names.__getitem__)
    comp_order = sorted(range(len(comps)), key=comps.__getitem__)
    canonical_axes = [{"name": names[i], "values": domains[i]} for i in axis_order]
    canonical_comps = [comps[i] for i in comp_order]
    known_comps = set(comps)
    rows: list[dict[str, Any]] = []
    seen_rows: set[tuple[tuple[int, Any], ...]] = set()
    for i, row in enumerate(sequence(data["contract"], "contract")):
        fields(row, {"axes", "behavior"}, f"contract[{i}]")
        values = sequence(row["axes"], f"contract[{i}].axes")
        behavior = sequence(row["behavior"], f"contract[{i}].behavior")
        require(len(values) == len(names), f"contract[{i}]: incomplete axis vector")
        require(len(behavior) == len(comps), f"contract[{i}]: incomplete behavior vector")
        keys = tuple(scalar_key(v) for v in values)
        for j, key in enumerate(keys):
            require(key in domain_keys[j], f"contract[{i}]: value outside axis {names[j]!r}")
        for value in behavior:
            scalar_key(value)
        require(keys not in seen_rows, f"contract[{i}]: duplicate configuration")
        seen_rows.add(keys)
        rows.append({"axes": [values[j] for j in axis_order],
                     "behavior": [behavior[j] for j in comp_order]})
    rows.sort(key=lambda row: tuple(scalar_key(v) for v in row["axes"]))
    edges: list[dict[str, Any]] = []
    seen_edges: set[tuple[str, ...]] = set()
    for i, edge in enumerate(sequence(data["hyperedges"], "hyperedges")):
        fields(edge, {"components", "weight"}, f"hyperedges[{i}]")
        members = sorted(unique_names(edge["components"], f"hyperedges[{i}].components"))
        require(set(members) <= known_comps, f"hyperedges[{i}]: unknown component")
        weight = edge["weight"]
        require(type(weight) is int and weight >= 0, f"hyperedges[{i}]: weight must be a natural number")
        require(len(members) < 2 or weight > 0, f"hyperedges[{i}]: interacting edge requires positive weight")
        key = tuple(members)
        require(key not in seen_edges, f"hyperedges[{i}]: repeated edge set")
        seen_edges.add(key)
        edges.append({"components": members, "weight": weight})
    edges.sort(key=lambda edge: edge["components"])
    return {"schema": 1, "name": name, "axes": canonical_axes,
            "components": canonical_comps, "contract": rows, "hyperedges": edges}


def encode(instance: Any) -> dict[str, Any]:
    """Embed finite scalar labels into Nat for the Lean instance adapter.

    Encoding is injective across the four scalar types. Only equality of values
    matters to Hma; names are represented by positions in their sorted lists.
    """
    data = normalize(instance)
    keys = {scalar_key(v) for axis in data["axes"] for v in axis["values"]}
    keys.update(scalar_key(v) for row in data["contract"] for v in row["behavior"])
    codes = {key: i for i, key in enumerate(sorted(keys))}
    comp_ids = {name: i for i, name in enumerate(data["components"])}
    return {
        "axes": [axis["name"] for axis in data["axes"]],
        "components": data["components"],
        "ranges": [[codes[scalar_key(v)] for v in axis["values"]] for axis in data["axes"]],
        "contract": [{"axes": [codes[scalar_key(v)] for v in row["axes"]],
                      "behavior": [codes[scalar_key(v)] for v in row["behavior"]]}
                     for row in data["contract"]],
        "hyperedges": [{"components": [comp_ids[name] for name in edge["components"]],
                        "weight": edge["weight"]} for edge in data["hyperedges"]],
    }


def solve(instance: Any) -> dict[str, Any]:
    data = normalize(instance)
    encoded = encode(data)
    names = encoded["axes"]
    comps = encoded["components"]
    rows = encoded["contract"]
    count = 1 << len(names)
    full = count - 1
    live_masks = [0] * count

    # Each unordered row pair contributes precisely its differing components
    # to its differing-axis mask. Identity pairs never witness a change.
    for i, left in enumerate(rows):
        for right in rows[i + 1:]:
            changed_axes = 0
            for j, (a, b) in enumerate(zip(left["axes"], right["axes"])):
                if a != b:
                    changed_axes |= 1 << j
            changed_components = 0
            for j, (a, b) in enumerate(zip(left["behavior"], right["behavior"])):
                if a != b:
                    changed_components |= 1 << j
            live_masks[changed_axes] |= changed_components

    # A pair is an S-variation exactly when its differing-axis mask is inside S.
    # This subset closure computes the union of witnesses for every S.
    for j in range(len(names)):
        bit = 1 << j
        for mask in range(count):
            if mask & bit:
                live_masks[mask] |= live_masks[mask ^ bit]

    return result_from_live_masks(data, live_masks)


def result_from_live_masks(instance: Any, live_masks: list[int]) -> dict[str, Any]:
    """Render the complete finite result from an already computed liveness table.

    This shared output routine performs no row-pair search. The batch and
    incremental algorithms supply their independently maintained live masks.
    Rendering the explicit subset table and minimal list still costs exponential
    space/output in the number of axes; incrementality does not remove that cost.
    """
    data = normalize(instance)
    names = [axis["name"] for axis in data["axes"]]
    comps = data["components"]
    rows = data["contract"]
    count = 1 << len(names)
    full = count - 1
    require(type(live_masks) is list and len(live_masks) == count,
            "liveness table: incomplete subset coverage")
    require(all(type(mask) is int and 0 <= mask < (1 << len(comps))
                for mask in live_masks), "liveness table: invalid component mask")
    comp_ids = {name: i for i, name in enumerate(comps)}
    edge_masks = [sum(1 << comp_ids[name] for name in edge["components"])
                  for edge in data["hyperedges"]]
    engaged_ids: list[list[int]] = []
    mu: list[int] = []
    lam = [mask.bit_count() for mask in live_masks]
    for live_mask in live_masks:
        engaged = [i for i, edge in enumerate(data["hyperedges"])
                   if len(edge["components"]) >= 2 and edge_masks[i] & live_mask == edge_masks[i]]
        engaged_ids.append(engaged)
        mu.append(sum(data["hyperedges"][i]["weight"] for i in engaged))
    sufficient = [value == mu[full] for value in mu]

    # Monotonicity makes one-axis deletions enough: any sufficient proper
    # subset lies inside a sufficient one-axis deletion. All 2^|A| subsets
    # have still been enumerated. The Lean checker independently checks the
    # full proper-subset definition, not this implementation shortcut.
    minimal = [sufficient[mask] and not any(sufficient[mask ^ (1 << i)]
               for i in range(len(names)) if mask & (1 << i)) for mask in range(count)]
    minimal_masks = [mask for mask in range(count) if minimal[mask]]

    def axis_list(mask: int) -> list[str]:
        return [name for i, name in enumerate(names) if mask & (1 << i)]

    best_rho = max((mu[mask], lam[mask]) for mask in minimal_masks)
    highest = [minimal[mask] and (mu[mask], lam[mask]) == best_rho for mask in range(count)]
    selected = min((mask for mask in minimal_masks if highest[mask]), key=axis_list)
    minimal_masks.sort(key=axis_list)

    def live_list(mask: int) -> list[str]:
        return [name for i, name in enumerate(comps) if live_masks[mask] & (1 << i)]

    def engaged_list(mask: int) -> list[dict[str, Any]]:
        return [data["hyperedges"][i] for i in engaged_ids[mask]]

    dispositions = []
    for i, name in enumerate(names):
        bit = 1 << i
        membership = ("chosen" if selected & bit else
                      "alternative" if any(mask & bit for mask in minimal_masks) else "none")
        dispositions.append({"axis": name, "membership": membership,
                             "emergent_dead": live_masks[full ^ bit] == live_masks[full]})
    return {
        "schema": 1,
        "name": data["name"],
        "axes": names,
        "components": comps,
        "chosen": {"axes": axis_list(selected), "rho": [mu[selected], lam[selected]]},
        "full": {"mu": mu[full], "live": live_list(full), "engaged": engaged_list(full)},
        "minimal": [{"axes": axis_list(mask), "rho": [mu[mask], lam[mask]]} for mask in minimal_masks],
        "dispositions": dispositions,
        "counts": {"axes": len(names), "components": len(comps), "contract_rows": len(rows),
                   "hyperedges": len(edge_masks), "subsets": count,
                   "row_pairs": len(rows) * (len(rows) - 1) // 2},
        "subsets": [{"axes": axis_list(mask), "rho": [mu[mask], lam[mask]],
                     "live": live_list(mask), "engaged": engaged_list(mask),
                     "sufficient": sufficient[mask], "minimal": minimal[mask],
                     "highest": highest[mask]} for mask in range(count)],
    }


def dumps(value: Any) -> str:
    """The byte contract: UTF-8, sorted keys, compact separators, one newline."""
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"), allow_nan=False) + "\n"


def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    obj: dict[str, Any] = {}
    for key, value in pairs:
        require(key not in obj, f"duplicate JSON key: {key!r}")
        obj[key] = value
    return obj


def reject_constant(value: str) -> None:
    raise InvalidInstance(f"non-finite JSON number: {value}")


def loads(source: str) -> dict[str, Any]:
    return normalize(json.loads(source, object_pairs_hook=unique_object, parse_constant=reject_constant))


def load(path: str | Path) -> dict[str, Any]:
    return loads(Path(path).read_text(encoding="utf-8"))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("instance", help="finite table in schema 1 JSON")
    args = parser.parse_args()
    try:
        result = solve(load(args.instance))
        sys.stdout.buffer.write(dumps(result).encode("utf-8"))
    except (InvalidInstance, OSError, ValueError) as error:
        print(f"Rejected: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
