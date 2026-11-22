#!/usr/bin/env python3
"""Deterministic exhaustive solver for the HMA table contract."""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from itertools import combinations
import json
import sys
from typing import Any

from model import InputError, Table, encode_table, load_table


@dataclass(frozen=True)
class State:
    axes: tuple[int, ...]
    live: tuple[int, ...]
    engaged: tuple[int, ...]
    mu: int
    lam: int

    @property
    def rho(self) -> tuple[int, int]:
        return (self.mu, self.lam)


def all_subsets(axis_count: int) -> list[tuple[int, ...]]:
    return [subset
            for size in range(axis_count + 1)
            for subset in combinations(range(axis_count), size)]


def solve(table: Table) -> dict[str, Any]:
    encoded = encode_table(table)
    axes = encoded.axis_names
    components = encoded.component_names
    rows = encoded.configurations
    behaviors = encoded.behaviors
    subsets = all_subsets(len(axes))
    row_pairs = list(combinations(range(len(rows)), 2))

    states: dict[tuple[int, ...], State] = {}
    for subset in subsets:
        selected = set(subset)
        live: list[int] = []
        for component_index in range(len(components)):
            varies = False
            for left, right in row_pairs:
                if (behaviors[left][component_index] != behaviors[right][component_index]
                        and all(rows[left][axis_index] == rows[right][axis_index]
                                for axis_index in range(len(axes))
                                if axis_index not in selected)):
                    varies = True
                    break
            if varies:
                live.append(component_index)
        live_set = set(live)

        engaged_edges: list[int] = []
        mu = 0
        for edge_index, (edge, weight) in enumerate(encoded.edges):
            if len(edge) >= 2 and all(component_index in live_set for component_index in edge):
                engaged_edges.append(edge_index)
                mu += weight
        states[subset] = State(subset, tuple(live), tuple(engaged_edges), mu, len(live))

    all_axes = tuple(range(len(axes)))
    full_state = states[all_axes]
    minimal_states: list[State] = []
    for state in states.values():
        if state.mu != full_state.mu:
            continue
        selected = set(state.axes)
        has_sufficient_proper_subset = any(
            len(other.axes) < len(state.axes)
            and set(other.axes).issubset(selected)
            and other.mu == full_state.mu
            for other in states.values()
        )
        if not has_sufficient_proper_subset:
            minimal_states.append(state)

    if not minimal_states:
        # The Lean theorem Hma.highestexists says this cannot happen for a
        # valid instance. Treat a violation as an implementation failure.
        raise RuntimeError("no minimal sufficient subset found")

    highest_rho = max(state.rho for state in minimal_states)
    highest_states = [state for state in minimal_states if state.rho == highest_rho]
    selected_state = min(highest_states, key=lambda state: tuple(axes[i] for i in state.axes))
    minimal_states.sort(key=lambda state: (-state.mu, -state.lam, tuple(axes[i] for i in state.axes)))

    live_all = [components[i] for i in full_state.live]
    engaged_all = [
        {
            "components": [components[i] for i in encoded.edges[edge_index][0]],
            "weight": encoded.edges[edge_index][1],
        }
        for edge_index in full_state.engaged
    ]
    chosen_set = set(selected_state.axes)
    minimal_axes = [set(state.axes) for state in minimal_states]
    dispositions: dict[str, dict[str, Any]] = {}
    for axis_index, axis_name in enumerate(axes):
        if axis_index in chosen_set:
            membership = "in-selected"
        elif any(axis_index in members for members in minimal_axes):
            membership = "in-other-minimal"
        else:
            membership = "in-none"
        without_axis = tuple(i for i in all_axes if i != axis_index)
        emergent_dead = states[without_axis].live == full_state.live
        dispositions[axis_name] = {
            "membership": membership,
            "emergent_dead": emergent_dead,
        }

    return {
        "format": "hma-result-v1",
        "instance": table.name,
        "selected": [axes[i] for i in selected_state.axes],
        "selected_rho": {"mu": selected_state.mu, "lambda": selected_state.lam},
        "mu_all": full_state.mu,
        "live_all": live_all,
        "engaged_all": engaged_all,
        "minimal_sufficient": [
            {
                "axes": [axes[i] for i in state.axes],
                "rho": {"mu": state.mu, "lambda": state.lam},
            }
            for state in minimal_states
        ],
        "axis_dispositions": dispositions,
        "counts": {
            "axes": len(axes),
            "contract_rows": len(rows),
            "behavior_cells": len(rows) * len(components),
            "hyperedges": len(encoded.edges),
            "subsets": len(subsets),
            "contract_row_pairs": len(row_pairs),
        },
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("table", help="path to an hma-table-v1 JSON file")
    args = parser.parse_args(argv)
    try:
        result = solve(load_table(args.table))
    except (InputError, RuntimeError) as exc:
        print(f"hma-solver: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2, allow_nan=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
