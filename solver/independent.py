"""Separate, deliberately direct brute-force oracle for the X control."""
from __future__ import annotations

from itertools import combinations
from typing import Any

from model import Table, canonical


def brute_force(table: Table) -> dict[str, Any]:
    """Enumerate subsets and contract-row pairs directly from the JSON table."""
    axis_names = sorted(axis.name for axis in table.axes)
    component_names = list(table.components)
    all_subsets = [
        tuple(subset)
        for size in range(len(axis_names) + 1)
        for subset in combinations(axis_names, size)
    ]

    def live_for(subset: tuple[str, ...]) -> list[str]:
        varying_axes = set(subset)
        live_components: list[str] = []
        for component in component_names:
            found = False
            for left_index in range(len(table.contract)):
                for right_index in range(left_index + 1, len(table.contract)):
                    left = table.contract[left_index]
                    right = table.contract[right_index]
                    unchanged_outside = all(
                        canonical(left.configuration[axis]) == canonical(right.configuration[axis])
                        for axis in axis_names
                        if axis not in varying_axes
                    )
                    if (unchanged_outside
                            and canonical(left.behavior[component]) != canonical(right.behavior[component])):
                        found = True
                        break
                if found:
                    break
            if found:
                live_components.append(component)
        return live_components

    def measure(subset: tuple[str, ...]) -> tuple[list[str], list[tuple[tuple[str, ...], int]], int, int]:
        live = live_for(subset)
        live_set = set(live)
        engaged: list[tuple[tuple[str, ...], int]] = []
        mu = 0
        for edge in table.edges:
            if len(edge.components) >= 2 and all(vertex in live_set for vertex in edge.components):
                engaged.append((edge.components, edge.weight))
                mu += edge.weight
        return live, engaged, mu, len(live)

    measurements = {subset: measure(subset) for subset in all_subsets}
    full_mu = measurements[tuple(axis_names)][2]
    minimal: list[dict[str, Any]] = []
    for subset in all_subsets:
        mu = measurements[subset][2]
        if mu != full_mu:
            continue
        selected = set(subset)
        proper_sufficient = any(
            len(other) < len(subset)
            and set(other).issubset(selected)
            and measurements[other][2] == full_mu
            for other in all_subsets
        )
        if not proper_sufficient:
            minimal.append({
                "axes": list(subset),
                "rho": {"mu": mu, "lambda": measurements[subset][3]},
            })

    minimal.sort(key=lambda item: (
        -item["rho"]["mu"],
        -item["rho"]["lambda"],
        tuple(item["axes"]),
    ))
    if not minimal:
        raise AssertionError("independent oracle found no minimal sufficient subset")
    return {
        "selected": minimal[0]["axes"],
        "selected_rho": minimal[0]["rho"],
        "mu_all": full_mu,
        "minimal_sufficient": minimal,
    }
