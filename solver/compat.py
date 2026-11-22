"""Adapters for the hma-table-v1 / hma-result-v1 interface already on main.

There is one computation engine. Arbitrary legacy JSON values become injective
canonical JSON strings, preserving the old equality relation without imposing
numeric or object meaning on Hma's finite labels.
"""
from __future__ import annotations

from typing import Any

from model import Axis, Edge, Row, Table, canonical


def instance(table: Table) -> dict[str, Any]:
    axes = [axis.name for axis in table.axes]
    return {
        "schema": 1, "name": table.name,
        "axes": [{"name": axis.name, "values": [canonical(v) for v in axis.values]}
                 for axis in table.axes],
        "components": list(table.components),
        "contract": [{"axes": [canonical(row.configuration[a]) for a in axes],
                      "behavior": [canonical(row.behavior[b]) for b in table.components]}
                     for row in table.contract],
        "hyperedges": [{"components": list(edge.components), "weight": edge.weight}
                       for edge in table.edges],
    }


def table(source: dict[str, Any]) -> Table:
    """Expose a schema-1 fixture through the existing named-column interface."""
    axes = tuple(Axis(a["name"], tuple(a["values"])) for a in source["axes"])
    comps = tuple(source["components"])
    return Table(source["name"], axes, comps,
                 tuple(Row(dict(zip((a.name for a in axes), row["axes"])),
                           dict(zip(comps, row["behavior"]))) for row in source["contract"]),
                 tuple(Edge(tuple(e["components"]), e["weight"]) for e in source["hyperedges"]))


def result(table: Table, output: dict[str, Any]) -> dict[str, Any]:
    """Preserve public output names, rho ordering, and declared component order."""
    dispositions = {d["axis"]: d for d in output["dispositions"]}
    members = {tuple(e["components"]) for e in output["full"]["engaged"]}
    membership = {"chosen": "in-selected", "alternative": "in-other-minimal", "none": "in-none"}
    minima = sorted(output["minimal"], key=lambda m: (-m["rho"][0], -m["rho"][1], m["axes"]))
    return {
        "format": "hma-result-v1", "instance": table.name,
        "selected": output["chosen"]["axes"],
        "selected_rho": dict(zip(("mu", "lambda"), output["chosen"]["rho"])),
        "mu_all": output["full"]["mu"],
        "live_all": [b for b in table.components if b in output["full"]["live"]],
        "engaged_all": [{"components": list(e.components), "weight": e.weight}
                        for e in table.edges if tuple(sorted(e.components)) in members],
        "minimal_sufficient": [{"axes": m["axes"], "rho": dict(zip(("mu", "lambda"), m["rho"]))}
                               for m in minima],
        "axis_dispositions": {a: {"membership": membership[dispositions[a]["membership"]],
                                  "emergent_dead": dispositions[a]["emergent_dead"]}
                              for a in table.axis_names},
        "counts": {"axes": len(table.axes), "contract_rows": len(table.contract),
                   "behavior_cells": len(table.contract) * len(table.components),
                   "hyperedges": len(table.edges), "subsets": 1 << len(table.axes),
                   "contract_row_pairs": len(table.contract) * (len(table.contract) - 1) // 2},
    }
