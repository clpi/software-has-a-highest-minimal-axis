#!/usr/bin/env python3
"""Independent brute-force checker for the Highest Minimal Axis solver.

This is a deliberately separate code path from solver.py: it shares no
helper functions with the solver's core and does not import it. Where the
solver uses the section 7 difference-set shortcut, this checker applies
the section 2 definition literally, as a naive triple loop:

    for each subset S of the axes
      for each component b
        for each ordered pair (x, x') of contract rows
          b is live under S iff x and x' agree on every axis outside S
          (checked axis by axis) and b's values at x and x' differ.

It then recomputes mu, lambda, rho, the minimal sufficient list and the
highest minimal set (maximal rho, ties broken by the lexicographically
smallest sorted axis-name list) directly from those live sets.

Usage: python3 checker.py <instance.json>
Prints one JSON object to stdout. Python 3, standard library only.
"""

import itertools
import json
import sys


def main(argv):
    if len(argv) != 2:
        sys.stderr.write("usage: python3 checker.py <instance.json>\n")
        return 2
    with open(argv[1], "r", encoding="utf-8") as handle:
        inst = json.load(handle)

    axis_names = [axis["name"] for axis in inst["axes"]]
    rows = inst["contract"]
    comps = list(inst["components"])
    table = inst["behavior"]
    edges = [
        (list(edge["components"]), edge.get("weight", 1))
        for edge in inst.get("hyperedges", [])
    ]
    n = len(axis_names)

    all_subsets = []
    for size in range(n + 1):
        for combo in itertools.combinations(range(n), size):
            all_subsets.append(combo)

    live_by_key = {}
    mu_by_key = {}
    lambda_by_key = {}
    pair_checks = 0
    for combo in all_subsets:
        chosen = set(combo)
        live = []
        for comp in comps:
            found = False
            for i in range(len(rows)):
                for j in range(len(rows)):
                    pair_checks += 1
                    # agree off S, checked axis by axis
                    agree = True
                    for k in range(n):
                        if k not in chosen and rows[i][k] != rows[j][k]:
                            agree = False
                            break
                    if agree and table[comp][i] != table[comp][j]:
                        found = True
                        break
                if found:
                    break
            if found:
                live.append(comp)
        key = ",".join(sorted(axis_names[k] for k in combo))
        live_by_key[key] = sorted(live)
        total = 0
        for members, weight in edges:
            if len(set(members)) >= 2 and set(members) <= set(live):
                total += weight
        mu_by_key[key] = total
        lambda_by_key[key] = len(live)

    full_key = ",".join(sorted(axis_names))
    mu_full = mu_by_key[full_key]

    def key_of(combo):
        return ",".join(sorted(axis_names[k] for k in combo))

    sufficient = [
        combo for combo in all_subsets if mu_by_key[key_of(combo)] == mu_full
    ]
    minimal = []
    for combo in sufficient:
        combo_set = set(combo)
        has_sufficient_proper = False
        for other in sufficient:
            if set(other) < combo_set:
                has_sufficient_proper = True
                break
        if not has_sufficient_proper:
            minimal.append(combo)

    minimal_list = []
    for combo in minimal:
        key = key_of(combo)
        minimal_list.append({
            "vector": sorted(axis_names[k] for k in combo),
            "rho": [mu_by_key[key], lambda_by_key[key]],
            "live": live_by_key[key],
        })
    minimal_list.sort(key=lambda item: (
        -item["rho"][0], -item["rho"][1], item["vector"]))

    highest = None
    for entry in minimal_list:
        if highest is None:
            highest = entry
            continue
        if entry["rho"] > highest["rho"]:
            highest = entry
        elif entry["rho"] == highest["rho"] \
                and entry["vector"] < highest["vector"]:
            highest = entry

    full_live = live_by_key[full_key]
    engaged_full = []
    for members, weight in edges:
        if len(set(members)) >= 2 and set(members) <= set(full_live):
            engaged_full.append({
                "components": sorted(set(members)), "weight": weight})

    result = {
        "instance": inst.get("name", ""),
        "highest_vector": highest["vector"] if highest else None,
        "rho_highest": highest["rho"] if highest else None,
        "mu_full": mu_full,
        "live_full": full_live,
        "engaged_full": engaged_full,
        "live_by_subset": live_by_key,
        "mu_by_subset": mu_by_key,
        "minimal_sufficient": minimal_list,
        "counts": {
            "subsets_enumerated": len(all_subsets),
            "contract_rows": len(rows),
            "pair_component_checks": pair_checks,
        },
    }
    sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
