#!/usr/bin/env python3
"""Highest Minimal Axis solver.

Implements SPEC.md (the specification at the root of this
repository) sections 2-4 and the solver contract of section 7,
exactly as defined there:

  - live(b, S): some pair of contract rows agreeing off S gives b different
    values. Computed by the difference-set rule of section 7: with
    D(x, x') the set of axes where two rows differ, live(b, S) holds iff
    some pair has D(x, x') a subset of S and b differing on that pair.
  - Live(S): the set of components live under S.
  - engaged(S): hyperedges of size >= 2 entirely inside Live(S).
  - mu(S): sum of weights of engaged(S). lambda(S) = |Live(S)|.
    rho(S) = (mu(S), lambda(S)), lexicographic.
  - sufficient(S): mu(S) = mu(A). minimal(S): sufficient and no proper
    subset sufficient. Highest: maximal rho among minimal sufficient sets;
    ties beyond rho break by the lexicographically smallest sorted
    axis-name list (section 7), so the output is a deterministic function
    of the instance.
  - emergent-dead(a): Live(A without a) = Live(A) (section 4 definition).

Usage: python3 solver.py <instance.json>
Prints one JSON object to stdout (sorted keys, fixed formatting), so the
same instance file always yields byte-identical output.

Python 3, standard library only.
"""

import itertools
import json
import sys


def load_instance(path):
    with open(path, "r", encoding="utf-8") as handle:
        inst = json.load(handle)

    axes = inst["axes"]
    axis_names = [axis["name"] for axis in axes]
    if len(set(axis_names)) != len(axis_names):
        raise ValueError("axis names must be unique")
    axis_values = {axis["name"]: list(axis["values"]) for axis in axes}

    contract = [list(row) for row in inst["contract"]]
    for row in contract:
        if len(row) != len(axis_names):
            raise ValueError("each contract row must give one value per axis")
        for name, value in zip(axis_names, row):
            if value not in axis_values[name]:
                raise ValueError(
                    "contract value %r is not in the value list of axis %r"
                    % (value, name)
                )

    components = list(inst["components"])
    if len(set(components)) != len(components):
        raise ValueError("component names must be unique")

    behavior = inst["behavior"]
    for comp in components:
        if comp not in behavior:
            raise ValueError("behavior table is missing component %r" % comp)
        if len(behavior[comp]) != len(contract):
            raise ValueError(
                "behavior row for component %r must have one value per "
                "contract row" % comp
            )

    hyperedges = []
    for edge in inst.get("hyperedges", []):
        members = list(edge["components"])
        for member in members:
            if member not in components:
                raise ValueError(
                    "hyperedge mentions unknown component %r" % member
                )
        weight = edge.get("weight", 1)
        if len(set(members)) >= 2:
            if not isinstance(weight, int) or isinstance(weight, bool) \
                    or weight <= 0:
                raise ValueError(
                    "hyperedge weight must be a positive integer on "
                    "hyperedges of size at least 2"
                )
        hyperedges.append({"components": members, "weight": weight})

    return {
        "name": inst.get("name", ""),
        "axis_names": axis_names,
        "contract": contract,
        "components": components,
        "behavior": behavior,
        "hyperedges": hyperedges,
    }


def solve(inst):
    axis_names = inst["axis_names"]
    contract = inst["contract"]
    components = inst["components"]
    behavior = inst["behavior"]
    hyperedges = inst["hyperedges"]
    n_axes = len(axis_names)
    n_rows = len(contract)

    # Pair scan (section 7 difference-set rule). Each unordered pair of
    # distinct contract rows is scanned once: record the set of axes where
    # the rows differ and the set of components whose values differ.
    pair_diffs = []  # list of (frozenset of axis indices, frozenset of comps)
    pairs_scanned = 0
    for i, j in itertools.combinations(range(n_rows), 2):
        pairs_scanned += 1
        diff_axes = frozenset(
            k for k in range(n_axes) if contract[i][k] != contract[j][k]
        )
        diff_comps = frozenset(
            comp for comp in components
            if behavior[comp][i] != behavior[comp][j]
        )
        pair_diffs.append((diff_axes, diff_comps))

    def live_set(subset_mask):
        subset = frozenset(
            k for k in range(n_axes) if subset_mask & (1 << k)
        )
        live = set()
        for diff_axes, diff_comps in pair_diffs:
            if diff_axes <= subset:
                live |= diff_comps
        return live

    def engaged_edges(live):
        engaged = []
        for edge in hyperedges:
            members = set(edge["components"])
            if len(members) >= 2 and members <= live:
                engaged.append(edge)
        return engaged

    def measures(subset_mask):
        live = live_set(subset_mask)
        engaged = engaged_edges(live)
        mu = sum(edge["weight"] for edge in engaged)
        return live, engaged, mu, len(live)

    # Enumerate all subsets of A.
    subsets_enumerated = 0
    per_subset = {}  # mask -> (live, engaged, mu, lambda)
    for mask in range(1 << n_axes):
        subsets_enumerated += 1
        per_subset[mask] = measures(mask)

    full_mask = (1 << n_axes) - 1
    full_live, full_engaged, full_mu, full_lambda = per_subset[full_mask]

    def is_sufficient(mask):
        return per_subset[mask][2] == full_mu

    def proper_submask_exists(mask, predicate):
        sub = (mask - 1) & mask
        while True:
            if sub != mask and predicate(sub):
                return True
            if sub == 0:
                return False
            sub = (sub - 1) & mask

    minimal_masks = []
    for mask in range(1 << n_axes):
        if not is_sufficient(mask):
            continue
        if proper_submask_exists(mask, is_sufficient):
            continue
        minimal_masks.append(mask)

    def sorted_names(mask):
        return sorted(
            axis_names[k] for k in range(n_axes) if mask & (1 << k)
        )

    def rho_of(mask):
        entry = per_subset[mask]
        return (entry[2], entry[3])

    # Highest: maximal rho; ties beyond rho break by the lexicographically
    # smallest sorted axis-name list (section 7).
    best_mask = None
    for mask in minimal_masks:
        if best_mask is None:
            best_mask = mask
            continue
        rho_new, rho_best = rho_of(mask), rho_of(best_mask)
        if rho_new > rho_best:
            best_mask = mask
        elif rho_new == rho_best and sorted_names(mask) < sorted_names(best_mask):
            best_mask = mask

    minimal_sufficient = []
    for mask in minimal_masks:
        live, engaged, mu, lam = per_subset[mask]
        minimal_sufficient.append({
            "vector": sorted_names(mask),
            "rho": [mu, lam],
            "live": sorted(live),
            "engaged": [
                {"components": sorted(set(e["components"])),
                 "weight": e["weight"]}
                for e in engaged
            ],
        })
    # Deterministic presentation order: rho descending, then name list.
    minimal_sufficient.sort(key=lambda item: (
        -item["rho"][0], -item["rho"][1], item["vector"]))

    # Axis dispositions (section 4 and section 7). Membership disposition
    # and the emergent-dead flag are reported separately as well as
    # combined, because they are not exclusive: an axis can satisfy the
    # Live-removal definition of emergent-dead while still belonging to
    # some minimal sufficient set (axis c of Instance X is exactly this;
    # see README.md).
    in_some_minimal = set()
    for mask in minimal_masks:
        in_some_minimal |= {
            axis_names[k] for k in range(n_axes) if mask & (1 << k)
        }
    best_names = set(sorted_names(best_mask))
    dispositions = {}
    for k, name in enumerate(axis_names):
        without_mask = full_mask & ~(1 << k)
        emergent_dead = per_subset[without_mask][0] == full_live
        if name in best_names:
            membership = "in the return"
        elif name in in_some_minimal:
            membership = "in some minimal sufficient set only"
        else:
            membership = "in none"
        labels = [membership]
        if emergent_dead:
            labels.append("emergent-dead")
        dispositions[name] = {
            "disposition": membership,
            "emergent_dead": emergent_dead,
            "dispositions": labels,
        }

    best_live, best_engaged, best_mu, best_lambda = per_subset[best_mask]
    return {
        "instance": inst["name"],
        "returned_vector": sorted_names(best_mask),
        "rho_returned": [best_mu, best_lambda],
        "mu_full": full_mu,
        "lambda_full": full_lambda,
        "live_full": sorted(full_live),
        "engaged_full": [
            {"components": sorted(set(e["components"])),
             "weight": e["weight"]}
            for e in full_engaged
        ],
        "live_returned": sorted(best_live),
        "engaged_returned": [
            {"components": sorted(set(e["components"])),
             "weight": e["weight"]}
            for e in best_engaged
        ],
        "minimal_sufficient": minimal_sufficient,
        "axis_dispositions": dispositions,
        "counts": {
            "subsets_enumerated": subsets_enumerated,
            "contract_rows": n_rows,
            "pairs_scanned": pairs_scanned,
        },
    }


def main(argv):
    if len(argv) != 2:
        sys.stderr.write("usage: python3 solver.py <instance.json>\n")
        return 2
    inst = load_instance(argv[1])
    result = solve(inst)
    sys.stdout.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
