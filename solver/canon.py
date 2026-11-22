#!/usr/bin/env python3
"""Render a solver run in the canonical lines of the gate.

Reads one solver output (the JSON the solver prints for one
instance) and the instance file it ran on, and prints the
canonical expectation lines for that instance: the same lines
the Lean expectations program (proof/Expect.lean) prints from
the proved definitions. The gate diffs the two renderings.

The instance file supplies the declared orders the canonical
form uses: components in instance order, hyperedges in
instance order with members in component order, axes in
instance order. The solver prints live sets and edge members
in name order; this renderer re-orders them to the declared
orders so the comparison is about the computed values, not
about presentation order.

Usage: python3 canon.py <solver-output.json> <instance.json>

Python 3, standard library only.
"""

import json
import sys


def joined(names):
    return " ".join(names) if names else "-"


def engaged_text(entries, comps):
    if not entries:
        return "-"
    parts = []
    for entry in entries:
        members = [c for c in comps if c in entry["components"]]
        parts.append(",".join(members) + ":" + str(entry["weight"]))
    return ";".join(parts)


def live_text(names, comps):
    return joined([c for c in comps if c in names])


def main(argv):
    if len(argv) != 3:
        sys.stderr.write(
            "usage: python3 canon.py <solver-output.json> "
            "<instance.json>\n")
        return 2
    with open(argv[1], "r", encoding="utf-8") as handle:
        out = json.load(handle)
    with open(argv[2], "r", encoding="utf-8") as handle:
        inst = json.load(handle)

    comps = list(inst["components"])
    axes = [axis["name"] for axis in inst["axes"]]
    lines = []
    lines.append("instance " + out["instance"])
    lines.append("returned " + joined(out["returned_vector"]))
    lines.append("rho %d %d" % tuple(out["rho_returned"]))
    lines.append("mu-full %d" % out["mu_full"])
    lines.append("lambda-full %d" % out["lambda_full"])
    lines.append("live-full " + live_text(out["live_full"], comps))
    lines.append("engaged-full " + engaged_text(out["engaged_full"], comps))
    lines.append("live-returned " + live_text(out["live_returned"], comps))
    lines.append(
        "engaged-returned " + engaged_text(out["engaged_returned"], comps))
    minimal = sorted(
        out["minimal_sufficient"],
        key=lambda item: (-item["rho"][0], -item["rho"][1], item["vector"]))
    lines.append("minimal-count %d" % len(minimal))
    for entry in minimal:
        lines.append(
            "minimal %s | %d %d | %s | %s" % (
                joined(entry["vector"]),
                entry["rho"][0],
                entry["rho"][1],
                live_text(entry["live"], comps),
                engaged_text(entry["engaged"], comps)))
    for name in axes:
        disp = out["axis_dispositions"][name]
        lines.append(
            "axis %s | %s | dead %s" % (
                name,
                disp["disposition"],
                "true" if disp["emergent_dead"] else "false"))
    counts = out["counts"]
    lines.append(
        "counts %d %d %d" % (
            counts["subsets_enumerated"],
            counts["contract_rows"],
            counts["pairs_scanned"]))
    lines.append("end")
    sys.stdout.write("\n".join(lines) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
