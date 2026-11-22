# Recovered arena validation instance

`../instances/arena.json` is the platform arena's complete 1,152-row contract
at seed 11 and period 8. It has eight axes, five behavior components, and four
weight-one hyperedges. It runs through the ordinary solver and Lean agreement
check with no arena-specific solver path.

## Source and reproducibility

The model was recovered from
[`clpi/idol-sites` at `545eccb3ac605b1246a731bbd609a50d9afdf716`](https://github.com/clpi/idol-sites/blob/545eccb3ac605b1246a731bbd609a50d9afdf716/muse/frontier-before-weights/index.html),
`muse/frontier-before-weights/index.html`, section 6b. The source blob is
`06e822d8cad9c46eaca4d63bba075c1609dd43ef`. Its UTF-8 SHA256 is
`493207f8c6a6cab2220c91f220b0716a0493ea36492775ab631d363490460ff8`.

`arena-model.cjs` contains verbatim pure-function and constant extracts from
that source. The only additions are closing the extracted `SCEN.platform`
record and exporting `hmaBuildInstance`. The platform layout, reachable
successor relation, plan candidates, weight-based selection, and execution
observations use the original functions. The upstream `hmaSolve` implementation
is **not** part of the extract or the agreement oracle.

`provenance.json` records every extracted source range, start/end delimiter,
substring SHA256, the module SHA256, and the raw and compact table receipts.
Given a separately retrieved copy of the pinned HTML, `extract.py` verifies its
full source hash and each range before reproducing the module:

```sh
python3 solver/arena/extract.py /tmp/pinned-index.html > /tmp/arena-model.cjs
cmp solver/arena/arena-model.cjs /tmp/arena-model.cjs
```

The HMA section first appears in the inspected path history at
`e2a168b456d4f05e72af62fb462305bc0a7a4385`; its HMA functions agree with the
chosen source pin. The coordinator file named in the ticket was unavailable.
This is a reconstruction from the published arena model; byte identity with
an unshared coordinator artifact is not claimed.

From the repository root, with Node.js and Python 3.10 or newer:

```sh
node solver/arena/generate-arena.cjs > /tmp/arena.json
cmp solver/instances/arena.json /tmp/arena.json
python3 solver/arena/check.py
```

The offline check verifies the frozen model hash, regenerates the compact
fixture byte for byte, regenerates all original behavior labels, checks their
pinned raw-table SHA256, and decodes every interned observation back to its
original string. Missing Node, any changed receipt, or any disagreement fails
the check. No network service or browser is used. The recorded regeneration
used Node.js v24.22.3; a different runtime must pass the same byte receipts.

To recover the original labels or the complete inverse dictionary:

```sh
node solver/arena/generate-arena.cjs --raw > /tmp/arena-raw.json
node solver/arena/generate-arena.cjs --dictionary /tmp/arena-dictionary.json > /tmp/arena.json
```

The raw table has 21,799,529 bytes and SHA256
`d8719eba53bd3f0143a37597f6c1c555b6c8042adadf987890347041c2bcb865`.
It is regenerated instead of committing repeated 22 MB observation strings.

## Exact encoding

The contract axes are the full product:

| Axis | Values in the stored table |
| --- | --- |
| count | `0`, `4` |
| place | `"scatter"`, `"columns"`, `"floating"`, `"wide"` |
| material | `"stone"`, `"ice"`, `"mixed"` |
| motion | `"off"`, `"h"`, `"v"` |
| wsteps | `"0.4"`, `1` |
| wspecials | `"0.05"`, `1` |
| wentropy | `0`, `"0.5"` |
| wslides | `0`, `1` |

Only the three nonintegral numeric axis labels are relabeled to decimal
strings, after the original model computes its observations. This is an
injective relabeling in each axis; it removes floating-point values from the
solver input while preserving every equality of configurations. The weights
of the **hyperedges** remain positive integers, all one.

For each component separately, exact original observation strings are sorted
and interned to integers. No hash is used as semantic equality. `layout` has
38 distinct values, `successors` 36, `plan` 25, `selection` 40, and `execution`
18. The dictionary keyed by component and integer is lossless. Liveness only
compares the values of the same component across configurations, so this
encoding preserves all relevant equalities. The raw-label regeneration and
decode check make that correspondence executable evidence.

## Expected result and scope

The recovered upstream solver's result was `{count}`, with `rho = (4, 5)`.
Its full minimal list was `{count}`, `{material}`, `{motion}`, `{place}`, each
with `rho = (4, 5)`. All five components are live under the full axis set, all
four hyperedges are engaged, and all eight axes are emergent-dead. The four
weight axes occur in no minimal sufficient set. These historical executable
results are context, not the oracle for this repository: the gate independently
checks the implementation against its Lean definitions.

This fixture is a finite qualification of the published arena model at one
seed and period. It does not establish all seeds, all periods, universal
planning optimality, successful reversal of every action, or fidelity of the
arena to physical systems. The original planner itself considers three
search profiles and has a 20,000-pop guard. Its existing choices are preserved
as observation-producing source, not promoted to new theorems.
