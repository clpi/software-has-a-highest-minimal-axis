# Highest Minimal Axis solver

The deterministic solver of the specification's section 7
contract, landed in this repository. Python 3, standard
library only.

## What is claimed, exactly

The solver is an implementation, not a theorem. What is
claimed for it is what the gate checks at the pin: on
Instances X, D, both forms of E, and the arena instance
at seeds 11 and 23, its output agrees line for line with
the values the proved definitions of the core
(`proof/Hma.lean`) compute on the same instances, the
expectations being evaluated from those definitions by
`proof/Expect.lean`; and its output is byte-identical
across two runs on every one of those instances. The
full gate is `proof/gate.sh`; it fails closed on any
disagreement. No claim is made here about instances the
gate does not run.

## Command line

```
python3 solver.py <instance.json>
```

The solver prints one JSON object to stdout and nothing
else, so the same instance file always produces
byte-identical output. It enumerates all subsets of the
axis set and prints its search counts in the output's
counts field: how many subsets were enumerated, how
many contract rows the instance has, and how many
unordered pairs of distinct contract rows were scanned
(once each, under the specification's section 7
difference-set rule). The exact field names of the
output are listed with the output fields below.

## Instance JSON schema (as implemented)

One JSON object:

- `name` (string, optional): instance label, echoed in
  the output.
- `axes` (array, required): one object per axis, in a
  fixed order — `{"name": <string>, "values": [<value>,
  ...]}`. Values may be any JSON values; contract
  entries are checked against these lists.
- `contract` (array, required): the explicit list of
  allowed configurations. Each entry is an array with
  exactly one value per axis, in the `axes` order. May
  be empty (Instance E) or a singleton.
- `components` (array of strings, required): behavior
  component names.
- `behavior` (object, required): the behavior table —
  for each component name, an array with exactly one
  value per contract row, in the `contract` order:
  `behavior[component][i]` is that component's value at
  contract row `i`. (This is F restricted to C, per
  specification section 7.)
- `hyperedges` (array, optional, default []): one object
  per hyperedge — `{"components": [<component name>,
  ...], "weight": <positive int>}`. `weight` is optional
  and defaults to 1; on hyperedges of size at least 2
  the weight must be a positive integer.

Instances in `instances/`: Instance X, Instance D,
Instance E in its empty and singleton forms, and the
arena instance at seeds 11 and 23.

## Output fields

In prose: the returned vector is the highest minimal
axis vector — maximal rho = (mu, lambda) among minimal
sufficient sets, ties beyond rho broken by the
lexicographically smallest sorted axis-name list. The
output also carries the returned vector's rho; the mu
and lambda of the full axis set; the live set and the
engaged list of the full axis set; the same pair for
the returned vector; the full list of minimal
sufficient sets, each with its vector, its rho, its
live set, and its engaged list, ordered by rho
descending then axis-name list ascending; the per-axis
dispositions, each with a membership label (one of "in
the return", "in some minimal sufficient set only", "in
none"), the emergent-dead flag, and the combined label
list; and the search counts described above. The exact
field names, in output order:

```
returned_vector
rho_returned
mu_full
lambda_full
live_full
engaged_full
live_returned
engaged_returned
minimal_sufficient  (each entry: vector, rho, live, engaged)
axis_dispositions   (each entry: disposition, emergent_dead, dispositions)
counts              (subsets_enumerated, contract_rows, pairs_scanned)
```

## The arena instance

The files of this directory:

```
solver.py       the solver
checker.py      the earlier independent checker (provenance only)
canon.py        the canonical renderer the gate diffs with
encode.py       the encoder into coded Lean data
arena_model.py  the arena model the arena instance was built from
```

The arena model file is the phase-2 arena semantics as
an executable miniature (grid platformer, planner
profiles, selection, execution, reversibility through
the same successor function). Running it regenerates
the two arena instance files. The instance runs through
the solver with no special-casing, as the
specification's validation bar (c) requires.

`encode.py` encodes an instance file as Lean data
(`proof/Arena.lean`) for the expectations program: axis
values coded by position, behavior values coded per
component by first occurrence, the behavior table keyed
by the mixed radix key of the configuration. The coding
preserves equality exactly, which is all liveness and
the emergence measure depend on.

## The checker in the gate

The gate's checker is the Lean expectations program:
`proof/Expect.lean` evaluates the proved definitions on
the control instances of `proof/Controls.lean` and on
the coded arena instances of `proof/Arena.lean`, and
`canon.py` renders the solver's output in the same
canonical lines for the diff. Three proved identities
in the expectations program keep the evaluation shared:
the engaged list read off one computed live list, mu as
the weight sum over the engaged list, and the live list
read off the instance's pair table (the difference-set
form of liveness, proved against the definition of
live). All three are proved from the definitions, so
the expectations are the definitions' own values, not a
second informal reading of them.

`checker.py` is the earlier independent Python
brute-force checker (a literal triple loop over the
specification's section 2 definition, no shared code
with the solver), kept for provenance. It is not the
gate's checker; the gate's agreement is against the
Lean definitions, which is the stronger statement.

## One named resolution (read before relying on dispositions)

Membership disposition and emergent-dead are reported
as separate fields because they are NOT mutually
exclusive. Specification section 4 defines
emergent-dead by Live-removal (Live(A without a) =
Live(A)) and asserts a dead axis belongs to no minimal
sufficient set; that assertion fails on Instance X,
where axis c is emergent-dead by the definition yet
{c} is minimal sufficient. The solver follows the
Live-removal definition for the flag. The corrected
claim (a dead axis makes the full set non-minimal) is
what the core proves.

## Differences from the out-of-repo validated implementation

The solver was first built and validated outside this
repository (Instances X/D/E agreement against the
independent Python checker, byte-exact determinism,
arena instance at both seeds). The landing ports it
with these named differences:

- The checker's seat is now held by the Lean
  expectations program, as above; the Python checker is
  landed alongside for provenance.
- The validation output files of the out-of-repo run
  are not landed; the gate regenerates the agreement
  evidence on every run instead.
- The arena instance files live in `instances/` with
  the other instances, and their model and encoder are
  landed alongside them.
- The solver's header names this repository's SPEC.md
  as the contract it implements.
