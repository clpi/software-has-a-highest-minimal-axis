# Incremental recomputation: the HMA solve under row joins

The finite HMA solve with carried state: per difference set (the axes on
which a row pair differs), the components some pair with that difference set
distinguishes; per subset, its live set, engaged edges and rho. A join appends
contract rows and computes only the pairs with a new row; a subset re-measures
only when a new pair whose difference set lies inside it adds a live
component. Minimality and the highest selection are re-derived from carried
measures; no pair is rescanned. Withdrawals keep a support count per (difference set, component): a component
leaves only when its last support goes, so alternate supports are kept, and
only subsets containing a shrunk difference set re-measure. A changed behavior
cell is a withdrawal plus a join; join itself refuses it. The checker is ../solver.py's solve(), unmodified.

Run: `python3 -B solver/incremental/gate.py s3` and
`LEAN=/path/to/lean-4.19.0 sh solver/incremental/lean/check.sh proof`.

Measured (counts): x, d, e-empty, e-singleton agree with solver.py at every
row-append prefix (full JSON result). 6 axes, 200 to 220 rows: 4,190 new pairs
vs 24,090, 0 of 64 subsets re-measured (saturated). A staged join that first
varies axis f: 24 of 64 re-measured, all containing f. A 2-axis join: 2 of 4
(3 of 4 is the most possible, since the empty subset is never live). A mutant
that skips supersets is caught.

Lean, over ../../proof/Hma.lean unchanged: agreeoff_iff_diff, join_live,
scoped_live, witness_mono, scoped_rho, delete_live, scoped_delete,
survives_of_witness, scoped_rho_delete. This file sits outside proof/ so
proof/check.sh and its pinned theorem counts are untouched.
