# Solver validation at the requested pin

Target base: `63d9d3fdce1f81c81cd5cda2bd9850b0c1494646`.

The [cited estate-census note](https://github.com/clpi/software-is-a-closed-loop/blob/ae85d7aa2d17/census/software-has-a-highest-minimal-axis.md) records that the solver was proposed but not implemented in-tree and that the arena instance was absent at its pinned snapshot.

The solver was checked with Lean 4.19.0 by generating a temporary Lean instance of `Hma.Inst` for each available fixture. Its output is checked against the repository's definitions for minimality, highest rho, full-axis mu/liveness/engagement, rho values, and per-axis dispositions. The minimal-set checker is linked to `Hma.minimal` through the existing `Hma.subsetrep` theorem. These are concrete checked instances; they do not establish a general theorem about the Python implementation.

## Results

| Case | Solver result | Lean agreement | Byte-exact repeat | Additional check |
| --- | --- | --- | --- | --- |
| X | `{a}`, rho `(1,3)`; complete minima `{a}` `(1,3)`, `{c}` `(1,2)` | Pass | Pass | Independent direct brute-force oracle agrees |
| D | `{a,b,c}`, rho `(1,2)`; only minimal sufficient set `{a,b,c}` | Pass | Pass | — |
| E-empty | `∅`, rho `(0,0)`; only minimal sufficient set `∅` | Pass | Pass | Empty contract |
| E-singleton | `∅`, rho `(0,0)`; only minimal sufficient set `∅` | Pass | Pass | Singleton contract |
| Arena | No result | Not run | Not run | Required exact fixture absent at `solver/fixtures/arena.json` |

The full gate compiled the original 58 theorem declarations (42 in `Hma.lean`, 16 in `Controls.lean`), found no proof escape tokens, and confirmed the printed axioms remain within `{propext, Classical.choice, Quot.sound}`. The gate exits nonzero by design because the required arena fixture is missing. Its captured output is `proof/CHECK.log`.

## Not landed / cannot say

- The arena instance is not included or validated. The exact arena model/table (or the coordinator record containing its complete table) was not available in the shared workspace. No substitute was invented. Therefore there is no arena result and the all-cases gate is not green.
- The implementation has not been established as correct for all possible programs, Lean instances, or arbitrary data by a general proof. The Lean certificates check the concrete table fixtures against the pinned definitions.
- The solver consumes the finite explicit table form and does not emit an executable induced transformation. The repository's existing transformation theorems are unchanged; this solver work makes no additional transformation claim.
- No performance benchmark or empirical scalability claim is made beyond the per-run enumeration counts. The search is exhaustive and exponential in the number of axes.
- The current log records a blocked full gate, not a passing arena-inclusive gate. A green full gate and arena PR validation cannot be claimed until the exact arena table is supplied and checked.
