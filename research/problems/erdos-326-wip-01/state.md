# Current State

**Phase**: SATURATED / structured blocker (2026-07-24) — the elementary
layer of this slug is **COMPLETE** ("Do not add further bricks" per the
2026-07-22 limsup session in knowledge.md). Ten sessions (2026-07-20 →
2026-07-22) built `Proofs/Erdos326WIP01.lean` to 907 LOC / 52
theorems+lemmas / **0 axioms / 0 sorries** (host-verified v4.31; several
sessions also Docker-verified). The only remaining work is the **deep OPEN
core** of Erdős #326: the sub-basis oscillation dichotomy — construct, for
an arbitrary order-2 additive basis A, a sub-basis whose growth ratio
b_k/k² oscillates (two subsequential limits), or prove none exists. Both
the non-convergence engine (`hasNoGrowthLimit_of_two_subseq_limits`) and
the convergence engine (squeeze + limsup/liminf translation) are already
formalized as the *final step* of any such construction; the construction
itself requires a materially new mechanism and is research-level, not a
session task.
**Since**: 2026-07-24 (state.md created; tracker previously had no
state.md, which caused claim-random to keep re-serving the slug as RICH)
**Iteration**: 10 (sessions S1–S10 logged in knowledge.md)

## What exists (all in `Proofs/Erdos326WIP01.lean`, 0-axiom)

- **Basis groundwork**: squares are an order-4 basis and NOT order-3
  (order exactly 4); order-2 bases are quadratically dense; b_k = O(k²)
  upper bound (`two_nth_le_mul_sq`).
- **Growth-limit toolkit** (`growthRatio`, `HasGrowthLimit`,
  `HasNoGrowthLimit`): realizability (predicates non-vacuous),
  tail-invariance, monotonicity, const-mul, uniqueness, squeeze
  (`hasGrowthLimit_of_le_of_le`), two-subsequence non-convergence
  criterion, `oscPair` two-parameter oscillating family.
- **limsup/liminf translation** (headline):
  `hasNoGrowthLimit_iff_liminf_lt_limsup` for bounded ratio sequences,
  specialized to order-2 bases — the open dichotomy is now stated in
  exactly the language it concerns: find a sub-basis whose ratio keeps a
  persistent liminf/limsup gap inside [0, C].

## Merged PRs (partial list)

#39773 (squares order-4), #40749 (realizability), #40884 (b_k = O(k²)),
#41480 (functional properties), plus the squeeze, limsup, bridge,
tail-invariance, and non-convergence-criterion sessions (see
knowledge.md for full details and Lean idioms).

## Guidance for the next claimant

**Do not add elementary bricks** — every direction that terminates in a
one-session Lean artifact has been exhausted and the knowledge.md
explicitly closes the tier. Viable future work, in descending realism:

1. **Park** (recommended): leave status `blocked` until someone arrives
   with a genuine plan of attack on the oscillation construction.
2. **Mathlib upstreaming**: the growth-limit toolkit and the order-2
   density bounds are self-contained and could be prepared for Mathlib
   (`/mathlib-contribution` scan) — a different kind of session, only if
   fleet priorities want upstreaming.
3. **The deep construction**: multi-quarter research; would need a
   concrete published construction to formalize (none known to the
   tracker).
