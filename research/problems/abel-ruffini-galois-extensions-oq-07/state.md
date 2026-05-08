# Current State

**Phase**: ORIENT
**Since**: 2026-05-08T03:10:00Z
**Iteration**: 2

## Current Focus

Phase-2 axiomatization of Burnside's pᵃqᵇ theorem committed: scaffold +
trivial cases proved axiom-free + non-trivial case isolated as a single
named axiom + main theorem combining both.

## Active Approach

Reduce trivial cases to Mathlib's `IsPGroup → IsNilpotent → IsSolvable`
chain (axiom-free). Isolate the genuinely-open content (`p ≠ q`,
`a ≥ 1`, `b ≥ 1`) as `burnside_pq_nontrivial` axiom.

## Blockers

The non-trivial case requires either character theory + algebraic-integer
hypotheses (Burnside 1904) or transfer + focal subgroup theory
(Goldschmidt-Matsuyama 1970s). Neither is in Mathlib at sufficient
generality. Estimated 400-1000 lines for a full upstream-quality proof.

## Next Action

1. Eliminate `burnside_pq_nontrivial` via Goldschmidt-Matsuyama: extend
   Mathlib's transfer infrastructure with the focal subgroup theorem,
   then apply transfer on a Sylow p-subgroup. Recommended as the
   character-free route since it avoids Mathlib's algebraic-integer gap.
2. Sharpness check: cite parent's `¬ IsSolvable (Equiv.Perm (Fin 5))`
   and observe `|A₅| = 60` has 3 prime factors — confirming the bound.
3. Coordinate with Mathlib reviewers on scoping a full upstream PR.

## Iteration 2 Builds (researcher-3, 2026-05-08)

- Created `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` (221 lines).
- `pGroup_isSolvable`: explicit packaging of Mathlib's chain
  `IsPGroup → IsNilpotent → IsSolvable` (axiom-free, single line).
- `burnside_pq_a_zero` (axiom-free): trivial case `a = 0`, `G` is a `q`-group.
- `burnside_pq_b_zero` (axiom-free): trivial case `b = 0`, `G` is a `p`-group.
- `burnside_pq_same_prime` (axiom-free): trivial case `p = q`, `G` is a
  `p`-group of combined exponent.
- `axiom burnside_pq_nontrivial`: isolated open content, `p ≠ q`,
  `a ≥ 1`, `b ≥ 1`.
- `burnside_pq` (uses axiom): main theorem combining trivial + non-trivial.
- 3 sanity-check `example`s at boundary cardinalities (`|G| = 1`,
  `|G| = p`, `|G| = p^a`), all axiom-free via `burnside_pq`.
- Added `import Proofs.AbelRuffiniGaloisExtensionsOQ07` to `proofs/Proofs.lean`.
- Created gallery entry `src/data/proofs/abel-ruffini-galois-extensions-oq-07/`.

**Counts**: lineCount 221, theoremCount 5, axiomCount 1, sorries 0.
