# Current State

**Phase**: ACT
**Since**: 2026-05-08T07:00:00Z
**Iteration**: 4

## Current Focus

Iteration 4 axiom-narrowing committed: `burnside_pq_pq_case` (axiom-free
`a = b = 1` case) plus `squarefreeOrder_isSolvable` (general squarefree-order
bridge), backed by Mathlib's `IsZGroup.of_squarefree`. The axiom
`burnside_pq_nontrivial` was narrowed to require `2 ≤ a ∨ 2 ≤ b`; the
`a = b = 1` sub-case is no longer axiom-dependent.

## Active Approach

The squarefree route exhausts what `IsZGroup` can prove: any squarefree-order
finite group is solvable (covers `pq`, `pqr`, `pqrs`, …). It does NOT extend
to `pᵃqᵇ` with `a ≥ 2` or `b ≥ 2`. The next phase is Sylow-analysis-based
sub-case proofs (`p²q`, `pq²`, `p²q²`) on the way to a full
Goldschmidt-Matsuyama discharge of the axiom.

## Blockers

The residual axiom (orders divisible by `p²` or `q²` for distinct primes)
requires either character theory + algebraic-integer hypotheses or
transfer + focal subgroup theory. Mathlib's `Mathlib.GroupTheory.Focal`
provides scaffolding for the character-free route (focal subgroup,
`transferFocal`, `commutator_inf_eq_focalSubgroup`); estimated 200-400
lines on top of this for full Goldschmidt-Matsuyama.

## Next Action

1. **(S5)** Prove `|G| = p² · q` axiom-free via Sylow analysis (~50-100 lines).
   Sylow's third theorem: `n_p ≡ 1 (mod p)` and `n_p | q`; `n_q ≡ 1 (mod q)`
   and `n_q | p²`. Case-analysis on `(n_p, n_q)` yields a normal Sylow.
2. **(S6)** Prove `|G| = p · q²` axiom-free (symmetric, ~30-50 lines).
3. **(S7)** Prove `|G| = p² · q²` axiom-free (~80-150 lines).
4. **(S8+)** Build Goldschmidt-Matsuyama on top of `Mathlib.GroupTheory.Focal`.

## Iteration 4 Builds (researcher-1, 2026-05-08)

- Updated `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` (277→384 lines).
- Added `import Mathlib.GroupTheory.SpecificGroups.ZGroup`.
- `squarefreeOrder_isSolvable`: axiom-free `Squarefree (Nat.card G) → IsSolvable G`
  via `IsZGroup.of_squarefree` + `[Finite][IsZGroup] → IsSolvable` instance.
- `burnside_pq_pq_case`: axiom-free `a = b = 1` case (`|G| = p · q`, `p ≠ q`)
  via `Nat.coprime_primes` + `Prime.squarefree` + `Nat.squarefree_mul`.
- Narrowed `burnside_pq_nontrivial`: added hypothesis `2 ≤ a ∨ 2 ≤ b`.
- Updated `burnside_pq` main theorem: `by_cases h11 : a = 1 ∧ b = 1` to peel
  off the squarefree case axiom-free, then derive `2 ≤ a ∨ 2 ≤ b` for the
  axiom invocation.
- 2 new sanity-check examples: `|G| = pq` via `burnside_pq_pq_case`;
  `|G| = 30` via `squarefreeOrder_isSolvable` (squarefree route beyond two
  primes).
- Updated gallery entry meta.json (lineCount 278→384, theoremCount 8→10,
  axiomCount unchanged at 1, sections updated, originalContributions and
  assumptions updated).

**Counts**: lineCount 384, theoremCount 10, axiomCount 1 (narrowed),
sorries 0.
