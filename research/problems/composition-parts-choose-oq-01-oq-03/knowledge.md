# composition-parts-choose-oq-01-oq-03 — Third moment, symmetry, and vanishing skewness of the part-count

**Status:** COMPLETED (VERIFIED, 0-axiom) — PR shipped 2026-07-01.

## Problem

Leaf of the `composition-parts-choose` family (graded refinements of composition
counts via the "cut-set / double-erase" technique). A composition of `n` is an
ordered tuple of positive integers summing to `n` (Mathlib's `Composition n`);
its part-count is `c.length`. The family had built the count `2^(n−1)`, the
graded count `C(n−1,k−1)`, the first moment (mean `(n+1)/2`), and the second
moment / variance `(n−1)/4`. The sibling `oq-01-oq-01-oq-01`'s open question
asked for the **third moment / skewness** — this leaf answers it.

## Result (Proofs/CompositionPartsChooseOQ01OQ03.lean, 228L, 5 thm)

1. `sum_choose_mul_cube` : `8·∑_k C(m,k)·k³ = m²(m+3)·2^m` — cubic binomial
   identity by **double absorption** (`Nat.add_one_mul_choose_eq` drops one
   `(k+1)`, reducing `k³` to the family's `k²`, `k`, plain sums).
2. `sum_finset_card_cube` : subset form `8·∑_{s⊆Fin m} |s|³ = m²(m+3)2^m`
   (via `Finset.sum_powerset_apply_card`).
3. `third_moment` : `8·∑_c (c.length)³ + 2^n = (n³+6n²+3n)·2^(n−1)` (n ≥ 1);
   raw value `(n³+6n²+3n−2)·2^(n−3)`.
4. `parts_distribution_symmetric` : **structural** — for any `g : ℕ → M`,
   `∑_c g(c.length) = ∑_c g(n+1−c.length)`. Proved by the **complement
   involution** `s ↦ sᶜ` on `Finset (Fin (n−1))` (`|sᶜ| = (n−1)−|s|`), the graded
   form of `C(n−1,k−1) = C(n−1,n−k)`.
5. `third_central_moment_zero` : `∑_c ((c.length:ℚ) − (n+1)/2)³ = 0` — zero
   skewness, one line from (4) via the odd weight `g(k)=(k−(n+1)/2)³`,
   `g(n+1−k) = −g(k)`. Kills every odd central moment.

## Key techniques

- Gap bijection `gapsEquiv : Composition n ≃ Finset (Fin (n−1))` + bridge
  `length_eq_card_gaps` (from `oq-01-oq-01`); transport sums with `Equiv.sum_comp`.
- Double absorption for weighted binomial sums (reuse of family lemmas
  `sum_choose_mul`, `sum_choose_mul_sq`, `sum_finset_card`, `sum_finset_card_sq`).
- Reindex-by-involution (`s ↦ sᶜ`) for the symmetry theorem — the new idea here.

## Provenance

Adopted an orphan `.lean` left untracked in the main working tree by a prior
session; verified it typechecks against main's Mathlib cache
(`env -u LAKE lake env lean`) and confirmed `#print axioms` = `[propext,
Classical.choice, Quot.sound]` only (0 substantive). Authored the full gallery
entry (meta.json, annotations.json, index.ts).

## Follow-ups (see meta.json openQuestions)

- Fourth moment / kurtosis via `∑ k⁴ C(m,k)` + the same absorption chain.
- Symmetry/moments of *largest part* or *number of distinct part-sizes* — does
  gap-bijection transport survive for non-additive statistics?
