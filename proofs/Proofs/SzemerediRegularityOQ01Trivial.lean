/-
  Szemerédi Regularity Lemma — OQ-01 (companion): the trivial-regularity threshold

  The sibling file `SzemerediRegularityOQ01.lean` develops structural facts about
  edge density and ε-regularity — symmetry, complement transfer, and
  **monotonicity in the parameter** (`isEpsilonRegular_mono`,
  `card_irregularOrderedPairs_antitone`: larger `eps` is a weaker requirement, so
  the irregular-pair count is non-increasing).

  This companion pins down the *endpoint* of that monotonicity: once `eps ≥ 1` the
  ε-regularity condition is **vacuously true for every pair**.  The reason is
  purely quantitative — edge densities always lie in `[0, 1]`
  (`edgeDensity_mem_Icc`), so for any subsets `A' ⊆ A`, `B' ⊆ B` the density gap
  satisfies

      `|d(A', B') − d(A, B)| ≤ 1 ≤ eps`,

  independently of the size conditions.  Consequently no pair can be irregular and
  the irregular-pair set is empty:

  * `isEpsilonRegular_of_one_le` — `1 ≤ eps ⟹ IsEpsilonRegular G eps A B` for all
    `A, B` (the trivial-regularity threshold).
  * `irregularOrderedPairs_eq_empty_of_one_le` — `1 ≤ eps ⟹` the ordered
    irregular pairs of any partition form the empty set.
  * `card_irregularOrderedPairs_eq_zero_of_one_le` — its cardinality is `0`, the
    exact value the antitone bound `card_irregularOrderedPairs_antitone` decreases
    towards.

  This is the sharp upper endpoint complementing the sibling's monotone
  bookkeeping: every graph is trivially `1`-regular, so the interesting regime of
  the regularity lemma is `0 < eps < 1`.

  All results are fully machine-checked (0 axioms, 0 sorries).
-/

import Mathlib
import Proofs.SzemerediRegularityOQ01

namespace Szemeredi.Regularity.OQ01

open Classical Szemeredi.Core Szemeredi.Regularity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Trivial-regularity threshold.**  If `eps ≥ 1` then *every* pair `(A, B)` is
ε-regular: for any witnesses `A' ⊆ A`, `B' ⊆ B` the two edge densities lie in
`[0, 1]`, so their difference has absolute value at most `1 ≤ eps`, and the size
conditions are irrelevant.  This is the endpoint of `isEpsilonRegular_mono`: at
`eps = 1` regularity becomes unconditional. -/
theorem isEpsilonRegular_of_one_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 1 ≤ eps) (A B : Finset V) :
    IsEpsilonRegular G eps A B := by
  intro A' B' _ _ _ _
  have h1 := edgeDensity_mem_Icc G A' B'
  have h2 := edgeDensity_mem_Icc G A B
  rw [Set.mem_Icc] at h1 h2
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **No irregular pairs above the threshold.**  For `eps ≥ 1` the ordered
irregular pairs of any partition form the empty set: every pair is ε-regular by
`isEpsilonRegular_of_one_le`, so the `¬IsEpsilonRegular` filter keeps nothing. -/
theorem irregularOrderedPairs_eq_empty_of_one_le (G : SimpleGraph V)
    [DecidableRel G.Adj] {eps : ℚ} (heps : 1 ≤ eps) (parts : Finset (Finset V)) :
    irregularOrderedPairs G eps parts = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  rintro ⟨P, Q⟩ hx
  simp only [irregularOrderedPairs, Finset.mem_filter, Finset.mem_product] at hx
  exact hx.2.2 (isEpsilonRegular_of_one_le G heps P Q)

/-- **The irregular-pair count vanishes above the threshold.**  Cardinality form:
`eps ≥ 1 ⟹ card (irregularOrderedPairs G eps parts) = 0`.  This is the value the
non-increasing count `card_irregularOrderedPairs_antitone` bottoms out at — every
partition is `1`-regular, so the `IsRegularPartition` threshold is met trivially. -/
theorem card_irregularOrderedPairs_eq_zero_of_one_le (G : SimpleGraph V)
    [DecidableRel G.Adj] {eps : ℚ} (heps : 1 ≤ eps) (parts : Finset (Finset V)) :
    (irregularOrderedPairs G eps parts).card = 0 := by
  rw [irregularOrderedPairs_eq_empty_of_one_le G heps parts, Finset.card_empty]

end Szemeredi.Regularity.OQ01
