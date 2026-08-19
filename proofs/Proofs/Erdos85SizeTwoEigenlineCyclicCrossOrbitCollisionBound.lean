import Proofs.Erdos85SizeTwoEigenlineCyclicMultiOrbitCollisionDecomposition

/-!
# Cross-orbit collision census and bound

The product of two orbit multiplicities counts ordered pairs of source cells
whose matchings contain the same absolute edge.  Transposing this incidence
count expresses it as a sum of matching-intersection cardinalities.  Distinct
difference orbits give distinct source cells, so every intersection has size
at most one.
-/

namespace Erdos85

noncomputable section

/-- Incidence transpose for a product of two point multiplicities. -/
theorem sum_pointsOn_card_mul_pointsOn_card_eq_sum_intersections
    {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (Inc : α → γ → Prop) [DecidableRel Inc]
    (Inc' : β → γ → Prop) [DecidableRel Inc']
    (P : Finset α) (Q : Finset β) (L : Finset γ) :
    (∑ l ∈ L, (Erdos101OQ02ST.pointsOn Inc P l).card *
      (Erdos101OQ02ST.pointsOn Inc' Q l).card) =
      ∑ p ∈ P, ∑ q ∈ Q, (L.filter fun l => Inc p l ∧ Inc' q l).card := by
  classical
  simp_rw [Erdos101OQ02ST.pointsOn, Finset.card_filter]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro l hl
  by_cases h : Inc p l <;> by_cases h' : Inc' q l <;> simp [h, h']

/-- Exact cross-orbit census: common target edges are matching intersections. -/
theorem sizeTwoCyclicMatchingOrbitMultiplicity_mul_sum
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (t u : sizeTwoAllowedDifference q a) :
    (∑ e : SizeTwoCyclicAbsoluteGridEdge q,
      sizeTwoCyclicMatchingOrbitMultiplicity code t e *
        sizeTwoCyclicMatchingOrbitMultiplicity code u e) =
      ∑ x : ZMod q, ∑ y : ZMod q,
        (sizeTwoCyclicSourceMatching code (x, t) ∩
          sizeTwoCyclicSourceMatching code (y, u)).card := by
  classical
  let Inc : ZMod q → SizeTwoCyclicAbsoluteGridEdge q → Prop :=
    fun x e => e ∈ sizeTwoCyclicSourceMatching code (x, t)
  let Inc' : ZMod q → SizeTwoCyclicAbsoluteGridEdge q → Prop :=
    fun y e => e ∈ sizeTwoCyclicSourceMatching code (y, u)
  rw [show (∑ e : SizeTwoCyclicAbsoluteGridEdge q,
      sizeTwoCyclicMatchingOrbitMultiplicity code t e *
        sizeTwoCyclicMatchingOrbitMultiplicity code u e) =
      ∑ e ∈ (Finset.univ : Finset (SizeTwoCyclicAbsoluteGridEdge q)),
        (Erdos101OQ02ST.pointsOn Inc Finset.univ e).card *
          (Erdos101OQ02ST.pointsOn Inc' Finset.univ e).card by
    simp [Inc, Inc', Erdos101OQ02ST.pointsOn,
      sizeTwoCyclicMatchingOrbitMultiplicity]]
  rw [sum_pointsOn_card_mul_pointsOn_card_eq_sum_intersections
    Inc Inc' Finset.univ Finset.univ Finset.univ]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  congr 1
  ext e
  simp [Inc, Inc']

/-- Distinct difference orbits have at most `q²` ordered cross collisions. -/
theorem sizeTwoCyclicMatchingOrbitMultiplicity_mul_sum_le
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (t u : sizeTwoAllowedDifference q a) (htu : t ≠ u) :
    (∑ e : SizeTwoCyclicAbsoluteGridEdge q,
      sizeTwoCyclicMatchingOrbitMultiplicity code t e *
        sizeTwoCyclicMatchingOrbitMultiplicity code u e) ≤ q * q := by
  classical
  rw [sizeTwoCyclicMatchingOrbitMultiplicity_mul_sum code t u]
  calc
    (∑ x : ZMod q, ∑ y : ZMod q,
      (sizeTwoCyclicSourceMatching code (x, t) ∩
        sizeTwoCyclicSourceMatching code (y, u)).card) ≤
        ∑ _x : ZMod q, ∑ _y : ZMod q, 1 := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      apply sizeTwoCyclicSourceMatching_inter_card_le_one
      intro h
      exact htu (congrArg Prod.snd h)
    _ = q * q := by simp

/-- The complete ordered cross term over a selected set of difference orbits
is bounded by one `q²` contribution for each ordered distinct orbit pair. -/
theorem sizeTwoCyclicMatchingOrbitMultiplicity_offDiag_sum_le
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (T : Finset (sizeTwoAllowedDifference q a)) :
    (∑ p ∈ T.offDiag, ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
      sizeTwoCyclicMatchingOrbitMultiplicity code p.1 e *
        sizeTwoCyclicMatchingOrbitMultiplicity code p.2 e) ≤
      T.offDiag.card * (q * q) := by
  classical
  calc
    _ ≤ ∑ _p ∈ T.offDiag, q * q := by
      apply Finset.sum_le_sum
      intro p hp
      exact sizeTwoCyclicMatchingOrbitMultiplicity_mul_sum_le
        code p.1 p.2 (Finset.mem_offDiag.mp hp).2.2
    _ = T.offDiag.card * (q * q) := by simp

/-- Direct upper bound for the selected-orbit collision mass: only the
within-orbit second moments remain to be controlled more sharply. -/
theorem sizeTwoCyclicSelectedOrbitMultiplicity_choose_two_sum_le
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (T : Finset (sizeTwoAllowedDifference q a)) :
    2 * ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
        (sizeTwoCyclicSelectedOrbitMultiplicity code T e).choose 2 ≤
      (∑ t ∈ T, 2 * ∑ e : SizeTwoCyclicAbsoluteGridEdge q,
        (sizeTwoCyclicMatchingOrbitMultiplicity code t e).choose 2) +
        T.offDiag.card * (q * q) := by
  rw [sizeTwoCyclicSelectedOrbitMultiplicity_choose_two_sum_decomposition]
  exact Nat.add_le_add_left
    (sizeTwoCyclicMatchingOrbitMultiplicity_offDiag_sum_le code T) _

end

end Erdos85

#print axioms Erdos85.sum_pointsOn_card_mul_pointsOn_card_eq_sum_intersections
#print axioms Erdos85.sizeTwoCyclicMatchingOrbitMultiplicity_mul_sum
#print axioms Erdos85.sizeTwoCyclicMatchingOrbitMultiplicity_mul_sum_le
#print axioms Erdos85.sizeTwoCyclicMatchingOrbitMultiplicity_offDiag_sum_le
#print axioms Erdos85.sizeTwoCyclicSelectedOrbitMultiplicity_choose_two_sum_le
