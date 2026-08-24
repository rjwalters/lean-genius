import Proofs.Erdos85CrossNeighborhoodFlipDefectExpansion

/-!
# Quadratic residual-pair carrier for the `01--01` cell

This file formalizes `(73rnz_cjibkzza)--(73rnz_cjibkzzk)`: an odd-by-odd
cross flag has odd augmentation, its orientation-free compression is the
polar term of the quadratic pair count, and a closed-state coboundary moves
all vertex-separable terms to complementary physical transitions.
-/

namespace Erdos85

/-- The parity of the number of unordered pairs in a finite residual set. -/
def residualPairQuadratic {R : Type*} [DecidableEq R]
    (S : Finset R) : ZMod 2 := S.card.choose 2

private theorem choose_two_add (a b : ℕ) :
    (a + b).choose 2 = a.choose 2 + b.choose 2 + a * b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.add_succ, Nat.choose_succ_succ, ih, Nat.choose_succ_succ]
    simp [Nat.mul_succ]
    omega

/-- Polarization of the quadratic pair count over a disjoint union. -/
theorem residualPairQuadratic_union_of_disjoint
    {R : Type*} [DecidableEq R] (A B : Finset R)
    (hdisj : Disjoint A B) :
    residualPairQuadratic (A ∪ B) =
      residualPairQuadratic A + residualPairQuadratic B +
        (A.card : ZMod 2) * (B.card : ZMod 2) := by
  unfold residualPairQuadratic
  rw [Finset.card_union_of_disjoint hdisj, choose_two_add]
  push_cast
  ring

/-- For two odd disjoint endpoint residual sets, the cross flag is the
nonzero polar term `(73rnz_cjibkzzi)`. -/
theorem residualPairQuadratic_union_of_disjoint_odd
    {R : Type*} [DecidableEq R] (A B : Finset R)
    (hdisj : Disjoint A B) (hAodd : Odd A.card) (hBodd : Odd B.card) :
    residualPairQuadratic (A ∪ B) =
      residualPairQuadratic A + residualPairQuadratic B + 1 := by
  rw [residualPairQuadratic_union_of_disjoint A B hdisj]
  have hAcast : (A.card : ZMod 2) = 1 := by
    obtain ⟨k, hk⟩ := hAodd
    rw [hk]
    push_cast
    have htwo : (2 : ZMod 2) = 0 := by decide
    rw [htwo, zero_mul, zero_add]
  have hBcast : (B.card : ZMod 2) = 1 := by
    obtain ⟨k, hk⟩ := hBodd
    rw [hk]
    push_cast
    have htwo : (2 : ZMod 2) = 0 := by decide
    rw [htwo, zero_mul, zero_add]
  rw [hAcast, hBcast]
  norm_num

/-- The ordered endpoint choices underlying the orientation-free residual
pair flags have odd augmentation.  Disjointness is what makes forgetting
the endpoint orientation injective, while this theorem records the required
augmentation `(73rnz_cjibkzzb)`. -/
theorem residualCrossFlag_augmentation_eq_one
    {R : Type*} [DecidableEq R] (A B : Finset R)
    (hAodd : Odd A.card) (hBodd : Odd B.card) :
    (∑ _p ∈ A ×ˢ B, (1 : ZMod 2)) = 1 := by
  simp only [Finset.sum_const, Finset.card_product, nsmul_eq_mul]
  have hAcast : (A.card : ZMod 2) = 1 := by
    obtain ⟨k, hk⟩ := hAodd
    rw [hk]
    push_cast
    have htwo : (2 : ZMod 2) = 0 := by decide
    rw [htwo, zero_mul, zero_add]
  have hBcast : (B.card : ZMod 2) = 1 := by
    obtain ⟨k, hk⟩ := hBodd
    rw [hk]
    push_cast
    have htwo : (2 : ZMod 2) = 0 := by decide
    rw [htwo, zero_mul, zero_add]
  push_cast
  rw [hAcast, hBcast]
  norm_num

/-- Closed-census form of `(73rnz_cjibkzzk)`.  On each distinguished
`01--01` H occurrence, polarization writes its unit as a quadratic union
flag plus a vertex coboundary.  Since the full physical H/V/S census is
closed, the cell coboundaries equal the complementary transition
coboundaries, leaving only the bounded quadratic carrier. -/
theorem residualPairQuadratic_closedCensus
    {Edge : Type*} [Fintype Edge] [DecidableEq Edge]
    (cell : Finset Edge) (qUnion cob : Edge → ZMod 2)
    (hcell : ∀ e ∈ cell, (1 : ZMod 2) = qUnion e + cob e)
    (hclosed : ∑ e, cob e = 0) :
    (∑ _e ∈ cell, (1 : ZMod 2)) =
      (∑ e ∈ cell, qUnion e) + ∑ e ∈ cellᶜ, cob e := by
  have hcellSum : (∑ _e ∈ cell, (1 : ZMod 2)) =
      (∑ e ∈ cell, qUnion e) + ∑ e ∈ cell, cob e := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    exact hcell e he
  have hcob : (∑ e ∈ cell, cob e) = ∑ e ∈ cellᶜ, cob e := by
    have hpartition : (∑ e, cob e) =
        (∑ e ∈ cell, cob e) + ∑ e ∈ cellᶜ, cob e := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun e => e ∈ cell)]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
      congr 1
      apply Finset.sum_congr
      · ext e
        simp
      · intro e he
        rfl
    rw [hclosed] at hpartition
    have htwo : (2 : ZMod 2) = 0 := by decide
    let x := ∑ e ∈ cell, cob e
    let y := ∑ e ∈ cellᶜ, cob e
    change 0 = x + y at hpartition
    change x = y
    have hxx : x + x = 0 := by
      rw [← two_mul, htwo, zero_mul]
    calc
      x = x + 0 := by simp
      _ = x + (x + y) := by rw [← hpartition]
      _ = (x + x) + y := by ring
      _ = y := by rw [hxx, zero_add]
  rw [hcellSum, hcob]

end Erdos85

#print axioms Erdos85.residualPairQuadratic_union_of_disjoint
#print axioms Erdos85.residualPairQuadratic_union_of_disjoint_odd
#print axioms Erdos85.residualCrossFlag_augmentation_eq_one
#print axioms Erdos85.residualPairQuadratic_closedCensus
