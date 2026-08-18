import Proofs.Erdos85MuThreeMixedGridForeignRectangleMonodromyEvenCycleCount

/-!
# A type constraint for six-point derangement cocycles

Among even derangements of six points, the two possible cycle types are
`(4,2)` and `(3,3)`.  A finite group calculation shows that if two factors
and their product are all derangements, then two `(3,3)` factors force the
product to have type `(3,3)` as well.  Consequently a cocycle triangle cannot
contain exactly two `(3,3)` monodromies.
-/

namespace Erdos85

open Equiv

/-- A canonical `(3,3)` permutation on six labelled points. -/
def finSixThreeThree : Equiv.Perm (Fin 6) :=
  (Equiv.swap 0 1 * Equiv.swap 1 2) *
    (Equiv.swap 3 4 * Equiv.swap 4 5)

theorem finSixThreeThree_cycleType : finSixThreeThree.cycleType = {3, 3} := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
/-- With one `(3,3)` factor in canonical coordinates, a second fixed-point-free
order-three factor whose product is fixed-point-free has order-three product.
This is the finite core of the conjugacy-invariant cocycle constraint. -/
theorem finSixThreeThree_mul_orderThree_of_derangements
    (τ : Equiv.Perm (Fin 6))
    (hτfree : ∀ x, τ x ≠ x)
    (hprodFree : ∀ x, (τ * finSixThreeThree) x ≠ x)
    (hτthree : τ ^ 3 = 1) :
    (τ * finSixThreeThree) ^ 3 = 1 := by
  revert τ
  decide

/-- Conjugacy-invariant form: two `(3,3)` derangements on six points cannot
have a fixed-point-free product of type `(4,2)`. -/
theorem finSix_threeThree_product_pow_three_of_derangement
    (σ τ : Equiv.Perm (Fin 6))
    (hσtype : σ.cycleType = {3, 3})
    (hτtype : τ.cycleType = {3, 3})
    (hτfree : ∀ x, τ x ≠ x)
    (hprodFree : ∀ x, (τ * σ) x ≠ x) :
    (τ * σ) ^ 3 = 1 := by
  have hconj : IsConj finSixThreeThree σ :=
    Equiv.Perm.isConj_iff_cycleType_eq.2
      (finSixThreeThree_cycleType.trans hσtype.symm)
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  let τ' := c⁻¹ * τ * c
  have hτ'three : τ' ^ 3 = 1 := by
    have hτthree : τ ^ 3 = 1 := by
      rw [Equiv.Perm.pow_prime_eq_one_iff]
      intro n hn
      rw [hτtype] at hn
      simp at hn
      omega
    dsimp [τ']
    calc
      (c⁻¹ * τ * c) ^ 3 = c⁻¹ * τ ^ 3 * c := by
        simp only [pow_succ, pow_zero]
        group
      _ = 1 := by rw [hτthree]; simp
  have hτ'free : ∀ x, τ' x ≠ x := by
    intro x hx
    have hfix : τ (c x) = c x := by
      have := congrArg c hx
      simpa [τ'] using this
    exact hτfree (c x) hfix
  have hprod'free : ∀ x, (τ' * finSixThreeThree) x ≠ x := by
    intro x hx
    have hfix : (τ * σ) (c x) = c x := by
      have := congrArg c hx
      rw [← hc]
      simpa [τ'] using this
    exact hprodFree (c x) hfix
  have hprod'three := finSixThreeThree_mul_orderThree_of_derangements
    τ' hτ'free hprod'free hτ'three
  rw [← hc]
  have heq : τ * (c * finSixThreeThree * c⁻¹) =
      c * (τ' * finSixThreeThree) * c⁻¹ := by
    dsimp [τ']
    group
  rw [heq, conj_pow, hprod'three]
  simp

/-- Hence the fixed-point-free product itself has cycle type `(3,3)`. -/
theorem finSix_threeThree_product_threeThree_of_derangement
    (σ τ : Equiv.Perm (Fin 6))
    (hσtype : σ.cycleType = {3, 3})
    (hτtype : τ.cycleType = {3, 3})
    (hτfree : ∀ x, τ x ≠ x)
    (hprodFree : ∀ x, (τ * σ) x ≠ x) :
    (τ * σ).cycleType = {3, 3} := by
  have hthree := finSix_threeThree_product_pow_three_of_derangement
    σ τ hσtype hτtype hτfree hprodFree
  have hσeven : σ.sign = 1 := by
    rw [Equiv.Perm.sign_of_cycleType, hσtype]
    decide
  have hτeven : τ.sign = 1 := by
    rw [Equiv.Perm.sign_of_cycleType, hτtype]
    decide
  rcases even_fixedPointFree_cycleType_eq_fourTwo_or_threeThree
      (by decide : Fintype.card (Fin 6) = 6) (τ * σ) hprodFree
      (by simp [Equiv.Perm.sign_mul, hσeven, hτeven]) with hfourTwo | hthreeThree
  · have hallThree : ∀ c ∈ (τ * σ).cycleType, c = 3 :=
      Equiv.Perm.pow_prime_eq_one_iff.mp hthree
    have htwo : 2 ∈ (τ * σ).cycleType := by rw [hfourTwo]; simp
    have := hallThree 2 htwo
    omega
  · exact hthreeThree

/-- **No exactly-two `(3,3)` cocycle triangle.**  For three fixed-point-free
six-point permutations related by `υ = τ * σ`, any two having type `(3,3)`
force the third to have that type as well. -/
theorem finSix_threeThree_cocycle_pairwise_closure
    (σ τ : Equiv.Perm (Fin 6))
    (hσfree : ∀ x, σ x ≠ x)
    (hτfree : ∀ x, τ x ≠ x)
    (hprodFree : ∀ x, (τ * σ) x ≠ x) :
    (σ.cycleType = {3, 3} ∧ τ.cycleType = {3, 3} →
      (τ * σ).cycleType = {3, 3}) ∧
    (τ.cycleType = {3, 3} ∧ (τ * σ).cycleType = {3, 3} →
      σ.cycleType = {3, 3}) ∧
    (σ.cycleType = {3, 3} ∧ (τ * σ).cycleType = {3, 3} →
      τ.cycleType = {3, 3}) := by
  constructor
  · rintro ⟨hσ, hτ⟩
    exact finSix_threeThree_product_threeThree_of_derangement
      σ τ hσ hτ hτfree hprodFree
  constructor
  · rintro ⟨hτ, hprod⟩
    have hτinvType : τ⁻¹.cycleType = {3, 3} := by simpa using hτ
    have hτinvFree : ∀ x, τ⁻¹ x ≠ x := by
      intro x hx
      have := congrArg τ hx
      exact hτfree x (by simpa using this.symm)
    have hσeq : τ⁻¹ * (τ * σ) = σ := by group
    rw [← hσeq]
    exact finSix_threeThree_product_threeThree_of_derangement
      (τ * σ) τ⁻¹ hprod hτinvType hτinvFree (by simpa [hσeq] using hσfree)
  · rintro ⟨hσ, hprod⟩
    have hσinvType : σ⁻¹.cycleType = {3, 3} := by simpa using hσ
    have hσinvFree : ∀ x, σ⁻¹ x ≠ x := by
      intro x hx
      have := congrArg σ hx
      exact hσfree x (by simpa using this.symm)
    have hτeq : (τ * σ) * σ⁻¹ = τ := by group
    rw [← hτeq]
    exact finSix_threeThree_product_threeThree_of_derangement
      σ⁻¹ (τ * σ) hσinvType hprod hprodFree (by simpa [hτeq] using hτfree)

end Erdos85

#print axioms Erdos85.finSixThreeThree_mul_orderThree_of_derangements
#print axioms Erdos85.finSix_threeThree_product_threeThree_of_derangement
#print axioms Erdos85.finSix_threeThree_cocycle_pairwise_closure
