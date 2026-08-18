import Mathlib.Tactic

/-!
# Arithmetic rigidity of the square unit-component bouquet

In the residual exact-square configuration, let `k` be the number of
coefficient-one components, let `t` be the number of distinct coefficient-two
targets of their mass-two escapes, and let `m` be the common target-fiber
size forced by the restricted quotient-square equation.  Put `j = N-k`, the
coefficient mass outside the unit layer.  The identities are

* `p = s²+s+3` and `N = s²-s+3`;
* `2m+pj = 4s²+8` (the quotient-square row identity);
* `mt = k` (equal nonempty fibers);
* `2t ≤ j` (each distinct target costs coefficient mass at least two).

For odd `s ≥ 7` these equations have only one possibility: `j=2`, `t=1`,
and `m=k=N-2`.  Thus all unit components share one double-cover target and
there is no coefficient mass left for any other component.
-/

namespace Erdos85

/-- Summing the restricted quotient-square equation across a unit-component
row expresses the size of the corresponding double-cover target fiber. -/
theorem square_unit_target_fiber_equation
    {U T : Type*} [Fintype U] [DecidableEq U] [DecidableEq T]
    (Q : U → U → ℕ) (target : U → T) (s p : ℕ)
    (hrow : ∀ c, ∑ e, Q c e = s * s + 1)
    (hsq : ∀ c e,
      (∑ f, Q c f * Q f e) +
          2 * (if target c = target e then 1 else 0) =
        s * s * (if c = e then 1 else 0) + p)
    (c : U) :
    (s * s + 1) * (s * s + 1) +
        2 * (Finset.univ.filter fun e ↦ target c = target e).card =
      s * s + p * Fintype.card U := by
  have hpaths : (∑ e, ∑ f, Q c f * Q f e) =
      (s * s + 1) * (s * s + 1) := by
    rw [Finset.sum_comm]
    calc
      (∑ f, ∑ e, Q c f * Q f e) =
          ∑ f, Q c f * (∑ e, Q f e) := by
            apply Finset.sum_congr rfl
            intro f hf
            rw [Finset.mul_sum]
      _ = ∑ f, Q c f * (s * s + 1) := by
            apply Finset.sum_congr rfl
            intro f hf
            rw [hrow f]
      _ = (s * s + 1) * (s * s + 1) := by
            rw [← Finset.sum_mul, hrow c]
  have hfiber :
      (∑ e : U, 2 * (if target c = target e then 1 else 0)) =
        2 * (Finset.univ.filter fun e ↦ target c = target e).card := by
    rw [← Finset.mul_sum]
    congr 1
    exact Finset.sum_boole
      (fun e : U ↦ target c = target e) Finset.univ
  have hdiag :
      (∑ e : U, s * s * (if c = e then 1 else 0)) = s * s := by
    simp
  have hconst : (∑ _e : U, p) = p * Fintype.card U := by
    simp [Nat.mul_comm]
  have hsum := Finset.sum_congr rfl (fun e (_he : e ∈ Finset.univ) ↦ hsq c e)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hpaths, hfiber,
    hdiag, hconst] at hsum
  exact hsum

/-- In the exact-square parameterization, the fiber equation becomes the
small-defect identity used by `square_unit_bouquet_arithmetic`. -/
theorem square_unit_target_fiber_defect_equation
    (s p N k j m : ℕ) (hs7 : 7 ≤ s)
    (hp : p = s * s + s + 3)
    (hN : N = s * s - s + 3)
    (hkj : k + j = N)
    (hfiber :
      (s * s + 1) * (s * s + 1) + 2 * m =
        s * s + p * k) :
    2 * m + p * j = 4 * s * s + 8 := by
  have hss : s ≤ s * s := by nlinarith
  have hNadd : N + s = s * s + 3 := by omega
  have hpkj : p * k + p * j = p * N := by
    nlinarith [congrArg (fun x : ℕ ↦ p * x) hkj]
  have hpN : p * N = s ^ 4 + 5 * s * s + 9 := by
    have hmul := congrArg (fun x : ℕ ↦ p * x) hNadd
    rw [hp] at hmul
    nlinarith [sq_nonneg (s * s), sq_nonneg s]
  rw [hpN] at hpkj
  nlinarith [hfiber]

/-- **Square unit-bouquet arithmetic rigidity.** -/
theorem square_unit_bouquet_arithmetic
    (s p N k m t j : ℕ)
    (hs7 : 7 ≤ s) (hsOdd : Odd s)
    (hp : p = s * s + s + 3)
    (hN : N = s * s - s + 3)
    (hjk : k + j = N)
    (hmass : 2 * m + p * j = 4 * s * s + 8)
    (hmpos : 0 < m) (htpos : 0 < t)
    (hfibers : m * t = k)
    (htargetMass : 2 * t ≤ j) :
    j = 2 ∧ t = 1 ∧ m = k ∧ k = N - 2 := by
  have hjpos : 0 < j := by omega
  have hjle : j ≤ 3 := by
    by_contra hj
    have hj4 : 4 ≤ j := by omega
    have hpLower : s * s + s + 3 ≤ p := by omega
    have hprodLower : 4 * p ≤ p * j := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left p hj4
    have hspos : 0 < s := by omega
    have htooLarge : 4 * s * s + 8 < 4 * p := by
      rw [hp]
      nlinarith
    omega
  have hjne3 : j ≠ 3 := by
    intro hj3
    subst j
    have hpOdd : Odd p := by
      obtain ⟨a, ha⟩ := hsOdd
      refine ⟨2 * a * a + 3 * a + 2, ?_⟩
      rw [hp, ha]
      ring
    obtain ⟨a, ha⟩ := hpOdd
    have hleftOdd : Odd (2 * m + p * 3) := by
      refine ⟨m + 3 * a + 1, ?_⟩
      rw [ha]
      ring
    have hrightEven : Even (4 * s * s + 8) := by
      refine ⟨2 * s * s + 4, ?_⟩
      ring
    obtain ⟨b, hb⟩ := hleftOdd
    obtain ⟨c, hc⟩ := hrightEven
    rw [hmass] at hb
    omega
  have hj2 : j = 2 := by omega
  have ht1 : t = 1 := by omega
  have hmk : m = k := by simpa [ht1] using hfibers
  have hk : k = N - 2 := by omega
  exact ⟨hj2, ht1, hmk, hk⟩

/-- **Abstract quotient-system bouquet classification.**  A nonempty unit
layer with a surjective target map, the residual restricted row and square
identities, and coefficient mass `2 * #targets ≤ j` has exactly one target.
All but two units of the total coefficient mass lie in the unit layer. -/
theorem square_unit_bouquet_of_quotient_system
    {U T : Type*} [Fintype U] [DecidableEq U]
    [Fintype T] [DecidableEq T] [Nonempty U]
    (Q : U → U → ℕ) (target : U → T)
    (s p N j : ℕ)
    (hs7 : 7 ≤ s) (hsOdd : Odd s)
    (hp : p = s * s + s + 3)
    (hN : N = s * s - s + 3)
    (hkj : Fintype.card U + j = N)
    (htarget : Function.Surjective target)
    (htargetMass : 2 * Fintype.card T ≤ j)
    (hrow : ∀ c, ∑ e, Q c e = s * s + 1)
    (hsq : ∀ c e,
      (∑ f, Q c f * Q f e) +
          2 * (if target c = target e then 1 else 0) =
        s * s * (if c = e then 1 else 0) + p) :
    j = 2 ∧ Fintype.card T = 1 ∧
      Fintype.card U = N - 2 := by
  let c₀ : U := Classical.choice inferInstance
  let m := (Finset.univ.filter fun e : U ↦ target c₀ = target e).card
  have hfiber (c : U) :
      (Finset.univ.filter fun e : U ↦ target c = target e).card = m := by
    have hc := square_unit_target_fiber_equation Q target s p hrow hsq c
    have hc₀ := square_unit_target_fiber_equation Q target s p hrow hsq c₀
    dsimp only [m]
    omega
  have hmpos : 0 < m := by
    apply Finset.card_pos.mpr
    refine ⟨c₀, ?_⟩
    simp
  have htpos : 0 < Fintype.card T := by
    exact Fintype.card_pos_iff.mpr ⟨target c₀⟩
  have hmt : m * Fintype.card T = Fintype.card U := by
    calc
      m * Fintype.card T = ∑ _y : T, m := by simp [Nat.mul_comm]
      _ = ∑ y : T,
          (Finset.univ.filter fun e : U ↦ target e = y).card := by
            apply Finset.sum_congr rfl
            intro y hy
            obtain ⟨c, hc⟩ := htarget y
            rw [← hc]
            simpa [eq_comm] using (hfiber c).symm
      _ = Fintype.card U := by
            simpa using Finset.sum_card_fiberwise_eq_card_filter
              (Finset.univ : Finset U) (Finset.univ : Finset T) target
  have hc₀ := square_unit_target_fiber_equation Q target s p hrow hsq c₀
  have hdefect : 2 * m + p * j = 4 * s * s + 8 :=
    square_unit_target_fiber_defect_equation s p N (Fintype.card U) j m
      hs7 hp hN hkj (by simpa [m] using hc₀)
  obtain ⟨hj, ht, hm, hk⟩ := square_unit_bouquet_arithmetic
    s p N (Fintype.card U) m (Fintype.card T) j hs7 hsOdd hp hN hkj
      hdefect hmpos htpos hmt htargetMass
  exact ⟨hj, ht, hk⟩

/-- The quotient-system bouquet is impossible when a target can serve at
most one unit component.  Graphically, this injectivity follows from the
four-cycle obstruction for two sources of one cyclic double cover. -/
theorem false_of_square_unit_quotient_system_of_injective_target
    {U T : Type*} [Fintype U] [DecidableEq U]
    [Fintype T] [DecidableEq T] [Nonempty U]
    (Q : U → U → ℕ) (target : U → T)
    (s p N j : ℕ)
    (hs7 : 7 ≤ s) (hsOdd : Odd s)
    (hp : p = s * s + s + 3)
    (hN : N = s * s - s + 3)
    (hkj : Fintype.card U + j = N)
    (htargetSurj : Function.Surjective target)
    (htargetInj : Function.Injective target)
    (htargetMass : 2 * Fintype.card T ≤ j)
    (hrow : ∀ c, ∑ e, Q c e = s * s + 1)
    (hsq : ∀ c e,
      (∑ f, Q c f * Q f e) +
          2 * (if target c = target e then 1 else 0) =
        s * s * (if c = e then 1 else 0) + p) : False := by
  obtain ⟨-, ht, hk⟩ := square_unit_bouquet_of_quotient_system
    Q target s p N j hs7 hsOdd hp hN hkj htargetSurj htargetMass hrow hsq
  have hcardLe : Fintype.card U ≤ Fintype.card T :=
    Fintype.card_le_of_injective target htargetInj
  have hss : s ≤ s * s := by nlinarith
  have hNadd : N + s = s * s + 3 := by omega
  have h49 : 49 ≤ s * s := Nat.mul_le_mul hs7 hs7
  have h7s : 7 * s ≤ s * s := Nat.mul_le_mul_right s hs7
  rw [ht, hk] at hcardLe
  omega

end Erdos85
