import Mathlib
import Proofs.InverseGaloisA5

/-
# Toward Eliminating `three_dvd_gal_card` (OQ-06 → OQ-01)

This file makes progress on the last remaining axiom in InverseGaloisA5.lean:
  `axiom three_dvd_gal_card : 3 ∣ Fintype.card q.Gal`

where q = X⁵ - 5X⁴ + 10X³ - 10X² + 25X - 5.

## Results Proved

1. `q_rootSet_ℂ_card` : |rootSet q ℂ| = 5
2. `q_deriv_pos` : q'(x) > 0 for all real x (q'(x) = 5(x-1)⁴ + 20)
3. `q_strictMono` : q is strictly monotone on ℝ
4. `q_has_real_root` : q has at least one real root (IVT)
5. `q_rootSet_ℝ_card` : |rootSet q ℝ| = 1
6. `galConj_sq_eq_one` : complex conjugation squares to 1 in q.Gal
7. `galConj_nontrivial` : complex conjugation is nontrivial (4 non-real roots)
8. `two_dvd_gal_card` : 2 ∣ |Gal(q)|
9. `gal_card_ne_5` : |Gal(q)| ≠ 5
10. `q_ℤ_mod7_factorization` : q ≡ (X-5)(X-6)(cubic) mod 7 [decide]
11. `cubicMod7_no_roots` : cubic has no roots in 𝔽₇ [decide]

## Kummer-Dedekind Route for three_dvd_gal_card

  q mod 7 = (linear)(linear)(irred cubic)
  → Kummer-Dedekind: ∃ prime P above 7 with inertiaDeg = 3
  → tower multiplicativity: 3 ∣ inertiaDeg in SplittingField
  → fundamental identity: 3 ∣ |Gal(q)|

Blocked: verifying 7 ∤ [𝒪_ℚ(α) : ℤ[α]] for Kummer-Dedekind instantiation.

## Key API Used

- `Polynomial.hasDerivAt_aeval` / `deriv_aeval` : derivative of aeval
- `Polynomial.differentiable_aeval` : continuity of polynomial evaluation
- `Polynomial.mem_rootSet_of_ne` : rootSet membership
- `Polynomial.Gal.card_complex_roots_eq_card_real_add_card_not_gal_inv` : root count identity
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped Classical

namespace InverseGaloisOQ06OQ01

open InverseGaloisA5 Polynomial

-- ============================================================================
-- § 1. Root Count in ℂ
-- ============================================================================

/-- q has exactly 5 roots in ℂ (q separable, degree 5, ℂ algebraically closed). -/
theorem q_rootSet_ℂ_card : Fintype.card (q.rootSet ℂ) = 5 :=
  (Polynomial.card_rootSet_eq_natDegree q_separable
    (IsAlgClosed.splits_codomain q)).trans q_natDegree

-- ============================================================================
-- § 2. Derivative Analysis: q'(x) = 5(x-1)⁴ + 20 > 0
-- ============================================================================

/-- q'(x) = 5(x-1)⁴ + 20 > 0 for all real x.
    Uses `Polynomial.deriv_aeval` (simp): deriv (aeval · q) x = aeval x (derivative q). -/
theorem q_deriv_pos (x : ℝ) : 0 < aeval x (Polynomial.derivative q) := by
  have : aeval x (Polynomial.derivative q) = 5 * (x - 1) ^ 4 + 20 := by
    simp only [q, derivative_sub, derivative_add, derivative_mul, derivative_pow,
      derivative_X, derivative_C, derivative_one, Nat.cast_ofNat,
      aeval_sub, aeval_add, aeval_mul, aeval_pow, aeval_X, aeval_C, aeval_one,
      mul_one, nsmul_eq_mul]
    push_cast; ring
  linarith [show (0 : ℝ) ≤ (x - 1) ^ 4 from by positivity, this.symm.le]

-- ============================================================================
-- § 3. Strict Monotonicity and Unique Real Root
-- ============================================================================

/-- q, evaluated at real numbers, is strictly monotone.
    Uses `Polynomial.deriv_aeval` and `strictMonoOn_of_deriv_pos`. -/
theorem q_strictMono : StrictMono (fun x : ℝ => aeval x q) := by
  intro a b hab
  have hmono : StrictMonoOn (fun x : ℝ => aeval x q) Set.univ :=
    strictMonoOn_of_deriv_pos convex_univ
      q.differentiable_aeval.continuous.continuousOn
      (fun x _ => by rw [Polynomial.deriv_aeval]; exact q_deriv_pos x)
  exact hmono (Set.mem_univ a) (Set.mem_univ b) hab

/-- q(0) = -5. -/
private theorem q_aeval_zero : aeval (0 : ℝ) q = -5 := by
  simp [q, aeval_sub, aeval_add, aeval_mul, aeval_pow, aeval_X, aeval_C]; norm_num

/-- q(6) > 0. -/
private theorem q_aeval_six_pos : 0 < aeval (6 : ℝ) q := by
  have h : aeval (6 : ℝ) q = 3241 := by
    simp only [q, aeval_sub, aeval_add, aeval_mul, aeval_pow, aeval_X, aeval_C, aeval_one]
    push_cast; norm_num
  linarith

/-- q has at least one real root by IVT (q(0) = -5 < 0, q(6) > 0). -/
theorem q_has_real_root : ∃ r : ℝ, aeval r q = 0 := by
  obtain ⟨c, -, hc⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 6)
    q.differentiable_aeval.continuous.continuousOn
    ⟨by rw [q_aeval_zero]; norm_num, q_aeval_six_pos.le⟩
  exact ⟨c, hc⟩

/-- q has exactly 1 real root.
    At most 1: q_strictMono.injective → any two real roots are equal.
    At least 1: q_has_real_root. -/
theorem q_rootSet_ℝ_card : Fintype.card (q.rootSet ℝ) = 1 := by
  obtain ⟨r, hr⟩ := q_has_real_root
  have hmem : r ∈ q.rootSet ℝ :=
    (Polynomial.mem_rootSet_of_ne q_irreducible.ne_zero).mpr hr
  apply Nat.le_antisymm
  · rw [Fintype.card_le_one_iff]
    intro ⟨a, ha⟩ ⟨b, hb⟩
    apply Subtype.ext
    have ha' := (Polynomial.mem_rootSet_of_ne q_irreducible.ne_zero).mp ha
    have hb' := (Polynomial.mem_rootSet_of_ne q_irreducible.ne_zero).mp hb
    exact q_strictMono.injective (ha'.trans hb'.symm)
  · rw [Nat.one_le_iff_ne_zero, Fintype.card_ne_zero_iff]
    exact ⟨⟨r, hmem⟩⟩

-- ============================================================================
-- § 4. Complex Conjugation Element of q.Gal
-- ============================================================================

/-- Complex conjugation as a ℚ-algebra automorphism of ℂ. -/
noncomputable def conjAeQ : ℂ ≃ₐ[ℚ] ℂ := Complex.conjAe.restrictScalars ℚ

/-- q splits over ℂ (needed for Polynomial.Gal.restrict). -/
instance q_splits_ℂ : Fact (q.Splits (algebraMap ℚ ℂ)) :=
  ⟨IsAlgClosed.splits_codomain q⟩

/-- The complex conjugation element of q.Gal. -/
noncomputable def galConj : q.Gal :=
  Polynomial.Gal.restrict q ℂ conjAeQ

/-- conjAeQ² = 1. -/
private theorem conjAeQ_sq : conjAeQ ^ 2 = 1 := by
  ext z; simp [sq, AlgEquiv.mul_apply, conjAeQ, Complex.conjAe_apply, starRingEnd_apply]

/-- galConj² = 1 in q.Gal (since restrict is a MonoidHom). -/
theorem galConj_sq_eq_one : galConj ^ 2 = 1 := by
  show Polynomial.Gal.restrict q ℂ conjAeQ ^ 2 = 1
  rw [← map_pow, conjAeQ_sq, map_one]

/-- The support of galConj's action on q.rootSet ℂ has size 4.
    Key identity: |rootSet ℂ| = |rootSet ℝ| + support.card → 5 = 1 + support.card. -/
theorem galConj_support_card :
    (Polynomial.Gal.galActionHom q ℂ galConj).support.card = 4 := by
  have hkey := Polynomial.Gal.card_complex_roots_eq_card_real_add_card_not_gal_inv q
  simp only [Set.toFinset_card] at hkey
  -- galConj is definitionally equal to restrict q ℂ (AlgEquiv.restrictScalars ℚ Complex.conjAe)
  have : (Polynomial.Gal.galActionHom q ℂ
      (Polynomial.Gal.restrict q ℂ (AlgEquiv.restrictScalars ℚ Complex.conjAe))).support.card =
      (Polynomial.Gal.galActionHom q ℂ galConj).support.card := rfl
  rw [← this, q_rootSet_ℂ_card, q_rootSet_ℝ_card] at hkey
  omega

/-- galConj is nontrivial (support is nonempty, so not the identity). -/
theorem galConj_nontrivial : galConj ≠ 1 := by
  intro h
  have := galConj_support_card
  rw [show galConj = 1 from h, map_one, Equiv.Perm.support_one,
      Finset.card_empty] at this
  norm_num at this

/-- 2 ∣ |Gal(q/ℚ)|: galConj has order 2. -/
theorem two_dvd_gal_card : 2 ∣ Fintype.card q.Gal := by
  have hord : orderOf galConj = 2 :=
    orderOf_eq_prime galConj_sq_eq_one galConj_nontrivial
  rw [← hord]; exact orderOf_dvd_card

/-- |Gal(q/ℚ)| ≠ 5 (since 2 ∣ |Gal| but 2 ∤ 5). -/
theorem gal_card_ne_5 : Fintype.card q.Gal ≠ 5 := by
  intro h; have := two_dvd_gal_card; omega

-- ============================================================================
-- § 5. Factorization mod 7 (computational evidence for Kummer-Dedekind)
-- ============================================================================

/-- The integer version of q for mod-7 reduction. -/
private noncomputable def q_ℤ : ℤ[X] :=
  X ^ 5 - C 5 * X ^ 4 + C 10 * X ^ 3 - C 10 * X ^ 2 + C 25 * X - C 5

/-- The cubic factor X³ + 6X² + 4X + 1 over 𝔽₇. -/
noncomputable def cubicMod7 : (ZMod 7)[X] :=
  X ^ 3 + C 6 * X ^ 2 + C 4 * X + C 1

/-- q ≡ (X-5)(X-6)(cubicMod7) mod 7 (verified by decide). -/
theorem q_ℤ_mod7_factorization :
    q_ℤ.map (Int.castRingHom (ZMod 7)) = (X - C 5) * (X - C 6) * cubicMod7 := by
  simp only [q_ℤ, cubicMod7]; decide

/-- cubicMod7 has no roots in 𝔽₇ (all 7 elements checked by decide). -/
theorem cubicMod7_no_roots : ∀ x : ZMod 7, eval x cubicMod7 ≠ 0 := by decide

-- ============================================================================
-- § 6. three_dvd_gal_card
-- ============================================================================

/-- 3 ∣ |Gal(q)|: currently uses the axiom from InverseGaloisA5.
    The Kummer-Dedekind architecture above provides the route to a proof. -/
theorem three_dvd_gal_card_proved : 3 ∣ Fintype.card q.Gal :=
  InverseGaloisA5.three_dvd_gal_card

end InverseGaloisOQ06OQ01
