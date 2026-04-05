import Mathlib
import Proofs.InverseGaloisA5

/-
# Toward Eliminating `three_dvd_gal_card` (OQ-06 → OQ-01)

This file makes progress on the last remaining axiom in InverseGaloisA5.lean:
  `axiom three_dvd_gal_card : 3 ∣ Fintype.card q.Gal`

where q = X⁵ - 5X⁴ + 10X³ - 10X² + 25X - 5.

## Results Proved

1. `q_rootSet_ℂ_card` : |rootSet q ℂ| = 5
2. `q_deriv_pos` : q'(x) = 5(x-1)⁴ + 20 > 0 for all real x
3. `q_strictMono` : q is strictly monotone on ℝ
4. `q_has_real_root` : q has at least one real root (IVT)
5. `q_rootSet_ℝ_card` : |rootSet q ℝ| = 1
6. `galConj_sq_eq_one` : complex conjugation squares to 1 in q.Gal
7. `galConj_nontrivial` : complex conjugation is nontrivial
8. `two_dvd_gal_card` : 2 ∣ |Gal(q)|
9. `gal_card_ne_5` : |Gal(q)| ≠ 5
10. `q_ℤ_mod7_factorization` : q ≡ (X-5)(X-6)(cubic) mod 7 [proved via ext+interval_cases+decide]
11. `cubicMod7_no_roots` : cubic has no roots in 𝔽₇ [fin_cases + decide]

## Key Mathlib API

- `Polynomial.Gal.restrict` needs `[Fact ((p.map (algebraMap F E)).Splits)]` (not `p.Splits`)
- `map_pow` (not `aeval_pow`): `aeval_pow` is not in Lean 4.26.0; use `map_pow` for AlgHom.map_pow
- `Polynomial.deriv_aeval` (@[simp]): `deriv (aeval · q) x = aeval x (derivative q)`
- `Polynomial.differentiable_aeval`: `Differentiable 𝕜 (fun x => aeval x q)`
- `Polynomial.Gal.card_complex_roots_eq_card_real_add_card_not_gal_inv`
- `AlgEquiv.symm_apply_apply` for involution proofs (Complex.conjAe_apply not in 4.26.0)
- `Fintype.card_pos_iff` (not `Fintype.card_ne_zero_iff` which is not in 4.26.0)
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped Classical

namespace InverseGaloisOQ06OQ01

open InverseGaloisA5 Polynomial

-- ============================================================================
-- § 1. Root Count in ℂ
-- ============================================================================

/-- q has exactly 5 roots in ℂ. -/
theorem q_rootSet_ℂ_card : Fintype.card (q.rootSet ℂ) = 5 :=
  -- card_rootSet_eq_natDegree needs (q.map ℂ).Splits, not q.Splits (algebraMap ℚ ℂ)
  -- IsAlgClosed.splits (q.map (algebraMap ℚ ℂ)) gives exactly this
  (Polynomial.card_rootSet_eq_natDegree q_separable
    (IsAlgClosed.splits (q.map (algebraMap ℚ ℂ)))).trans q_natDegree

-- ============================================================================
-- § 2. Derivative Analysis
-- ============================================================================

/-- q'(x) = 5(x-1)⁴ + 20 > 0 for all real x. -/
theorem q_deriv_pos (x : ℝ) : 0 < aeval x (Polynomial.derivative q) := by
  have : aeval x (Polynomial.derivative q) = 5 * (x - 1) ^ 4 + 20 := by
    simp only [q, derivative_sub, derivative_add, derivative_mul, derivative_pow,
      derivative_X, derivative_C, derivative_one, Nat.cast_ofNat,
      aeval_sub, aeval_add, aeval_mul, map_pow, aeval_X, aeval_C, aeval_one, map_zero,
      mul_one, nsmul_eq_mul, zero_mul, mul_zero, zero_add, add_zero]
    -- algebraMap ℚ ℝ = Rat.cast definitionally; Rat.cast_ofNat reduces numerals
    simp only [show (algebraMap ℚ ℝ) = ((↑) : ℚ → ℝ) from rfl,
      Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one]
    ring
  linarith [show (0 : ℝ) ≤ (x - 1) ^ 4 from by positivity, this.symm.le]

-- ============================================================================
-- § 3. Strict Monotonicity and Unique Real Root
-- ============================================================================

/-- q is strictly monotone on ℝ. -/
theorem q_strictMono : StrictMono (fun x : ℝ => aeval x q) := by
  intro a b hab
  exact strictMonoOn_of_deriv_pos convex_univ
    q.differentiable_aeval.continuous.continuousOn
    (fun x _ => by rw [Polynomial.deriv_aeval]; exact q_deriv_pos x)
    (Set.mem_univ a) (Set.mem_univ b) hab

/-- q(0) = -5. -/
private theorem q_aeval_zero : aeval (0 : ℝ) q = -5 := by
  simp only [q, aeval_sub, aeval_add, aeval_mul, map_pow, aeval_X, aeval_C, aeval_one]
  simp only [show (algebraMap ℚ ℝ) = ((↑) : ℚ → ℝ) from rfl,
    Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one]
  norm_num

/-- q(6) > 0. -/
private theorem q_aeval_six_pos : 0 < aeval (6 : ℝ) q := by
  have : aeval (6 : ℝ) q = 3241 := by
    simp only [q, aeval_sub, aeval_add, aeval_mul, map_pow, aeval_X, aeval_C, aeval_one]
    simp only [show (algebraMap ℚ ℝ) = ((↑) : ℚ → ℝ) from rfl,
      Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one]
    norm_num
  linarith

/-- q has at least one real root (IVT: q(0) = -5 < 0, q(6) > 0). -/
theorem q_has_real_root : ∃ r : ℝ, aeval r q = 0 := by
  obtain ⟨c, -, hc⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 6)
    q.differentiable_aeval.continuous.continuousOn
    ⟨by rw [q_aeval_zero]; norm_num, q_aeval_six_pos.le⟩
  exact ⟨c, hc⟩

/-- q has exactly 1 real root. -/
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
  · -- Fintype.card_ne_zero_iff is not in Lean 4.26.0; use card_pos_iff instead
    have hpos : 0 < Fintype.card (q.rootSet ℝ) := Fintype.card_pos_iff.mpr ⟨⟨r, hmem⟩⟩
    omega

-- ============================================================================
-- § 4. Complex Conjugation Element of q.Gal
-- ============================================================================

-- NOTE: Polynomial.Gal.restrict needs [Fact ((p.map (algebraMap F E)).Splits)]
-- NOT [Fact (p.Splits (algebraMap F E))].
-- Use IsAlgClosed.splits applied to the MAPPED polynomial.

/-- q.map ℂ splits over ℂ (needed for Polynomial.Gal.restrict). -/
instance q_map_splits_ℂ : Fact ((q.map (algebraMap ℚ ℂ)).Splits) :=
  ⟨IsAlgClosed.splits _⟩

/-- Complex conjugation as a ℚ-algebra automorphism of ℂ. -/
noncomputable def conjAeQ : ℂ ≃ₐ[ℚ] ℂ := Complex.conjAe.restrictScalars ℚ

/-- The complex conjugation element of q.Gal. -/
noncomputable def galConj : q.Gal :=
  Polynomial.Gal.restrict q ℂ conjAeQ

/-- conjAeQ² = 1.
NOTE: Complex.conjAe_apply is not in Lean 4.26.0.
Use AlgEquiv.symm_apply_apply: conjAe is an involution (symm = self). -/
private theorem conjAeQ_sq : conjAeQ ^ 2 = 1 := by
  ext z
  simp only [sq, AlgEquiv.mul_apply, AlgEquiv.one_apply, conjAeQ, AlgEquiv.restrictScalars_apply]
  exact Complex.conjAe.symm_apply_apply z

/-- galConj² = 1 in q.Gal. -/
theorem galConj_sq_eq_one : galConj ^ 2 = 1 := by
  show Polynomial.Gal.restrict q ℂ conjAeQ ^ 2 = 1
  rw [← map_pow, conjAeQ_sq, map_one]

/-- The support of galConj acting on q.rootSet ℂ has size 4. -/
theorem galConj_support_card :
    (Polynomial.Gal.galActionHom q ℂ galConj).support.card = 4 := by
  have hkey := Polynomial.Gal.card_complex_roots_eq_card_real_add_card_not_gal_inv q
  simp only [Set.toFinset_card] at hkey
  -- galConj = restrict q ℂ (AlgEquiv.restrictScalars ℚ Complex.conjAe)
  -- The hkey uses restrict with conjAe.restrictScalars ℚ, same as conjAeQ
  rw [show (Polynomial.Gal.restrict q ℂ (AlgEquiv.restrictScalars ℚ Complex.conjAe)) =
      galConj from rfl, q_rootSet_ℂ_card, q_rootSet_ℝ_card] at hkey
  omega

/-- galConj is nontrivial. -/
theorem galConj_nontrivial : galConj ≠ 1 := by
  intro h
  have := galConj_support_card
  rw [show galConj = 1 from h, map_one, Equiv.Perm.support_one, Finset.card_empty] at this
  norm_num at this

/-- 2 ∣ |Gal(q/ℚ)|. -/
theorem two_dvd_gal_card : 2 ∣ Fintype.card q.Gal := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hord : orderOf galConj = 2 :=
    orderOf_eq_prime galConj_sq_eq_one galConj_nontrivial
  rw [← hord]; exact orderOf_dvd_card

/-- |Gal(q/ℚ)| ≠ 5. -/
theorem gal_card_ne_5 : Fintype.card q.Gal ≠ 5 := by
  intro h; have := two_dvd_gal_card; omega

-- ============================================================================
-- § 5. Factorization mod 7
-- ============================================================================

private noncomputable def q_ℤ : ℤ[X] :=
  X ^ 5 - C 5 * X ^ 4 + C 10 * X ^ 3 - C 10 * X ^ 2 + C 25 * X - C 5

/-- The cubic factor X³ + 6X² + 4X + 1 over 𝔽₇. -/
noncomputable def cubicMod7 : (ZMod 7)[X] :=
  X ^ 3 + C 6 * X ^ 2 + C 4 * X + C 1

-- NOTE: `decide`/`native_decide` fail for (ZMod 7)[X] equality in Lean 4.26.0:
-- `Polynomial.semiring` has no executable code, and `DecidableEq (ZMod 7)[X]`
-- uses tactics internally (rw/simp), causing kernel reduction to get stuck.
-- A coefficient-by-coefficient proof via Polynomial.ext + decide is needed.
-- set_option must precede the doc comment in Lean 4.
set_option maxHeartbeats 800000 in
/-- q ≡ (X-5)(X-6)(cubicMod7) mod 7. -/
theorem q_ℤ_mod7_factorization :
    q_ℤ.map (Int.castRingHom (ZMod 7)) = (X - C 5) * (X - C 6) * cubicMod7 := by
  have h1 : (X - C 5 : (ZMod 7)[X]) = X + C 2 := by
    simp only [sub_eq_add_neg, ← Polynomial.C_neg,
      show (-5 : ZMod 7) = 2 from by decide]
  have h2 : (X - C 6 : (ZMod 7)[X]) = X + C 1 := by
    simp only [sub_eq_add_neg, ← Polynomial.C_neg,
      show (-6 : ZMod 7) = 1 from by decide]
  rw [h1, h2]
  apply Polynomial.ext; intro n
  by_cases hn : n < 6
  · interval_cases n <;>
      simp only [Polynomial.coeff_map, q_ℤ, cubicMod7,
        Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_mul,
        Polynomial.coeff_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_C,
        Polynomial.coeff_X, Polynomial.coeff_one, Polynomial.coeff_zero,
        Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
        Finset.sum_empty, Finset.sum_cons, Finset.sum_singleton,
        Finset.mem_cons, Finset.mem_singleton, Prod.mk.injEq,
        mul_ite, ite_mul, if_true, if_false] <;>
      decide
  · push_neg at hn
    have hqZ_deg : q_ℤ.natDegree ≤ 5 := by
      simp only [q_ℤ]; compute_degree
    have hrd_deg : ((X + C 2 : (ZMod 7)[X]) * (X + C 1) * cubicMod7).natDegree ≤ 5 := by
      simp only [cubicMod7]; compute_degree
    have hld : (q_ℤ.map (Int.castRingHom (ZMod 7))).natDegree < n := by
      have hle : (q_ℤ.map (Int.castRingHom (ZMod 7))).natDegree ≤ q_ℤ.natDegree :=
        Polynomial.natDegree_map_le
      omega
    have hrd : ((X + C 2 : (ZMod 7)[X]) * (X + C 1) * cubicMod7).natDegree < n := by
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hld,
        Polynomial.coeff_eq_zero_of_natDegree_lt hrd]

/-- cubicMod7 has no roots in 𝔽₇. -/
theorem cubicMod7_no_roots : ∀ x : ZMod 7, eval x cubicMod7 ≠ 0 := by
  intro x
  fin_cases x <;>
    simp only [cubicMod7, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_one,
      eval_neg, eval_zero] <;>
    decide

-- ============================================================================
-- § 6. Summary
-- ============================================================================

/-- 3 ∣ |Gal(q)|: uses axiom from InverseGaloisA5 (Kummer-Dedekind route in progress). -/
theorem three_dvd_gal_card_proved : 3 ∣ Fintype.card q.Gal :=
  InverseGaloisA5.three_dvd_gal_card

end InverseGaloisOQ06OQ01
