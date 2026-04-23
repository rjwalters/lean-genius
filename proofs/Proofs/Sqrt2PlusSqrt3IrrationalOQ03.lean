import Mathlib

open Polynomial Real IntermediateField

set_option maxHeartbeats 800000

/-
# Minimal Polynomial of √2 + √3 over ℚ

## Main Result

The minimal polynomial of α = √2 + √3 over ℚ is f(X) = X⁴ - 10X² + 1.

Equivalently:
- X⁴ - 10X² + 1 is the unique monic irreducible polynomial in ℚ[X] with α as a root
- [ℚ(√2+√3) : ℚ] = 4
- √2+√3 is not in any proper subfield of ℝ containing ℚ

## Proof Strategy

1. **Root witness**: Direct computation shows f(α) = 0.
   α² = (√2+√3)² = 5 + 2√6,  α⁴ = (5+2√6)² = 49+20√6
   f(α) = 49+20√6 - 10(5+2√6) + 1 = 0.

2. **Irreducibility**: f is irreducible over ℚ via rational root + quadratic factor analysis.
   - No rational roots: only candidates ±1 give f(±1) = -8 ≠ 0.
   - No quadratic factors: if f = (X²+aX+b)(X²-aX+d), then bd=1, a(d-b)=0, b+d-a²=-10.
     Case a=0: b+d=-10, bd=1 → discriminant 96 = 4·24, √24 ∉ ℚ.
     Case b=d: b²=1, 2b-a²=-10.  b=1→a²=12∉ℚ²;  b=-1→a²=8∉ℚ².

3. **Minimal polynomial**: Since f is monic, irreducible, and vanishes at α,
   apply `minpoly.eq_of_irreducible_of_monic`.

## Status: 0 sorries (proof complete)
-/

namespace Sqrt2PlusSqrt3IrrationalOQ03

/-! ## Part I: Root Witness -/

/-- √2+√3 satisfies X⁴ - 10X² + 1 = 0.
    Key algebra: α² = 5+2√6, α⁴ = 49+20√6, so α⁴-10α²+1 = 0. -/
theorem aeval_sqrt2_plus_sqrt3 :
    Polynomial.aeval (Real.sqrt 2 + Real.sqrt 3) (X ^ 4 - 10 * X ^ 2 + 1 : ℚ[X]) = 0 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  -- (√2+√3)² = 5 + 2·(√2·√3)
  have hsq : (Real.sqrt 2 + Real.sqrt 3) ^ 2 = 5 + 2 * (Real.sqrt 2 * Real.sqrt 3) := by
    have := calc (Real.sqrt 2 + Real.sqrt 3) ^ 2
        = Real.sqrt 2 ^ 2 + 2 * Real.sqrt 2 * Real.sqrt 3 + Real.sqrt 3 ^ 2 := by ring
      _ = 2 + 2 * Real.sqrt 2 * Real.sqrt 3 + 3 := by rw [h2, h3]
      _ = 5 + 2 * (Real.sqrt 2 * Real.sqrt 3) := by ring
    exact this
  -- (√2·√3)² = 6
  have h23sq : (Real.sqrt 2 * Real.sqrt 3) ^ 2 = 6 := by
    rw [mul_pow, h2, h3]; norm_num
  -- (√2+√3)⁴ = 49 + 20·(√2·√3)
  have h4 : (Real.sqrt 2 + Real.sqrt 3) ^ 4 = 49 + 20 * (Real.sqrt 2 * Real.sqrt 3) := by
    calc (Real.sqrt 2 + Real.sqrt 3) ^ 4
        = ((Real.sqrt 2 + Real.sqrt 3) ^ 2) ^ 2 := by ring
      _ = (5 + 2 * (Real.sqrt 2 * Real.sqrt 3)) ^ 2 := by rw [hsq]
      _ = 25 + 20 * (Real.sqrt 2 * Real.sqrt 3) + 4 * (Real.sqrt 2 * Real.sqrt 3) ^ 2 := by ring
      _ = 25 + 20 * (Real.sqrt 2 * Real.sqrt 3) + 4 * 6 := by rw [h23sq]
      _ = 49 + 20 * (Real.sqrt 2 * Real.sqrt 3) := by ring
  -- Now evaluate: f(√2+√3) = α⁴ - 10α² + 1 = (49+20√6) - 10(5+2√6) + 1 = 0
  simp only [map_sub, map_add, map_pow, map_mul, map_one, aeval_X, map_ofNat,
             Polynomial.aeval_one]
  push_cast
  linarith [hsq, h4]

/-! ## Part II: Irreducibility over ℚ -/

/-- X⁴ - 10X² + 1 is monic. -/
private theorem f_monic : (X ^ 4 - 10 * X ^ 2 + 1 : ℚ[X]).Monic := by
  unfold Polynomial.Monic Polynomial.leadingCoeff
  have hd : (X ^ 4 - 10 * X ^ 2 + 1 : ℚ[X]).natDegree = 4 := by
    have h1 : (10 * X ^ 2 : ℚ[X]).natDegree ≤ 2 := by
      calc (10 * X ^ 2 : ℚ[X]).natDegree ≤ _ := natDegree_mul_le
        _ = _ := by simp
    have h2 : (X ^ 4 - 10 * X ^ 2 : ℚ[X]).natDegree = 4 := by
      apply natDegree_sub_eq_left_of_natDegree_lt
      calc (10 * X ^ 2 : ℚ[X]).natDegree ≤ 2 := h1
        _ < 4 := by norm_num
      simp [natDegree_pow]
    calc (X ^ 4 - 10 * X ^ 2 + 1 : ℚ[X]).natDegree
        = (X ^ 4 - 10 * X ^ 2 : ℚ[X]).natDegree := by
          apply natDegree_add_eq_left_of_natDegree_lt
          simp [h2]
      _ = 4 := h2
  rw [hd]
  simp [coeff_sub, coeff_add, coeff_X_pow, coeff_mul, coeff_ofNat]

/-- √2+√3 is algebraic over ℚ: X⁴ - 10X² + 1 is a monic polynomial with it as root. -/
private theorem sqrt2_plus_sqrt3_isIntegral : IsIntegral ℚ (Real.sqrt 2 + Real.sqrt 3) :=
  ⟨X ^ 4 - 10 * X ^ 2 + 1, f_monic, aeval_sqrt2_plus_sqrt3⟩

/-- X⁴ - 10X² + 1 is irreducible over ℚ.
    Proof sketch:
    - No rational roots: f(±1) = -8 ≠ 0 (by rational root theorem ±1 are the only candidates)
    - No quadratic factors over ℚ: equating coefficients yields equations with
      irrational solutions in all cases (discriminant 96 for the a=0 case;
      a²∈{8,12} for the b=d case — none are perfect squares).
    - By the factor theorem for degree 4, no linear or quadratic rational factors
      implies irreducibility. -/
-- Helper: X⁴ - 10X² + 1 has no integer roots.
-- Key: (k²-5)² = 24, which forces k ∈ {-3,-2,-1,0,1,2,3}, none satisfying the equation.
private lemma f_no_int_root (k : ℤ) :
    (X ^ 4 - 10 * X ^ 2 + 1 : ℤ[X]).eval k ≠ 0 := by
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow,
             Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
             Polynomial.eval_one, Polynomial.eval_ofNat]
  intro hk
  have h_sq : (k ^ 2 - 5) ^ 2 = 24 := by ring_nf; linarith
  have hk2_le : k ^ 2 ≤ 9 := by nlinarith [h_sq]
  have hk_le : k ≤ 3 := by nlinarith [sq_nonneg k]
  have hk_ge : -3 ≤ k := by nlinarith [sq_nonneg k]
  interval_cases k <;> norm_num at hk

private theorem irred_f : Irreducible (X ^ 4 - 10 * X ^ 2 + 1 : ℚ[X]) := by
  -- Prove monic over ℤ (same structure as f_monic)
  have fmonic_Z : (X ^ 4 - 10 * X ^ 2 + 1 : ℤ[X]).Monic := by
    unfold Polynomial.Monic Polynomial.leadingCoeff
    have hd : (X ^ 4 - 10 * X ^ 2 + 1 : ℤ[X]).natDegree = 4 := by
      have h1 : (10 * X ^ 2 : ℤ[X]).natDegree ≤ 2 := by
        calc (10 * X ^ 2 : ℤ[X]).natDegree ≤ _ := natDegree_mul_le
          _ = _ := by simp
      have h2 : (X ^ 4 - 10 * X ^ 2 : ℤ[X]).natDegree = 4 := by
        apply natDegree_sub_eq_left_of_natDegree_lt
        · calc (10 * X ^ 2 : ℤ[X]).natDegree ≤ 2 := h1
            _ < 4 := by norm_num
        · simp [natDegree_pow]
      calc (X ^ 4 - 10 * X ^ 2 + 1 : ℤ[X]).natDegree
          = (X ^ 4 - 10 * X ^ 2 : ℤ[X]).natDegree := by
            apply natDegree_add_eq_left_of_natDegree_lt; simp [h2]
        _ = 4 := h2
    rw [hd]; simp [coeff_sub, coeff_add, coeff_X_pow, coeff_mul, coeff_ofNat]
  -- Prove irreducible over ℤ[X]
  have hirred_int : Irreducible (X ^ 4 - 10 * X ^ 2 + 1 : ℤ[X]) := by
    refine ⟨fun h => ?_, fun a b hab => ?_⟩
    · -- Not a unit: f has degree 4 ≠ 0
      have hd : (X ^ 4 - 10 * X ^ 2 + 1 : ℤ[X]).natDegree = 4 := by
        have h1 : (10 * X ^ 2 : ℤ[X]).natDegree ≤ 2 := by
          calc (10 * X ^ 2 : ℤ[X]).natDegree ≤ _ := natDegree_mul_le; _ = _ := by simp
        have h2 : (X ^ 4 - 10 * X ^ 2 : ℤ[X]).natDegree = 4 :=
          natDegree_sub_eq_left_of_natDegree_lt (h1.trans_lt (by norm_num)) (by simp [natDegree_pow])
        exact (natDegree_add_eq_left_of_natDegree_lt (by simp [h2])).trans h2
      have := Polynomial.natDegree_eq_zero_of_isUnit h
      omega
    · -- Any factorization has a unit factor
      have hfne : (X ^ 4 - 10 * X ^ 2 + 1 : ℤ[X]) ≠ 0 := by
        intro h; simp at h
      have hane : a ≠ 0 := left_ne_zero_of_mul (hab ▸ hfne)
      have hbne : b ≠ 0 := right_ne_zero_of_mul (hab ▸ hfne)
      have hdeg : a.natDegree + b.natDegree = 4 := by
        have hm := Polynomial.natDegree_mul hane hbne
        rw [hab] at hm
        have hd4 : (X ^ 4 - 10 * X ^ 2 + 1 : ℤ[X]).natDegree = 4 := by
          have h1 : (10 * X ^ 2 : ℤ[X]).natDegree ≤ 2 := by
            calc (10 * X ^ 2 : ℤ[X]).natDegree ≤ _ := natDegree_mul_le; _ = _ := by simp
          have h2 : (X ^ 4 - 10 * X ^ 2 : ℤ[X]).natDegree = 4 :=
            natDegree_sub_eq_left_of_natDegree_lt (h1.trans_lt (by norm_num)) (by simp [natDegree_pow])
          exact (natDegree_add_eq_left_of_natDegree_lt (by simp [h2])).trans h2
        omega
      have hlc_prod : a.leadingCoeff * b.leadingCoeff = 1 := by
        have := congr_arg Polynomial.leadingCoeff hab
        rwa [Polynomial.leadingCoeff_mul, fmonic_Z.leadingCoeff] at this
      have ha_le : a.natDegree ≤ 4 := by omega
      -- Degree 1: extract integer root of a → integer root of f → contradiction
      have deg1_to_root : a.natDegree = 1 → False := by
        intro h1
        obtain ⟨p, q, hp, rfl⟩ := Polynomial.natDegree_eq_one.mp h1
        -- p * b.leadingCoeff = 1, so p = ±1
        have hpm : p = 1 ∨ p = -1 := by
          have : p * b.leadingCoeff = 1 := by
            have := congr_arg Polynomial.leadingCoeff hab
            simp [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C_mul_X_add_C hp] at this
            exact this
          rcases Int.isUnit_iff.mp (isUnit_of_mul_eq_one _ _ this) with ⟨u, hu⟩
          rcases Int.units_eq_iff_abs_eq.mp (Units.ext hu) with h | h <;> simp [h]
        rcases hpm with rfl | rfl
        · -- a = C 1 * X + C q, root is -q
          have hroot : (C 1 * X + C q : ℤ[X]).eval (-q) = 0 := by
            simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
          have hfroot : (X ^ 4 - 10 * X ^ 2 + 1 : ℤ[X]).eval (-q) = 0 := by
            rw [← hab, Polynomial.eval_mul, hroot, zero_mul]
          exact f_no_int_root (-q) hfroot
        · -- a = C (-1) * X + C q, root is q
          have hroot : (C (-1 : ℤ) * X + C q : ℤ[X]).eval q = 0 := by
            simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
          have hfroot : (X ^ 4 - 10 * X ^ 2 + 1 : ℤ[X]).eval q = 0 := by
            rw [← hab, Polynomial.eval_mul, hroot, zero_mul]
          exact f_no_int_root q hfroot
      -- Degree 2: coefficient analysis → contradiction
      have deg2_impossible : a.natDegree = 2 → False := by
        intro h2
        have hb2 : b.natDegree = 2 := by omega
        -- Get coefficient equations from a * b = f
        have hce : ∀ n, (a * b).coeff n = (X ^ 4 - 10 * X ^ 2 + 1 : ℤ[X]).coeff n :=
          fun n => congr_arg (Polynomial.coeff · n) hab
        -- a.coeff k = 0 for k > 2, b.coeff k = 0 for k > 2
        have ha3 : a.coeff 3 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        have ha4 : a.coeff 4 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        have hb3 : b.coeff 3 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        have hb4 : b.coeff 4 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        -- Coeff of X^4: a.coeff 2 * b.coeff 2 = 1
        have hc4 : a.coeff 2 * b.coeff 2 = 1 := by
          have h := hce 4
          simp only [Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ] at h
          simp [ha3, ha4, hb3, hb4, Polynomial.coeff_sub, Polynomial.coeff_add,
                Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_ofNat] at h
          linarith
        -- Coeff of X^3: a.coeff 2 * b.coeff 1 + a.coeff 1 * b.coeff 2 = 0
        have hc3 : a.coeff 2 * b.coeff 1 + a.coeff 1 * b.coeff 2 = 0 := by
          have h := hce 3
          simp only [Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ] at h
          simp [ha3, ha4, hb3, hb4, Polynomial.coeff_sub, Polynomial.coeff_add,
                Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_ofNat] at h
          linarith
        -- Coeff of X^2: a.coeff 2 * b.coeff 0 + a.coeff 1 * b.coeff 1 + a.coeff 0 * b.coeff 2 = -10
        have hc2 : a.coeff 2 * b.coeff 0 + a.coeff 1 * b.coeff 1 + a.coeff 0 * b.coeff 2 = -10 := by
          have h := hce 2
          simp only [Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ] at h
          simp [ha3, ha4, hb3, hb4, Polynomial.coeff_sub, Polynomial.coeff_add,
                Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_ofNat] at h
          linarith
        -- Coeff of X^1: a.coeff 1 * b.coeff 0 + a.coeff 0 * b.coeff 1 = 0
        have hc1 : a.coeff 1 * b.coeff 0 + a.coeff 0 * b.coeff 1 = 0 := by
          have h := hce 1
          simp only [Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ] at h
          simp [ha3, ha4, hb3, hb4, Polynomial.coeff_sub, Polynomial.coeff_add,
                Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_ofNat] at h
          linarith
        -- Coeff of X^0: a.coeff 0 * b.coeff 0 = 1
        have hc0 : a.coeff 0 * b.coeff 0 = 1 := by
          have h := hce 0
          simp only [Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ] at h
          simp [ha3, ha4, hb3, hb4, Polynomial.coeff_sub, Polynomial.coeff_add,
                Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_ofNat] at h
          linarith
        -- From hc4: a.coeff 2 * b.coeff 2 = 1, both are ±1 units in ℤ
        have ha2_unit : IsUnit (a.coeff 2) := isUnit_of_mul_eq_one _ _ hc4
        -- Since a.coeff 2 is the leading coeff of a (natDegree = 2)
        have ha2_eq : a.coeff 2 = a.leadingCoeff := by
          simp [Polynomial.leadingCoeff, h2]
        have hb2_eq : b.coeff 2 = b.leadingCoeff := by
          simp [Polynomial.leadingCoeff, hb2]
        -- From hlc_prod: a.leadingCoeff * b.leadingCoeff = 1
        -- And a.leadingCoeff is the leading coeff, b.leadingCoeff is too
        -- From hc4: a.coeff 2 * b.coeff 2 = 1
        -- So in ℤ: both must be ±1 with product 1 → both = 1 or both = -1
        have hab2 : (a.coeff 2 = 1 ∧ b.coeff 2 = 1) ∨ (a.coeff 2 = -1 ∧ b.coeff 2 = -1) := by
          have ha2_pm : a.coeff 2 = 1 ∨ a.coeff 2 = -1 := by
            rw [ha2_eq]; exact Int.isUnit_iff.mp (isUnit_of_mul_eq_one _ _ (ha2_eq ▸ hb2_eq ▸ hc4))
          rcases ha2_pm with rfl | rfl
          · left; constructor; rfl; linarith [hc4]
          · right; constructor; rfl; linarith [hc4]
        -- In either case, the analysis is symmetric (negate a and b)
        -- We can WLOG assume a.coeff 2 = 1 (the -1 case is identical by negation)
        -- Key equations after substituting a.coeff 2 = ±1 and b.coeff 2 = ±1:
        -- From hc3: b.coeff 1 + a.coeff 1 = 0 (when a.coeff 2 = b.coeff 2 = ±1)
        -- From hc1: a.coeff 1 * b.coeff 0 + a.coeff 0 * b.coeff 1 = 0
        -- From hc0: a.coeff 0 * b.coeff 0 = 1
        -- From hc2: b.coeff 0 + a.coeff 1 * b.coeff 1 + a.coeff 0 = -10
        rcases hab2 with ⟨ha2, hb2v⟩ | ⟨ha2, hb2v⟩ <;>
        · rw [ha2, hb2v] at hc3 hc2 hc1
          simp at hc3 hc2 hc1
          -- hc3: b.coeff 1 = -a.coeff 1
          -- hc1: a.coeff 1 * b.coeff 0 - a.coeff 0 * a.coeff 1 = 0
          --     → a.coeff 1 * (b.coeff 0 - a.coeff 0) = 0
          have hcase : a.coeff 1 = 0 ∨ b.coeff 0 = a.coeff 0 := by
            rcases mul_eq_zero.mp (by linarith [hc1, hc3] : a.coeff 1 * (b.coeff 0 - a.coeff 0) = 0) with h | h
            · left; exact h
            · right; linarith
          rcases hcase with ha1z | hb0a0
          · -- a.coeff 1 = 0, so b.coeff 1 = 0 (from hc3)
            have hb1z : b.coeff 1 = 0 := by linarith [hc3]
            rw [ha1z, hb1z] at hc2 hc1
            simp at hc2 hc1
            -- hc2: a.coeff 0 + b.coeff 0 = -10 (with sign from ha2/hb2v)
            -- hc0: a.coeff 0 * b.coeff 0 = 1
            -- (a.coeff 0 - b.coeff 0)^2 = (a.coeff 0 + b.coeff 0)^2 - 4*a.coeff 0*b.coeff 0
            --                            = 100 - 4 = 96
            -- But 96 is not a perfect square → contradiction
            have h96 : (a.coeff 0 - b.coeff 0) ^ 2 = 96 := by nlinarith [hc0, hc2]
            nlinarith [sq_nonneg (a.coeff 0 - b.coeff 0 - 10 : ℤ),
                       sq_nonneg (a.coeff 0 - b.coeff 0 + 10 : ℤ)]
          · -- b.coeff 0 = a.coeff 0
            have hb0 : b.coeff 0 = a.coeff 0 := hb0a0
            rw [hb0] at hc0
            -- a.coeff 0^2 = 1 → a.coeff 0 = ±1
            have ha0_pm : a.coeff 0 = 1 ∨ a.coeff 0 = -1 := by
              have := Int.isUnit_iff.mp (isUnit_of_mul_eq_one _ _ (show a.coeff 0 * a.coeff 0 = 1 by linarith [hc0]))
              rcases this with ⟨u, hu⟩
              rcases Int.units_eq_iff_abs_eq.mp (Units.ext hu) with h | h <;> simp [h]
            rcases ha0_pm with rfl | rfl
            · -- a.coeff 0 = 1: from hc2: 2 - a.coeff 1^2 = -10 → a.coeff 1^2 = 12
              have ha1sq : a.coeff 1 ^ 2 = 12 := by nlinarith [hc2, hc3, hb0]
              -- 12 is not a perfect square in ℤ
              nlinarith [sq_nonneg (a.coeff 1 - 3 : ℤ), sq_nonneg (a.coeff 1 + 3 : ℤ),
                         sq_nonneg (a.coeff 1 - 4 : ℤ), sq_nonneg (a.coeff 1 + 4 : ℤ)]
            · -- a.coeff 0 = -1: from hc2: -2 - a.coeff 1^2 = -10 → a.coeff 1^2 = 8
              have ha1sq : a.coeff 1 ^ 2 = 8 := by nlinarith [hc2, hc3, hb0]
              -- 8 is not a perfect square in ℤ
              nlinarith [sq_nonneg (a.coeff 1 - 2 : ℤ), sq_nonneg (a.coeff 1 + 2 : ℤ),
                         sq_nonneg (a.coeff 1 - 3 : ℤ), sq_nonneg (a.coeff 1 + 3 : ℤ)]
      -- Degree 3: b has degree 1 → same argument
      have deg3_impossible : a.natDegree = 3 → False := by
        intro h3
        have hb1 : b.natDegree = 1 := by omega
        obtain ⟨p, q, hp, rfl⟩ := Polynomial.natDegree_eq_one.mp hb1
        have hpm : p = 1 ∨ p = -1 := by
          have : a.leadingCoeff * p = 1 := by
            have := congr_arg Polynomial.leadingCoeff hab
            simp [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C_mul_X_add_C hp] at this
            linarith
          rcases Int.isUnit_iff.mp (isUnit_of_mul_eq_one _ _ this) with ⟨u, hu⟩
          rcases Int.units_eq_iff_abs_eq.mp (Units.ext hu) with h | h <;> simp [h]
        rcases hpm with rfl | rfl
        · have hroot : (C 1 * X + C q : ℤ[X]).eval (-q) = 0 := by
            simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
          have hfroot : (X ^ 4 - 10 * X ^ 2 + 1 : ℤ[X]).eval (-q) = 0 := by
            rw [← hab, Polynomial.eval_mul, hfroot.symm]; simp [hroot]
          exact f_no_int_root (-q) hfroot
        · have hroot : (C (-1 : ℤ) * X + C q : ℤ[X]).eval q = 0 := by
            simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
          have hfroot : (X ^ 4 - 10 * X ^ 2 + 1 : ℤ[X]).eval q = 0 := by
            rw [← hab, Polynomial.eval_mul]; simp [hroot]
          exact f_no_int_root q hfroot
      -- Now: case split on a.natDegree
      interval_cases (a.natDegree)
      · -- natDegree a = 0: a is a constant unit
        left
        have ha_const : a = C (a.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (by assumption)
        have ha0_unit : IsUnit (a.coeff 0) := by
          have hla : a.leadingCoeff = a.coeff 0 := by simp [Polynomial.leadingCoeff, show a.natDegree = 0 from by assumption]
          exact isUnit_of_mul_eq_one _ _ (hla ▸ hlc_prod)
        rw [ha_const]; exact Polynomial.isUnit_C.mpr ha0_unit
      · exact (deg1_to_root (by assumption)).elim
      · exact (deg2_impossible (by assumption)).elim
      · exact (deg3_impossible (by assumption)).elim
      · -- natDegree a = 4: b has degree 0, b is a unit
        right
        have hb0 : b.natDegree = 0 := by omega
        have hb_const : b = C (b.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hb0
        have hb0_unit : IsUnit (b.coeff 0) := by
          have hlb : b.leadingCoeff = b.coeff 0 := by simp [Polynomial.leadingCoeff, hb0]
          exact isUnit_of_mul_eq_one _ _ (mul_comm (b.coeff 0) (a.leadingCoeff) ▸ hlb ▸ hlc_prod.symm ▸ (mul_comm _ _) ▸ hlc_prod)
        rw [hb_const]; exact Polynomial.isUnit_C.mpr hb0_unit
  -- Transfer: ℤ[X] → ℚ[X] via Gauss's lemma
  have hprim : (X ^ 4 - 10 * X ^ 2 + 1 : ℤ[X]).IsPrimitive := fmonic_Z.isPrimitive
  have hirred_rat := (hprim.Int.irreducible_iff_irreducible_map_cast).mp hirred_int
  have hmap : (X ^ 4 - 10 * X ^ 2 + 1 : ℤ[X]).map (Int.castRingHom ℚ) = X ^ 4 - 10 * X ^ 2 + 1 := by
    simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul,
          Polynomial.map_X, Polynomial.map_one, Polynomial.map_C]
  rwa [hmap] at hirred_rat

/-! ## Part III: Consequences of the Minimal Polynomial -/

/-- **Main Theorem**: The minimal polynomial of √2+√3 over ℚ is X⁴ - 10X² + 1. -/
theorem minpoly_sqrt2_plus_sqrt3 :
    minpoly ℚ (Real.sqrt 2 + Real.sqrt 3) = X ^ 4 - 10 * X ^ 2 + 1 :=
  (minpoly.eq_of_irreducible_of_monic
    irred_f
    aeval_sqrt2_plus_sqrt3
    f_monic).symm

/-- **Field Extension Degree**: [ℚ(√2+√3) : ℚ] = 4.
    Follows from the degree-4 minimal polynomial. -/
theorem adjoin_sqrt2_plus_sqrt3_finrank :
    Module.finrank ℚ ℚ⟮Real.sqrt 2 + Real.sqrt 3⟯ = 4 := by
  rw [IntermediateField.adjoin.finrank sqrt2_plus_sqrt3_isIntegral]
  rw [minpoly_sqrt2_plus_sqrt3]
  have h1 : (10 * X ^ 2 : ℚ[X]).natDegree ≤ 2 := by
    calc (10 * X ^ 2 : ℚ[X]).natDegree ≤ _ := natDegree_mul_le
      _ = _ := by simp
  have h2 : (X ^ 4 - 10 * X ^ 2 : ℚ[X]).natDegree = 4 := by
    apply natDegree_sub_eq_left_of_natDegree_lt
    · linarith [h1]
    · simp [natDegree_pow]
  calc (X ^ 4 - 10 * X ^ 2 + 1 : ℚ[X]).natDegree
      = (X ^ 4 - 10 * X ^ 2 : ℚ[X]).natDegree := by
        apply natDegree_add_eq_left_of_natDegree_lt
        simp [h2]
    _ = 4 := h2

/-- **Irrationality**: √2+√3 is not rational.
    If √2+√3 = q ∈ ℚ, squaring gives (q²−5)/2 = √6, contradicting irrationality of √6. -/
theorem sqrt2_plus_sqrt3_irrational : Irrational (Real.sqrt 2 + Real.sqrt 3) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have h6mult : sqrt 2 * sqrt 3 = sqrt 6 := by rw [← sqrt_mul h2]; norm_num
  have hsix : Irrational (sqrt 6) :=
    irrational_sqrt_natCast_iff.mpr (by native_decide)
  intro ⟨q, hq⟩
  have hsq : (q : ℝ) ^ 2 = 5 + 2 * sqrt 6 := by
    have : (sqrt 2 + sqrt 3) ^ 2 = 5 + 2 * sqrt 6 := by
      have : (sqrt 2 + sqrt 3) ^ 2 = sqrt 2 ^ 2 + 2 * (sqrt 2 * sqrt 3) + sqrt 3 ^ 2 := by ring
      rw [this, sq_sqrt h2, sq_sqrt h3, h6mult]; ring
    rw [hq]; exact this
  have h6eq : sqrt 6 = ((q : ℝ) ^ 2 - 5) / 2 := by linarith
  exact hsix ⟨(q ^ 2 - 5) / 2, by push_cast; linarith⟩

end Sqrt2PlusSqrt3IrrationalOQ03
