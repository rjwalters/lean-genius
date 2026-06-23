/-
Proof: the fourth root of 2 has degree 4 over ℚ — irreducibility of X⁴ − 2
(Eisenstein at the prime 2, transferred to ℚ by Gauss's lemma), the minimal
polynomial, the field degree [ℚ(⁴√2) : ℚ] = 4, the quadratic tower
ℚ ⊂ ℚ(√2) ⊂ ℚ(⁴√2), and the ℚ-linear independence of the power basis
{1, ⁴√2, √2, ⁴√8}.
Research: fourth-root-2-irrational
Date: 2026-06-22

Fresh entry (sibling of `cube-root-3-irrational` and `sqrt2-irrational`). The
parent template only asks for the irrationality of `⁴√2`. We prove the sharp
algebraic statement that `⁴√2` has degree exactly 4 over ℚ.

The crux is the irreducibility of `X⁴ − 2`. Note this is precisely the case
Mathlib's Kummer-theory API cannot reach: `X_pow_sub_C_irreducible_of_prime_pow`
requires the prime `p ≠ 2`, and `X_pow_sub_C_irreducible_of_odd` requires odd
exponent — the source carries explicit `TODO: generalize to p = 2 / even n`.
Since `4 = 2²`, neither applies. We instead route through **Eisenstein's
criterion at the prime 2** over ℤ (`irreducible_of_eisenstein_criterion`, which
applies cleanly: the lower coefficients `0, 0, 0, -2` all lie in `(2)`, the
constant term `-2 ∉ (4) = (2)²`, and the leading coefficient `1 ∉ (2)`),
followed by **Gauss's lemma** (`IsPrimitive.Int.irreducible_iff_irreducible_map_cast`)
to descend irreducibility from ℤ[X] to ℚ[X].

Results:
  * `irreducible_X4_sub_2_int` — X⁴ − 2 is irreducible over ℤ (Eisenstein at 2);
  * `irreducible_X4_sub_2_rat` — hence irreducible over ℚ (Gauss);
  * `minpoly_fr2` — X⁴ − 2 is the minimal polynomial of ⁴√2 over ℚ;
  * `finrank_adjoin_fr2` — [ℚ(⁴√2) : ℚ] = 4;
  * `fr2_sq_eq_sqrt2` / `sqrt2_mem_adjoin_fr2` — the tower ℚ ⊂ ℚ(√2) ⊂ ℚ(⁴√2);
  * `linearIndependent_fr2_powers` — {1, ⁴√2, √2, ⁴√8} are ℚ-linearly independent;
  * `fr2_no_cubic_relation` — ⁴√2 satisfies no rational relation of degree ≤ 3.

`⁴√2` is modeled concretely as `Real.sqrt (Real.sqrt 2)`, so that `(⁴√2)² = √2`
and `(⁴√2)⁴ = 2` hold definitionally up to `Real.sq_sqrt`.
-/

import Mathlib

open Polynomial IntermediateField

namespace FourthRoot2Degree4

/-- The real fourth root of 2, modeled as `√√2`. -/
noncomputable def fr2 : ℝ := Real.sqrt (Real.sqrt 2)

theorem fr2_nonneg : 0 ≤ fr2 := Real.sqrt_nonneg _

/-- `(⁴√2)² = √2`. -/
theorem fr2_sq : fr2 ^ 2 = Real.sqrt 2 := by
  unfold fr2; rw [Real.sq_sqrt (Real.sqrt_nonneg 2)]

/-- `(⁴√2)⁴ = 2`. -/
theorem fr2_pow_four : fr2 ^ 4 = 2 := by
  have h : fr2 ^ 4 = (fr2 ^ 2) ^ 2 := by ring
  rw [h, fr2_sq, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-! ### The arithmetic input: 2 has no rational fourth root -/

/-- **No rational fourth root of 2.** If `q⁴ = 2` for `q : ℚ`, then `q²` is a
rational square root of 2, contradicting the irrationality of `√2`. -/
theorem no_rat_fourth_two (q : ℚ) : q ^ 4 ≠ 2 := by
  intro hq
  set r : ℚ := q ^ 2 with hr
  have hrR : (r : ℝ) = (q : ℝ) ^ 2 := by rw [hr]; push_cast; ring
  have hqR : (q : ℝ) ^ 4 = 2 := by exact_mod_cast hq
  have hr2 : (r : ℝ) ^ 2 = 2 := by rw [hrR]; nlinarith [hqR]
  have hrnn : (0 : ℝ) ≤ (r : ℝ) := by rw [hrR]; positivity
  have hsqrt : Real.sqrt 2 = (r : ℝ) := by
    rw [← hr2, Real.sqrt_sq hrnn]
  exact irrational_sqrt_two ⟨r, hsqrt.symm⟩

/-- **`⁴√2` is irrational.** -/
theorem fr2_irrational : Irrational fr2 := by
  rintro ⟨q, hq⟩
  apply no_rat_fourth_two q
  have h : (q : ℝ) ^ 4 = 2 := by rw [hq]; exact fr2_pow_four
  exact_mod_cast h

/-- `⁴√2` is integral over ℚ: a root of the monic polynomial `X⁴ − 2`. -/
theorem fr2_isIntegral : IsIntegral ℚ fr2 :=
  ⟨X ^ 4 - C 2, monic_X_pow_sub_C _ (by norm_num),
    by simp [fr2_pow_four]⟩

/-! ### Irreducibility of `X⁴ − 2`: Eisenstein at 2, then Gauss -/

/-- Coefficient description of `X⁴ − 2` over ℤ. -/
private theorem coeff_X4_sub_2 (n : ℕ) :
    (X ^ 4 - C 2 : ℤ[X]).coeff n
      = (if n = 4 then (1 : ℤ) else 0) - (if n = 0 then 2 else 0) := by
  simp only [coeff_sub, coeff_X_pow, coeff_C]

/-- **X⁴ − 2 is irreducible over ℤ**, by Eisenstein's criterion at the prime 2:
the leading coefficient `1` avoids `(2)`, all lower coefficients lie in `(2)`,
and the constant term `−2` avoids `(2)² = (4)`. -/
theorem irreducible_X4_sub_2_int : Irreducible (X ^ 4 - C 2 : ℤ[X]) := by
  have hmonic : (X ^ 4 - C 2 : ℤ[X]).Monic := monic_X_pow_sub_C _ (by norm_num)
  have hlc : (X ^ 4 - C 2 : ℤ[X]).leadingCoeff = 1 := hmonic
  have hdeg : (X ^ 4 - C 2 : ℤ[X]).degree = 4 :=
    degree_X_pow_sub_C (by norm_num) 2
  apply irreducible_of_eisenstein_criterion (P := Ideal.span {2})
  · -- (2) is prime
    rw [Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)]
    exact Int.prime_two
  · -- leadingCoeff = 1 ∉ (2)
    rw [hlc, Ideal.mem_span_singleton]; norm_num
  · -- lower coefficients lie in (2)
    intro n hn
    rw [hdeg] at hn
    have hn4 : n ≠ 4 := by
      intro h; rw [h] at hn; exact absurd hn (by norm_num)
    rw [coeff_X4_sub_2, if_neg hn4, Ideal.mem_span_singleton]
    split_ifs <;> norm_num
  · -- 0 < degree
    rw [hdeg]; norm_num
  · -- constant term −2 ∉ (2)² = (4)
    rw [coeff_X4_sub_2, if_neg (by norm_num : (0:ℕ) ≠ 4), if_pos rfl,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    norm_num
  · -- primitive (monic ⇒ primitive)
    exact hmonic.isPrimitive

/-- **X⁴ − 2 is irreducible over ℚ.** Gauss's lemma descends irreducibility of
the primitive integer polynomial to ℚ. -/
theorem irreducible_X4_sub_2_rat : Irreducible (X ^ 4 - C 2 : ℚ[X]) := by
  have hprim : (X ^ 4 - C 2 : ℤ[X]).IsPrimitive :=
    (monic_X_pow_sub_C _ (by norm_num)).isPrimitive
  have h := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp
    irreducible_X4_sub_2_int
  have hmap : (X ^ 4 - C 2 : ℤ[X]).map (Int.castRingHom ℚ) = X ^ 4 - C 2 := by
    simp [Polynomial.map_sub, Polynomial.map_pow, map_X, map_ofNat]
  rwa [hmap] at h

/-! ### Minimal polynomial and field degree -/

/-- **X⁴ − 2 is the minimal polynomial of `⁴√2` over ℚ.** -/
theorem minpoly_fr2 : minpoly ℚ fr2 = X ^ 4 - C 2 :=
  (minpoly.eq_of_irreducible_of_monic irreducible_X4_sub_2_rat
    (by simp [fr2_pow_four]) (monic_X_pow_sub_C _ (by norm_num))).symm

theorem minpoly_natDegree_fr2 : (minpoly ℚ fr2).natDegree = 4 := by
  rw [minpoly_fr2, natDegree_X_pow_sub_C]

/-- **The field degree `[ℚ(⁴√2) : ℚ] = 4`.** -/
theorem finrank_adjoin_fr2 : Module.finrank ℚ ℚ⟮fr2⟯ = 4 := by
  rw [IntermediateField.adjoin.finrank fr2_isIntegral, minpoly_natDegree_fr2]

/-! ### The quadratic tower ℚ ⊂ ℚ(√2) ⊂ ℚ(⁴√2)

`⁴√2` generates `√2` (since `(⁴√2)² = √2`), so `ℚ(√2) ⊆ ℚ(⁴√2)`; the field
degrees multiply as `4 = 2 · 2`. -/

/-- `√2` lies in `ℚ(⁴√2)`, being `(⁴√2)²`. -/
theorem sqrt2_mem_adjoin_fr2 : Real.sqrt 2 ∈ ℚ⟮fr2⟯ := by
  rw [← fr2_sq]
  exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ fr2) 2

/-- `[ℚ(√2) : ℚ] = 2`: the bottom step of the tower. -/
theorem finrank_adjoin_sqrt2 : Module.finrank ℚ ℚ⟮Real.sqrt 2⟯ = 2 := by
  have hint : IsIntegral ℚ (Real.sqrt 2) :=
    ⟨X ^ 2 - C 2, monic_X_pow_sub_C _ (by norm_num),
      by simp [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]⟩
  have hirr : Irreducible (X ^ 2 - C 2 : ℚ[X]) := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · rw [Finset.mem_Icc, natDegree_X_pow_sub_C]; omega
    · intro x hx
      rw [IsRoot.def] at hx
      simp only [eval_sub, eval_pow, eval_X, eval_C] at hx
      -- x² = 2 has no rational solution
      have hx2 : (x : ℝ) ^ 2 = 2 := by exact_mod_cast (by linarith [hx] : x ^ 2 = (2:ℚ))
      have hxnn : (0:ℝ) ≤ |(x:ℝ)| := abs_nonneg _
      have : Real.sqrt 2 = |(x:ℝ)| := by
        rw [← hx2, Real.sqrt_sq_eq_abs]
      exact irrational_sqrt_two ⟨|x|, by push_cast at this ⊢; rw [this]⟩
  have hmp : minpoly ℚ (Real.sqrt 2) = X ^ 2 - C 2 :=
    (minpoly.eq_of_irreducible_of_monic hirr
      (by simp [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)])
      (monic_X_pow_sub_C _ (by norm_num))).symm
  rw [IntermediateField.adjoin.finrank hint, hmp, natDegree_X_pow_sub_C]

/-! ### ℚ-linear independence of the power basis {1, ⁴√2, √2, ⁴√8} -/

/-- **The powers `{1, ⁴√2, (⁴√2)², (⁴√2)³} = {1, ⁴√2, √2, ⁴√8}` are ℚ-linearly
independent.** Direct consequence of `[ℚ(⁴√2):ℚ] = 4`: the powers below the
degree of the minimal polynomial are independent. -/
theorem linearIndependent_fr2_powers :
    LinearIndependent ℚ (fun i : Fin 4 => fr2 ^ (i : ℕ)) := by
  have h := linearIndependent_pow (K := ℚ) fr2
  rw [minpoly_natDegree_fr2] at h
  exact h

/-- **`⁴√2` satisfies no rational relation of degree ≤ 3:** if
`a + b·⁴√2 + c·(⁴√2)² + d·(⁴√2)³ = 0` with `a,b,c,d ∈ ℚ`, then all are zero. -/
theorem fr2_no_cubic_relation (a b c d : ℚ)
    (H : (a : ℝ) + (b : ℝ) * fr2 + (c : ℝ) * fr2 ^ 2 + (d : ℝ) * fr2 ^ 3 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hli := linearIndependent_fr2_powers
  rw [Fintype.linearIndependent_iff] at hli
  have key := hli ![a, b, c, d] ?_
  · exact ⟨key 0, key 1, key 2, key 3⟩
  · have h2 : ((2 : Fin 4) : ℕ) = 2 := rfl
    have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
      Fin.val_zero, Fin.val_one, h2, h3, pow_zero, pow_one, Rat.smul_def]
    linear_combination H

end FourthRoot2Degree4
