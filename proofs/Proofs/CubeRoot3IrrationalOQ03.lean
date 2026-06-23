/-
Proof: ∛3 has degree 3 over ℚ — irreducibility of X³ − 3, the minimal
polynomial, and the field degree [ℚ(∛3) : ℚ] = 3.
Research: cube-root-3-irrational-oq-03
Date: 2026-06-22

Open question (child of `cube-root-3-irrational`): extend the irrationality of
∛3 to the full statement that ∛3 has degree 3 over ℚ.

The original open-question wording asks for linear independence of
`{1, ∛3, (∛3)²}` over ℚ. A sibling entry (`cube-root-3-irrational-oq-04`, file
`CubeRoot3IrrationalOQ04NotQuadratic.lean`) already established the "no quadratic
relation" half via an abstract elementary elimination. To make genuine new
progress we go further and connect to Mathlib's field-theory layer, which the
sibling deliberately avoids:

  * `irreducible_X_cubed_sub_C_three` — **X³ − 3 is irreducible over ℚ**
    (the structural reason behind the linear independence), proved from the
    single arithmetic fact `no_rat_cube_three` via Mathlib's degree-≤3
    no-root ⇒ irreducible criterion;
  * `minpoly_cbrt3` — hence **X³ − 3 is the minimal polynomial of ∛3**;
  * `finrank_adjoin_cbrt3` — hence **[ℚ(∛3) : ℚ] = 3**.

We also record the linear-independence content directly, both in elementary
explicit form (`linindep_triple`) and in Mathlib's `LinearIndependent` predicate
form (`linearIndependent_cbrt3_powers`), the latter of which the sibling does
not provide.

## The one arithmetic input

Every result rests on: **3 has no rational cube root** (`no_rat_cube_three`).
Given `q³ = 3` with `q : ℚ`, the real number `(q : ℝ)` is a cube root of 3,
hence equal to `∛3` (the cube map `x ↦ x³` is injective on ℝ), making `∛3`
rational — contradicting the parent's `irrational_cbrt3`.
-/

import Mathlib
import Proofs.CubeRoot3Irrational

open CubeRoot3Irrational Polynomial IntermediateField

namespace CubeRoot3IrrationalOQ03

/-- The defining cubic of `∛3`, inherited from the parent file. -/
theorem cbrt3_pow_three : cbrt3 ^ 3 = 3 := cbrt3_cubed

/-- `∛3` is irrational, inherited from the parent file. -/
theorem cbrt3_irrational : Irrational cbrt3 := irrational_cbrt3

/-! ### The single arithmetic input: 3 is not a rational cube -/

/-- **No rational cube root of 3.** If `q³ = 3` for `q : ℚ` then `(q : ℝ)` is a
real cube root of 3, hence equal to `∛3` (the cube map is injective on ℝ),
making `∛3` rational — contradiction. -/
theorem no_rat_cube_three (q : ℚ) : q ^ 3 ≠ 3 := by
  intro hq
  have h1 : (q : ℝ) ^ 3 = cbrt3 ^ 3 := by
    rw [cbrt3_pow_three]; exact_mod_cast hq
  have hodd : Odd 3 := by norm_num
  have h2 : (q : ℝ) = cbrt3 := hodd.strictMono_pow.injective h1
  exact cbrt3_irrational ⟨q, h2⟩

/-- No rational cube root of `-3` (immediate from `no_rat_cube_three`). -/
theorem no_rat_cube_neg_three (q : ℚ) : q ^ 3 ≠ -3 := by
  intro hq
  apply no_rat_cube_three (-q)
  rw [show (-q) ^ 3 = -(q ^ 3) by ring, hq]; ring

/-! ### Irreducibility, minimal polynomial, and field degree

These are the genuinely new, field-theoretic results extending the parent. -/

/-- **X³ − 3 is irreducible over ℚ.** A monic cubic is irreducible over a field
iff it has no root; here the no-root condition is exactly `no_rat_cube_three`. -/
theorem irreducible_X_cubed_sub_C_three :
    Irreducible (X ^ 3 - C 3 : ℚ[X]) := by
  have hnd : (X ^ 3 - C 3 : ℚ[X]).natDegree = 3 := natDegree_X_pow_sub_C
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [Finset.mem_Icc, hnd]; omega
  · intro x hx
    rw [IsRoot.def] at hx
    simp only [eval_sub, eval_pow, eval_X, eval_C] at hx
    exact no_rat_cube_three x (by linarith [hx])

/-- `∛3` is integral over ℚ: it is a root of the monic polynomial `X³ − 3`. -/
theorem cbrt3_isIntegral : IsIntegral ℚ cbrt3 :=
  ⟨X ^ 3 - C 3, monic_X_pow_sub_C _ (by norm_num),
    by simp [cbrt3_pow_three]⟩

/-- **X³ − 3 is the minimal polynomial of `∛3` over ℚ.** Immediate from
irreducibility, monicity, and `(∛3)³ = 3`. -/
theorem minpoly_cbrt3 : minpoly ℚ cbrt3 = X ^ 3 - C 3 :=
  (minpoly.eq_of_irreducible_of_monic irreducible_X_cubed_sub_C_three
    (by simp [aeval_X_pow, aeval_C, cbrt3_pow_three])
    (monic_X_pow_sub_C _ (by norm_num))).symm

/-- **The field degree `[ℚ(∛3) : ℚ] = 3`.** The dimension of the simple
extension equals the degree of the minimal polynomial. -/
theorem finrank_adjoin_cbrt3 : Module.finrank ℚ ℚ⟮cbrt3⟯ = 3 := by
  rw [IntermediateField.adjoin.finrank cbrt3_isIntegral, minpoly_cbrt3,
    natDegree_X_pow_sub_C]

/-! ### Linear independence of `{1, ∛3, (∛3)²}` over ℚ

The original open-question statement. We give a self-contained elementary proof
(the elimination reduces to `no_rat_cube_three`) and package it in Mathlib's
`LinearIndependent` predicate form. -/

/-- **`{1, ∛3, (∛3)²}` are linearly independent over ℚ**, explicit form: any
rational combination `a·1 + b·∛3 + c·(∛3)²` that vanishes has `a = b = c = 0`. -/
theorem linindep_triple (a b c : ℚ)
    (H : (a : ℝ) + (b : ℝ) * cbrt3 + (c : ℝ) * cbrt3 ^ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  by_cases hc : c = 0
  · subst hc
    simp only [Rat.cast_zero, zero_mul, add_zero] at H
    by_cases hb : b = 0
    · subst hb
      simp only [Rat.cast_zero, zero_mul, add_zero] at H
      exact ⟨by exact_mod_cast H, rfl, rfl⟩
    · exfalso
      have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
      have ht : cbrt3 = ((-a / b : ℚ) : ℝ) := by
        have hcast : ((-a / b : ℚ) : ℝ) = -(a : ℝ) / (b : ℝ) := by push_cast; ring
        rw [hcast, eq_div_iff hbR]
        linear_combination H
      exact cbrt3_irrational ⟨-a / b, ht.symm⟩
  · exfalso
    have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    -- second relation: multiply by `t` and use `t³ = 3`
    have hE1 : 3 * (c : ℝ) + (a : ℝ) * cbrt3 + (b : ℝ) * cbrt3 ^ 2 = 0 := by
      linear_combination cbrt3 * H - (c : ℝ) * cbrt3_pow_three
    -- eliminate `t²` between H and hE1
    have hI : ((a : ℝ) * (c : ℝ) - (b : ℝ) ^ 2) * cbrt3
        = (a : ℝ) * (b : ℝ) - 3 * (c : ℝ) ^ 2 := by
      linear_combination (c : ℝ) * hE1 - (b : ℝ) * H
    by_cases hα : a * c - b ^ 2 = 0
    · -- degenerate case forces `(b/c)³ = 3`
      have hαR : (a : ℝ) * (c : ℝ) - (b : ℝ) ^ 2 = 0 := by exact_mod_cast hα
      rw [hαR, zero_mul] at hI
      have hβ : a * b - 3 * c ^ 2 = 0 := by
        have : (a : ℝ) * (b : ℝ) - 3 * (c : ℝ) ^ 2 = 0 := by linarith [hI]
        exact_mod_cast this
      have hab : a * b = 3 * c ^ 2 := by linarith [hβ]
      have hb3 : b ^ 3 = 3 * c ^ 3 := by
        have hbb : b ^ 3 = c * (a * b) := by linear_combination (-b) * hα
        rw [hab] at hbb; rw [hbb]; ring
      apply no_rat_cube_three (b / c)
      have hc3 : c ^ 3 ≠ 0 := pow_ne_zero 3 hc
      rw [div_pow, hb3, mul_div_assoc, div_self hc3, mul_one]
    · -- nondegenerate case forces `∛3` rational
      have hαR : (a : ℝ) * (c : ℝ) - (b : ℝ) ^ 2 ≠ 0 := by
        intro h; exact hα (by exact_mod_cast h)
      have ht : cbrt3 = (((a * b - 3 * c ^ 2) / (a * c - b ^ 2) : ℚ) : ℝ) := by
        have hcast : (((a * b - 3 * c ^ 2) / (a * c - b ^ 2) : ℚ) : ℝ)
            = ((a : ℝ) * (b : ℝ) - 3 * (c : ℝ) ^ 2)
              / ((a : ℝ) * (c : ℝ) - (b : ℝ) ^ 2) := by push_cast; ring
        rw [hcast, eq_div_iff hαR]
        linear_combination hI
      exact cbrt3_irrational ⟨_, ht.symm⟩

/-- **Linear independence in Mathlib's `LinearIndependent` form.** The family
`![1, ∛3, (∛3)²] : Fin 3 → ℝ` is linearly independent over ℚ. -/
theorem linearIndependent_cbrt3_powers :
    LinearIndependent ℚ ![(1 : ℝ), cbrt3, cbrt3 ^ 2] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Rat.smul_def] at hg
  rw [mul_one] at hg
  have key := linindep_triple (g 0) (g 1) (g 2) hg
  intro i
  fin_cases i
  · exact key.1
  · exact key.2.1
  · exact key.2.2

/-- Restated negatively: `∛3` satisfies no rational polynomial of degree ≤ 2 —
there is no quadratic relation `(∛3)² = b·∛3 + c` with `b, c ∈ ℚ`. -/
theorem cbrt3_no_quadratic_relation (b c : ℚ)
    (H : cbrt3 ^ 2 = (b : ℝ) * cbrt3 + (c : ℝ)) : False := by
  have := linindep_triple (-c) (-b) 1 (by push_cast; linear_combination H)
  exact one_ne_zero this.2.2

end CubeRoot3IrrationalOQ03
