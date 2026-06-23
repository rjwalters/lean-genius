/-
  ∛3 generates a degree-3 extension of ℚ that is NOT normal (not Galois)
  =====================================================================

  Open question `cube-root-3-irrational-oq-03`.

  Sibling files already establish the *size* of ℚ(∛3): `X³ − 3` is irreducible
  over ℚ (OQ-01/OQ-02), it is the minimal polynomial of ∛3, and the extension
  has degree 3 (OQ-04Degree). None of them touches the *structure* of the
  extension — whether ℚ(∛3)/ℚ is normal/Galois. This file fills that gap.

  The phenomenon: ℚ(∛3) is a degree-3 extension that is **not normal**. The
  reason is real-analytic. Cubing is strictly monotone on ℝ, so `X³ − 3` has a
  *unique* real root, namely ∛3; over ℝ it factors as

      X³ − 3 = (X − ∛3)·(X² + ∛3·X + ∛9),

  and the quadratic cofactor has negative discriminant (∛9 − 4·∛9 = −3·∛9 < 0),
  hence stays strictly positive and has no real root. Therefore `X³ − 3` does
  not split into linear factors even over the *whole* of ℝ, let alone over the
  real subfield ℚ(∛3). Since the minimal polynomial of ∛3 fails to split inside
  ℚ(∛3), the extension is not normal.

  This is the classic first example of a finite, separable, but non-normal
  extension — degree 3 yet not Galois, with Galois closure ℚ(∛3, ω) of degree 6.

  ── Self-contained ─────────────────────────────────────────────────────────
  Re-derives `cbrt3`, `cbrt3_cubed`, and irrationality locally (only `import
  Mathlib`) so the file builds without the parent oleans.

  ── Main results ───────────────────────────────────────────────────────────
    unique_real_cube_root        x³ = 3 ↔ x = ∛3   (exactly one real cube root)
    quadratic_cofactor_pos       0 < x² + ∛3·x + ∛9  (cofactor has no real root)
    real_factorization           X³ − 3 = (X − ∛3)(X² + ∛3 X + ∛9) over ℝ
    not_splits_over_real         ¬ (X³ − 3 : ℝ[X]).Splits
    minpoly_cbrt3                 minpoly ℚ ∛3 = X³ − 3
    cbrt3_not_normal             ¬ Normal ℚ ℚ⟮∛3⟯   ← the headline
-/
import Mathlib

open Polynomial IntermediateField

namespace CubeRoot3IrrationalOQ03

/-- The real cube root of `3`. -/
noncomputable def cbrt3 : ℝ := (3 : ℝ) ^ (1 / 3 : ℝ)

/-- `(∛3)³ = 3`. -/
theorem cbrt3_cubed : cbrt3 ^ 3 = 3 := by
  unfold cbrt3
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-- `∛3 > 0`. -/
theorem cbrt3_pos : 0 < cbrt3 := Real.rpow_pos_of_pos (by norm_num) _

/-! ### Exactly one real cube root -/

/-- Cubing is injective on `ℝ` (odd power of a linearly ordered ring). -/
theorem cube_injective : Function.Injective (fun x : ℝ => x ^ 3) :=
  (Odd.strictMono_pow (by decide : Odd 3)).injective

/-- `3` has a **unique** real cube root, namely `∛3`. -/
theorem unique_real_cube_root (x : ℝ) : x ^ 3 = 3 ↔ x = cbrt3 := by
  constructor
  · intro hx
    exact cube_injective (show x ^ 3 = cbrt3 ^ 3 by rw [hx, cbrt3_cubed])
  · intro hx; rw [hx, cbrt3_cubed]

/-! ### The real quadratic cofactor has no real root -/

/-- The cofactor `x² + ∛3·x + ∛9` is strictly positive: its discriminant
`(∛3)² − 4·(∛3)² = −3·(∛3)²` is negative, so it never vanishes on `ℝ`. -/
theorem quadratic_cofactor_pos (x : ℝ) : 0 < x ^ 2 + cbrt3 * x + cbrt3 ^ 2 := by
  have h := cbrt3_pos
  nlinarith [sq_nonneg (2 * x + cbrt3), mul_pos h h]

/-! ### Real factorization and non-splitting -/

/-- Over `ℝ`, `X³ − 3 = (X − ∛3)(X² + ∛3·X + ∛9)`. -/
theorem real_factorization :
    (X ^ 3 - C 3 : ℝ[X]) = (X - C cbrt3) * (X ^ 2 + C cbrt3 * X + C cbrt3 ^ 2) := by
  have h : (C (3 : ℝ) : ℝ[X]) = (C cbrt3) ^ 3 := by rw [← map_pow, cbrt3_cubed]
  rw [h]; ring

/-- `X³ − 3` is a nonzero polynomial over `ℝ`. -/
theorem X3_sub_3_ne_zero : (X ^ 3 - C 3 : ℝ[X]) ≠ 0 :=
  X_pow_sub_C_ne_zero (by norm_num) 3

/-- **`X³ − 3` does not split over `ℝ`.** A degree-2 real factor with no real
root obstructs splitting into linear factors. -/
theorem not_splits_over_real : ¬ (X ^ 3 - C 3 : ℝ[X]).Splits := by
  intro hsplit
  rw [real_factorization] at hsplit
  have hL : (X - C cbrt3 : ℝ[X]) ≠ 0 := (monic_X_sub_C cbrt3).ne_zero
  have hR : (X ^ 2 + C cbrt3 * X + C cbrt3 ^ 2 : ℝ[X]) ≠ 0 := by
    have h0 := X3_sub_3_ne_zero
    rw [real_factorization] at h0
    exact right_ne_zero_of_mul h0
  obtain ⟨_, hQ⟩ := (splits_mul_iff hL hR).mp hsplit
  have hdeg2 : (X ^ 2 + C cbrt3 * X + C cbrt3 ^ 2 : ℝ[X]).degree = 2 := by
    compute_degree!
  obtain ⟨r, hr⟩ := hQ.exists_eval_eq_zero (by rw [hdeg2]; decide)
  have hval : r ^ 2 + cbrt3 * r + cbrt3 ^ 2 = 0 := by
    simpa [eval_add, eval_mul, eval_pow, eval_X, eval_C] using hr
  linarith [quadratic_cofactor_pos r]

/-! ### Irreducibility and the minimal polynomial (self-contained) -/

/-- `3` is not a perfect cube in `ℤ` (`1³ = 1 < 3 < 8 = 2³`). -/
theorem three_not_perfect_cube : ¬ ∃ n : ℤ, n ^ 3 = 3 := by
  rintro ⟨n, hn⟩
  have h1 : 0 < n := by
    by_contra h
    push_neg at h
    have hn3 : n ^ 3 ≤ 0 := by
      have : n ^ 3 = n * n * n := by ring
      rw [this]; nlinarith
    omega
  have h2 : n < 2 := by
    by_contra h
    push_neg at h
    have hn3 : n ^ 3 ≥ 8 := by
      have : n ^ 3 = n * n * n := by ring
      rw [this]; nlinarith
    omega
  have : n = 1 := by omega
  rw [this] at hn; norm_num at hn

/-- `∛3` is not an integer. -/
theorem cbrt3_not_int : ¬ ∃ n : ℤ, cbrt3 = n := by
  rintro ⟨n, hn⟩
  have h : n ^ 3 = 3 := by
    have : cbrt3 ^ 3 = 3 := cbrt3_cubed
    rw [hn] at this; exact_mod_cast this
  exact three_not_perfect_cube ⟨n, h⟩

/-- `∛3` is irrational. -/
theorem irrational_cbrt3 : Irrational cbrt3 := by
  apply irrational_nrt_of_notint_nrt 3 3
  · exact_mod_cast cbrt3_cubed
  · exact cbrt3_not_int
  · norm_num

/-- `3` has no cube root in `ℚ`: a rational cube root would force `∛3 ∈ ℚ`. -/
theorem not_cube_rat (b : ℚ) : b ^ 3 ≠ 3 := by
  intro hb
  have hcast : (b : ℝ) ^ 3 = 3 := by exact_mod_cast hb
  exact irrational_cbrt3 ⟨b, (unique_real_cube_root b).mp hcast⟩

/-- `X³ − 3` is irreducible over `ℚ` (Kummer / Eisenstein at the prime 3). -/
theorem irreducible_X_cubed_sub_C : Irreducible (X ^ 3 - C (3 : ℚ)) :=
  (X_pow_sub_C_irreducible_iff_of_prime (by norm_num : Nat.Prime 3)).mpr not_cube_rat

/-- `∛3` is a root of `X³ − 3`. -/
theorem aeval_cbrt3 : (aeval cbrt3) (X ^ 3 - C (3 : ℚ)) = 0 := by
  have h3 : (algebraMap ℚ ℝ) (3 : ℚ) = (3 : ℝ) := by norm_num
  simp only [map_sub, map_pow, aeval_X, aeval_C, h3]
  rw [cbrt3_cubed]; norm_num

/-- **The minimal polynomial of `∛3` over `ℚ` is `X³ − 3`.** -/
theorem minpoly_cbrt3 : minpoly ℚ cbrt3 = X ^ 3 - C (3 : ℚ) :=
  (minpoly.eq_of_irreducible_of_monic irreducible_X_cubed_sub_C aeval_cbrt3
    (monic_X_pow_sub_C (3 : ℚ) (by norm_num))).symm

/-! ### The minimal polynomial fails to split over ℝ ⊇ ℚ(∛3) -/

/-- The minimal polynomial of `∛3`, viewed over `ℝ`, does not split. Since
`ℚ(∛3) ⊆ ℝ`, it cannot split inside `ℚ(∛3)` either. -/
theorem not_splits_minpoly_over_real :
    ¬ ((X ^ 3 - C 3 : ℚ[X]).map (algebraMap ℚ ℝ)).Splits := by
  have h3 : (algebraMap ℚ ℝ) (3 : ℚ) = (3 : ℝ) := by norm_num
  have hmap : (X ^ 3 - C 3 : ℚ[X]).map (algebraMap ℚ ℝ) = (X ^ 3 - C 3 : ℝ[X]) := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, h3]
  rw [hmap]; exact not_splits_over_real

/-! ### The headline: ℚ(∛3) is not normal over ℚ -/

/-- **`ℚ(∛3)/ℚ` is not a normal extension** (hence not Galois). If it were
normal, the minimal polynomial `X³ − 3` of `∛3` would split inside `ℚ(∛3)`, and
therefore (pushing along `ℚ(∛3) ↪ ℝ`) over `ℝ` — contradicting
`not_splits_over_real`. This is a degree-3 extension that is not Galois. -/
theorem cbrt3_not_normal : ¬ Normal ℚ ℚ⟮cbrt3⟯ := by
  intro hnorm
  have h1 := hnorm.splits (AdjoinSimple.gen ℚ cbrt3)
  rw [IntermediateField.minpoly_gen] at h1
  have h2 : ((minpoly ℚ cbrt3).map (algebraMap ℚ ℝ)).Splits := splits_of_isScalarTower ℝ h1
  rw [minpoly_cbrt3] at h2
  exact not_splits_minpoly_over_real h2

end CubeRoot3IrrationalOQ03
