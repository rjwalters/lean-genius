import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-
# Niven's Theorem, OQ-01-OQ-02: the Vieta–Lucas monic recurrence, from scratch

## What This Proves

The parent entry `niven-theorem-oq-01` proves Niven's theorem but discharges its
deep half — "`2·cos θ` is an algebraic integer whenever `θ` is a rational multiple
of `π`" — by *citing* the Mathlib black box `Real.isIntegral_two_mul_cos_rat_mul_pi`
(proved internally via roots of unity).

This file replaces that citation with the classical, explicit mechanism: the
**Vieta–Lucas** (normalized Chebyshev-of-the-first-kind) polynomials

    C₀(x) = 2,   C₁(x) = x,   C_{n+2}(x) = x·C_{n+1}(x) − C_n(x)

are **monic integer** polynomials satisfying the fundamental identity

    2·cos(n θ) = C_n(2·cos θ)          for all n ∈ ℕ, θ ∈ ℝ.

Because each `C_n` (n ≥ 1) is monic with integer coefficients, and because
`2·cos(n θ) = ±2 ∈ ℤ` when `θ = (k/n)·π`, the number `2·cos θ` is a root of the
monic integer polynomial `C_n(X) − 2·cos(n θ) ∈ ℤ[X]`, hence an algebraic integer.

## Main results

* `C`                    — the Vieta–Lucas polynomials in `ℤ[X]`.
* `C_monic`              — `C (n+1)` is monic (of degree `n+1`).
* `C_eval_two_cos`       — `2·cos(n θ) = aeval (2·cos θ) (C n)`, by two-step induction
                           on the cosine addition formula. *This is the mathematical core.*
* `isIntegral_two_mul_cos`     — the explicit-witness replacement for
                                 `Real.isIntegral_two_mul_cos_rat_mul_pi`.
* `isIntegral_two_mul_cos_rat` — the same in the familiar `θ = (m/n)·π` form.

Everything is verified from scratch: no `sorry`, no `axiom`, and no appeal to the
Mathlib Niven lemma or to `Polynomial.Chebyshev`.
-/

open Polynomial Real

namespace NivenOQ0102

/-- The Vieta–Lucas polynomials `C n ∈ ℤ[X]`:
`C₀ = 2`, `C₁ = X`, `C_{n+2} = X·C_{n+1} − C_n`.
These are the monic normalization of the Chebyshev polynomials of the first kind:
`C_n(2 cos θ) = 2 cos(n θ)`. -/
noncomputable def C : ℕ → Polynomial ℤ
  | 0 => 2
  | 1 => Polynomial.X
  | (n + 2) => Polynomial.X * C (n + 1) - C n

@[simp] lemma C_zero : C 0 = 2 := rfl
@[simp] lemma C_one : C 1 = Polynomial.X := rfl

/-- Defining recurrence, as a rewrite lemma. -/
lemma C_succ_succ (n : ℕ) : C (n + 2) = Polynomial.X * C (n + 1) - C n := rfl

/-- `C 2 = X² − 2` (so `2 cos 2θ = (2 cos θ)² − 2`). -/
example : C 2 = Polynomial.X ^ 2 - 2 := by
  rw [C_succ_succ, C_one, C_zero]; ring

/-- `C 3 = X³ − 3X` (so `2 cos 3θ = (2 cos θ)³ − 3(2 cos θ)`). -/
example : C 3 = Polynomial.X ^ 3 - 3 * Polynomial.X := by
  rw [C_succ_succ, C_succ_succ, C_one, C_zero]; ring

/-- Both facts we need about the shape of `C`, proved together by two-step induction:
for every `n ≥ 1`, `C n` is monic of degree exactly `n`. Stated with the index shifted
to `n + 1` so that only the monic polynomials `C 1, C 2, …` are involved. -/
lemma C_monic_natDegree :
    ∀ n : ℕ, Monic (C (n + 1)) ∧ (C (n + 1)).natDegree = n + 1 := by
  -- Prove the statement together with its successor, so the two-step recurrence closes.
  have H : ∀ n : ℕ,
      (Monic (C (n + 1)) ∧ (C (n + 1)).natDegree = n + 1) ∧
      (Monic (C (n + 2)) ∧ (C (n + 2)).natDegree = n + 2) := by
    intro n
    induction n with
    | zero =>
      -- Base: handle C 1 = X and C 2 = X·X − 2 explicitly.
      have hm1 : Monic (C 1) := by rw [C_one]; exact monic_X
      have hd1 : (C 1).natDegree = 1 := by simp [C_one]
      have hmul : Monic (Polynomial.X * C 1) := monic_X.mul hm1
      have hmuld : (Polynomial.X * C 1).natDegree = 2 := by
        rw [Monic.natDegree_mul monic_X hm1, natDegree_X, hd1]
      have hd0 : (C 0).natDegree = 0 := by simp [C_zero]
      have hlt : (C 0).natDegree < (Polynomial.X * C 1).natDegree := by rw [hmuld, hd0]; omega
      refine ⟨⟨hm1, hd1⟩, ?_, ?_⟩
      · rw [C_succ_succ 0]; exact hmul.sub_of_left (degree_lt_degree hlt)
      · rw [C_succ_succ 0, natDegree_sub_eq_left_of_natDegree_lt hlt, hmuld]
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih          -- h1: about C (k+1);  h2: about C (k+2)
      refine ⟨h2, ?_⟩
      -- Now prove the claim for C (k+3) = X·C (k+2) − C (k+1).
      have hmul : Monic (Polynomial.X * C (k + 2)) := monic_X.mul h2.1
      have hmuld : (Polynomial.X * C (k + 2)).natDegree = k + 3 := by
        rw [Monic.natDegree_mul monic_X h2.1, natDegree_X, h2.2]; omega
      have hlt : (C (k + 1)).natDegree < (Polynomial.X * C (k + 2)).natDegree := by
        rw [hmuld, h1.2]; omega
      refine ⟨?_, ?_⟩
      · rw [C_succ_succ (k + 1)]; exact hmul.sub_of_left (degree_lt_degree hlt)
      · rw [C_succ_succ (k + 1), natDegree_sub_eq_left_of_natDegree_lt hlt, hmuld]
  exact fun n => (H n).1

/-- `C (n+1)` is monic. -/
lemma C_monic (n : ℕ) : Monic (C (n + 1)) := (C_monic_natDegree n).1

/-- `C (n+1)` has degree `n+1`. -/
lemma C_natDegree (n : ℕ) : (C (n + 1)).natDegree = n + 1 := (C_monic_natDegree n).2

/-- **The fundamental identity.** Evaluating the Vieta–Lucas polynomial at `2 cos θ`
returns `2 cos(n θ)`. Proved by two-step induction: the step *is* the cosine
addition/product-to-sum formula
`2 cos((n+2)θ) = (2 cos θ)·(2 cos((n+1)θ)) − 2 cos(n θ)`. -/
lemma C_eval_two_cos (θ : ℝ) :
    ∀ n : ℕ, (2 : ℝ) * Real.cos (n * θ) = Polynomial.aeval (2 * Real.cos θ) (C n) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp [map_ofNat]
  | one => simp [C_one]
  | more n ih1 ih2 =>
    rw [C_succ_succ, map_sub, map_mul, aeval_X, ← ih1, ← ih2]
    -- Goal: 2·cos((n+2)θ) = (2 cos θ)·(2 cos((n+1)θ)) − 2 cos(n θ)
    push_cast
    rw [show ((n : ℝ) + 2) * θ = ((n : ℝ) + 1) * θ + θ by ring,
        show (n : ℝ) * θ = ((n : ℝ) + 1) * θ - θ by ring,
        Real.cos_add, Real.cos_sub]
    ring

/-- **Algebraic-integer core (explicit witness).**
If `θ` is a rational multiple of `π` — witnessed by `n·θ = k·π` with `n ≥ 1` — then
`2·cos θ` is a root of the monic integer polynomial `C n − 2·cos(n θ)`, hence an
algebraic integer. This is the from-scratch replacement for
`Real.isIntegral_two_mul_cos_rat_mul_pi`. -/
theorem isIntegral_two_mul_cos (θ : ℝ) (n : ℕ) (hn : 1 ≤ n) (k : ℤ)
    (hθ : (n : ℝ) * θ = k * π) : IsIntegral ℤ (2 * Real.cos θ) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  -- `2 cos((j+1)θ) = 2 cos(kπ) = ±2` is an integer; name that integer `z`.
  obtain ⟨z, hz⟩ : ∃ z : ℤ, (z : ℝ) = 2 * Real.cos (((j + 1 : ℕ) : ℝ) * θ) := by
    rcases Int.even_or_odd k with hk | hk
    · exact ⟨2, by rw [hθ, Real.cos_int_mul_pi, hk.neg_one_zpow]; norm_num⟩
    · exact ⟨-2, by rw [hθ, Real.cos_int_mul_pi, hk.neg_one_zpow]; norm_num⟩
  -- Witness polynomial:  C (j+1) − z.
  refine ⟨C (j + 1) - Polynomial.C z, ?_, ?_⟩
  · -- Monic: subtracting a constant does not disturb the leading term of the degree-(j+1) poly.
    refine (C_monic j).sub_of_left ?_
    have hne : C (j + 1) ≠ 0 := (C_monic j).ne_zero
    rw [degree_eq_natDegree hne, C_natDegree j]
    exact lt_of_le_of_lt degree_C_le (by exact_mod_cast Nat.succ_pos j)
  · -- Root: aeval (2 cos θ) (C (j+1)) = 2 cos((j+1)θ) = z.
    rw [← aeval_def, map_sub, ← C_eval_two_cos, aeval_C, algebraMap_int_eq, eq_intCast, hz]
    ring

/-- **Familiar form.** For `θ = (m/n)·π` with `n ≥ 1`, `2·cos θ` is an algebraic
integer. This is exactly the fact the parent Niven entry cited from Mathlib. -/
theorem isIntegral_two_mul_cos_rat (m : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    IsIntegral ℤ (2 * Real.cos (((m : ℝ) / n) * π)) := by
  refine isIntegral_two_mul_cos _ n hn m ?_
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : n ≠ 0)
  field_simp

/-- Sanity example: `2·cos(π/5)` (the golden ratio `(1+√5)/2`) is an algebraic integer. -/
example : IsIntegral ℤ (2 * Real.cos (π / 5)) := by
  have h : π / 5 = ((1 : ℝ) / (5 : ℕ)) * π := by push_cast; ring
  rw [h]
  simpa using isIntegral_two_mul_cos_rat 1 5 (by norm_num)

end NivenOQ0102
