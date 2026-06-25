/-
  OQ-01-OQ-03: Effective closed form for the n-sphere surface constant
  (circumference-via-differentiation-oq-01-oq-03)

  Open question (extension of `circumference-via-differentiation-oq-01`,
  "n-Dimensional Surface Area via Differentiation of Volume"):

    The surface-area constant is `C_n = nSphereSurfaceConst n = n · ω_n`, and
    the parent already proves `C_n = 2π^(n/2)/Γ(n/2)`.  For practical
    computation one wants `C_n` for many `n`.  Mathlib provides
    `Real.Gamma_one_half_eq` (Γ(1/2) = √π) and `Real.Gamma_add_one`
    (Γ(s+1) = s·Γ(s)) but NO closed form for the half-integer values Γ(k+1/2).
    Can the file be extended with an explicit recursive / closed-form
    evaluation of `nSphereSurfaceConst (2k+1)` derived programmatically from
    the half-integer Gamma values?

  ── ANSWER (this session) ──────────────────────────────────────────────────

  Yes.  The crux is the half-integer Gamma value, which we establish by a
  one-line induction off the two Mathlib lemmas named above:

      Γ(k + 1/2) = (2k)! / (4^k · k!) · √π                 (`gamma_nat_add_half`)

  Feeding this into the parent's `nSphereSurfaceConst_eq_gamma` collapses the
  √π and yields the fully effective ODD-dimensional closed form

      C_{2k+1} = 2 · (4π)^k · k! / (2k)!                   (`nSphereSurfaceConst_odd`)

  together with the first-order recursion

      C_{2k+3} = C_{2k+1} · 2π/(2k+1)                       (`nSphereSurfaceConst_odd_succ`)

  Sanity checks (all derived, not assumed):
      C_1 = 2,  C_3 = 4π,  C_5 = 8π²/3,  C_7 = 16π³/15.

  The EVEN case needs no new ingredient — Γ(m) = (m-1)! is already in Mathlib
  (`Gamma_nat_eq_factorial`) — and is recorded for completeness:

      C_{2m} = 2π^m / (m-1)!                                (`nSphereSurfaceConst_even`)

  Status: 0 sorries, 0 axioms.  Self-contained on top of OQ-01.
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic
import Proofs.CircumferenceViaDifferentiationOQ01

open Real

noncomputable section

namespace CircumferenceViaDifferentiationOQ01OQ03

open CircumferenceViaDifferentiationOQ01

-- ============================================================
-- Part 1: The half-integer Gamma value (the missing Mathlib lemma)
-- ============================================================

/-- **Half-integer Gamma value.**  For every `k : ℕ`,

      Γ(k + 1/2) = (2k)! / (4^k · k!) · √π.

    Proved by induction: the base case is `Real.Gamma_one_half_eq`
    (Γ(1/2) = √π) and the step is the functional equation
    `Real.Gamma_add_one` (Γ(s+1) = s·Γ(s)), exactly the two lemmas the
    open question pointed at.  Mathlib has no direct form for these values. -/
theorem gamma_nat_add_half (k : ℕ) :
    Gamma ((k : ℝ) + 1 / 2)
      = (Nat.factorial (2 * k) : ℝ) / (4 ^ k * Nat.factorial k) * √π := by
  induction k with
  | zero =>
    rw [Nat.cast_zero, zero_add, Gamma_one_half_eq]
    norm_num [Nat.factorial]
  | succ k ih =>
    have hcast : ((k + 1 : ℕ) : ℝ) + 1 / 2 = ((k : ℝ) + 1 / 2) + 1 := by
      push_cast; ring
    have hne : ((k : ℝ) + 1 / 2) ≠ 0 := by positivity
    rw [hcast, Gamma_add_one hne, ih]
    -- Factorial successors, lifted to ℝ.
    have hk1 : ((Nat.factorial (k + 1) : ℕ) : ℝ) = (k + 1) * Nat.factorial k := by
      rw [Nat.factorial_succ]; push_cast; ring
    have h2 : ((Nat.factorial (2 * (k + 1)) : ℕ) : ℝ)
        = (2 * k + 2) * (2 * k + 1) * Nat.factorial (2 * k) := by
      have e : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      rw [e, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
    rw [hk1, h2, pow_succ]
    have hkf : ((Nat.factorial k : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have h2kf : ((Nat.factorial (2 * k) : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hpow : ((4 : ℝ) ^ k) ≠ 0 := by positivity
    have hk1ne : ((k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring

-- ============================================================
-- Part 2: Effective closed form for odd dimensions
-- ============================================================

/-- **Odd-dimensional surface constant, closed form.**

      C_{2k+1} = 2 · (4π)^k · k! / (2k)!.

    Combines the parent's `nSphereSurfaceConst_eq_gamma` with the
    half-integer Gamma value `gamma_nat_add_half`; the √π cancels. -/
theorem nSphereSurfaceConst_odd (k : ℕ) :
    nSphereSurfaceConst (2 * k + 1)
      = 2 * (4 * π) ^ k * Nat.factorial k / Nat.factorial (2 * k) := by
  rw [nSphereSurfaceConst_eq_gamma (2 * k + 1) (by omega)]
  have hcast : ((2 * k + 1 : ℕ) : ℝ) / 2 = (k : ℝ) + 1 / 2 := by push_cast; ring
  have hpi : (π : ℝ) ^ ((k : ℝ) + 1 / 2) = π ^ k * √π := by
    rw [Real.rpow_add pi_pos, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  rw [hcast, gamma_nat_add_half, hpi]
  have hsqrt : √π ≠ 0 := Real.sqrt_ne_zero'.mpr pi_pos
  have hkf : ((Nat.factorial k : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have h2kf : ((Nat.factorial (2 * k) : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hpow : ((4 : ℝ) ^ k) ≠ 0 := by positivity
  field_simp
  ring

/-- **Odd-dimensional recursion.**

      C_{2k+3} = C_{2k+1} · 2π/(2k+1).

    The first-order recurrence that drives the "programmatic" evaluation;
    follows from the closed form by factorial arithmetic. -/
theorem nSphereSurfaceConst_odd_succ (k : ℕ) :
    nSphereSurfaceConst (2 * (k + 1) + 1)
      = nSphereSurfaceConst (2 * k + 1) * (2 * π / (2 * (k : ℝ) + 1)) := by
  rw [nSphereSurfaceConst_odd (k + 1), nSphereSurfaceConst_odd k]
  have hk1 : ((Nat.factorial (k + 1) : ℕ) : ℝ) = (k + 1) * Nat.factorial k := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h2 : ((Nat.factorial (2 * (k + 1)) : ℕ) : ℝ)
      = (2 * k + 2) * (2 * k + 1) * Nat.factorial (2 * k) := by
    have e : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
    rw [e, Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  rw [hk1, h2, pow_succ]
  have hkf : ((Nat.factorial k : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have h2kf : ((Nat.factorial (2 * k) : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2k1 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

-- ============================================================
-- Part 3: Concrete values (all derived from the closed form)
-- ============================================================

/-- C_1 = 2 (the "0-sphere" pair of points, total measure 2). -/
theorem nSphereSurfaceConst_one : nSphereSurfaceConst 1 = 2 := by
  have h := nSphereSurfaceConst_odd 0
  norm_num [Nat.factorial] at h
  rw [h]

/-- C_3 = 4π (surface area of the unit 2-sphere). -/
theorem nSphereSurfaceConst_three' : nSphereSurfaceConst 3 = 4 * π := by
  have h := nSphereSurfaceConst_odd 1
  norm_num [Nat.factorial] at h
  linear_combination h

/-- C_5 = 8π²/3 (surface area of the unit 4-sphere). -/
theorem nSphereSurfaceConst_five : nSphereSurfaceConst 5 = 8 * π ^ 2 / 3 := by
  have h := nSphereSurfaceConst_odd 2
  norm_num [Nat.factorial] at h
  linear_combination h

/-- C_7 = 16π³/15 (surface area of the unit 6-sphere). -/
theorem nSphereSurfaceConst_seven : nSphereSurfaceConst 7 = 16 * π ^ 3 / 15 := by
  have h := nSphereSurfaceConst_odd 3
  norm_num [Nat.factorial] at h
  linear_combination h

-- ============================================================
-- Part 4: Even dimensions (recorded for completeness)
-- ============================================================

/-- **Even-dimensional surface constant.**

      C_{2m} = 2π^m / (m-1)!   for m ≥ 1.

    No half-integer Gamma is needed here: Γ(m) = (m-1)! is the integer Gamma
    value `Gamma_nat_eq_factorial`. -/
theorem nSphereSurfaceConst_even (m : ℕ) (hm : 0 < m) :
    nSphereSurfaceConst (2 * m) = 2 * π ^ m / Nat.factorial (m - 1) := by
  rw [nSphereSurfaceConst_eq_gamma (2 * m) (by omega)]
  have hcast : ((2 * m : ℕ) : ℝ) / 2 = (m : ℝ) := by push_cast; ring
  have hmm : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
    rw [Nat.cast_sub hm, Nat.cast_one]; ring
  have hg : Gamma (m : ℝ) = (Nat.factorial (m - 1) : ℝ) := by
    rw [← hmm, Gamma_nat_eq_factorial]
  rw [hcast, Real.rpow_natCast, hg]

end CircumferenceViaDifferentiationOQ01OQ03

end -- noncomputable section

-- ============================================================
-- Examples
-- ============================================================

open CircumferenceViaDifferentiationOQ01OQ03

-- The half-integer Gamma value at k = 2: Γ(5/2) = 3√π/4.
example : Real.Gamma ((2 : ℝ) + 1 / 2) = 3 * √Real.pi / 4 := by
  have h := gamma_nat_add_half 2
  norm_num [Nat.factorial] at h
  rw [show (2 : ℝ) + 1 / 2 = 5 / 2 by norm_num]
  linear_combination h

#check @CircumferenceViaDifferentiationOQ01OQ03.nSphereSurfaceConst_odd
#check @CircumferenceViaDifferentiationOQ01OQ03.gamma_nat_add_half
