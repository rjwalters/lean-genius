/-
  Schnirelmann's inequality: the inf-extraction reduction.

  Target (open Mathlib TODO, `Mathlib/Combinatorics/Schnirelmann.lean`):
  "Prove Schnirelmann's theorem and Mann's theorem on the subadditivity of this
  density", i.e. Schnirelmann's inequality

      σ(A ⊕ B) ≥ σA + σB − σA·σB          (0 ∈ A, 0 ∈ B).

  This is also the *sole* remaining gap in `weak-goldbach-oq-01` for discharging
  the `schnirelmann_basis_theorem` axiom: prior sessions built the covering
  lemma (`SchnirelmannBasis.sumset_covers_of_density_add_ge_one`), the
  density-≥-½ order-2 corollary, the analytic iteration, and the composition
  bookkeeping (`isAdditiveBasis_of_sumsetPow_density_ge_half`). What is left is
  precisely Schnirelmann's inequality above.

  ## What this file contributes

  Schnirelmann's inequality has two layers in Nathanson's proof
  (*Additive Number Theory*, Thm 7.4):

    (1) a **pointwise gap-counting** inequality — purely about `Finset`
        cardinalities — of the shape

          C(n) ≥ A(n) + σB · (n − A(n))                     (†)

        where `A(n) = #{a ∈ Ioc 0 n | a ∈ A}` and likewise for `C = A ⊕ B`;

    (2) an **inf-extraction** step turning (†) into the density inequality by
        dividing by `n`, using `σA ≤ A(n)/n`, and taking the infimum over `n`.

  This file proves layer (2) unconditionally and in full generality as
  `schnirelmannDensity_add_le_of_countingBound`, thereby **reducing** the open
  inequality to the single purely-combinatorial statement (†). All of the
  real-analysis / infimum reasoning of Schnirelmann's inequality is discharged
  here (0 sorry / 0 axiom); the remaining work is the finite gap count (†),
  which mentions no densities on its left side beyond the constant `σB`.

  We take the counting hypothesis (†) as an argument rather than a `sorry` so
  that the file is genuinely axiom-free: it is an honest lemma
  "((†) for all n) → Schnirelmann's inequality", not a claim of the full result.
-/
import Mathlib

open Finset

namespace SchnirelmannInequality

variable {A B C : Set ℕ} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
  [DecidablePred (· ∈ C)]

/-- **Inf-extraction step of Schnirelmann's inequality.**

Given the pointwise gap-counting bound

  `A(n) + σB · (n − A(n)) ≤ C(n)`   for every `n > 0`,

where `A(n) = #{a ∈ Ioc 0 n | a ∈ A}` and `C(n) = #{c ∈ Ioc 0 n | c ∈ C}`,
one obtains Schnirelmann's inequality

  `σA + σB − σA·σB ≤ σC`.

This discharges the entire analytic layer of Schnirelmann's inequality: the
`C = A ⊕ B` sumset structure enters *only* through the counting hypothesis, and
no infimum manipulation remains outside this proof. The argument divides the
hypothesis by `n`, replaces `A(n)/n` by its lower bound `σA` (valid because
`1 − σB ≥ 0`), and takes the infimum over `n` via `le_schnirelmannDensity_iff`. -/
theorem schnirelmannDensity_add_le_of_countingBound
    (hcount : ∀ n : ℕ, 0 < n →
      (#{a ∈ Ioc 0 n | a ∈ A} : ℝ)
        + schnirelmannDensity B * ((n : ℝ) - #{a ∈ Ioc 0 n | a ∈ A})
      ≤ (#{c ∈ Ioc 0 n | c ∈ C} : ℝ)) :
    schnirelmannDensity A + schnirelmannDensity B
        - schnirelmannDensity A * schnirelmannDensity B
      ≤ schnirelmannDensity C := by
  rw [le_schnirelmannDensity_iff]
  intro n hn
  -- Abbreviations for the two counting functions at the point `n`.
  set a : ℝ := (#{a ∈ Ioc 0 n | a ∈ A} : ℝ) with ha
  set c : ℝ := (#{c ∈ Ioc 0 n | c ∈ C} : ℝ) with hc
  have hn0 : n ≠ 0 := hn.ne'
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  -- Density facts.
  have hσB0 : 0 ≤ schnirelmannDensity B := schnirelmannDensity_nonneg
  have hσB1 : schnirelmannDensity B ≤ 1 := schnirelmannDensity_le_one
  -- `σA ≤ A(n)/n`, i.e. `σA · n ≤ a`.
  have hσA_div : schnirelmannDensity A ≤ a / n := by
    rw [ha]; exact schnirelmannDensity_le_div hn0
  have hσA_mul : schnirelmannDensity A * n ≤ a := by
    rw [← ha] at *
    calc schnirelmannDensity A * n ≤ (a / n) * n := by
            apply mul_le_mul_of_nonneg_right hσA_div (le_of_lt hnpos)
      _ = a := by field_simp
  -- The counting hypothesis at `n`.
  have hcn := hcount n hn
  rw [← ha, ← hc] at hcn
  -- Rearranged: `a + σB·(n − a) ≤ c`, and `a·(1−σB) ≥ (σA·n)·(1−σB)`.
  have hfac : (1 : ℝ) - schnirelmannDensity B ≥ 0 := by linarith
  have hstep : schnirelmannDensity A * n * (1 - schnirelmannDensity B)
      ≤ a * (1 - schnirelmannDensity B) :=
    mul_le_mul_of_nonneg_right hσA_mul hfac
  -- Assemble: `(σA + σB − σA·σB)·n ≤ c`.
  have hkey : (schnirelmannDensity A + schnirelmannDensity B
      - schnirelmannDensity A * schnirelmannDensity B) * n ≤ c := by
    nlinarith [hcn, hstep, hnpos]
  -- Divide by `n > 0`.
  rw [le_div_iff₀ hnpos]
  linarith [hkey]

end SchnirelmannInequality
