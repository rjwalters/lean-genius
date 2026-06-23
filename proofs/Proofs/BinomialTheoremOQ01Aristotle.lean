/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 0f5baa8b-0499-46b6-a8d1-1b23bf0f57fb

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem genBinom_succ (α : ℝ) (k : ℕ) :
    genBinom α (k + 1) = genBinom α k * ((α - k) / (k + 1))

- theorem genBinom_nat_zero_of_gt (n k : ℕ) (hk : n < k) : genBinom (n : ℝ) k = 0

- theorem genBinom_neg_one (k : ℕ) : genBinom (-1 : ℝ) k = (-1) ^ k

- theorem genBinom_nat_eq_choose (n k : ℕ) (hkn : k ≤ n) :
    genBinom (n : ℝ) k = Nat.choose n k

- theorem genBinom_recurrence_deriv (α : ℝ) (k : ℕ) :
    (k + 1 : ℝ) * genBinom α (k + 1) = genBinom α k * (α - k)

- theorem genBinom_ode_coeff (α : ℝ) (k : ℕ) :
    (k + 1 : ℝ) * genBinom α (k + 1) + k * genBinom α k = α * genBinom α k

- theorem standard_binomial (n : ℕ) (x : ℝ) :
    (1 + x) ^ n = ∑ k ∈ Finset.range (n + 1), genBinom (n : ℝ) k * x ^ k
-/

/-
  Aristotle targets for Binomial Theorem OQ01
  Routine supporting lemmas for automated proof search.
  See BinomialTheoremOQ01.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (newton_generalized_binomial)
  - Known results likely in Mathlib (monotonicity, bounds, etc.)
  - Clean theorem statements with no definition sorries
  - No axioms (convert to theorem ... := by sorry instead)
-/
import Mathlib


open Real Finset

noncomputable def genBinom (α : ℝ) (k : ℕ) : ℝ :=
  (∏ i ∈ Finset.range k, (α - i)) / (Nat.factorial k : ℝ)

namespace BinomialTheoremOQ01Aristotle

/-- C(alpha, 0) = 1. -/
theorem genBinom_zero (α : ℝ) : genBinom α 0 = 1 := by
  simp [genBinom]

/-- C(alpha, 1) = alpha. -/
theorem genBinom_one (α : ℝ) : genBinom α 1 = α := by
  simp [genBinom, Finset.prod_range_succ]

/-- Recurrence: C(alpha, k+1) = C(alpha, k) * (alpha - k) / (k + 1). -/
theorem genBinom_succ (α : ℝ) (k : ℕ) :
    genBinom α (k + 1) = genBinom α k * ((α - k) / (k + 1)) := by
      -- Now use the definition of genBinom to rewrite the left-hand side.
      simp [genBinom] at *;
      rw [ div_mul_div_comm, div_eq_div_iff ] <;> first | positivity | push_cast [ Nat.factorial_succ, Finset.prod_range_succ ] ; ring;

/-- C(n, k) = 0 for natural n when k > n. -/
theorem genBinom_nat_zero_of_gt (n k : ℕ) (hk : n < k) : genBinom (n : ℝ) k = 0 := by
  unfold genBinom; rw [ Finset.prod_eq_zero ( Finset.mem_range.mpr hk ) ] <;> aesop;

/-- C(-1, k) = (-1)^k. -/
theorem genBinom_neg_one (k : ℕ) : genBinom (-1 : ℝ) k = (-1) ^ k := by
  unfold genBinom;
  field_simp;
  induction k <;> simp_all +decide [ Finset.prod_range_succ, pow_succ, Nat.factorial_succ ] ; ring

/-- C(n, k) = Nat.choose n k for natural n and k ≤ n. -/
theorem genBinom_nat_eq_choose (n k : ℕ) (hkn : k ≤ n) :
    genBinom (n : ℝ) k = Nat.choose n k := by
      unfold genBinom;
      field_simp;
      rw_mod_cast [ ← Nat.descFactorial_eq_factorial_mul_choose ];
      rw [ Nat.descFactorial_eq_prod_range ];
      rw [ Nat.cast_prod, Finset.prod_congr rfl ] ; intros ; rw [ Int.subNatNat_of_le ] ; linarith [ Finset.mem_range.mp ‹_› ]

/-- Derivative recurrence: (k+1) * C(alpha, k+1) = C(alpha, k) * (alpha - k). -/
theorem genBinom_recurrence_deriv (α : ℝ) (k : ℕ) :
    (k + 1 : ℝ) * genBinom α (k + 1) = genBinom α k * (α - k) := by
      -- By definition of genBinom, we have genBinom α (k + 1) = (α - k) * genBinom α k / (k + 1).
      have h_def : genBinom α (k + 1) = (α - k) * genBinom α k / (k + 1) := by
        rw [ genBinom_succ ] ; ring;
      rw [ h_def, mul_div_cancel₀ _ <| by positivity, mul_comm ]

/-- ODE coefficient identity: (k+1)*C(alpha,k+1) + k*C(alpha,k) = alpha*C(alpha,k). -/
theorem genBinom_ode_coeff (α : ℝ) (k : ℕ) :
    (k + 1 : ℝ) * genBinom α (k + 1) + k * genBinom α k = α * genBinom α k := by
      -- By multiplying both sides of the equation from genBinom_recurrence_deriv by (k + 1), we can simplify to get the desired result.
      have := genBinom_recurrence_deriv α k;
      field_simp at this;
      linarith

/-- The standard binomial theorem: (1+x)^n = finite sum for natural n. -/
theorem standard_binomial (n : ℕ) (x : ℝ) :
    (1 + x) ^ n = ∑ k ∈ Finset.range (n + 1), genBinom (n : ℝ) k * x ^ k := by
      rw [ add_comm, add_pow ];
      refine' Finset.sum_congr rfl fun k hk => _;
      rw [ mul_comm, genBinom_nat_eq_choose ] ; aesop;
      linarith [ Finset.mem_range.mp hk ]

end BinomialTheoremOQ01Aristotle