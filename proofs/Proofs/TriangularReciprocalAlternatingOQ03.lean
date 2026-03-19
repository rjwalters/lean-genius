import Mathlib

/-
Alternating Sum of Reciprocals of Triangular Numbers

Result:
  ∑_{n=1}^∞ (-1)^{n+1} · 2/(n(n+1)) = 4·ln(2) - 2 ≈ 0.7726

Proof Strategy:
  Partial fractions: (-1)^{n+1} · 2/(n(n+1)) = 2·(-1)^{n+1}/n - 2·(-1)^{n+1}/(n+1).
  Splitting the series gives two alternating sums:
    ∑(-1)^{n+1}/n = ln(2)       (alternating harmonic series)
    ∑(-1)^{n+1}/(n+1) = 1-ln(2) (shifted alternating harmonic)
  Combining: 2·ln(2) - 2·(1-ln(2)) = 4·ln(2) - 2.

Axioms (2):
  Both encode the Mercator series log(1+x) = ∑ (-1)^{n+1} x^n/n evaluated at x = 1.
  The boundary convergence requires Abel's theorem, not yet available in Mathlib.

Extends TriangularNumberReciprocals.lean which proves ∑ 2/(n(n+1)) = 2.
-/

namespace AlternatingTriangularReciprocals

open Finset BigOperators Filter Topology Real

-- ═══════════════════════════════════════════════════
-- Part I: Alternating Harmonic Series (Axiomatized)
-- ═══════════════════════════════════════════════════

/-- The alternating harmonic series: 1 - 1/2 + 1/3 - 1/4 + ⋯ = ln(2).
    Mercator (1668). Boundary convergence of the power series for log(1+x)
    requires Abel's theorem, not yet formalized in Mathlib. -/
axiom alternating_harmonic_hasSum :
    HasSum (fun n : ℕ => if n = 0 then (0 : ℝ) else (-1 : ℝ) ^ (n + 1) / (n : ℝ))
      (Real.log 2)

/-- Shifted alternating harmonic: 1/2 - 1/3 + 1/4 - ⋯ = 1 - ln(2).
    This is ∑_{n=2}^∞ (-1)^n/n, obtained from the alternating harmonic
    by removing the first term (= 1) and negating. Equivalently, it is the
    Mercator series for -log(1-x) at x = -1, minus the first term. -/
axiom shifted_alternating_hasSum :
    HasSum (fun n : ℕ => if n = 0 then (0 : ℝ) else (-1 : ℝ) ^ (n + 1) / ((n : ℝ) + 1))
      (1 - Real.log 2)

-- ═══════════════════════════════════════════════════════
-- Part II: Main Theorem
-- ═══════════════════════════════════════════════════════

/-- **Alternating Sum of Triangular Reciprocals**:
    ∑_{n=1}^∞ (-1)^{n+1} · 2/(n(n+1)) = 4·ln(2) - 2.

    By partial fractions, (-1)^{n+1} · 2/(n(n+1)) = 2·(-1)^{n+1}/n - 2·(-1)^{n+1}/(n+1).
    Summing: 2·ln(2) - 2·(1-ln(2)) = 4·ln(2) - 2. -/
theorem alternating_triangular_sum :
    HasSum (fun n : ℕ => if n = 0 then (0 : ℝ)
      else (-1 : ℝ) ^ (n + 1) * (2 / ((n : ℝ) * ((n : ℝ) + 1))))
      (4 * Real.log 2 - 2) := by
  -- Step 1: Rewrite the target function as 2·f - 2·g via partial fractions
  have h_feq : (fun n : ℕ => if n = 0 then (0 : ℝ)
      else (-1 : ℝ) ^ (n + 1) * (2 / ((n : ℝ) * ((n : ℝ) + 1)))) =
    (fun n : ℕ => 2 * (if n = 0 then (0 : ℝ) else (-1 : ℝ) ^ (n + 1) / (n : ℝ)) -
                  2 * (if n = 0 then (0 : ℝ) else (-1 : ℝ) ^ (n + 1) / ((n : ℝ) + 1))) := by
    ext n
    by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, ↓reduceIte]
      have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
  rw [h_feq]
  -- Step 2: Combine the two axiomatized HasSum results
  have h := (alternating_harmonic_hasSum.mul_left (2 : ℝ)).sub
            (shifted_alternating_hasSum.mul_left (2 : ℝ))
  -- h has value 2·log(2) - 2·(1 - log(2)); simplify to 4·log(2) - 2
  have h_val : (2 : ℝ) * Real.log 2 - 2 * (1 - Real.log 2) = 4 * Real.log 2 - 2 := by ring
  rw [h_val] at h
  exact h

/-- tsum version. -/
theorem alternating_triangular_tsum :
    ∑' n : ℕ, (if n = 0 then (0 : ℝ)
      else (-1 : ℝ) ^ (n + 1) * (2 / ((n : ℝ) * ((n : ℝ) + 1)))) =
    4 * Real.log 2 - 2 :=
  alternating_triangular_sum.tsum_eq

-- ═══════════════════════════════════════════════════
-- Part III: Corollary - Unscaled Version
-- ═══════════════════════════════════════════════════

/-- Unscaled: ∑_{n=1}^∞ (-1)^{n+1}/(n(n+1)) = 2·ln(2) - 1.
    Since 1/T_n = 2/(n(n+1)), this is also ∑ (-1)^{n+1}/(2·T_n) = 2·ln(2) - 1. -/
theorem alternating_reciprocal_product_sum :
    HasSum (fun n : ℕ => if n = 0 then (0 : ℝ)
      else (-1 : ℝ) ^ (n + 1) / ((n : ℝ) * ((n : ℝ) + 1)))
      (2 * Real.log 2 - 1) := by
  -- The scaled series = 2 * (unscaled series)
  have h := alternating_triangular_sum
  have h_feq : (fun n : ℕ => if n = 0 then (0 : ℝ)
      else (-1 : ℝ) ^ (n + 1) * (2 / ((n : ℝ) * ((n : ℝ) + 1)))) =
    (fun n : ℕ => 2 * (if n = 0 then (0 : ℝ)
      else (-1 : ℝ) ^ (n + 1) / ((n : ℝ) * ((n : ℝ) + 1)))) := by
    ext n
    by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, ↓reduceIte]; ring
  rw [h_feq] at h
  -- HasSum (2 · g) (4·log2 - 2)
  -- Extract: HasSum g ((4·log2 - 2)/2) = HasSum g (2·log2 - 1)
  have h2 : HasSum
      (fun n : ℕ => if n = 0 then (0 : ℝ)
        else (-1 : ℝ) ^ (n + 1) / ((n : ℝ) * ((n : ℝ) + 1)))
      ((4 * Real.log 2 - 2) / 2) := by
    rw [show (4 * Real.log 2 - 2) / 2 = (2 : ℝ)⁻¹ * (4 * Real.log 2 - 2) from by ring]
    rw [show (fun n : ℕ => if n = 0 then (0 : ℝ)
        else (-1 : ℝ) ^ (n + 1) / ((n : ℝ) * ((n : ℝ) + 1))) =
      (fun n : ℕ => (2 : ℝ)⁻¹ * (2 * (if n = 0 then (0 : ℝ)
        else (-1 : ℝ) ^ (n + 1) / ((n : ℝ) * ((n : ℝ) + 1))))) from by
      ext n; by_cases hn : n = 0 <;> simp [hn]]
    exact h.const_smul (2 : ℝ)⁻¹
  convert h2 using 1
  ring

/-- tsum version of unscaled corollary. -/
theorem alternating_reciprocal_product_tsum :
    ∑' n : ℕ, (if n = 0 then (0 : ℝ)
      else (-1 : ℝ) ^ (n + 1) / ((n : ℝ) * ((n : ℝ) + 1))) =
    2 * Real.log 2 - 1 :=
  alternating_reciprocal_product_sum.tsum_eq

-- ═══════════════════════════════════════════
-- Part IV: Summability
-- ═══════════════════════════════════════════

/-- The alternating triangular reciprocal series is summable. -/
theorem summable_alt_triangular :
    Summable (fun n : ℕ => if n = 0 then (0 : ℝ)
      else (-1 : ℝ) ^ (n + 1) * (2 / ((n : ℝ) * ((n : ℝ) + 1)))) :=
  alternating_triangular_sum.summable

-- ═══════════════════════════════════════════
-- Part V: Finite Partial Sums
-- ═══════════════════════════════════════════

/-- First partial sum: S₁ = 2/(1·2) = 1. -/
example : (2 : ℝ) / (1 * 2) = 1 := by norm_num

/-- Second partial sum: S₂ = 1 - 2/(2·3) = 2/3. -/
example : (1 : ℝ) - 2 / (2 * 3) = 2 / 3 := by norm_num

/-- Third partial sum: S₃ = 2/3 + 2/(3·4) = 5/6. -/
example : (2 : ℝ) / 3 + 2 / (3 * 4) = 5 / 6 := by norm_num

/-- Fourth partial sum: S₄ = 5/6 - 2/(4·5) = 11/15. -/
example : (5 : ℝ) / 6 - 2 / (4 * 5) = 11 / 15 := by norm_num

-- The partial sums oscillate around 4·ln(2) - 2 ≈ 0.7726:
-- S₁ = 1.0000, S₂ ≈ 0.6667, S₃ ≈ 0.8333, S₄ ≈ 0.7333, ...

#check alternating_triangular_sum
#check alternating_reciprocal_product_sum
#check summable_alt_triangular

end AlternatingTriangularReciprocals
