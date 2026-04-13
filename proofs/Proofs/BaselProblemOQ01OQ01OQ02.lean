import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

/-
# Formalizing Apéry's Proof of ζ(3) Irrationality

## Problem Statement
Can Apéry's 1978 proof of the irrationality of ζ(3) be formalized in Lean 4?

## Approach: The Apéry Sequences
Apéry constructed explicit sequences aₙ, bₙ satisfying:
1. Both satisfy the 3-term recurrence:
     (n+1)³ uₙ₊₁ - (2n+1)(17n²+17n+5) uₙ + n³ uₙ₋₁ = 0
2. bₙ = ∑_{k=0}^{n} C(n,k)² C(n+k,k)²  (positive integers)
3. bₙ ζ(3) - aₙ → 0  with |bₙ ζ(3) - aₙ| ≈ C · (√2-1)^{4n}
4. lcm(1,...,n)³ · aₙ ∈ ℤ, bₙ ∈ ℤ

The fast geometric decay of bₙ ζ(3) - aₙ combined with the polynomial
growth of the denominators forces irrationality.

## Status
- Apéry sequences defined and initial values verified
- Key recurrence relation stated (with sorry)
- Irrationality conclusion stated (with sorry)
- This is a scaffold for future work

## Axioms: 0
## Sorries: 4 (recurrence, growth bound, decay bound, main theorem)

Reference: Apéry (1979), van der Poorten (1979), Zudilin (2002)
-/

open BigOperators Finset Nat

namespace AperyZetaThree

-- ============================================================================
-- Part I: The ζ(3) Zeta Value
-- ============================================================================

/-- ζ(s) = ∑_{n=1}^∞ 1/n^s defined as a tsum over ℕ. -/
noncomputable def zetaValue (s : ℕ) : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ s

/-- The p-series ∑ 1/n^s converges for s ≥ 2. -/
theorem summable_zetaValue (s : ℕ) (hs : 2 ≤ s) :
    Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ s) := by
  have hlt : (1 : ℝ) < (s : ℝ) := by exact_mod_cast (show 1 < s by omega)
  have h := Real.summable_nat_rpow_inv.mpr hlt
  convert h using 1
  ext n; simp [div_eq_mul_inv]

/-- ζ(s) > 0 for s ≥ 2. -/
theorem zetaValue_pos (s : ℕ) (hs : 2 ≤ s) : 0 < zetaValue s := by
  unfold zetaValue
  apply tsum_pos (summable_zetaValue s hs) (fun n => by positivity) 1
  simp

-- ============================================================================
-- Part II: The Apéry Sequence bₙ
-- ============================================================================

/-- The Apéry b-sequence:
    bₙ = ∑_{k=0}^{n} C(n,k)² · C(n+k,k)²

    These are positive integers known as Apéry numbers.
    They satisfy the 3-term recurrence and grow like (1+√2)^{4n}. -/
def aperyB (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), (n.choose k) ^ 2 * ((n + k).choose k) ^ 2

/-- b₀ = 1 (the k=0 term: C(0,0)²·C(0,0)² = 1). -/
theorem aperyB_zero : aperyB 0 = 1 := by
  simp [aperyB, Finset.sum_range_succ]

/-- b₁ = 5 (terms: k=0 gives 1·1=1, k=1 gives 1·4=4, total 5). -/
theorem aperyB_one : aperyB 1 = 5 := by
  simp [aperyB, Finset.sum_range_succ]
  norm_num

/-- b₂ = 73 (six terms summing to 73). -/
theorem aperyB_two : aperyB 2 = 73 := by
  simp [aperyB, Finset.sum_range_succ]
  norm_num

/-- b₃ = 1445. -/
theorem aperyB_three : aperyB 3 = 1445 := by
  simp [aperyB, Finset.sum_range_succ]
  norm_num

/-- All Apéry numbers are positive. -/
theorem aperyB_pos (n : ℕ) : 0 < aperyB n := by
  unfold aperyB
  apply Finset.sum_pos
  · intro k hk
    apply Nat.mul_pos
    · exact Nat.pos_of_ne_zero (pow_ne_zero 2 (Nat.choose_pos (Finset.mem_range.mp hk |>.le) |>.ne'))
    · exact Nat.pos_of_ne_zero (pow_ne_zero 2 (Nat.choose_pos (Nat.le_add_left k n) |>.ne'))
  · exact ⟨0, Finset.mem_range.mpr (by omega)⟩

-- ============================================================================
-- Part III: The Apéry Recurrence
-- ============================================================================

/-- The Apéry recurrence coefficient: (2n+1)(17n²+17n+5).
    Both aₙ and bₙ satisfy:
      (n+1)³ uₙ₊₁ = (2n+1)(17n²+17n+5) uₙ - n³ uₙ₋₁  -/
def aperyRecCoeff (n : ℕ) : ℤ :=
  (2 * n + 1) * (17 * n ^ 2 + 17 * n + 5)

/-- The recurrence coefficient at n=0 is 5. -/
theorem aperyRecCoeff_zero : aperyRecCoeff 0 = 5 := by
  simp [aperyRecCoeff]

/-- The recurrence coefficient at n=1 is 117. -/
theorem aperyRecCoeff_one : aperyRecCoeff 1 = 117 := by
  simp [aperyRecCoeff]
  norm_num

/-- The Apéry b-sequence satisfies the 3-term recurrence:
    (n+1)³ bₙ₊₁ = aperyRecCoeff(n) · bₙ - n³ · bₙ₋₁

    This is verified for the first few values and is a classical identity
    proved by Zeilberger's algorithm (WZ-theory). -/
theorem aperyB_recurrence (n : ℕ) (hn : 0 < n) :
    ((n + 1 : ℤ) ^ 3) * (aperyB (n + 1) : ℤ) =
    aperyRecCoeff n * (aperyB n : ℤ) - (n : ℤ) ^ 3 * (aperyB (n - 1) : ℤ) := by
  sorry

-- Verify the recurrence for small values:

/-- Recurrence check at n=1: 8·b₂ = 117·b₁ - 1·b₀, i.e., 8·73 = 117·5 - 1. -/
theorem aperyB_rec_check_1 : 8 * 73 = 117 * 5 - 1 * 1 := by norm_num

/-- Recurrence check at n=2: 27·b₃ = 535·b₂ - 8·b₁, i.e., 27·1445 = 535·73 - 8·5. -/
theorem aperyB_rec_check_2 : 27 * 1445 = 535 * 73 - 8 * 5 := by norm_num

-- ============================================================================
-- Part IV: Growth and Decay Estimates
-- ============================================================================

/-- The Apéry numbers grow like (1+√2)^{4n}. Specifically:
    bₙ ~ C · (1+√2)^{4n} / n^{3/2}  as n → ∞

    The constant (1+√2)⁴ = 17 + 12√2 ≈ 33.97 is the larger root of
    the characteristic polynomial t² - 34t + 1 = 0 of the Apéry recurrence. -/
theorem aperyB_growth_upper (n : ℕ) (hn : 0 < n) :
    (aperyB n : ℝ) ≤ 34 ^ n := by
  sorry

/-- The linear form bₙ·ζ(3) - aₙ decays geometrically:
    |bₙ·ζ(3) - aₙ| ≤ C · (√2 - 1)^{4n}

    where (√2-1)⁴ = 17 - 12√2 ≈ 0.0294 is the smaller root of
    the characteristic polynomial. The fast decay (exponential with
    base < 1) is the engine of the irrationality proof. -/

/-- The characteristic polynomial of the Apéry recurrence: t² - 34t + 1.
    Roots: (1+√2)⁴ = 17+12√2 ≈ 33.97 and (√2-1)⁴ = 17-12√2 ≈ 0.029. -/
theorem apery_char_poly_discriminant :
    34 ^ 2 - 4 * 1 = 1152 := by norm_num

-- ============================================================================
-- Part V: The Irrationality Argument
-- ============================================================================

/-- **Main Theorem (Apéry 1978)**: ζ(3) is irrational.

    Proof sketch:
    1. Construct sequences aₙ ∈ ℚ and bₙ ∈ ℤ>₀ with bₙ·ζ(3) - aₙ ≠ 0
    2. Show |bₙ·ζ(3) - aₙ| → 0 geometrically (rate (√2-1)⁴ ≈ 0.029)
    3. Show lcm(1,...,n)³·aₙ ∈ ℤ (denominator control)
    4. By the prime number theorem, lcm(1,...,n)³ ~ e^{3n}
    5. So 2·lcm(1,...,n)³·bₙ·|bₙ·ζ(3) - aₙ| → 0
    6. But this quantity is a nonzero integer if ζ(3) = p/q, contradiction -/
theorem apery_theorem : Irrational (zetaValue 3) := by
  sorry

-- ============================================================================
-- Part VI: The Apéry a-Sequence (Rational Approximations)
-- ============================================================================

/-- The Apéry a-sequence is defined via the same recurrence as bₙ,
    but with initial conditions a₀ = 0, a₁ = 6.
    The values aₙ are rational; lcm(1,...,n)³ · aₙ is an integer.

    We define it recursively. Since the recurrence involves (n+1)³ in the
    denominator, the values are rational (not natural numbers). -/
noncomputable def aperyA : ℕ → ℚ
  | 0 => 0
  | 1 => 6
  | (n + 2) =>
    let coeff := (2 * (n + 1 : ℤ) + 1) * (17 * (n + 1 : ℤ) ^ 2 + 17 * (n + 1) + 5)
    let prev := aperyA (n + 1)
    let pprev := aperyA n
    (coeff * prev - (n + 1 : ℤ) ^ 3 * pprev) / (n + 2 : ℤ) ^ 3

/-- a₀ = 0. -/
theorem aperyA_zero : aperyA 0 = 0 := rfl

/-- a₁ = 6. -/
theorem aperyA_one : aperyA 1 = 6 := rfl

/-- a₂ = 351/4. Verified by direct computation from the recurrence:
    a₂ = (3 · 39 · 6 - 1 · 0) / 8 = 702/8 = 351/4. -/
theorem aperyA_two : aperyA 2 = 351 / 4 := by
  simp only [aperyA]
  norm_num

-- ============================================================================
-- Part VII: Harmonic Numbers and Generalized Harmonic Sums
-- ============================================================================

/-- The harmonic number H_n = ∑_{k=1}^{n} 1/k. -/
noncomputable def harmonicNumber (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, (1 : ℚ) / (k + 1)

/-- H₀ = 0. -/
theorem harmonicNumber_zero : harmonicNumber 0 = 0 := by
  simp [harmonicNumber]

/-- H₁ = 1. -/
theorem harmonicNumber_one : harmonicNumber 1 = 1 := by
  simp [harmonicNumber, Finset.sum_range_succ]

/-- H₂ = 3/2. -/
theorem harmonicNumber_two : harmonicNumber 2 = 3 / 2 := by
  simp [harmonicNumber, Finset.sum_range_succ]
  norm_num

/-- H₃ = 11/6. -/
theorem harmonicNumber_three : harmonicNumber 3 = 11 / 6 := by
  simp [harmonicNumber, Finset.sum_range_succ]
  norm_num

/-- Harmonic numbers are non-negative. -/
theorem harmonicNumber_nonneg (n : ℕ) : 0 ≤ harmonicNumber n := by
  unfold harmonicNumber
  apply Finset.sum_nonneg
  intro k _
  positivity

/-- Harmonic numbers are monotone increasing. -/
theorem harmonicNumber_mono (m n : ℕ) (hmn : m ≤ n) :
    harmonicNumber m ≤ harmonicNumber n := by
  unfold harmonicNumber
  apply Finset.sum_le_sum_of_subset
  exact Finset.range_mono hmn

/-- The generalized harmonic number H_n^{(s)} = ∑_{k=1}^{n} 1/k^s. -/
noncomputable def genHarmonicNumber (n : ℕ) (s : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, (1 : ℚ) / (k + 1) ^ s

/-- H_n^{(3)} is what appears in the a-sequence formula. -/
theorem genHarmonicNumber_three_zero : genHarmonicNumber 0 3 = 0 := by
  simp [genHarmonicNumber]

-- ============================================================================
-- Part VIII: LCM Bounds (Nair 1982)
-- ============================================================================

/-- lcm(1, 2, ..., n) defined as lcm over Finset.range. -/
def lcmUpTo (n : ℕ) : ℕ :=
  (Finset.range n).lcm (· + 1)

/-- lcm(1) = 1. -/
theorem lcmUpTo_one : lcmUpTo 1 = 1 := by
  simp [lcmUpTo, Finset.lcm]

/-- lcm(1, 2) = 2. -/
theorem lcmUpTo_two : lcmUpTo 2 = 2 := by
  simp [lcmUpTo, Finset.sum_range_succ, Finset.lcm]
  norm_num

/-- lcm(1, 2, ..., n) is positive for n ≥ 1. -/
theorem lcmUpTo_pos (n : ℕ) (hn : 1 ≤ n) : 0 < lcmUpTo n := by
  unfold lcmUpTo
  apply Nat.pos_of_ne_zero
  intro h
  have h1 : 1 ∣ (Finset.range n).lcm (· + 1) := Finset.dvd_lcm (Finset.mem_range.mpr (by omega))
  rw [h] at h1
  exact absurd h1 (by omega)

/-- **Nair's bound (1982)**: lcm(1, 2, ..., n) ≤ 4^n.
    This elementary bound bypasses the prime number theorem for
    the denominator control needed in Apéry's proof.
    Reference: M. Nair, "On Chebyshev-type inequalities for primes" (1982). -/
theorem nair_lcm_bound (n : ℕ) : lcmUpTo n ≤ 4 ^ n := by
  sorry

-- Verify for small values:
/-- lcm(1,...,4) = 12 ≤ 256 = 4⁴. -/
example : lcmUpTo 4 ≤ 4 ^ 4 := by
  simp [lcmUpTo, Finset.sum_range_succ, Finset.lcm]
  norm_num

-- ============================================================================
-- Part IX: The Linear Form bₙ·ζ(3) - aₙ
-- ============================================================================

/-- The linear form Lₙ = bₙ·ζ(3) - aₙ.
    This is the quantity that converges to 0, forcing irrationality. -/
noncomputable def linearForm (n : ℕ) : ℝ :=
  (aperyB n : ℝ) * zetaValue 3 - (aperyA n : ℝ)

/-- The linear form is nonzero for n ≥ 1 (assuming ζ(3) is irrational,
    which is what we're trying to prove — so this must be established
    independently, e.g., from the explicit formula for Lₙ). -/

/-- **Denominator control**: lcm(1,...,n)³ · aₙ is an integer.
    This is the key arithmetic property of the a-sequence.
    It follows from the fact that aₙ can be written as a sum
    involving 1/k³ terms with denominators dividing lcm(1,...,n)³. -/
theorem denominator_control (n : ℕ) :
    ∃ m : ℤ, (lcmUpTo n : ℚ) ^ 3 * aperyA n = m := by
  sorry

-- ============================================================================
-- Part X: Summary and Remaining Sorries
-- ============================================================================

/-
## What's Proved (this session adds Parts VI-IX)
- Apéry b-sequence defined and initial values verified
- All Apéry numbers are positive
- Recurrence verified numerically for n=1,2
- Characteristic polynomial discriminant
- **NEW**: Apéry a-sequence defined via recurrence (a₀=0, a₁=6, a₂=351/4)
- **NEW**: Harmonic numbers H_n and generalized H_n^{(s)} defined
- **NEW**: lcm(1,...,n) defined with small-value checks
- **NEW**: Linear form bₙ·ζ(3) - aₙ defined
- **NEW**: Denominator control stated (lcm³·aₙ ∈ ℤ)

## Remaining Sorries (5 → 6, added denominator_control and nair_lcm_bound)
1. **aperyB_recurrence**: 3-term recurrence (WZ-theory)
2. **aperyB_growth_upper**: bₙ ≤ 34^n (needs recurrence)
3. **apery_theorem**: Main irrationality theorem
4. **nair_lcm_bound**: lcm(1,...,n) ≤ 4^n (elementary but requires Chebyshev argument)
5. **denominator_control**: lcm(1,...,n)³ · aₙ ∈ ℤ (needs a-sequence formula)

## Critical Path
The sorries now have clear dependencies:
  nair_lcm_bound + denominator_control → arithmetic control
  aperyB_recurrence → aperyB_growth_upper → decay estimates
  All above → apery_theorem
-/

end AperyZetaThree
