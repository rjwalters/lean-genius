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
- apery_theorem (ζ(3) irrational) PROVED from 5 axioms
- Conditional irrationality theorem PROVED (integer-squeeze argument)
- Growth bound bₙ ≤ 34^n PROVED from recurrence
- Quantitative bound 27·(17-12√2) < 1 PROVED
- denominator_control_factorial — (n!)³·aₙ ∈ ℤ PROVED (axiom-free, Part XIX)

## Axioms: 5
## Sorries: 0

Remaining axioms:
1. aperyB_recurrence — WZ-theory recurrence
2. denominator_control — lcm³·aₙ ∈ ℤ (needs explicit a-sequence formula)
3. lcm_hanson_bound — lcm ≤ 3^n (Hanson 1974, needs Chebyshev theta)
4. apery_linearForm_decay — |Lₙ| ≤ C·(17-12√2)^n (needs integral repr.)
5. apery_linearForm_nonzero — Lₙ ≠ 0 (needs integral repr.)

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
  have h := (summable_zetaValue s hs).sum_le_tsum ({1} : Finset ℕ) (fun n _ => by positivity)
  simp only [Finset.sum_singleton, Nat.cast_one, one_pow, div_one] at h
  linarith

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

/-- b₂ = 73 (six terms summing to 73). -/
theorem aperyB_two : aperyB 2 = 73 := by native_decide

/-- b₃ = 1445. -/
theorem aperyB_three : aperyB 3 = 1445 := by native_decide

/-- All Apéry numbers are positive. -/
theorem aperyB_pos (n : ℕ) : 0 < aperyB n := by
  unfold aperyB
  apply Finset.sum_pos
  · intro k hk
    apply Nat.mul_pos
    · exact Nat.pos_of_ne_zero (pow_ne_zero 2 (Nat.choose_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) |>.ne'))
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

/-- The Apéry b-sequence satisfies the 3-term recurrence:
    (n+1)³ bₙ₊₁ = aperyRecCoeff(n) · bₙ - n³ · bₙ₋₁

    This is verified for the first few values and is a classical identity
    proved by Zeilberger's algorithm (WZ-theory). -/
-- Classical WZ-theory identity; axiomatized (Zeilberger algorithm, not in Mathlib)
axiom aperyB_recurrence (n : ℕ) (hn : 0 < n) :
    ((n + 1 : ℤ) ^ 3) * (aperyB (n + 1) : ℤ) =
    aperyRecCoeff n * (aperyB n : ℤ) - (n : ℤ) ^ 3 * (aperyB (n - 1) : ℤ)

-- Verify the recurrence for small values:

/-- Recurrence check at n=1: 8·b₂ = 117·b₁ - 1·b₀, i.e., 8·73 = 117·5 - 1. -/
theorem aperyB_rec_check_1 : 8 * 73 = 117 * 5 - 1 * 1 := by norm_num

/-- Recurrence check at n=2: 27·b₃ = 535·b₂ - 8·b₁, i.e., 27·1445 = 535·73 - 8·5. -/
theorem aperyB_rec_check_2 : 27 * 1445 = 535 * 73 - 8 * 5 := by norm_num

/-- The recurrence coefficient (2n+1)(17n²+17n+5) is bounded above by 34·(n+1)³.
    This is the key algebraic inequality behind the growth bound bₙ ≤ 34ⁿ:
      34(n+1)³ - (2n+1)(17n²+17n+5) = 51n² + 75n + 29 > 0. -/
theorem aperyRecCoeff_le_34_mul_cubeSucc (n : ℕ) :
    aperyRecCoeff n ≤ 34 * ((n : ℤ) + 1) ^ 3 := by
  unfold aperyRecCoeff
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  nlinarith [sq_nonneg (n : ℤ)]

-- ============================================================================
-- Part IV: Growth and Decay Estimates
-- ============================================================================

/-- From the recurrence, each Apéry number is at most 34 times the previous one.
    Proof: (n+1)³ b_{n+1} = coeff(n)·b_n - n³·b_{n-1} ≤ coeff(n)·b_n ≤ 34(n+1)³·b_n,
    then cancel (n+1)³ > 0. -/
private theorem aperyB_le_34_mul_pred (m : ℕ) (hm : 0 < m) :
    aperyB (m + 1) ≤ 34 * aperyB m := by
  -- Suffices to prove in ℤ, then cast back to ℕ
  suffices h : (aperyB (m + 1) : ℤ) ≤ 34 * ↑(aperyB m) by exact_mod_cast h
  -- Gather hypotheses
  have hrec := aperyB_recurrence m hm
  have hcoeff := aperyRecCoeff_le_34_mul_cubeSucc m
  -- Step 1: m³ · b_{m-1} ≥ 0 (both factors are ℕ cast to ℤ)
  have hm_nn : (0 : ℤ) ≤ (m : ℤ) := Int.ofNat_nonneg m
  have hbp_nn : (0 : ℤ) ≤ ↑(aperyB (m - 1)) := Int.ofNat_nonneg _
  have hb_nn : (0 : ℤ) ≤ ↑(aperyB m) := Int.ofNat_nonneg _
  have h_sub : 0 ≤ (m : ℤ) ^ 3 * ↑(aperyB (m - 1)) :=
    mul_nonneg (pow_nonneg hm_nn 3) hbp_nn
  -- Step 2: (m+1)³ b_{m+1} ≤ coeff(m) · b_m  (from recurrence, since m³·b_{m-1} ≥ 0)
  have h_le_coeff : (m + 1 : ℤ) ^ 3 * ↑(aperyB (m + 1)) ≤
      aperyRecCoeff m * ↑(aperyB m) := by linarith
  -- Step 3: coeff(m) · b_m ≤ 34·(m+1)³ · b_m  (coefficient bound × b_m ≥ 0)
  have h_coeff_bound : aperyRecCoeff m * ↑(aperyB m) ≤
      34 * ((m : ℤ) + 1) ^ 3 * ↑(aperyB m) :=
    mul_le_mul_of_nonneg_right hcoeff hb_nn
  -- Step 4: Combine into (m+1)³ · b_{m+1} ≤ (m+1)³ · (34 · b_m)
  have hcube_pos : (0 : ℤ) < ((m : ℤ) + 1) ^ 3 := by positivity
  have h_combined : ((m : ℤ) + 1) ^ 3 * ↑(aperyB (m + 1)) ≤
      ((m : ℤ) + 1) ^ 3 * (34 * ↑(aperyB m)) := by linarith
  -- Step 5: Cancel (m+1)³ > 0
  exact le_of_mul_le_mul_left h_combined hcube_pos

/-- Auxiliary: bₙ₊₁ ≤ 34^{n+1} by induction using the step bound. -/
private theorem aperyB_growth_upper_aux :
    ∀ n : ℕ, (aperyB (n + 1) : ℝ) ≤ 34 ^ (n + 1) := by
  intro n
  induction n with
  | zero =>
    -- b₁ = 5 ≤ 34 = 34¹
    simp [aperyB_one]; norm_num
  | succ k ih =>
    -- b_{k+2} ≤ 34 · b_{k+1} ≤ 34 · 34^{k+1} = 34^{k+2}
    have h_step : aperyB (k + 2) ≤ 34 * aperyB (k + 1) :=
      aperyB_le_34_mul_pred (k + 1) (by omega)
    have h_step_real : (aperyB (k + 2) : ℝ) ≤ 34 * (aperyB (k + 1) : ℝ) := by
      exact_mod_cast h_step
    calc (aperyB (k + 2) : ℝ)
        ≤ 34 * (aperyB (k + 1) : ℝ) := h_step_real
      _ ≤ 34 * 34 ^ (k + 1) := by nlinarith
      _ = 34 ^ (k + 2) := by ring

/-- The Apéry numbers grow like (1+√2)^{4n}. Specifically:
    bₙ ~ C · (1+√2)^{4n} / n^{3/2}  as n → ∞

    The constant (1+√2)⁴ = 17 + 12√2 ≈ 33.97 is the larger root of
    the characteristic polynomial t² - 34t + 1 = 0 of the Apéry recurrence.

    Note: This proof depends on aperyB_recurrence (currently sorry). Once the
    recurrence is proved, this result follows automatically. -/
theorem aperyB_growth_upper (n : ℕ) (hn : 0 < n) :
    (aperyB n : ℝ) ≤ 34 ^ n := by
  cases n with
  | zero => omega
  | succ k => exact aperyB_growth_upper_aux k

/-
The linear form bₙ·ζ(3) - aₙ decays geometrically:
    |bₙ·ζ(3) - aₙ| ≤ C · (√2 - 1)^{4n}

    where (√2-1)⁴ = 17 - 12√2 ≈ 0.0294 is the smaller root of
    the characteristic polynomial. The fast decay (exponential with
    base < 1) is the engine of the irrationality proof.
-/

/-- The characteristic polynomial of the Apéry recurrence: t² - 34t + 1.
    Roots: (1+√2)⁴ = 17+12√2 ≈ 33.97 and (√2-1)⁴ = 17-12√2 ≈ 0.029. -/
theorem apery_char_poly_discriminant :
    34 ^ 2 - 4 * 1 = 1152 := by norm_num

-- ============================================================================
-- Part V: The Irrationality Argument
-- ============================================================================

/-
**Main Theorem (Apéry 1978)**: ζ(3) is irrational.

    Proof sketch:
    1. Construct sequences aₙ ∈ ℚ and bₙ ∈ ℤ>₀ with bₙ·ζ(3) - aₙ ≠ 0
    2. Show |bₙ·ζ(3) - aₙ| → 0 geometrically (rate (√2-1)⁴ ≈ 0.029)
    3. Show lcm(1,...,n)³·aₙ ∈ ℤ (denominator control)
    4. By the prime number theorem, lcm(1,...,n)³ ~ e^{3n}
    5. So 2·lcm(1,...,n)³·bₙ·|bₙ·ζ(3) - aₙ| → 0
    6. But this quantity is a nonzero integer if ζ(3) = p/q, contradiction
-/
-- Apéry 1978; proved in Part XIII from decay + nonzero + denominator axioms
-- theorem apery_theorem : Irrational (zetaValue 3)  ← see Part XIII below

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
    ((aperyRecCoeff (n + 1) : ℚ) * aperyA (n + 1) - ((n + 1 : ℕ) : ℚ) ^ 3 * aperyA n) /
    ((n + 2 : ℕ) : ℚ) ^ 3

/-- a₀ = 0. -/
theorem aperyA_zero : aperyA 0 = 0 := rfl

/-- a₁ = 6. -/
theorem aperyA_one : aperyA 1 = 6 := rfl

/-- a₂ = 351/4. Verified by direct computation from the recurrence:
    a₂ = (3 · 39 · 6 - 1 · 0) / 8 = 702/8 = 351/4. -/
theorem aperyA_two : aperyA 2 = 351 / 4 := by
  simp only [aperyA, aperyRecCoeff]
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
  exact div_nonneg (by norm_num) (by exact_mod_cast (Nat.succ_pos k).le)

/-- Harmonic numbers are monotone increasing. -/
theorem harmonicNumber_mono (m n : ℕ) (hmn : m ≤ n) :
    harmonicNumber m ≤ harmonicNumber n := by
  unfold harmonicNumber
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
  intro k _ _
  exact div_nonneg (by norm_num) (by exact_mod_cast (Nat.succ_pos k).le)

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
theorem lcmUpTo_two : lcmUpTo 2 = 2 := by decide

/-- lcm(1, 2, ..., n) is positive for n ≥ 1. -/
theorem lcmUpTo_pos (n : ℕ) (hn : 1 ≤ n) : 0 < lcmUpTo n := by
  unfold lcmUpTo
  apply Nat.pos_of_ne_zero
  rw [Finset.lcm_ne_zero_iff]
  intro k _
  exact Nat.succ_ne_zero k

/-- lcm(1,...,n) is monotone: if n ≤ m then lcmUpTo n divides lcmUpTo m.
    Proof: Finset.range n ⊆ Finset.range m, so the lcm over the smaller set
    divides the lcm over the larger set. -/
theorem lcmUpTo_dvd_of_le {n m : ℕ} (h : n ≤ m) : lcmUpTo n ∣ lcmUpTo m := by
  unfold lcmUpTo
  apply Finset.lcm_dvd
  intro i hi
  exact Finset.dvd_lcm (Finset.mem_range.mpr (Nat.lt_of_lt_of_le (Finset.mem_range.mp hi) h))

/-- lcm(1,...,3) = 6. -/
theorem lcmUpTo_three : lcmUpTo 3 = 6 := by decide

/-- lcm(1,...,4) = 12. -/
theorem lcmUpTo_four : lcmUpTo 4 = 12 := by decide

-- ============================================================================
-- Part IX: The Linear Form bₙ·ζ(3) - aₙ
-- ============================================================================

/-- The linear form Lₙ = bₙ·ζ(3) - aₙ.
    This is the quantity that converges to 0, forcing irrationality. -/
noncomputable def linearForm (n : ℕ) : ℝ :=
  (aperyB n : ℝ) * zetaValue 3 - (aperyA n : ℝ)

/- The linear form is nonzero for n ≥ 1 (assuming ζ(3) is irrational,
    which is what we're trying to prove — so this must be established
    independently, e.g., from the explicit formula for Lₙ). -/

/-- **Denominator control**: lcm(1,...,n)³ · aₙ is an integer.
    This is the key arithmetic property of the a-sequence.
    It follows from the fact that aₙ can be written as a sum
    involving 1/k³ terms with denominators dividing lcm(1,...,n)³. -/
-- Key arithmetic: lcm³·aₙ ∈ ℤ; follows from a-sequence formula, axiomatized
axiom denominator_control (n : ℕ) :
    ∃ m : ℤ, (lcmUpTo n : ℚ) ^ 3 * aperyA n = m

-- ============================================================================
-- Part X: Summary and Remaining Sorries
-- ============================================================================

/-
## What's Proved (0 sorries)
- Apéry b-sequence defined and initial values (b₀=1, b₁=5, b₂=73, b₃=1445)
- All Apéry numbers are positive
- Recurrence verified numerically for n=1,2
- Growth bound bₙ ≤ 34^n (aperyB_growth_upper), proved from recurrence
- apery_decay_rate_pos: 0 < 17 - 12√2
- apery_product_lt_one: 27·(17-12√2) < 1 (the key quantitative threshold)
- Apéry a-sequence defined (a₀=0, a₁=6, a₂=351/4)
- Harmonic numbers and generalized harmonic sums
- lcmUpTo: positivity, divisibility, monotonicity (lcmUpTo_dvd_of_le),
  concrete values: lcmUpTo_three=6, lcmUpTo_four=12
- apery_irrationality_conditional: full integer-squeeze argument (proved)
- **apery_theorem**: ζ(3) irrational (PROVED from 5 axioms)

## Remaining Axioms (5)
1. **aperyB_recurrence**: 3-term recurrence (WZ-theory)
2. **denominator_control**: lcm³·aₙ ∈ ℤ (needs explicit a-sequence formula)
3. **lcm_hanson_bound**: lcm ≤ 3^n (Hanson 1974; needs Chebyshev theta)
4. **apery_linearForm_decay**: |Lₙ| ≤ C·(17-12√2)^n (needs integral repr.)
5. **apery_linearForm_nonzero**: Lₙ ≠ 0 for n ≥ 1 (needs integral repr.)

## Critical Path
- apery_theorem depends on axioms 3, 4, 5 and denominator_control
- Threshold: c < (1/(17-12√2))^{1/3} ≈ 3.24 makes 3^n just sufficient (3³=27)
-/

-- ============================================================================
-- Part XI: Divisibility Infrastructure for Irrationality
-- ============================================================================

/-- Every k with 0 < k ≤ n divides lcmUpTo n.
    Proof: k-1 ∈ Finset.range n, and the lcm is taken over (· + 1), so k | lcmUpTo n. -/
theorem dvd_lcmUpTo {k n : ℕ} (hk : 0 < k) (hkn : k ≤ n) : k ∣ lcmUpTo n := by
  unfold lcmUpTo
  have h1k : 1 ≤ k := hk
  have hmem : k - 1 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have hdvd : k - 1 + 1 ∣ (Finset.range n).lcm (· + 1) := Finset.dvd_lcm hmem
  rwa [Nat.sub_add_cancel h1k] at hdvd

/-- The denominator of any rational r divides lcmUpTo n when n ≥ r.den.
    This is the key divisibility fact enabling the integrality argument. -/
theorem rat_den_dvd_lcmUpTo (r : ℚ) {n : ℕ} (hn : r.den ≤ n) :
    (r.den : ℕ) ∣ lcmUpTo n :=
  dvd_lcmUpTo r.pos hn

/-- (lcmUpTo n)^3 * bₙ * r is an integer when r.den ≤ n.
    Key step: since r.den | lcmUpTo n, the cube provides enough cancellation.
    Explicitly: (q·r.den)³ · b · (r.num/r.den) = q³ · r.den² · b · r.num ∈ ℤ. -/
theorem apery_bterm_int (r : ℚ) (n : ℕ) (hn : r.den ≤ n) :
    ∃ m : ℤ, (lcmUpTo n : ℚ) ^ 3 * (aperyB n : ℚ) * r = m := by
  -- Get lcmUpTo n = r.den * q
  obtain ⟨q, hq⟩ := rat_den_dvd_lcmUpTo r hn
  -- The result is q^3 * r.den^2 * aperyB n * r.num
  use (q : ℤ) ^ 3 * (r.den : ℤ) ^ 2 * (aperyB n : ℤ) * r.num
  have hq_cast : (lcmUpTo n : ℚ) = (r.den : ℚ) * q := by exact_mod_cast hq
  have hrd : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.pos.ne'
  -- Rewrite lcmUpTo n and expand r = r.num / r.den
  have hrnd : r * (r.den : ℚ) = (r.num : ℚ) :=
    ((div_eq_iff hrd).mp (Rat.num_div_den r)).symm
  rw [hq_cast]
  calc ((r.den : ℚ) * q) ^ 3 * (aperyB n : ℚ) * r
      = (q : ℚ) ^ 3 * (r.den : ℚ) ^ 2 * (aperyB n : ℚ) * (r * r.den) := by ring
    _ = (q : ℚ) ^ 3 * (r.den : ℚ) ^ 2 * (aperyB n : ℚ) * r.num := by rw [hrnd]
    _ = ↑((q : ℤ) ^ 3 * (r.den : ℤ) ^ 2 * (aperyB n : ℤ) * r.num) := by push_cast; ring

-- ============================================================================
-- Part XII: Conditional Irrationality Theorem
-- ============================================================================

/-
## The Core Irrationality Argument

This theorem formalizes the logical heart of Apéry's 1978 proof. It shows that
IF the three key analytic properties hold, THEN ζ(3) must be irrational.

The three hypotheses correspond to the three main steps of Apéry's argument:
1. **h_decay**: d_n · |Lₙ| → 0  (fast decay: rate ≈ (17 - 12√2)ⁿ ≈ 0.029ⁿ)
2. **h_nonzero**: Lₙ ≠ 0 for all n ≥ 1  (non-degenerate approximation)
3. **h_denom**: lcm³ · aₙ ∈ ℤ  (denominator control)

The proof is by contradiction: if ζ(3) = r ∈ ℚ, then d_n · Lₙ is a nonzero
rational with integer numerator and denominator dividing q (= r.den), so
|d_n · Lₙ| ≥ 1/q. But h_decay gives d_n · |Lₙ| < 1/q for large n.
Contradiction.

More precisely: d_n · (bₙ · r - aₙ) = d_n · bₙ · r - d_n · aₙ, which is
a nonzero integer for n ≥ r.den (by h_denom and the key divisibility fact
that r.den | lcmUpTo n). So |d_n · Lₙ| ≥ 1, but h_decay gives < 1. □
-/

/-- The rational linear form Qₙ(r) = bₙ · r - aₙ.
    When r = ζ(3), this equals the real linear form Lₙ. -/
noncomputable def rationalLinearForm (r : ℚ) (n : ℕ) : ℚ :=
  (aperyB n : ℚ) * r - aperyA n

/-- When (r : ℝ) = ζ(3), the rational linear form casts to the real linear form. -/
theorem rationalLinearForm_cast {r : ℚ} {n : ℕ}
    (hr : (r : ℝ) = zetaValue 3) :
    (rationalLinearForm r n : ℝ) = linearForm n := by
  simp only [rationalLinearForm, linearForm]
  push_cast [hr]; ring

/-- **Conditional Irrationality of ζ(3)** — core of Apéry's 1978 proof.

    Given the three key analytic inputs (decay, non-degeneracy, denominator control),
    this proves ζ(3) is irrational via the classical integer-squeeze argument. -/
theorem apery_irrationality_conditional
    (h_decay : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (lcmUpTo n : ℝ) ^ 3 * |linearForm n| < ε)
    (h_nonzero : ∀ n : ℕ, 0 < n → linearForm n ≠ 0)
    (h_denom : ∀ n : ℕ, ∃ m : ℤ, (lcmUpTo n : ℚ) ^ 3 * aperyA n = m) :
    Irrational (zetaValue 3) := by
  -- Assume for contradiction that ζ(3) is rational
  intro ⟨r, hr⟩
  -- hr : (↑r : ℝ) = zetaValue 3
  -- -----------------------------------------------------------------------
  -- Choose N₀ large enough:
  --   (a) N₀ ≥ N_decay + 1, so the decay bound d_{N₀} · |L_{N₀}| < 1 holds
  --   (b) N₀ ≥ r.den, so r.den | lcmUpTo N₀ (divisibility for integrality)
  -- -----------------------------------------------------------------------
  obtain ⟨N_decay, hN_decay⟩ := h_decay 1 one_pos
  set N₀ := max (N_decay + 1) r.den with hN₀_def
  have hN₀_pos : 0 < N₀ :=
    Nat.lt_of_lt_of_le (Nat.succ_pos N_decay) (le_max_left _ _)
  have hN₀_den : r.den ≤ N₀ := le_max_right _ _
  have hN₀_decay : N_decay ≤ N₀ :=
    Nat.le_succ N_decay |>.trans (le_max_left _ _)
  -- -----------------------------------------------------------------------
  -- Decay bound: d_{N₀} · |L_{N₀}| < 1
  -- -----------------------------------------------------------------------
  have hsmall : (lcmUpTo N₀ : ℝ) ^ 3 * |linearForm N₀| < 1 :=
    hN_decay N₀ hN₀_decay
  -- -----------------------------------------------------------------------
  -- Integrality: d_{N₀} · Q_{N₀} is a nonzero integer
  -- where Q_{N₀} = rationalLinearForm r N₀  (a rational number)
  -- -----------------------------------------------------------------------
  -- Connection between rational and real linear forms
  have hQ_cast : (rationalLinearForm r N₀ : ℝ) = linearForm N₀ :=
    rationalLinearForm_cast hr
  -- d_{N₀} · Q_{N₀} is an integer
  obtain ⟨m_a, hm_a⟩ := h_denom N₀
  obtain ⟨m_b, hm_b⟩ := apery_bterm_int r N₀ hN₀_den
  -- d_{N₀} · bₙ · r - d_{N₀} · aₙ = m_b - m_a ∈ ℤ
  obtain ⟨M, hM⟩ : ∃ m : ℤ, (lcmUpTo N₀ : ℚ) ^ 3 * rationalLinearForm r N₀ = m :=
    ⟨m_b - m_a, by
      simp only [rationalLinearForm, mul_sub]
      rw [← mul_assoc, hm_b, hm_a]
      push_cast; ring⟩
  -- -----------------------------------------------------------------------
  -- M ≠ 0: because L_{N₀} ≠ 0 (by h_nonzero) and d_{N₀} > 0
  -- -----------------------------------------------------------------------
  have hlcm_pos_ℚ : (0 : ℚ) < (lcmUpTo N₀ : ℚ) ^ 3 :=
    pow_pos (by exact_mod_cast lcmUpTo_pos N₀ hN₀_pos) 3
  have hLnz : linearForm N₀ ≠ 0 := h_nonzero N₀ hN₀_pos
  have hQnz : rationalLinearForm r N₀ ≠ 0 := fun h =>
    hLnz (by rw [← hQ_cast, h, Rat.cast_zero])
  have hMnz : M ≠ 0 := by
    intro hM0
    apply hQnz
    have hM0' : (M : ℚ) = 0 := by exact_mod_cast hM0
    have h0 : (lcmUpTo N₀ : ℚ) ^ 3 * rationalLinearForm r N₀ = 0 := hM.trans hM0'
    exact (mul_eq_zero.mp h0).resolve_left (ne_of_gt hlcm_pos_ℚ)
  -- -----------------------------------------------------------------------
  -- Integer squeeze: |M| ≥ 1, but d_{N₀} · |L_{N₀}| = |M| < 1
  -- -----------------------------------------------------------------------
  have hMge1 : (1 : ℝ) ≤ |(M : ℝ)| := by exact_mod_cast Int.one_le_abs hMnz
  -- d_{N₀} · |L_{N₀}| = |(lcmUpTo N₀)³ · Q_{N₀}| = |M|
  have hlcm_nonneg : (0 : ℝ) ≤ (lcmUpTo N₀ : ℝ) ^ 3 :=
    pow_nonneg (Nat.cast_nonneg _) 3
  -- First show the real product equals M
  have hcast : (lcmUpTo N₀ : ℝ) ^ 3 * linearForm N₀ = (M : ℝ) := by
    have h := congr_arg (↑· : ℚ → ℝ) hM
    push_cast at h
    rwa [hQ_cast] at h
  -- Then extract absolute values
  have heq : (lcmUpTo N₀ : ℝ) ^ 3 * |linearForm N₀| = |(M : ℝ)| :=
    calc (lcmUpTo N₀ : ℝ) ^ 3 * |linearForm N₀|
        = |(lcmUpTo N₀ : ℝ) ^ 3 * linearForm N₀| := by
            rw [abs_mul, abs_of_nonneg hlcm_nonneg]
      _ = |(M : ℝ)| := by rw [hcast]
  -- Now: 1 ≤ |M| = d_{N₀} · |L_{N₀}| < 1 — contradiction
  linarith [heq ▸ hsmall]

-- ============================================================================
-- Part XIII: Quantitative Bounds and Main Theorem Proof
-- ============================================================================

/-- The Apéry decay rate 17 - 12√2 is positive.
    Since (17/12)² = 289/144 > 2, we have 17/12 > √2, so 17 > 12√2. -/
theorem apery_decay_rate_pos : (0 : ℝ) < 17 - 12 * Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 from by norm_num),
             Real.sqrt_nonneg 2,
             sq_nonneg (Real.sqrt 2 - 17 / 12)]

/-- Key quantitative bound: 27 · (17 - 12√2) < 1.
    Since (229/162)² = 52441/26244 < 2, we have 229/162 < √2, giving
    12√2 > 12·229/162 = 458/27, so 27·(17-12√2) < 27·(17-458/27) = 1. -/
theorem apery_product_lt_one : 27 * (17 - 12 * Real.sqrt 2) < 1 := by
  have h : (229 : ℝ) / 162 < Real.sqrt 2 := by
    have hsq : Real.sqrt ((229 / 162 : ℝ) ^ 2) = 229 / 162 :=
      Real.sqrt_sq (by norm_num)
    rw [← hsq]
    apply Real.sqrt_lt_sqrt (by norm_num)
    norm_num
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 from by norm_num), Real.sqrt_nonneg 2]

/-- **Hanson's bound (1974)**: lcm(1, 2, ..., n) ≤ 3^n.
    Sharper than Nair's 4^n; sufficient because 3³·(17-12√2) = 27·(17-12√2) < 1.
    Reference: D. Hanson, "On the product of the primes" (Canad. Math. Bull., 1974). -/
axiom lcm_hanson_bound (n : ℕ) : lcmUpTo n ≤ 3 ^ n

/-- The linear form Lₙ = bₙ·ζ(3) - aₙ decays geometrically at rate (17-12√2).
    From the integral representation, |Lₙ| ≤ C·(17-12√2)^n for some C > 0. -/
axiom apery_linearForm_decay : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
    |linearForm n| ≤ C * (17 - 12 * Real.sqrt 2) ^ n

/-- The linear form Lₙ = bₙ·ζ(3) - aₙ is nonzero for n ≥ 1.
    Follows from the integral representation: the integrand has definite sign,
    so Lₙ ≠ 0 independently of whether ζ(3) is rational. -/
axiom apery_linearForm_nonzero : ∀ n : ℕ, 0 < n → linearForm n ≠ 0

/-- **Apéry's Theorem (1978)**: ζ(3) is irrational.

    Applies `apery_irrationality_conditional` with:
    · Hanson's lcm ≤ 3^n  →  (lcmUpTo n)³ ≤ 27^n
    · Decay |Lₙ| ≤ C·(17-12√2)^n, and 27·(17-12√2) < 1
    · Therefore (lcmUpTo n)³·|Lₙ| ≤ C·(27·(17-12√2))^n → 0.

    Original: R. Apéry, "Irrationalité de ζ(2) et ζ(3)", 1978. -/
theorem apery_theorem : Irrational (zetaValue 3) := by
  apply apery_irrationality_conditional
  · -- h_decay: ∀ ε > 0, ∃ N, ∀ n ≥ N, (lcmUpTo n)³ · |Lₙ| < ε
    intro ε hε
    obtain ⟨C, hC_pos, hC⟩ := apery_linearForm_decay
    have hδ_pos : (0 : ℝ) < 17 - 12 * Real.sqrt 2 := apery_decay_rate_pos
    have hr1 : 27 * (17 - 12 * Real.sqrt 2) < 1 := apery_product_lt_one
    set r := (27 : ℝ) * (17 - 12 * Real.sqrt 2) with hr_def
    have hr_pos : 0 < r := by positivity
    -- r^n → 0 since 0 < r < 1
    have htend : Filter.Tendsto (fun n : ℕ => r ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hr_pos.le hr1
    -- C · r^n → 0 and eventually C · r^n < ε
    have hev : ∀ᶠ n : ℕ in Filter.atTop, C * r ^ n < ε := by
      have htend_C : Filter.Tendsto (fun n : ℕ => C * r ^ n) Filter.atTop (nhds 0) := by
        have hconst : Filter.Tendsto (fun _ : ℕ => C) Filter.atTop (nhds C) :=
          tendsto_const_nhds
        have h := hconst.mul htend
        simp at h
        exact h
      exact htend_C.eventually (Iio_mem_nhds hε)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    refine ⟨N, fun n hn => ?_⟩
    -- Key algebra: (3^n)^3 = 27^n
    have h27 : ((3 : ℝ) ^ n) ^ 3 = (27 : ℝ) ^ n := by
      rw [← pow_mul, mul_comm, pow_mul, show (3 : ℝ) ^ 3 = 27 from by norm_num]
    have hlcm : (lcmUpTo n : ℝ) ≤ (3 : ℝ) ^ n := by exact_mod_cast lcm_hanson_bound n
    calc (lcmUpTo n : ℝ) ^ 3 * |linearForm n|
        ≤ ((3 : ℝ) ^ n) ^ 3 * (C * (17 - 12 * Real.sqrt 2) ^ n) :=
          mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hlcm 3)
            (hC n) (abs_nonneg _) (by positivity)
      _ = C * r ^ n := by rw [h27, hr_def, mul_pow]; ring
      _ < ε := hN n hn
  · exact apery_linearForm_nonzero
  · exact denominator_control


-- ============================================================================
-- Part XV: Lower Bound on ζ(3) — Concrete Nonzero Base Case
-- ============================================================================

/-- Lower bound: ζ(3) > 6/5. Proved via the 16-term partial sum S₁₆ > 1.2.
    Uses: ζ(3) ≥ ∑_{n ∈ range 17} 1/n³ (partial sum bound from Summable),
    and the 16-term sum exceeds 6/5 by direct computation. -/
theorem zetaValue_three_gt_6_5 : (6 : ℝ) / 5 < zetaValue 3 := by
  have hsum : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 3) := summable_zetaValue 3 (by norm_num)
  have hle : ∑ n ∈ Finset.range 17, (1 : ℝ) / (n : ℝ) ^ 3 ≤ zetaValue 3 := by
    unfold zetaValue
    exact sum_le_hasSum (Finset.range 17) (fun n _ => by positivity) hsum.hasSum
  have hbound : (6 : ℝ) / 5 < ∑ n ∈ Finset.range 17, (1 : ℝ) / (n : ℝ) ^ 3 := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  linarith

/-- The linear form L₁ = b₁·ζ(3) - a₁ = 5ζ(3) - 6 is strictly positive.

    This is a concrete proved instance of the nonzero property for n = 1,
    established from the elementary lower bound ζ(3) > 6/5, without
    using the integral representation required for the general case. -/
theorem linearForm_one_pos : 0 < linearForm 1 := by
  unfold linearForm
  have hb : (aperyB 1 : ℝ) = 5 := by exact_mod_cast aperyB_one
  have ha : (aperyA 1 : ℝ) = 6 := by exact_mod_cast aperyA_one
  rw [hb, ha]
  linarith [zetaValue_three_gt_6_5]

-- ============================================================================
-- Part XVI: Tail Lower Bound — ζ(3) ≥ S_N + 1/(2N²) for N ≥ 1
-- ============================================================================

/-- Algebraic inequality: 1/(2x²) - 1/(2(x+1)²) ≤ 1/x³ for x ≥ 1.
    Proof: Cross-multiply: (2(x+1)² - 2x²)·x³ ≤ 4x²(x+1)², i.e. (4x+2)x³ ≤ 4x²(x+1)². -/
private lemma cube_inv_ge_telescoping' (x : ℝ) (hx : 1 ≤ x) :
    (1 : ℝ) / (2 * x ^ 2) - 1 / (2 * (x + 1) ^ 2) ≤ 1 / x ^ 3 := by
  have hxpos : (0 : ℝ) < x := by linarith
  rw [div_sub_div _ _ (by positivity) (by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg x, pow_pos hxpos 2]

/-- Telescoping partial sum: ∑_{k=0}^{M-1} [1/(2(k+N)²) - 1/(2(k+N+1)²)] = 1/(2N²) - 1/(2(M+N)²). -/
private lemma telescope_sum_eq (N M : ℕ) :
    ∑ k ∈ Finset.range M, ((1 : ℝ) / (2 * ((k : ℝ) + N) ^ 2) - 1 / (2 * ((k : ℝ) + N + 1) ^ 2)) =
    1 / (2 * (N : ℝ) ^ 2) - 1 / (2 * ((M : ℝ) + N) ^ 2) := by
  induction M with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast; ring

/-- **Quantitative lower bound on ζ(3)**:
    For any N ≥ 1, the N-term partial sum plus 1/(2N²) is a lower bound for ζ(3).

    Proof: The tail ∑_{k≥N} 1/k³ telescopes as:
      ∑_{k≥N} 1/k³ ≥ ∑_{k≥N} [1/(2k²) - 1/(2(k+1)²)] = 1/(2N²).

    This gives ζ(3) = S_N + tail ≥ S_N + 1/(2N²). -/
theorem zetaValue_three_tail_lb (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.range N, (1 : ℝ) / (k : ℝ) ^ 3 + 1 / (2 * (N : ℝ) ^ 2) ≤ zetaValue 3 := by
  have hsum : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 3) := summable_zetaValue 3 (by norm_num)
  -- Split ζ(3) = S_N + tail
  have hsplit : zetaValue 3 = ∑ k ∈ Finset.range N, (1 : ℝ) / (k : ℝ) ^ 3 +
      ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + N) ^ 3 := by
    unfold zetaValue
    rw [← hsum.sum_add_tsum_nat_add N]
    congr 1; apply tsum_congr; intro k; push_cast; ring
  rw [hsplit]
  -- Suffices to show 1/(2N²) ≤ tail
  suffices h : (1 : ℝ) / (2 * (N : ℝ) ^ 2) ≤ ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + N) ^ 3 by linarith
  -- The shifted series is summable
  have hshifted : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + N) ^ 3) := by
    have h1 : Summable (fun k : ℕ => (1 : ℝ) / ((k + N : ℕ) : ℝ) ^ 3) :=
      (summable_nat_add_iff N).mpr hsum
    convert h1 using 1; ext k; push_cast; ring
  -- For every M, 1/(2N²) - 1/(2(M+N)²) ≤ tail
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hle : ∀ M : ℕ, (1 : ℝ) / (2 * (N : ℝ) ^ 2) - 1 / (2 * ((M : ℝ) + N) ^ 2) ≤
      ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + N) ^ 3 := fun M =>
    calc (1 : ℝ) / (2 * (N : ℝ) ^ 2) - 1 / (2 * ((M : ℝ) + N) ^ 2)
        = ∑ k ∈ Finset.range M, (1 / (2 * ((k : ℝ) + N) ^ 2) - 1 / (2 * ((k : ℝ) + N + 1) ^ 2)) :=
          (telescope_sum_eq N M).symm
      _ ≤ ∑ k ∈ Finset.range M, (1 : ℝ) / ((k : ℝ) + N) ^ 3 :=
          Finset.sum_le_sum fun k _ => cube_inv_ge_telescoping' ((k : ℝ) + N) (by
            have : (1 : ℝ) ≤ N := hN'
            have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
            linarith)
      _ ≤ ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + N) ^ 3 :=
          sum_le_hasSum _ (fun k _ => by positivity) hshifted.hasSum
  -- Take limit: 1/(2*(M+N)²) → 0 as M → ∞
  have h0 : Filter.Tendsto (fun M : ℕ => (1 : ℝ) / (2 * ((M : ℝ) + N) ^ 2))
      Filter.atTop (nhds 0) := by
    apply squeeze_zero (fun M => by positivity) _
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    intro M
    have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have h2MN : (0 : ℝ) < 2 * ((M : ℝ) + N) ^ 2 := by positivity
    rw [div_le_div_iff₀ h2MN hM1]
    have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    nlinarith [hMnn, hN', sq_nonneg ((M : ℝ) + N), mul_nonneg hMnn hMnn]
  -- Conclude: 1/(2N²) ≤ tail via limit: f(M) = 1/(2N²) - 1/(2(M+N)²) → 1/(2N²)
  have h1 : Filter.Tendsto (fun _ : ℕ => (1 : ℝ) / (2 * (N : ℝ) ^ 2))
      Filter.atTop (nhds (1 / (2 * (N : ℝ) ^ 2))) := tendsto_const_nhds
  have h2 := h1.sub h0
  simp only [sub_zero] at h2
  exact le_of_tendsto' h2 hle

-- ============================================================================
-- Part XVII: Tail Upper Bound — ζ(3) ≤ S_{N+1} + 1/(2N²) for N ≥ 1
-- ============================================================================

/-- Algebraic inequality: 1/(x+1)³ ≤ 1/(2x²) - 1/(2(x+1)²) for x ≥ 1.
    Equivalently: (x+1)·(2x+1) ≥ 2x², i.e. 3x+1 ≥ 0. -/
private lemma cube_succ_inv_le_telescoping (x : ℝ) (hx : 1 ≤ x) :
    (1 : ℝ) / (x + 1) ^ 3 ≤ 1 / (2 * x ^ 2) - 1 / (2 * (x + 1) ^ 2) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hx1pos : (0 : ℝ) < x + 1 := by linarith
  rw [div_sub_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
  have hpoly : 2 * (2 * x + 1) * (x + 1) ^ 3 - 4 * x ^ 2 * (x + 1) ^ 2 =
      (x + 1) ^ 2 * (6 * x + 2) := by ring
  nlinarith [pow_nonneg hx1pos.le 2, sq_nonneg (x + 1), hpoly]

/-- **Quantitative upper bound on ζ(3)**:
    For any N ≥ 1, the (N+1)-term partial sum plus 1/(2N²) is an upper bound for ζ(3).

    Proof: The tail ∑_{k≥N+1} 1/k³ telescopes as:
      ∑_{k≥N+1} 1/k³ ≤ ∑_{k≥N} [1/(2k²) - 1/(2(k+1)²)] = 1/(2N²).

    This gives ζ(3) = S_{N+1} + tail ≤ S_{N+1} + 1/(2N²). -/
theorem zetaValue_three_tail_ub (N : ℕ) (hN : 1 ≤ N) :
    zetaValue 3 ≤ ∑ k ∈ Finset.range (N + 1), (1 : ℝ) / (k : ℝ) ^ 3 + 1 / (2 * (N : ℝ) ^ 2) := by
  have hsum : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 3) := summable_zetaValue 3 (by norm_num)
  -- Split ζ(3) = S_{N+1} + tail_{N+1}
  have hsplit : zetaValue 3 = ∑ k ∈ Finset.range (N + 1), (1 : ℝ) / (k : ℝ) ^ 3 +
      ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + (N + 1)) ^ 3 := by
    unfold zetaValue
    rw [← hsum.sum_add_tsum_nat_add (N + 1)]
    congr 1; apply tsum_congr; intro k; push_cast; ring
  rw [hsplit]
  -- Suffices to show tail_{N+1} ≤ 1/(2N²)
  suffices h : ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + (N + 1)) ^ 3 ≤ 1 / (2 * (N : ℝ) ^ 2) by linarith
  -- The shifted series is summable
  have hshifted : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + (N + 1)) ^ 3) := by
    apply Summable.congr ((summable_nat_add_iff (N + 1)).mpr hsum)
    intro k; push_cast; ring
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  -- For every M, the M-term partial sum of the tail is ≤ 1/(2N²)
  have hle_ub : ∀ M : ℕ, ∑ k ∈ Finset.range M, (1 : ℝ) / ((k : ℝ) + (N + 1)) ^ 3 ≤
      1 / (2 * (N : ℝ) ^ 2) := fun M =>
    calc ∑ k ∈ Finset.range M, (1 : ℝ) / ((k : ℝ) + (N + 1)) ^ 3
        ≤ ∑ k ∈ Finset.range M,
            ((1 : ℝ) / (2 * ((k : ℝ) + N) ^ 2) - 1 / (2 * ((k : ℝ) + N + 1) ^ 2)) :=
          Finset.sum_le_sum fun k _ => by
            have h := cube_succ_inv_le_telescoping ((k : ℝ) + N)
              (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
            convert h using 2; push_cast; ring
      _ = 1 / (2 * (N : ℝ) ^ 2) - 1 / (2 * ((M : ℝ) + N) ^ 2) :=
          telescope_sum_eq N M
      _ ≤ 1 / (2 * (N : ℝ) ^ 2) := sub_le_self _ (by positivity)
  -- tail = limit of partial sums ≤ 1/(2N²)
  exact le_of_tendsto' hshifted.hasSum.tendsto_sum_nat hle_ub

-- ============================================================================
-- Part XVIII: Second Concrete Nonzero Base Case
-- ============================================================================

/-- The linear form L₂ = b₂·ζ(3) - a₂ = 73·ζ(3) - 351/4 is strictly positive.

    This is a second concrete proved instance of the nonzero property for n = 2.
    Since 73·ζ(3) - 351/4 > 0 iff ζ(3) > 351/292 ≈ 1.20205479,
    we verify this from the quantitative lower bound with N = 200 terms. -/
theorem linearForm_two_pos : 0 < linearForm 2 := by
  unfold linearForm
  have hb : (aperyB 2 : ℝ) = 73 := by exact_mod_cast aperyB_two
  have ha : (aperyA 2 : ℝ) = 351 / 4 := by rw [aperyA_two]; norm_num
  rw [hb, ha]
  -- Suffices: ζ(3) > 351/292 ≈ 1.20205479
  suffices h : (351 : ℝ) / 292 < zetaValue 3 by linarith
  -- Lower bound: ζ(3) ≥ S₁₀₀ + 1/(2·100²). Need N ≥ 63 for S_N + 1/(2N²) > 351/292.
  -- Use native_decide over ℚ (fast native OCaml computation) then cast to ℝ.
  have hlb := zetaValue_three_tail_lb 100 (by norm_num)
  have hbound : (351 : ℝ) / 292 <
      ∑ k ∈ Finset.range 100, (1 : ℝ) / (k : ℝ) ^ 3 + 1 / (2 * (100 : ℝ) ^ 2) := by
    have h : (351 : ℚ) / 292 <
        ∑ k ∈ Finset.range 100, (1 : ℚ) / (k : ℚ) ^ 3 + 1 / (2 * (100 : ℚ) ^ 2) := by
      native_decide
    have h2 : ((351 : ℚ) / 292 : ℝ) <
        ((∑ k ∈ Finset.range 100, (1 : ℚ) / (k : ℚ) ^ 3 +
          1 / (2 * (100 : ℚ) ^ 2) : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at h2
    linarith
  linarith

-- ============================================================================
-- Part XIX: Factorial Denominator Control (Axiom-Free) & Linear Form Base Cases
-- ============================================================================

/-- a₃ = 62531/36. From the recurrence:
    a₃ = (aperyRecCoeff(2) · a₂ - 2³ · a₁) / 3³ = (535·351/4 - 48) / 27. -/
theorem aperyA_three : aperyA 3 = 62531 / 36 := by
  simp only [aperyA, aperyRecCoeff]
  norm_num

/-- The key recurrence for factorial denominator control:
    (n+2)!³ · a_{n+2} = coeff(n+1) · (n+1)!³ · a_{n+1} - (n+1)⁶ · n!³ · a_n

    Proof: From the definition, (n+2)³ · a_{n+2} = c · a_{n+1} - (n+1)³ · a_n.
    Multiplying by (n+1)!³ and using (n+2)! = (n+2) · (n+1)!. -/
private lemma aperyA_factorial_step (n : ℕ) :
    ((n + 2).factorial : ℚ) ^ 3 * aperyA (n + 2) =
    ↑(aperyRecCoeff (n + 1)) * ((n + 1).factorial : ℚ) ^ 3 * aperyA (n + 1) -
    ((n + 1 : ℕ) : ℚ) ^ 6 * (n.factorial : ℚ) ^ 3 * aperyA n := by
  have hn2 : ((n + 2 : ℕ) : ℚ) ≠ 0 := by positivity
  -- Unfold aperyA (n+2) directly from its recursive definition
  have hunf : aperyA (n + 2) =
      (↑(aperyRecCoeff (n + 1)) * aperyA (n + 1) - ((n + 1 : ℕ) : ℚ) ^ 3 * aperyA n) /
      ((n + 2 : ℕ) : ℚ) ^ 3 := by
    simp only [aperyA]
  have hf2 : ((n + 2).factorial : ℚ) ^ 3 =
      ((n + 2 : ℕ) : ℚ) ^ 3 * ((n + 1).factorial : ℚ) ^ 3 := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hf1 : ((n + 1).factorial : ℚ) ^ 3 =
      ((n + 1 : ℕ) : ℚ) ^ 3 * (n.factorial : ℚ) ^ 3 := by
    rw [Nat.factorial_succ]; push_cast; ring
  -- Combine: (n+2)!³ = (n+2)³*(n+1)!³, then cancel (n+2)³ vs denominator
  rw [hunf, hf2]
  field_simp
  rw [hf1]
  push_cast; ring

/-- **Factorial denominator control (axiom-free)**:
    (n!)³ · aₙ ∈ ℤ for all n, proved by 2-step induction on the Apéry recurrence.

    This is a weaker form of `denominator_control` (which requires lcm instead of n!)
    but is completely free of axioms. The difference matters because lcm(1,...,n) ~ eⁿ
    while n! ~ (n/e)ⁿ — factorial grows faster, making it easier to prove integrality.

    The proof key: `aperyA_factorial_step` gives a recurrence for (k!)³·aₖ that
    preserves integrality, so induction closes the argument. -/
theorem denominator_control_factorial (n : ℕ) :
    ∃ m : ℤ, (n.factorial : ℚ) ^ 3 * aperyA n = m := by
  -- Prove by 2-step induction: package both n and n+1 together
  suffices h : ∀ k : ℕ,
      (∃ m : ℤ, (k.factorial : ℚ) ^ 3 * aperyA k = m) ∧
      (∃ m : ℤ, ((k + 1).factorial : ℚ) ^ 3 * aperyA (k + 1) = m) from (h n).1
  intro k
  induction k with
  | zero =>
    refine ⟨⟨0, ?_⟩, ⟨6, ?_⟩⟩
    · norm_num [aperyA_zero, Nat.factorial_zero]
    · norm_num [aperyA_one, Nat.factorial_zero, Nat.factorial_succ]
  | succ n ih =>
    obtain ⟨⟨m₁, hm₁⟩, ⟨m₂, hm₂⟩⟩ := ih
    refine ⟨⟨m₂, hm₂⟩, ?_⟩
    -- Prove ((n+2)!)³ · a_{n+2} ∈ ℤ
    -- By aperyA_factorial_step: = coeff * m₂ - (n+1)^6 * m₁
    use aperyRecCoeff (n + 1) * m₂ - (n + 1 : ℤ) ^ 6 * m₁
    have := aperyA_factorial_step n
    rw [this]
    push_cast
    linear_combination (↑(aperyRecCoeff (n + 1)) : ℚ) * hm₂ -
      ((n : ℚ) + 1) ^ 6 * hm₁

/-- The linear form L₃ = b₃·ζ(3) - a₃ = 1445·ζ(3) - 62531/36 is strictly positive.

    Since 1445·ζ(3) - 62531/36 > 0 iff ζ(3) > 62531/52020 ≈ 1.202056903...,
    and ζ(3) ≈ 1.202056903159594..., the gap is only ≈ 3×10⁻⁸.

    We verify this from the quantitative lower bound with N = 350 terms.
    N ≥ 325 is required since the error in the bound is ≈ 1/N³ and the gap is 3×10⁻⁸. -/
theorem linearForm_three_pos : 0 < linearForm 3 := by
  unfold linearForm
  have hb : (aperyB 3 : ℝ) = 1445 := by exact_mod_cast aperyB_three
  have ha : (aperyA 3 : ℝ) = 62531 / 36 := by rw [aperyA_three]; norm_num
  rw [hb, ha]
  -- Suffices: ζ(3) > 62531/52020 (= a₃/b₃)
  suffices h : (62531 : ℝ) / 52020 < zetaValue 3 by linarith
  -- Lower bound: ζ(3) ≥ S₁₀₀₀ + 1/(2·1000²). N=1000 gives bound error ≈ 5×10⁻⁷.
  have hlb := zetaValue_three_tail_lb 1000 (by norm_num)
  have hbound : (62531 : ℝ) / 52020 <
      ∑ k ∈ Finset.range 1000, (1 : ℝ) / (k : ℝ) ^ 3 + 1 / (2 * (1000 : ℝ) ^ 2) := by
    have h : (62531 : ℚ) / 52020 <
        ∑ k ∈ Finset.range 1000, (1 : ℚ) / (k : ℚ) ^ 3 + 1 / (2 * (1000 : ℚ) ^ 2) := by
      native_decide
    have h2 : ((62531 : ℚ) / 52020 : ℝ) <
        ((∑ k ∈ Finset.range 1000, (1 : ℚ) / (k : ℚ) ^ 3 +
          1 / (2 * (1000 : ℚ) ^ 2) : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at h2
    linarith
  linarith

end AperyZetaThree
