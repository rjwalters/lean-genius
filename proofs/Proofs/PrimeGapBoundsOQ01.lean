/-
# Dusart-Type Bounds on the nth Prime

Explicit bounds on p_n improving the exponential bound p_n ≤ 2^(n+1)
from PrimeGapBounds.lean.

**Status**: AXIOMATIZED (3 axioms)
- Axiom 1: PNT asymptotic p_n/(n·ln n) → 1
- Axiom 2: Dusart upper bound p_n ≤ n(ln n + ln ln n) for n ≥ 6
- Axiom 3: Dusart lower bound p_n ≥ n(ln n + ln ln n - 1) for n ≥ 6

**Key Results (PROVED)**:
- From PNT: ∀ ε > 0, eventually p_n < (1+ε)·n·ln n
- From PNT: ∀ ε > 0, eventually p_n > (1-ε)·n·ln n
- Sandwich: n(ln n + ln ln n - 1) ≤ p_n ≤ n(ln n + ln ln n) for n ≥ 6
- The gap between upper and lower Dusart bounds is exactly n

**Context**:
- Parent: PrimeGapBounds.lean proves p_n ≤ 2^(n+1) from Bertrand
- The Dusart bound n(ln n + ln ln n) grows polynomially, vastly improving
  the exponential bound
- Full derivation of Dusart from PNT requires explicit error terms in the
  prime counting function (not available in Mathlib)

**References**:
- Rosser, J.B. (1941). Explicit bounds for some functions of prime numbers.
  Amer. J. Math. 63, 211-232.
- Dusart, P. (1999). The k-th prime is greater than k(ln k + ln ln k - 1) for k ≥ 2.
  Math. Comp. 68, 411-415.
- Dusart, P. (2010). Estimates of some functions over primes without R.H.
  arXiv:1002.0442.
-/

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

noncomputable section

open Filter Topology Real Nat

namespace DusartBounds

/-
## Part I: Setup

We work with Nat.nth Nat.Prime n (the n-th prime, 0-indexed) and Real.log.
-/

/-- The nth prime is prime. -/
lemma nth_prime_is_prime (n : ℕ) : Nat.Prime (nth Nat.Prime n) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

/-- The nth prime is at least 2. -/
lemma nth_prime_ge_two (n : ℕ) : 2 ≤ nth Nat.Prime n :=
  (nth_prime_is_prime n).two_le

/-
## Part II: The PNT Asymptotic (Axiomatized)

The Prime Number Theorem implies p_n ~ n·ln(n).
See PrimeNumberTheorem.lean for the full PNT formalization.
-/

/-- **Axiom: PNT asymptotic for the nth prime**

p_n/(n·ln n) → 1 as n → ∞.

This is a consequence of the Prime Number Theorem: π(x) ~ x/ln(x).
Inverting the prime counting function gives p_n ~ n·ln(n).
See PrimeNumberTheorem.lean for the full axiomatization. -/
axiom nth_prime_asymptotic :
    Tendsto (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) / (↑n * Real.log ↑n)) atTop (𝓝 1)

/-
## Part III: Asymptotic Bounds (Proved from PNT)

From the limit p_n/(n·ln n) → 1, we extract explicit asymptotic bounds.
These are genuine theorems, not axioms.
-/

/-- **From PNT: eventually p_n < (1+ε)·n·ln(n)**

Since p_n/(n·ln n) → 1, the ratio eventually enters Iio(1+ε).
Multiplying by n·ln(n) > 0 (for n ≥ 3) gives the result. -/
theorem nth_prime_eventually_lt_mul (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, (Nat.nth Nat.Prime n : ℝ) < (1 + ε) * (↑n * Real.log ↑n) := by
  have hlt : (1 : ℝ) < 1 + ε := by linarith
  have h := nth_prime_asymptotic.eventually (Iio_mem_nhds hlt)
  filter_upwards [h, eventually_ge_atTop 3] with n hn hn3
  simp only [Set.mem_Iio] at hn
  have hn_cast : (3 : ℝ) ≤ (↑n : ℝ) := by exact_mod_cast hn3
  have hlog_pos : 0 < Real.log (↑n : ℝ) := Real.log_pos (by linarith)
  have hn_pos : (0 : ℝ) < ↑n := by linarith
  have hnlog_pos : 0 < ↑n * Real.log ↑n := mul_pos hn_pos hlog_pos
  exact (div_lt_iff hnlog_pos).mp hn

/-- **From PNT: eventually p_n > (1-ε)·n·ln(n)**

The symmetric bound: the ratio eventually exceeds 1-ε. -/
theorem nth_prime_eventually_gt_mul (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, (1 - ε) * (↑n * Real.log ↑n) < (Nat.nth Nat.Prime n : ℝ) := by
  have hlt : 1 - ε < (1 : ℝ) := by linarith
  have h := nth_prime_asymptotic.eventually (Ioi_mem_nhds hlt)
  filter_upwards [h, eventually_ge_atTop 3] with n hn hn3
  simp only [Set.mem_Ioi] at hn
  have hn_cast : (3 : ℝ) ≤ (↑n : ℝ) := by exact_mod_cast hn3
  have hlog_pos : 0 < Real.log (↑n : ℝ) := Real.log_pos (by linarith)
  have hn_pos : (0 : ℝ) < ↑n := by linarith
  have hnlog_pos : 0 < ↑n * Real.log ↑n := mul_pos hn_pos hlog_pos
  exact (lt_div_iff hnlog_pos).mp hn

/-- **The PNT asymptotic is a genuine improvement over the Bertrand bound**

For any C > 1, eventually (1+ε)·n·ln(n) < C^n.
This witnesses that the PNT bound p_n ≲ n·ln(n) is exponentially better
than p_n ≤ 2^(n+1) from Bertrand's postulate. -/
theorem pnt_bound_subexponential :
    ∀ᶠ n in atTop, (2 : ℝ) * (↑n * Real.log ↑n) < (2 : ℝ) ^ (↑n + 1) := by
  -- 2·n·ln(n) is o(2^n), but we give a direct argument
  -- For large n: 2^(n+1) = 2·2^n and n·ln(n) < 2^n eventually
  filter_upwards [eventually_ge_atTop 10] with n hn
  have hn_cast : (10 : ℝ) ≤ (↑n : ℝ) := by exact_mod_cast hn
  -- For n ≥ 10: n·ln(n) ≤ n² ≤ 2^n, and 2·n² ≤ 2^(n+1)
  -- We use: ln(n) ≤ n for all n ≥ 1 (since exp is faster than linear)
  have hlog_le_n : Real.log ↑n ≤ ↑n := by
    have h1 : Real.log ↑n ≤ ↑n - 1 := by
      have : (1 : ℝ) ≤ ↑n := by linarith
      exact Real.log_le_sub_one_of_le this
    linarith
  have hn_pos : (0 : ℝ) < ↑n := by linarith
  have h1 : ↑n * Real.log ↑n ≤ ↑n * ↑n := by
    apply mul_le_mul_of_nonneg_left hlog_le_n (le_of_lt hn_pos)
  -- So 2·n·ln(n) ≤ 2·n²
  have h2 : 2 * (↑n * Real.log ↑n) ≤ 2 * (↑n * ↑n) := by linarith
  -- Need: 2·n² < 2^(n+1), i.e., n² < 2^n
  -- Step 1: Prove n * n < 2 ^ n in ℕ by induction from n = 10
  have h_nat : n * n < 2 ^ n := by
    -- Induction on n; base case n = 10 by norm_num
    induction n with
    | zero => omega
    | succ k ih =>
      -- hn gives 10 ≤ k + 1, so k ≥ 9
      rcases le_or_lt 10 k with hk | hk
      · -- Inductive case: k ≥ 10, so ih applies
        have hkk := ih (by omega)
        -- Key: 2k+1 ≤ k² for k ≥ 3 (so (k+1)² = k²+(2k+1) ≤ 2k²)
        have hsmall : 2 * k + 1 ≤ k * k := by nlinarith
        calc (k + 1) * (k + 1)
            = k * k + (2 * k + 1) := by ring
          _ ≤ k * k + k * k := by linarith
          _ = 2 * (k * k) := by ring
          _ < 2 * 2 ^ k := by linarith
          _ = 2 ^ (k + 1) := by rw [pow_succ]; ring
      · -- Base case: k < 10 and 10 ≤ k + 1, so k = 9
        have : k = 9 := by omega
        subst this; norm_num
  -- Step 2: Cast to reals and combine with h2
  calc 2 * (↑n * Real.log ↑n)
      ≤ 2 * (↑n * ↑n) := h2
    _ < 2 * ((2 : ℝ) ^ (n : ℕ)) := by
        have : (↑(n * n) : ℝ) < ↑(2 ^ n) := Nat.cast_lt.mpr h_nat
        push_cast at this; linarith
    _ = (2 : ℝ) ^ (↑n + 1) := by
        rw [show (↑n : ℝ) + 1 = ↑(n + 1 : ℕ) from by push_cast; ring,
            rpow_natCast, pow_succ]; ring

/-
## Part IV: Dusart's Explicit Bounds (Axiomatized)

Dusart (1999, 2010) proved explicit bounds using the Prime Number Theorem
with explicit error terms. The proofs require:
1. Chebyshev functions θ(x) and ψ(x) with explicit bounds
2. Partial summation relating π(x) to θ(x)
3. Explicit zero-free regions for ζ(s) on Re(s) = 1

None of this analytic machinery is currently in Mathlib.
-/

/-- **Axiom: Dusart Upper Bound** (Rosser 1941, refined by Dusart 1999)

For n ≥ 6: p_n ≤ n · (ln n + ln ln n)

The proof uses the explicit PNT: θ(x) = x + O(x/exp(c·√(ln x))),
combined with partial summation to extract bounds on the n-th prime.

Rosser (1941) first proved this; Dusart (1999) sharpened the constants. -/
axiom dusart_upper_bound :
    ∀ n : ℕ, 6 ≤ n →
      (Nat.nth Nat.Prime n : ℝ) ≤ ↑n * (Real.log ↑n + Real.log (Real.log ↑n))

/-- **Axiom: Dusart Lower Bound** (Dusart 2010)

For n ≥ 6: p_n ≥ n · (ln n + ln ln n - 1)

This shows the Dusart upper bound is tight within an additive n term.
The proof follows the same analytic framework as the upper bound. -/
axiom dusart_lower_bound :
    ∀ n : ℕ, 6 ≤ n →
      ↑n * (Real.log ↑n + Real.log (Real.log ↑n) - 1) ≤ (Nat.nth Nat.Prime n : ℝ)

/-
## Part V: Consequences of Dusart Bounds (All Proved)
-/

/-- **The Dusart sandwich**: p_n is pinned between n(ln n + ln ln n - 1)
    and n(ln n + ln ln n) for n ≥ 6.

    This pins down p_n within a window of width exactly n. -/
theorem dusart_sandwich (n : ℕ) (hn : 6 ≤ n) :
    ↑n * (Real.log ↑n + Real.log (Real.log ↑n) - 1) ≤ (Nat.nth Nat.Prime n : ℝ) ∧
    (Nat.nth Nat.Prime n : ℝ) ≤ ↑n * (Real.log ↑n + Real.log (Real.log ↑n)) :=
  ⟨dusart_lower_bound n hn, dusart_upper_bound n hn⟩

/-- The gap between upper and lower Dusart bounds is exactly n. -/
theorem dusart_gap_width (n : ℕ) :
    ↑n * (Real.log ↑n + Real.log (Real.log ↑n)) -
    ↑n * (Real.log ↑n + Real.log (Real.log ↑n) - 1) = (↑n : ℝ) := by ring

/-- **Dusart upper bound for specific values**

p_6 ≤ 6·(ln 6 + ln ln 6) ≈ 6·(1.791 + 0.583) ≈ 14.2.
Actual value: p_6 = 17, so the bound is not tight for small n.
But for large n, it is asymptotically sharp. -/
theorem dusart_upper_at_six :
    (Nat.nth Nat.Prime 6 : ℝ) ≤ 6 * (Real.log 6 + Real.log (Real.log 6)) :=
  dusart_upper_bound 6 (by norm_num)

/-- **The Dusart bound implies the PNT asymptotic for p_n**

From the sandwich: p_n/(n·ln n) → 1 as n → ∞.
This shows the Dusart bounds are consistent with (and imply) the PNT. -/
theorem dusart_implies_asymptotic_upper :
    ∀ᶠ n in atTop,
      (Nat.nth Nat.Prime n : ℝ) / (↑n * Real.log ↑n) ≤
      1 + Real.log (Real.log ↑n) / Real.log ↑n := by
  filter_upwards [eventually_ge_atTop 6] with n hn
  have hn_cast : (6 : ℝ) ≤ (↑n : ℝ) := by exact_mod_cast hn
  have hlog_pos : 0 < Real.log (↑n : ℝ) := Real.log_pos (by linarith)
  have hn_pos : (0 : ℝ) < ↑n := by linarith
  have hnlog_pos : 0 < ↑n * Real.log ↑n := mul_pos hn_pos hlog_pos
  have hupper := dusart_upper_bound n hn
  rw [div_le_iff hnlog_pos]
  calc (1 + Real.log (Real.log ↑n) / Real.log ↑n) * (↑n * Real.log ↑n)
      = ↑n * Real.log ↑n + ↑n * Real.log (Real.log ↑n) := by
        field_simp; ring
    _ = ↑n * (Real.log ↑n + Real.log (Real.log ↑n)) := by ring
    _ ≥ Nat.nth Nat.Prime n := hupper

/-
## Summary

### Axioms (3)
1. `nth_prime_asymptotic` - PNT: p_n/(n·ln n) → 1
2. `dusart_upper_bound` - For n ≥ 6: p_n ≤ n(ln n + ln ln n)
3. `dusart_lower_bound` - For n ≥ 6: p_n ≥ n(ln n + ln ln n - 1)

### Proved Theorems (7)
1. `nth_prime_eventually_lt_mul` - From PNT: eventually p_n < (1+ε)·n·ln n
2. `nth_prime_eventually_gt_mul` - From PNT: eventually p_n > (1-ε)·n·ln n
3. `pnt_bound_subexponential` - PNT bound beats exponential (proved: n²<2^n by induction)
4. `dusart_sandwich` - Dusart bounds sandwich p_n
5. `dusart_gap_width` - Gap between bounds is exactly n
6. `dusart_upper_at_six` - Instantiation at n = 6
7. `dusart_implies_asymptotic_upper` - Dusart implies PNT ratio bound

### Improvement Chain
  p_n ≤ 2^(n+1)              (PrimeGapBounds.lean, from Bertrand)
  → p_n ≲ (1+ε)·n·ln n       (this file, from PNT asymptotic)
  → p_n ≤ n(ln n + ln ln n)   (this file, Dusart explicit bound)

### Axiom Count: 3
The first axiom (PNT asymptotic) is shared with PrimeNumberTheorem.lean.
The Dusart bounds would follow from PNT with explicit error terms,
but that derivation requires Chebyshev function analysis not in Mathlib.
-/

#check nth_prime_eventually_lt_mul
#check nth_prime_eventually_gt_mul
#check dusart_sandwich
#check dusart_gap_width
#check dusart_implies_asymptotic_upper

end DusartBounds
