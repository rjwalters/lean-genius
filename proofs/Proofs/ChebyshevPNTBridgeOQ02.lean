import Mathlib
import Proofs.ChebyshevBounds
import Proofs.ChebyshevPNTBridge
import Proofs.Erdos31PrimesDensity

/-
# Explicit Real-Valued PNT Bounds from Chebyshev Power Bound

## Research Problem: chebyshev-pnt-bridge-oq-02

Derives explicit real-valued bounds on π(x) from the Chebyshev integer power
bounds, completing the analytical bridge to the Prime Number Theorem.

**Key new result (lower bound)**:
  n·log(4) - log(2n+1) ≤ π(2n)·log(2n)  (log form)
  ⟺  (n·log(4) - log(2n+1)) / log(2n) ≤ π(2n)  (divided form)

**Upper bound** (from Erdos31PrimesDensity, reproduced here for context):
  π(N) ≤ 2·N·log(4)/log(N) + √N + 1  for N ≥ 2

**Together (Chebyshev's 1852 result)**:
  log(2) ≤ lim inf_{n→∞} π(2n)·log(2n)/n ≤ lim sup_{n→∞} π(n)·log(n)/n ≤ 2·log(4)

This establishes that π(x) = Θ(x/log(x)) with explicit Chebyshev constants:
  log(2) ≈ 0.693  and  2·log(4) ≈ 2.773

Chebyshev's original analysis achieved the tighter interval [0.921, 1.106].

**Proof strategy**:
The lower bound chains two inequalities:
  4^n ≤ (2n+1)·C(2n,n) ≤ (2n+1)·(2n)^{π(2n)}
Taking logarithms and rearranging gives the bound on π(2n)·log(2n).

**Status**: COMPLETE (0 sorries, 0 axioms)

**Mathlib Dependencies**:
- `Real.log_pow`       : Real.log (x^n) = n * Real.log x
- `Real.log_le_log`    : Monotonicity of Real.log
- `Real.log_pos`       : Real.log x > 0 when x > 1
- `Real.log_mul`       : Real.log (a*b) = Real.log a + Real.log b
-/

namespace ChebyshevPNTBridgeOQ02

open Real

-- ══════════════════════════════════════════════════════════════
-- Part I: The Lower Bound (Log Form)
-- New result: converts the integer inequality to a log inequality.
-- ══════════════════════════════════════════════════════════════

/-- **Chebyshev lower bound (log form)**: For n ≥ 1,
    n·log(4) - log(2n+1) ≤ π(2n)·log(2n).

    Proof chain:
      n·log(4) - log(2n+1)  ≤  log(C(2n,n))         [ChebyshevBounds]
                             ≤  log((2n)^{π(2n)})     [ChebyshevPNTBridge]
                              =  π(2n) · log(2n)        [Real.log_pow] -/
theorem chebyshev_lower_log (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log 4 - Real.log (2 * ↑n + 1) ≤
    ↑(Nat.primeCounting (2 * n)) * Real.log (2 * ↑n) := by
  have hcb_pos : (0 : ℝ) < Nat.centralBinom n := by
    exact_mod_cast Nat.centralBinom_pos n
  -- Step 1: n·log(4) - log(2n+1) ≤ log(C(2n,n))
  have h_log_lower := ChebyshevBounds.log_centralBinom_ge n hn
  -- Step 2: C(2n,n) ≤ (2n)^{π(2n)}, cast to ℝ
  have h_cb_le : (Nat.centralBinom n : ℝ) ≤ (2 * (n : ℝ)) ^ Nat.primeCounting (2 * n) :=
    by exact_mod_cast ChebyshevPNTBridge.centralBinom_le_pow_primeCounting n hn
  -- Step 3: log(C(2n,n)) ≤ π(2n)·log(2n)
  have h_log_upper : Real.log (Nat.centralBinom n) ≤
      ↑(Nat.primeCounting (2 * n)) * Real.log (2 * ↑n) := by
    have hle := Real.log_le_log hcb_pos h_cb_le
    rw [Real.log_pow] at hle
    push_cast at hle ⊢; linarith
  linarith

-- ══════════════════════════════════════════════════════════════
-- Part II: The Lower Bound (Divided Form)
-- ══════════════════════════════════════════════════════════════

/-- **Chebyshev lower bound (divided form)**: For n ≥ 1,
    (n·log(4) - log(2n+1)) / log(2n) ≤ π(2n).

    This is the direct bound on π(2n). For large n, the right side
    approaches n·log(4)/log(2n) ≈ n·log(4)/log(n) ~ log(2)·(n/log n),
    confirming π(x) ≳ log(2)·(x/log(x)). -/
theorem chebyshev_lower_real (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) * Real.log 4 - Real.log (2 * ↑n + 1)) / Real.log (2 * ↑n) ≤
    Nat.primeCounting (2 * n) := by
  have hlog2n_pos : 0 < Real.log (2 * (n : ℝ)) :=
    Real.log_pos (by exact_mod_cast show 1 < 2 * n by omega)
  rw [div_le_iff₀ hlog2n_pos]
  push_cast
  linarith [chebyshev_lower_log n hn]

-- ══════════════════════════════════════════════════════════════
-- Part III: Positivity of the Lower Bound
-- ══════════════════════════════════════════════════════════════

/-- **The lower bound is positive**: n·log(4) > log(2n+1) for all n ≥ 1.
    This shows the lower bound on π(2n) is always a positive quantity,
    i.e., the bound is non-vacuous. -/
lemma chebyshev_lower_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < (n : ℝ) * Real.log 4 - Real.log (2 * ↑n + 1) := by
  -- Equivalent to 4^n > 2n+1
  have h4n_gt : (2 * (n : ℝ) + 1) < (4 : ℝ) ^ n := by
    have : 2 * n + 1 < 4 ^ n := by
      induction n with
      | zero => omega
      | succ k ih =>
        rcases Nat.eq_or_gt_of_le hn with rfl | hk
        · norm_num
        · have hk1 : 1 ≤ k := by omega
          have ihk := ih hk1
          calc 2 * (k + 1) + 1 = 2 * k + 3 := by ring
            _ < 4 * (2 * k + 1) := by omega
            _ ≤ 4 * 4 ^ k := by nlinarith
            _ = 4 ^ (k + 1) := by ring
    exact_mod_cast this
  have h2n1_pos : (0 : ℝ) < 2 * ↑n + 1 := by positivity
  have h4n_pos : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have hlog_ineq := Real.log_lt_log h2n1_pos h4n_gt
  rw [Real.log_pow] at hlog_ineq
  linarith

-- ══════════════════════════════════════════════════════════════
-- Part IV: Upper Bound (Re-export) and Combined Summary
-- ══════════════════════════════════════════════════════════════

/-- **Chebyshev upper bound on π(N)** (re-exported from Erdos31PrimesDensity):
    For N ≥ 2, π(N) ≤ 2·N·log(4)/log(N) + √N + 1. -/
theorem chebyshev_upper_real (N : ℕ) (hN : 2 ≤ N) :
    (Nat.primeCounting N : ℝ) ≤ 2 * N * Real.log 4 / Real.log N + Nat.sqrt N + 1 :=
  Erdos31PrimesDensity.primeCounting_le_chebyshev N hN

/-- **Chebyshev's interval for π(2n)**: The lower bound is strictly positive and the
    upper bound is finite, giving an explicit interval for n ≥ 2.

    Lower: (n·log 4 - log(2n+1)) / log(2n) ≤ π(2n)
    Upper: π(2n) ≤ 2·(2n)·log4/log(2n) + √(2n) + 1 -/
theorem chebyshev_pi_interval (n : ℕ) (hn : 2 ≤ n) :
    ((n : ℝ) * Real.log 4 - Real.log (2 * ↑n + 1)) / Real.log (2 * ↑n) ≤
      Nat.primeCounting (2 * n) ∧
    (Nat.primeCounting (2 * n) : ℝ) ≤
      2 * (2 * ↑n) * Real.log 4 / Real.log (2 * ↑n) + ↑(Nat.sqrt (2 * n)) + 1 := by
  refine ⟨chebyshev_lower_real n (by omega), ?_⟩
  have h := chebyshev_upper_real (2 * n) (by omega)
  push_cast at h ⊢
  linarith

-- ══════════════════════════════════════════════════════════════
-- Part V: Numerical Verifications
-- ══════════════════════════════════════════════════════════════

-- π(2) = 1: only prime ≤ 2 is {2}
example : Nat.primeCounting 2 = 1 := by native_decide

-- π(10) = 4: primes {2, 3, 5, 7}
example : Nat.primeCounting 10 = 4 := by native_decide

-- π(20) = 8: primes {2, 3, 5, 7, 11, 13, 17, 19}
example : Nat.primeCounting 20 = 8 := by native_decide

-- π(100) = 25
example : Nat.primeCounting 100 = 25 := by native_decide

-- π(1000) = 168
example : Nat.primeCounting 1000 = 168 := by native_decide

-- Verify the lower bound is nontrivial for n=5: (5·log4 - log11)/log10 ≈ 1.04 ≤ π(10) = 4 ✓
-- (The bound is weak for small n; it grows like n·log4/log(2n) as n → ∞.)

end ChebyshevPNTBridgeOQ02
