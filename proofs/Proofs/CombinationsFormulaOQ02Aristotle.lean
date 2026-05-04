/-
  Aristotle targets for CombinationsFormulaOQ02 (Catalan Numbers)
  Routine supporting lemmas for automated proof search.
  See CombinationsFormulaOQ02.lean for the main formalization.

  Targets (in order of difficulty):
  1. catalan_pos: C_n > 0 for n ≤ 4 (by norm_num via definitions)
  2. centralBinom_ge_two_pow: C(2n, n) ≥ 2^n for n ≥ 1 (induction)
     - Inductive step: C(2m+2, m+1) ≥ 2 * C(2m, m) via Pascal identity
  3. catalan_mul_succ: C_n * (n+1) = C(2n, n) (fundamental identity)
  4. choose_2n_succ_divides: (n+1) | C(2n, n) * n (divisibility)

  Not targeted (too hard / require WZ-theory or Vandermonde):
  - catalan_convolution: requires Vandermonde identity
  - catalan_mono: requires catalan_mul_succ first
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

open Nat Finset BigOperators

namespace CatalanNumbers

def catalan (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n - Nat.choose (2 * n) (n + 1)

abbrev centralBinom (n : ℕ) : ℕ := Nat.choose (2 * n) n

/-- C_n > 0 for all n (verified for n ≤ 5 by computation, general case via catalan_mul_succ). -/
theorem catalan_pos_small (n : ℕ) (hn : n ≤ 5) : 0 < catalan n := by
  interval_cases n <;> decide

/-- C(2n, n) ≥ 2^n for n ≥ 1.
    Proof: Pascal gives C(2n+2,n+1) = C(2n,n) + 2*C(2n,n+1) ≥ 2*C(2n,n). -/
theorem centralBinom_ge_two_pow (n : ℕ) (hn : 1 ≤ n) : 2 ^ n ≤ centralBinom n := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · -- m = 0: C(2,1) = 2 ≥ 2^1 = 2
      simp [centralBinom, Nat.choose]
    · -- m ≥ 1: C(2m+2, m+1) = C(2m,m) + 2*C(2m,m+1) ≥ 2*C(2m,m) ≥ 2^(m+1)
      have ihm := ih hm
      -- C(2m+2, m+1) = C(2m+1, m) + C(2m+1, m+1) via Pascal
      -- = (C(2m,m)+C(2m,m-1)) + (C(2m,m)+C(2m,m+1))... complex
      -- Use C(2(m+1), m+1) ≥ 2*C(2m, m) via the two-step bound
      simp only [centralBinom, show 2 * (m + 1) = 2 * m + 2 from by ring]
      rw [show m + 1 + 1 = m + 1 + 1 from rfl]  -- tautology, real proof below
      -- C(2m+2, m+1) = C(2m+1,m+1) + C(2m+1,m) by Pascal
      -- C(2m+1, m+1) = C(2m, m+1) + C(2m, m) by Pascal
      -- C(2m+1, m) = C(2m, m-1) + C(2m, m) by Pascal (for m ≥ 1)
      -- So C(2m+2, m+1) = 2*C(2m, m) + C(2m, m+1) + C(2m, m-1) ≥ 2*C(2m, m)
      have h1 : Nat.choose (2*m+2) (m+1) ≥ 2 * Nat.choose (2*m) m := by
        have := @Nat.choose_succ_succ (2*m+1) m
        have := @Nat.choose_succ_succ (2*m) m
        have := @Nat.choose_succ_succ (2*m) (m-1)
        omega
      linarith [pow_pos (by norm_num : 0 < 2) m]

/-- The divisibility fact: (n+1) divides C(2n, n).
    Proof by induction using choose_2n_succ + coprimality. -/
theorem succ_dvd_centralBinom (n : ℕ) : (n + 1) ∣ centralBinom n := by
  simp only [centralBinom]
  induction n with
  | zero => simp
  | succ m ih =>
    simp only [show 2 * (m + 1) = 2 * m + 2 from by ring]
    -- choose_2n_succ gives C(2m+2,m+2)*(m+2) = C(2m+2,m+1)*(m+1)
    have hstep : Nat.choose (2 * m + 2) (m + 2) * (m + 2) =
                 Nat.choose (2 * m + 2) (m + 1) * (m + 1) := by
      have := choose_2n_succ (m + 1)
      simp only [show 2 * (m + 1) = 2 * m + 2 from by ring,
                 show m + 1 + 1 = m + 2 from by ring] at this
      exact this
    -- (m+2) | C(2m+2,m+1)*(m+1) [via C(2m+2,m+2)*(m+2)]
    have hdvd : (m + 2) ∣ Nat.choose (2 * m + 2) (m + 1) * (m + 1) :=
      ⟨Nat.choose (2 * m + 2) (m + 2), by linarith⟩
    -- gcd(m+2, m+1)=1 → (m+2) | C(2m+2,m+1)
    have hcop : Nat.Coprime (m + 2) (m + 1) := by
      rw [Nat.coprime_comm]; exact Nat.coprime_succ_self (m + 1)
    exact hcop.dvd_of_dvd_mul_right hdvd

/-- **Fundamental Catalan identity**: C_n * (n+1) = C(2n, n). -/
theorem catalan_mul_succ (n : ℕ) :
    catalan n * (n + 1) = centralBinom n := by
  sorry

/-- C(2n, n+1) * (n+1) = C(2n, n) * n (divisibility relationship). -/
theorem choose_2n_succ (n : ℕ) :
    Nat.choose (2 * n) (n + 1) * (n + 1) = Nat.choose (2 * n) n * n := by
  -- From Nat.choose_succ_right_eq: C(N, k+1) * (k+1) = (N-k) * C(N, k)
  -- Apply with N=2n, k=n: C(2n,n+1)*(n+1) = (2n-n)*C(2n,n) = n*C(2n,n)
  have h := Nat.choose_succ_right_eq (2 * n) n
  simp only [show 2 * n - n = n from by omega] at h
  linarith [mul_comm (Nat.choose (2 * n) n) n]

end CatalanNumbers
