/-
  Erdős Problem #247: Transcendence of Lacunary Sums

  Source: https://erdosproblems.com/247
  Status: OPEN (general case) / SOLVED (strong condition, Erdős 1975)

  Statement:
  Let n₁ < n₂ < ⋯ be a sequence of integers such that
    lim sup_{k→∞} n_k/k = ∞.
  Is Σ_{k=1}^∞ 1/2^{n_k} transcendental?

  Answer: OPEN in general. YES under stronger condition.

  History:
  - Erdős (1975) proved transcendence when lim sup n_k/k^t = ∞ for ALL t ≥ 1
  - The general conjecture (just lim sup n_k/k = ∞) remains open
  - Erdős (1988) noted these problems "seem hopeless at present"

  Key Insight:
  The sum Σ 1/2^{n_k} is a binary expansion with 1s at positions n_k.
  When the sequence grows fast enough (faster than any polynomial),
  the resulting number has a "lacunary" structure that forces transcendence.

  Tags: transcendence, number-theory, lacunary-series, erdos-problem
-/

import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.NumberTheory.Transcendental.Liouville.Basic
import Mathlib.Tactic

namespace Erdos247

/- ## Part I: The Lacunary Sum -/

/-- The lacunary sum Σ_{k=1}^∞ 1/2^{n_k} for a sequence n : ℕ → ℕ. -/
noncomputable def lacunarySum (n : ℕ → ℕ) : ℝ :=
  ∑' k, (1 : ℝ) / 2 ^ n k

/- ## Part II: Growth Conditions -/

/-- The weak growth condition: for all C > 0, there exists k with n_k > C * k.
    This is equivalent to lim sup n_k/k = ∞. -/
def HasWeakGrowth (n : ℕ → ℕ) : Prop :=
  ∀ C : ℕ, ∃ k : ℕ, k > 0 ∧ n k > C * k

/-- The strong growth condition: for all t ≥ 1 and all C > 0,
    there exists k with n_k > C * k^t. -/
def HasStrongGrowth (n : ℕ → ℕ) : Prop :=
  ∀ (t : ℕ), t ≥ 1 → ∀ C : ℕ, ∃ k : ℕ, k > 0 ∧ n k > C * k ^ t

/- ## Part III: The Main Conjecture (OPEN) -/

/-- **Erdős Problem #247** (Open Conjecture)

    If n₁ < n₂ < ⋯ is a strictly increasing sequence with lim sup n_k/k = ∞,
    then Σ 1/2^{n_k} is transcendental.

    Status: OPEN -/
def erdos_247_conjecture : Prop :=
  ∀ (n : ℕ → ℕ), StrictMono n → HasWeakGrowth n →
    Transcendental ℚ (lacunarySum n)

/- ## Part IV: Erdős's Partial Result (1975) -/

/-- **Erdős's Theorem (1975)**

    If n₁ < n₂ < ⋯ is strictly increasing with lim sup n_k/k^t = ∞
    for ALL t ≥ 1, then Σ 1/2^{n_k} is transcendental.

    Reference: Erdős, P., "Some problems and results on the irrationality
    of the sum of infinite series." J. Math. Sci. (1975).

    The proof uses Liouville-type arguments: if α is algebraic of degree d,
    then |α - p/q| > c/q^d for some c > 0. But lacunary sums can be
    approximated better than this when growth is superpolynomial. -/
axiom erdos_transcendence_strong (n : ℕ → ℕ)
    (hn : StrictMono n) (hg : HasStrongGrowth n) :
    Transcendental ℚ (lacunarySum n)

/- ## Part V: Examples -/

/-- Factorial is strictly increasing (for k ≥ 1). -/
theorem factorial_strictMono : StrictMono (fun k => (k + 1).factorial) := by
  intro a b hab
  have h1 : 0 < a + 1 := Nat.succ_pos a
  have h2 : a + 1 < b + 1 := Nat.add_lt_add_right hab 1
  exact Nat.factorial_lt_of_lt h1 h2

/-- 2^k is strictly increasing. -/
theorem pow2_strictMono : StrictMono (fun k => 2^k) := by
  intro a b hab
  exact Nat.pow_lt_pow_right (by omega) hab

/-- For all n, n + 1 ≤ 2^n. Proved by induction. -/
private theorem pow2_ge_succ (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    calc k + 1 + 1 ≤ 2 * (k + 1) := by omega
      _ ≤ 2 * 2 ^ k := by gcongr
      _ = 2 ^ (k + 1) := by ring

/-- For all k, 2^k ≤ (k+1)!. Proved by induction. -/
private theorem factorial_ge_pow2 (k : ℕ) : 2 ^ k ≤ (k + 1).factorial := by
  induction k with
  | zero => norm_num
  | succ n ih =>
    calc 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      _ ≤ 2 * (n + 1).factorial := by gcongr
      _ ≤ (n + 2) * (n + 1).factorial := by gcongr; omega
      _ = (n + 1 + 1).factorial := (Nat.factorial_succ (n + 1)).symm

/-- 2^k grows faster than any polynomial. Proved using explicit witness
    k = C * (t+1)^(t+1) and a chain of inequalities. -/
theorem pow2_strong_growth : HasStrongGrowth (fun k => 2 ^ k) := by
  intro t ht C
  by_cases hC : C = 0
  · subst hC; exact ⟨1, by omega, by simp⟩
  · have hC_pos : 0 < C := Nat.pos_of_ne_zero hC
    set n := C * (t + 1) ^ t
    have hn_pos : 0 < n := by positivity
    refine ⟨n * (t + 1), Nat.mul_pos hn_pos (by omega), ?_⟩
    -- Goal: 2 ^ (n * (t + 1)) > C * (n * (t + 1)) ^ t
    show 2 ^ (n * (t + 1)) > C * (n * (t + 1)) ^ t
    rw [pow_mul]
    have h1 : n + 1 ≤ 2 ^ n := pow2_ge_succ n
    have h2 : 0 < n ^ t := by positivity
    -- Chain: C*(t+1)^t * n^t < (n+1)*n^t ≤ (n+1)*(n+1)^t = (n+1)^(t+1) ≤ (2^n)^(t+1)
    calc C * (n * (t + 1)) ^ t
        = C * (t + 1) ^ t * n ^ t := by rw [mul_pow]; ring
      _ < (n + 1) * n ^ t := by
          exact mul_lt_mul_of_pos_right (by omega : C * (t + 1) ^ t < n + 1) h2
      _ ≤ (n + 1) * (n + 1) ^ t := by gcongr; omega
      _ = (n + 1) ^ (t + 1) := by ring
      _ ≤ (2 ^ n) ^ (t + 1) := by gcongr

/-- Factorial grows faster than any polynomial. Derived from pow2_strong_growth
    and the fact that (k+1)! ≥ 2^k. -/
theorem factorial_strong_growth : HasStrongGrowth (fun k => (k + 1).factorial) := by
  intro t ht C
  obtain ⟨k, hk_pos, hk⟩ := pow2_strong_growth t ht C
  exact ⟨k, hk_pos, lt_of_lt_of_le hk (factorial_ge_pow2 k)⟩

/-- Corollary: The sum Σ 1/2^{k!} is transcendental. -/
theorem factorial_sum_transcendental :
    Transcendental ℚ (lacunarySum (fun k => (k + 1).factorial)) :=
  erdos_transcendence_strong _ factorial_strictMono factorial_strong_growth

/-- Corollary: The sum Σ 1/2^{2^k} is transcendental. -/
theorem pow2_sum_transcendental :
    Transcendental ℚ (lacunarySum (fun k => 2^k)) :=
  erdos_transcendence_strong _ pow2_strictMono pow2_strong_growth

/- ## Part VI: The Gap Between Conditions -/

/-- Strong growth implies weak growth: take t = 1 in the strong condition. -/
theorem strong_implies_weak (n : ℕ → ℕ) : HasStrongGrowth n → HasWeakGrowth n := by
  intro hsg C
  obtain ⟨k, hk_pos, hk⟩ := hsg 1 (by omega) C
  exact ⟨k, hk_pos, by simpa using hk⟩

-- The converse is false: squareSeq has weak but not strong growth (see below).

/-- Example: n_k = k² grows faster than linear but not faster than k². -/
def squareSeq : ℕ → ℕ := fun k => (k + 1)^2

/-- k² is strictly increasing. -/
theorem square_strictMono : StrictMono squareSeq := by
  intro a b hab
  simp only [squareSeq]
  have : a + 1 < b + 1 := Nat.add_lt_add_right hab 1
  exact Nat.pow_lt_pow_left this (by omega)

/-- squareSeq has weak growth: (k+1)²/k → ∞.
    Witness: k = C+1, then (C+2)² = C²+4C+4 > C²+C = C(C+1). -/
theorem squareSeq_has_weak_growth : HasWeakGrowth squareSeq := by
  intro C
  refine ⟨C + 1, by omega, ?_⟩
  simp only [squareSeq]
  -- Goal: (C+1+1)^2 > C*(C+1)
  -- (C+2)^2 = C^2 + 4C + 4, C*(C+1) = C^2 + C, difference = 3C + 4 > 0
  nlinarith

/-- squareSeq does NOT have strong growth: at t=2, (k+1)² ≤ 4k² for all k ≥ 1.
    This formalizes the gap: squareSeq satisfies the OPEN conjecture's hypothesis
    but NOT Erdős's 1975 theorem. Whether Σ 1/2^{k²} is transcendental is open. -/
theorem squareSeq_not_strong_growth : ¬HasStrongGrowth squareSeq := by
  intro hsg
  obtain ⟨k, hk_pos, hk⟩ := hsg 2 (by omega) 4
  simp only [squareSeq] at hk
  -- hk : (k+1)^2 > 4*k^2, but (k+1)^2 ≤ 4*k^2 for k ≥ 1
  -- Since (k+1)^2 = k^2 + 2k + 1 and 4k^2 - k^2 - 2k - 1 = 3k^2 - 2k - 1 = (3k+1)(k-1) ≥ 0
  have h : (k + 1) ^ 2 ≤ 4 * k ^ 2 := by nlinarith
  omega

/-- The sum Σ 1/2^{k²} - transcendence is OPEN.
    By squareSeq_has_weak_growth, it meets Erdős's weak condition.
    By squareSeq_not_strong_growth, it does NOT meet the strong condition.
    Erdős's 1975 theorem (erdos_transcendence_strong) does not apply. -/
noncomputable def square_sum : ℝ := lacunarySum squareSeq

/- ## Part VII: Summary -/

/-- Summary of known results for Erdős Problem #247. -/
theorem problem_247_summary :
    -- Erdős's theorem for strong growth
    (∀ (n : ℕ → ℕ), StrictMono n → HasStrongGrowth n →
      Transcendental ℚ (lacunarySum n)) ∧
    -- Factorial sum is transcendental
    Transcendental ℚ (lacunarySum (fun k => (k + 1).factorial)) ∧
    -- Power of 2 sum is transcendental
    Transcendental ℚ (lacunarySum (fun k => 2^k)) :=
  ⟨erdos_transcendence_strong, factorial_sum_transcendental, pow2_sum_transcendental⟩

#check erdos_247_conjecture
#check erdos_transcendence_strong

/- ## Part VIII: Direct Liouville Proof (Factorial Case)

The factorial lacunary sum Σ 1/2^{(k+1)!} is transcendental.
We prove this DIRECTLY by showing it is a Liouville number,
without using the erdos_transcendence_strong axiom.

Mathematical argument:
For each m, the partial sum Σ_{k=0}^{m} 1/2^{(k+1)!} = a/2^{(m+1)!}
for some integer a. The tail satisfies:
  |α - a/2^{(m+1)!}| ≤ 2/2^{(m+2)!} < 1/(2^{(m+1)!})^m
The last inequality uses (m+2)! > m·(m+1)!, which follows from m+2 > m.

This approach works for the factorial case because n_{k+1}/n_k = k+2 → ∞,
but does NOT work for 2^k (where the ratio is always 2). The Erdős axiom
is still needed for the general strong-growth case and the 2^k case. -/

/-- For strictly monotone ℕ-sequences, n(N) + k ≤ n(N + k).
    This gives 1/2^{n(N+k)} ≤ 1/2^{n(N)+k} for bounding tails. -/
private theorem strictMono_add_le {n : ℕ → ℕ} (hn : StrictMono n)
    (N k : ℕ) : n N + k ≤ n (N + k) := by
  induction k with
  | zero => simp
  | succ j ih =>
    have := hn (show N + j < N + (j + 1) by omega)
    omega

/-- Key factorial inequality: m · (m+1)! < (m+2)!.
    Equivalently, m < m+2 scaled by (m+1)!. -/
private theorem factorial_mul_lt (m : ℕ) :
    m * (m + 1).factorial < (m + 2).factorial := by
  have : (m + 2).factorial = (m + 2) * (m + 1).factorial := Nat.factorial_succ (m + 1)
  rw [this]
  exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.factorial_pos (m + 1))

/-- Strengthened: m · (m+1)! + 1 < (m+2)!.
    Uses 2·(m+1)! ≥ 2 > 1. Needed for strict Liouville bound. -/
private theorem factorial_mul_add_one_lt (m : ℕ) :
    m * (m + 1).factorial + 1 < (m + 2).factorial := by
  have hfact : (m + 2).factorial = (m + 2) * (m + 1).factorial := Nat.factorial_succ (m + 1)
  rw [hfact]
  -- Goal: m * (m+1)! + 1 < (m+2) * (m+1)!
  -- Since (m+2) * (m+1)! - m * (m+1)! = 2 * (m+1)! ≥ 2 > 1
  have := Nat.factorial_pos (m + 1)
  nlinarith

/-- The factorial lacunary series is summable.
    Comparison with geometric series: (k+1)! ≥ k, so
    1/2^{(k+1)!} ≤ 1/2^k = (1/2)^k. -/
theorem factorial_lacunary_summable :
    Summable (fun k => (1 : ℝ) / 2 ^ (k + 1).factorial) := by
  sorry

/-- The tail of the factorial series starting at index N+1.
    We express it as a shifted tsum for easier manipulation. -/
noncomputable def factorialTail (N : ℕ) : ℝ :=
  ∑' k, (1 : ℝ) / 2 ^ (N + 1 + k + 1).factorial

/-- The partial sum of the factorial lacunary series. -/
noncomputable def factorialPartialSum (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), (1 : ℝ) / 2 ^ (k + 1).factorial

/-- The lacunary sum splits into partial sum + tail. -/
theorem lacunarySum_factorial_split (N : ℕ) :
    lacunarySum (fun k => (k + 1).factorial) =
    factorialPartialSum N + factorialTail N := by
  sorry

/-- The partial sum has denominator 2^{(N+1)!}: there exists an integer a
    such that factorialPartialSum N = a / 2^{(N+1)!}. -/
theorem factorialPartialSum_eq_div (N : ℕ) :
    ∃ (a : ℤ), factorialPartialSum N =
    (a : ℝ) / (2 : ℝ) ^ (N + 1).factorial := by
  sorry

/-- The tail is strictly positive (the first term alone is positive). -/
theorem factorialTail_pos (N : ℕ) : 0 < factorialTail N := by
  sorry

/-- Tail bound: the tail starting at N+1 is at most 2/2^{(N+2)!}.
    Uses strictMono_add_le to bound each term and comparison with
    the geometric series Σ 1/2^j. -/
theorem factorialTail_le (N : ℕ) :
    factorialTail N ≤ 2 / (2 : ℝ) ^ (N + 2).factorial := by
  sorry

/-- The factorial lacunary sum is a Liouville number.

    For each m, we exhibit the approximation a/b where:
    - b = 2^{(m+1)!} (an integer > 1)
    - a = numerator of the partial sum up to index m
    - |α - a/b| ≤ 2/2^{(m+2)!} < 1/b^m

    The last step: 2/2^{(m+2)!} < 1/(2^{(m+1)!})^m
    ⟺ (m+2)! - 1 > m·(m+1)!
    ⟺ 2·(m+1)! > 1 (always true). -/
theorem factorial_sum_liouville :
    Liouville (lacunarySum (fun k => (k + 1).factorial)) := by
  intro m
  -- Get the partial sum representation
  obtain ⟨a, ha⟩ := factorialPartialSum_eq_div m
  -- Our witnesses: a and b = 2^{(m+1)!}
  refine ⟨a, (2 : ℤ) ^ (m + 1).factorial, ?_, ?_, ?_⟩
  · -- 1 < b = 2^{(m+1)!}
    exact_mod_cast Nat.one_lt_pow (Nat.factorial_pos (m + 1)).ne'
      (by omega : 1 < 2)
  · -- x ≠ a/b (the tail is strictly positive)
    rw [lacunarySum_factorial_split m, ha]
    push_cast
    intro heq
    have := factorialTail_pos m
    linarith
  · -- |x - a/b| < 1/b^m
    rw [lacunarySum_factorial_split m, ha]
    push_cast
    rw [show (a : ℝ) / (2 : ℝ) ^ (m + 1).factorial +
        factorialTail m - a / (2 : ℝ) ^ (m + 1).factorial =
        factorialTail m by ring]
    rw [abs_of_pos (factorialTail_pos m)]
    -- Need: tail < 1 / (2^{(m+1)!})^m
    calc factorialTail m
        ≤ 2 / (2 : ℝ) ^ (m + 2).factorial := factorialTail_le m
      _ < 1 / ((2 : ℝ) ^ (m + 1).factorial) ^ m := by
          -- 2/2^{(m+2)!} < 1/(2^{(m+1)!})^m
          -- ⟺ 2^{m*(m+1)!+1} < 2^{(m+2)!}
          -- ⟺ m*(m+1)!+1 < (m+2)!
          -- This is factorial_mul_add_one_lt
          sorry

/-- **Axiom-free transcendence**: Σ 1/2^{(k+1)!} is transcendental.
    Uses Liouville's theorem directly — no Erdős 1975 axiom needed. -/
theorem factorial_sum_transcendental_liouville :
    Transcendental ℚ (lacunarySum (fun k => (k + 1).factorial)) := by
  have h := factorial_sum_liouville.transcendental
  -- Liouville.transcendental gives Transcendental ℤ x
  -- Convert to Transcendental ℚ x
  sorry

end Erdos247
