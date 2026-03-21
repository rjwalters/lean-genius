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
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.NumberTheory.Transcendental.Liouville.Basic
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.Tactic
import Proofs.LiouvilleTheorem

set_option maxHeartbeats 800000

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

/- ## Part VIII: Axiom-Free Factorial Transcendence via Liouville Numbers

The key observation: lacunarySum (fun k => (k+1)!) = liouvilleNumber 2 - 1/2.
Since liouvilleNumber 2 is transcendental (proved in LiouvilleTheorem.lean via
Mathlib's Liouville theory), and subtracting a rational preserves transcendence,
the factorial lacunary sum is transcendental WITHOUT the erdos_transcendence_strong axiom.
-/

/- ### Infrastructure: Summability and Splitting -/

/-- The factorial lacunary series is summable. -/
private theorem factorial_lacunary_summable :
    Summable (fun k => (1 : ℝ) / 2 ^ (k + 1).factorial) := by
  apply Summable.of_nonneg_of_le
  · intro k; positivity
  · intro k
    show (1 : ℝ) / 2 ^ (k + 1).factorial ≤ (1 / 2) ^ k
    rw [one_div, one_div, inv_pow]
    apply inv_anti₀ (by positivity : (0 : ℝ) < 2 ^ k)
    exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2)
      (le_trans (Nat.le_succ k) (Nat.self_le_factorial (k + 1)))
  · exact summable_geometric_of_lt_one (by positivity) (by norm_num)

/-- The base-2 Liouville series is summable. -/
private theorem liouville_summable :
    Summable (fun n : ℕ => (1 : ℝ) / 2 ^ n.factorial) := by
  apply Summable.of_nonneg_of_le
  · intro n; positivity
  · intro n
    show (1 : ℝ) / 2 ^ n.factorial ≤ (1 / 2) ^ n
    rw [one_div, one_div, inv_pow]
    apply inv_anti₀ (by positivity : (0 : ℝ) < 2 ^ n)
    exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) (Nat.self_le_factorial n)
  · exact summable_geometric_of_lt_one (by positivity) (by norm_num)

/-- The tail of the factorial lacunary sum starting at position N+1. -/
noncomputable def factorialTail (N : ℕ) : ℝ :=
  ∑' k, (1 : ℝ) / 2 ^ (N + 1 + k + 1).factorial

/-- The shifted factorial series (tail starting at index N+1) is summable. -/
private theorem factorial_tail_summable (N : ℕ) :
    Summable (fun k => (1 : ℝ) / 2 ^ (N + 1 + k + 1).factorial) := by
  apply Summable.of_nonneg_of_le
  · intro k; positivity
  · intro k
    show (1 : ℝ) / 2 ^ (N + 1 + k + 1).factorial ≤ (1 / 2) ^ k
    rw [one_div, one_div, inv_pow]
    apply inv_anti₀ (by positivity : (0 : ℝ) < 2 ^ k)
    have hk_le : k ≤ (N + 1 + k + 1).factorial := by
      calc k ≤ N + 1 + k + 1 := by omega
        _ ≤ (N + 1 + k + 1).factorial := Nat.self_le_factorial _
    exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) hk_le
  · exact summable_geometric_of_lt_one (by positivity) (by norm_num)

/-- The factorial lacunary sum splits into partial sum + tail. -/
theorem lacunarySum_factorial_split (N : ℕ) :
    lacunarySum (fun k => (k + 1).factorial) =
    (∑ k ∈ Finset.range (N + 1), (1 : ℝ) / 2 ^ (k + 1).factorial) +
    factorialTail N := by
  unfold lacunarySum factorialTail
  -- Prove by induction: split tsum at index N+1
  induction N with
  | zero =>
    rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [factorial_lacunary_summable.tsum_eq_zero_add]
    congr 1
    apply tsum_congr; intro k; congr 1; congr 1; congr 1; omega
  | succ n ih =>
    rw [ih]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [add_assoc]
    congr 1
    -- tail_n = f(n+1) + tail_{n+1}, use tsum_eq_zero_add
    have h := (factorial_tail_summable n).tsum_eq_zero_add
    -- Normalize arithmetic in h to match goal
    simp only [show n + 1 + 0 + 1 = n + 1 + 1 from by omega] at h
    rw [h]
    congr 1
    apply tsum_congr; intro k
    simp only [show n + 1 + (k + 1) + 1 = n + 1 + 1 + k + 1 from by omega]

/-- The partial sum can be expressed as an integer divided by 2^{(N+1)!}. -/
theorem factorialPartialSum_eq_div (N : ℕ) :
    ∃ (a : ℤ),
    (∑ k ∈ Finset.range (N + 1), (1 : ℝ) / 2 ^ (k + 1).factorial) =
    (a : ℝ) / (2 : ℝ) ^ (N + 1).factorial := by
  induction N with
  | zero =>
    exact ⟨1, by simp [Finset.sum_range_succ, Finset.sum_range_zero]⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := ih
    -- partial_{n+1} = a/2^{(n+1)!} + 1/2^{(n+2)!}
    -- = (a * 2^{(n+2)!-(n+1)!} + 1) / 2^{(n+2)!}
    have hle : (n + 1).factorial ≤ (n + 2).factorial :=
      Nat.factorial_le (by omega)
    set d := (n + 2).factorial - (n + 1).factorial with hd_def
    refine ⟨a * (2 : ℤ) ^ d + 1, ?_⟩
    rw [Finset.sum_range_succ, ha]
    have h2pos : (2 : ℝ) ^ (n + 1).factorial ≠ 0 := by positivity
    have h2pos' : (2 : ℝ) ^ (n + 1 + 1).factorial ≠ 0 := by positivity
    have hpow : (2 : ℝ) ^ (n + 1 + 1).factorial =
        (2 : ℝ) ^ (n + 1).factorial * (2 : ℝ) ^ d := by
      rw [show (n + 1 + 1).factorial = (n + 1).factorial + d from
        (Nat.add_sub_cancel' hle).symm]
      exact pow_add 2 (n + 1).factorial d
    rw [hpow]
    push_cast
    field_simp

/- ### Path A: Via Liouville Number Connection -/

/-- Transcendence over ℤ implies transcendence over ℚ.
    Contrapositive: IsAlgebraic ℚ x → IsAlgebraic ℤ x (clearing denominators).
    Given p ∈ ℚ[X] with p(x) = 0, multiply by the product of all coefficient
    denominators to get q ∈ ℤ[X] with q(x) = 0. -/
theorem transcendental_int_to_rat {x : ℝ} (h : Transcendental ℤ x) :
    Transcendental ℚ x :=
  fun halg => h ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr halg)

/-- Subtracting a rational from a transcendental number gives a transcendental number. -/
theorem Transcendental.sub_rat {x : ℝ} (hx : Transcendental ℚ x) (r : ℚ) :
    Transcendental ℚ (x - (r : ℝ)) := by
  intro halg
  apply hx
  have hr : IsAlgebraic ℚ ((r : ℝ)) := isAlgebraic_algebraMap r
  have hsum := halg.add hr
  rwa [sub_add_cancel] at hsum

/-- The factorial lacunary sum equals the Liouville number minus 1/2.
    liouvilleNumber 2 = Σ_{n≥0} 1/2^{n!} = 1/2^{0!} + Σ_{k≥0} 1/2^{(k+1)!}
    = 1/2 + lacunarySum (fun k => (k+1)!) -/
theorem factorial_sum_eq_liouville_sub :
    lacunarySum (fun k => (k + 1).factorial) =
    liouvilleNumber 2 - 1 / 2 := by
  -- liouvilleNumber 2 = ∑' n, 1/(2:ℝ)^(n!) = f 0 + ∑' n, f (n+1)
  -- where f n = 1/(2:ℝ)^(n!)
  -- f 0 = 1/(2:ℝ)^(0!) = 1/2^1 = 1/2
  -- ∑' n, f (n+1) = ∑' k, 1/(2:ℝ)^((k+1)!) = lacunarySum ...
  -- liouvilleNumber 2 = ∑' n, 1/(2:ℝ)^(n!)
  -- Split at n=0: = 1/2^(0!) + ∑' k, 1/2^((k+1)!)
  -- 0! = 1, so = 1/2 + lacunarySum (fun k => (k+1)!)
  -- Therefore lacunarySum = liouvilleNumber 2 - 1/2
  unfold lacunarySum liouvilleNumber
  have hsumm := liouville_summable
  have hsplit := hsumm.tsum_eq_zero_add
  -- hsplit : ∑' n, f n = f 0 + ∑' n, f (n + 1)
  linarith [hsplit]

/-- **Axiom-Free Factorial Transcendence**

    The sum Σ 1/2^{k!} is transcendental, proved without the
    erdos_transcendence_strong axiom. Uses Mathlib's Liouville theory
    via the observation that this sum differs from liouvilleNumber 2
    by a rational constant. -/
theorem factorial_sum_transcendental_axiom_free :
    Transcendental ℚ (lacunarySum (fun k => (k + 1).factorial)) := by
  rw [factorial_sum_eq_liouville_sub]
  have h1 : Transcendental ℚ (liouvilleNumber 2) :=
    transcendental_int_to_rat LiouvilleTheorem.liouville_base_2_transcendental
  convert Transcendental.sub_rat h1 (1/2) using 1
  push_cast; ring

/- ### Path B: Direct Liouville Proof -/

/-- m*(m+1)! + 1 < (m+2)! for all m. Key inequality for the Liouville bound. -/
theorem factorial_mul_add_one_lt (m : ℕ) :
    m * (m + 1).factorial + 1 < (m + 2).factorial := by
  rw [Nat.factorial_succ (m + 1)]
  -- (m+2)! = (m+2)*(m+1)!
  -- Need: m*(m+1)! + 1 < (m+2)*(m+1)!
  -- i.e., 1 < 2*(m+1)!
  have h := Nat.factorial_pos (m + 1)
  nlinarith

/-- The tail is strictly positive (each term is positive, and tsum of positive
    terms over a nonempty index is positive). -/
theorem factorialTail_pos (N : ℕ) : 0 < factorialTail N := by
  unfold factorialTail
  exact (factorial_tail_summable N).tsum_pos (fun k => by positivity) 0 (by positivity)

/-- Tail bound: the tail starting at N+1 is at most 2/2^{(N+2)!}. -/
theorem factorialTail_le (N : ℕ) :
    factorialTail N ≤ 2 / (2 : ℝ) ^ (N + 2).factorial := by
  unfold factorialTail
  -- Each term 1/2^{(N+2+k)!} ≤ 1/2^{(N+2)!+k} since (N+2+k)! ≥ (N+2)!+k
  -- Sum of RHS = 1/2^{(N+2)!} * ∑ 1/2^k = 1/2^{(N+2)!} * 2 = 2/2^{(N+2)!}
  -- Use hasSum_le for the comparison
  -- Pointwise bound: each term ≤ corresponding geometric term
  have hfact_bound : ∀ k, (N + 2).factorial + k ≤ (N + 1 + k + 1).factorial := by
    intro k
    rw [show N + 1 + k + 1 = N + 2 + k from by omega]
    calc (N + 2).factorial + k
        ≤ (N + 2).factorial * (k + 1) := by nlinarith [Nat.factorial_pos (N + 2)]
      _ ≤ (N + 2 + k).factorial := by
          induction k with
          | zero => simp
          | succ m ihm =>
            calc (N + 2).factorial * (m + 1 + 1)
                = (N + 2).factorial * (m + 1) + (N + 2).factorial := by ring
              _ ≤ (N + 2 + m).factorial + (N + 2 + m).factorial :=
                  add_le_add ihm (Nat.factorial_le (by omega))
              _ ≤ (N + 2 + m).factorial * (N + 2 + m + 1) := by
                  nlinarith [Nat.factorial_pos (N + 2 + m)]
              _ = (N + 2 + m + 1).factorial := by
                  rw [Nat.factorial_succ]; ring
  have hle : ∀ k, (1 : ℝ) / 2 ^ (N + 1 + k + 1).factorial ≤
      (1 / 2 ^ (N + 2).factorial) * (1 / 2) ^ k := by
    intro k
    -- Rewrite RHS to common form: 1/2^{(N+2)!+k}
    have hrw : (1 : ℝ) / 2 ^ (N + 2).factorial * (1 / 2) ^ k =
        1 / 2 ^ ((N + 2).factorial + k) := by
      rw [pow_add, one_div, one_div, inv_pow, ← mul_inv]; ring_nf
    rw [hrw]
    exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : (0 : ℝ) < 2 ^ ((N + 2).factorial + k))
      (by exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) (hfact_bound k))
  have hgeo_summable : Summable (fun k => (1 / 2 ^ (N + 2).factorial) * ((1 : ℝ) / 2) ^ k) :=
    Summable.mul_left _ (summable_geometric_of_lt_one (by positivity) (by norm_num))
  calc ∑' k, (1 : ℝ) / 2 ^ (N + 1 + k + 1).factorial
      ≤ ∑' k, (1 / 2 ^ (N + 2).factorial) * ((1 : ℝ) / 2) ^ k :=
        hasSum_le hle (factorial_tail_summable N).hasSum hgeo_summable.hasSum
    _ = (1 / 2 ^ (N + 2).factorial) * ∑' k, ((1 : ℝ) / 2) ^ k := tsum_mul_left
    _ = (1 / 2 ^ (N + 2).factorial) * 2 := by
        rw [tsum_geometric_of_lt_one (by positivity) (by norm_num)]; norm_num
    _ = 2 / (2 : ℝ) ^ (N + 2).factorial := by ring

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
  obtain ⟨a, ha⟩ := factorialPartialSum_eq_div m
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
    calc factorialTail m
        ≤ 2 / (2 : ℝ) ^ (m + 2).factorial := factorialTail_le m
      _ < 1 / ((2 : ℝ) ^ (m + 1).factorial) ^ m := by
          -- Cross-multiply: 2 * (2^{(m+1)!})^m < 2^{(m+2)!}
          rw [div_lt_div_iff₀ (by positivity) (by positivity)]
          rw [one_mul, ← pow_mul]
          rw [show (m + 1).factorial * m = m * (m + 1).factorial from by ring]
          -- 2 * 2^{m*(m+1)!} < 2^{(m+2)!}
          -- i.e., 2^{m*(m+1)!+1} < 2^{(m+2)!}
          have h1 : (2 : ℝ) * (2 : ℝ) ^ (m * (m + 1).factorial) =
              (2 : ℝ) ^ (m * (m + 1).factorial + 1) := by
            rw [pow_succ]; ring
          rw [h1]
          have h2 : m * (m + 1).factorial + 1 < (m + 2).factorial := by
            rw [Nat.factorial_succ (m + 1)]
            have := Nat.factorial_pos (m + 1); nlinarith
          exact_mod_cast Nat.pow_lt_pow_right (by omega : 1 < 2) h2

/-- **Axiom-free transcendence via direct Liouville proof.**
    Uses Liouville's theorem directly — no Erdős 1975 axiom needed. -/
theorem factorial_sum_transcendental_liouville :
    Transcendental ℚ (lacunarySum (fun k => (k + 1).factorial)) := by
  exact transcendental_int_to_rat factorial_sum_liouville.transcendental

end Erdos247
