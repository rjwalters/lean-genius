/-
# Erdős Problem #5: Limit Points of Normalized Prime Gaps

Let p_n denote the n-th prime. Define the normalized gap ratio
  g(n) = (p_{n+1} - p_n) / log(p_n).

Let S be the set of all limit points of the sequence g(n).
Erdős conjectured S = [0, ∞), i.e., for every C ≥ 0 there exist
infinitely many n with g(n) → C.

Known results:
- 0 ∈ S: Goldston–Pintz–Yıldırım (2009)
- ∞ ∈ S: Westzynthius (1931), improved by Rankin, Erdős, Ford–Green–Konyagin–Tao
- S has positive Lebesgue measure: Erdős–Ricci
- S contains arbitrarily large finite values: Hildebrand–Maier
- At least 1/3 of [0, ∞) belongs to S: Merikoski (2020)

Status: OPEN.

Reference: https://erdosproblems.com/5
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Basic

/- ## Definitions -/

/-- The n-th prime number (0-indexed: nthPrime 0 = 2, nthPrime 1 = 3, ...).
    Defined using Mathlib's Nat.nth enumeration of the infinite set of primes.
    Previously axiomatized; now concrete via Nat.nth. -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- nthPrime n is always prime.
    Previously axiomatized (with unnecessary hypothesis 1 ≤ n);
    now proved directly from the Nat.nth definition. -/
theorem nthPrime_prime (n : ℕ) : (nthPrime n).Prime := by
  unfold nthPrime
  exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

/-- nthPrime is strictly increasing.
    Previously axiomatized; now proved from Nat.nth_strictMono. -/
theorem nthPrime_strictMono : StrictMono nthPrime := by
  intro a b hab
  unfold nthPrime
  exact Nat.nth_strictMono Nat.infinite_setOf_prime hab

/-- The normalized prime gap ratio g(n) = (p_{n+1} - p_n) / log(p_n). -/
noncomputable def normalizedGap (n : ℕ) : ℝ :=
  (nthPrime (n + 1) - nthPrime n : ℤ) / Real.log (nthPrime n)

/-- A real number C is a limit point of the normalized gap sequence
    if for every ε > 0, there exist infinitely many n with |g(n) - C| < ε. -/
def IsLimitPointOfGaps (C : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
    |normalizedGap n - C| < ε

/- ## Known Results -/

/- 0 ∈ S: Goldston–Pintz–Yıldırım (2009) proved
   lim inf (p_{n+1} - p_n) / log(p_n) = 0. -/
/-- ∞ ∈ S: Westzynthius (1931) proved the gaps can be arbitrarily large
    relative to log(p_n). Formally: for every M, there exist infinitely many n
    with g(n) > M. -/
axiom gaps_unbounded (M : ℝ) :
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ normalizedGap n > M

/-- Hildebrand–Maier: for any C > 0 there exist infinitely many n
    with g(n) > C. (Strengthening: S contains arbitrarily large finite values.)
    Previously axiomatized; now derived from gaps_unbounded. -/
theorem hildebrand_maier_large_gaps (C : ℝ) (hC : 0 < C) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ normalizedGap n > C :=
  gaps_unbounded C

/- Merikoski (2020): at least 1/3 of any bounded interval [0, T]
   is covered by S. Formally: the Lebesgue measure of
   S ∩ [0, T] is at least T/3 for all T > 0. -/

/- ## Basic Properties -/

/-- The n-th prime is at least 2, since 2 is the smallest prime. -/
theorem nthPrime_ge_two (n : ℕ) : 2 ≤ nthPrime n :=
  (nthPrime_prime n).two_le

/-- log(p_n) > 0 for every n, since p_n ≥ 2 > 1. -/
theorem log_nthPrime_pos (n : ℕ) : 0 < Real.log (nthPrime n) := by
  apply Real.log_pos
  have h : (2 : ℝ) ≤ (nthPrime n : ℝ) := by exact_mod_cast nthPrime_ge_two n
  linarith

/-- The normalized gap is strictly positive for every n: the numerator
    p_{n+1} - p_n is positive (strict monotonicity) and log(p_n) > 0. -/
theorem normalizedGap_pos (n : ℕ) : 0 < normalizedGap n := by
  unfold normalizedGap
  apply div_pos
  · have h : nthPrime n < nthPrime (n + 1) := nthPrime_strictMono (Nat.lt_succ_self n)
    have hz : (0 : ℤ) < (nthPrime (n + 1) : ℤ) - (nthPrime n : ℤ) := by
      have hlt : (nthPrime n : ℤ) < (nthPrime (n + 1) : ℤ) := by exact_mod_cast h
      omega
    exact_mod_cast hz
  · exact log_nthPrime_pos n

/-- Normalized gaps are non-negative for every n. -/
theorem normalizedGap_nonneg (n : ℕ) : 0 ≤ normalizedGap n :=
  (normalizedGap_pos n).le

/-- Every limit point C of the normalized gap sequence is non-negative.
    Equivalently, S ⊆ [0, ∞) — the trivial containment of Erdős's conjecture,
    holding unconditionally since every g(n) ≥ 0. -/
theorem limitPoint_nonneg {C : ℝ} (hC : IsLimitPointOfGaps C) : 0 ≤ C := by
  by_contra h
  push_neg at h
  obtain ⟨n, _, hn⟩ := hC (-C) (by linarith) 0
  rw [abs_lt] at hn
  have hg : 0 ≤ normalizedGap n := normalizedGap_nonneg n
  linarith [hn.2]

/- ## The Conjecture -/

/-- **Erdős Problem #5** (the full conjecture): the set S of limit points of
    g(n) = (p_{n+1} - p_n)/log(p_n) equals [0, ∞). That is, every C ≥ 0 is a
    limit point of the normalized gap sequence.

    The containment S ⊆ [0, ∞) is the trivial direction, proved unconditionally
    in `limitPoint_nonneg`. The reverse — that every non-negative real is
    actually attained as a limit point — is the open part of the problem.
    Westzynthius (`gaps_unbounded`) handles the ∞ endpoint; GPY handles 0. -/
def ErdosProblem5 : Prop :=
  ∀ C : ℝ, 0 ≤ C → IsLimitPointOfGaps C
