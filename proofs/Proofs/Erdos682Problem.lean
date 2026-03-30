/-
Erdős Problem #682: Rough Numbers Between Consecutive Primes

Source: https://erdosproblems.com/682
Status: SOLVED (Gafni-Tao 2025)

Statement:
Is it true that for almost all n there exists some m ∈ (p_n, p_{n+1}) such that
p(m) ≥ p_{n+1} - p_n, where p(m) denotes the least prime factor of m?

Background:
- p_n denotes the n-th prime number
- p(m) is the smallest prime dividing m
- A number m is "k-rough" if p(m) ≥ k
- The question asks if gaps between primes usually contain rough numbers

History:
- Erdős initially thought this should be true for all large n
- He found a conditional counterexample via Dickson's conjecture
- The counterexample: if 2183+30030d and 2201+30030d are consecutive primes,
  then the gap [2184, 2200] contains no number with smallest prime factor ≥ 18,
  since 30030 = 2·3·5·7·11·13

Answer: YES (Gafni-Tao 2025)
- True for almost all n
- Number of exceptional n ∈ [1,X] is ≪ X/(log X)²
- Conditionally (prime tuples conjecture): ~ c·X/(log X)² for explicit c > 0

References:
- Gafni, Tao (2025): "Rough numbers between consecutive primes" arXiv:2508.06463
- Related: Erdős Problems #680, #681
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.OrderIsoNat

open Nat

namespace Erdos682

noncomputable section

/-
## Part I: Basic Definitions
-/

/--
**The n-th Prime (0-indexed):**
`nthPrime n` is the n-th prime: nthPrime 0 = 2, nthPrime 1 = 3, etc.
Defined via `Nat.nth Nat.Prime` from Mathlib (was previously an axiom).
-/
def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/--
**Least Prime Factor:**
p(m) is the smallest prime dividing m.
For m = 1, we set p(1) = ∞ (represented as 0 in this formalization).
-/
noncomputable def leastPrimeFactor (m : ℕ) : ℕ :=
  if m ≤ 1 then 0
  else Nat.minFac m

/--
**Basic Property of Least Prime Factor:**
-/
theorem leastPrimeFactor_prime (m : ℕ) (hm : m > 1) :
    Nat.Prime (leastPrimeFactor m) := by
  simp [leastPrimeFactor, hm]
  exact Nat.minFac_prime (Nat.one_lt_iff_ne_one.mp hm)

/--
**Least Prime Factor Divides:**
-/
theorem leastPrimeFactor_dvd (m : ℕ) (hm : m > 1) :
    leastPrimeFactor m ∣ m := by
  simp [leastPrimeFactor, hm]
  exact Nat.minFac_dvd m

/-
## Part II: k-Rough Numbers
-/

/--
**k-Rough Number:**
A positive integer m is k-rough if its smallest prime factor is at least k.
Equivalently, m is not divisible by any prime less than k.
-/
def isKRough (m k : ℕ) : Prop :=
  m ≥ 1 ∧ leastPrimeFactor m ≥ k

/--
**1-Rough Characterization:**
Every positive integer is 1-rough.
-/
theorem one_rough_all (m : ℕ) (hm : m ≥ 1) : isKRough m 1 := by
  constructor
  · exact hm
  · simp

/--
**Rough Number Examples:**
-/
example : isKRough 7 7 := by
  constructor
  · norm_num
  · simp [leastPrimeFactor]
    norm_num

/-
## Part III: Prime Gaps
-/

/--
**Prime Gap:**
The gap g_n between the n-th and (n+1)-th prime: g_n = p_{n+1} - p_n
-/
def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/--
**Gap Interval:**
The interval (p_n, p_{n+1}) between consecutive primes.
-/
def gapInterval (n : ℕ) : Set ℕ :=
  {m : ℕ | nthPrime n < m ∧ m < nthPrime (n + 1)}

/--
**Non-empty Gaps:**
For n ≥ 2, the gap contains composite numbers (the gap is at least 2).
-/

/-
## Part IV: The Main Property
-/

/--
**Rough Number in Gap Property:**
n satisfies the Erdős property if there exists m ∈ (p_n, p_{n+1})
with p(m) ≥ p_{n+1} - p_n (i.e., m is (p_{n+1} - p_n)-rough).
-/
def hasRoughNumberInGap (n : ℕ) : Prop :=
  ∃ m : ℕ, m ∈ gapInterval n ∧ isKRough m (primeGap n)

/--
**Exceptional Index:**
n is exceptional if no rough number exists in the gap.
-/
def isExceptional (n : ℕ) : Prop := ¬hasRoughNumberInGap n

/-
## Part V: Erdős's Counterexample Construction
-/

/--
**Primorial:**
n# = product of all primes ≤ n.
30030 = 2·3·5·7·11·13 = 13#
Available as `Nat.primorial` from Mathlib.NumberTheory.Primorial.
(Removed axiom — was unused in any theorem.)
-/

/--
**Dickson's Conjecture (Special Case):**
There are infinitely many d such that both 2183 + 30030d and 2201 + 30030d are prime.
-/

/--
**Erdős's Conditional Counterexample:**
If p = 2183 + 30030d and q = 2201 + 30030d are consecutive primes,
then every m ∈ [2184, 2200] + 30030d is divisible by one of 2,3,5,7,11,13.
Thus the gap (p, q) contains no 18-rough number, but q - p = 18.
-/

/--
**Infinitely Many Exceptional n (Conditional):**
Assuming Dickson's conjecture, there are infinitely many exceptional n.
-/

/-
## Part VI: The Main Question
-/

/--
**Almost All Property:**
A property holds for almost all n if the exceptions have density 0.
-/
def holdsForAlmostAll (P : ℕ → Prop) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ X ≥ N,
    (Finset.filter (fun n => ¬P n) (Finset.range X)).card < ε * X

/--
**Erdős Problem #682:**
Is it true that for almost all n, there exists m ∈ (p_n, p_{n+1}) with p(m) ≥ g_n?
-/
def erdos682Question : Prop := holdsForAlmostAll hasRoughNumberInGap

/-
## Part VII: Gafni-Tao Theorem (2025)
-/

/--
**Counting Exceptional n:**
Let E(X) = |{n ≤ X : n is exceptional}|.
-/
def exceptionalCount (X : ℕ) : ℕ :=
  (Finset.filter isExceptional (Finset.range X)).card

/--
**Gafni-Tao Upper Bound (2025):**
E(X) ≪ X / (log X)²
-/
axiom gafni_tao_upper_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ X : ℕ, X ≥ 3 →
    (exceptionalCount X : ℝ) ≤ C * X / (Real.log X)^2

/--
**Gafni-Tao Conditional Asymptotic (2025):**
Assuming a form of the prime tuples conjecture,
E(X) ~ c · X / (log X)² for some explicit c > 0.
-/

/--
**Gafni-Tao Main Theorem:**
The property holds for almost all n.
-/
axiom gafni_tao_main_theorem : holdsForAlmostAll hasRoughNumberInGap

/--
**Affirmative Answer:**
The answer to Erdős Problem #682 is YES.
-/
theorem erdos682_answer : erdos682Question := gafni_tao_main_theorem

/-
## Part VIII: Density Implications
-/

/--
**Logarithmic Density:**
Since E(X) ≪ X/(log X)², the exceptional set has logarithmic density 0.
-/
theorem exceptional_density_zero :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ X ≥ N,
      (exceptionalCount X : ℝ) / X < ε := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := gafni_tao_upper_bound
  -- log n → ∞ as n → ∞
  have h_log : Filter.Tendsto (fun n : ℕ => Real.log (↑n)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- Eventually log X ≥ √(C/ε) + 1 and X ≥ 3
  set L := Real.sqrt (C / ε) + 1 with hL_def
  have hL_pos : L > 0 := by positivity
  have h_ev_log : ∀ᶠ X : ℕ in Filter.atTop, L ≤ Real.log (↑X) :=
    h_log.eventually (Filter.mem_atTop L)
  have h_ev_ge3 : ∀ᶠ X : ℕ in Filter.atTop, (3 : ℕ) ≤ X :=
    Filter.eventually_atTop.mpr ⟨3, fun _ h => h⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h_ev_log.and h_ev_ge3)
  refine ⟨N, fun X hX => ?_⟩
  obtain ⟨hlog, hX3⟩ := hN X hX
  have hX_pos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hlog_pos : (0 : ℝ) < Real.log (↑X) := lt_of_lt_of_le hL_pos hlog
  have hlog2_pos : (0 : ℝ) < (Real.log (↑X)) ^ 2 := by positivity
  -- Key: C/ε < (log X)², so C/(log X)² < ε
  have hCε_lt : C / ε < (Real.log (↑X)) ^ 2 := by
    have h1 : Real.sqrt (C / ε) < L := by linarith
    have h2 : 0 ≤ Real.sqrt (C / ε) := Real.sqrt_nonneg _
    calc C / ε = Real.sqrt (C / ε) ^ 2 := (Real.sq_sqrt (div_nonneg hC.le hε.le)).symm
      _ < L ^ 2 := by nlinarith [sq_nonneg (L - Real.sqrt (C / ε))]
      _ ≤ (Real.log (↑X)) ^ 2 := by nlinarith [sq_nonneg (Real.log (↑X) - L)]
  have hkey : C / (Real.log (↑X)) ^ 2 < ε := by
    rwa [div_lt_iff hlog2_pos, ← div_lt_iff hε]
  -- E(X)/X ≤ C·X/(log X)²/X = C/(log X)² < ε
  calc (exceptionalCount X : ℝ) / ↑X
      ≤ C * ↑X / (Real.log ↑X) ^ 2 / ↑X :=
        div_le_div_of_nonneg_right (hbound X hX3) hX_pos.le
    _ = C / (Real.log ↑X) ^ 2 := by rw [mul_div_assoc, div_div_cancel_left₀ hX_pos.ne']
    _ < ε := hkey

/--
**Most Gaps Contain Rough Numbers:**
Non-exceptional indices + exceptional indices = total,
so non-exceptional count ≥ total - exceptional count.
-/
theorem most_gaps_have_rough :
    ∀ X : ℕ,
      (Finset.filter hasRoughNumberInGap (Finset.range X)).card ≥
      X - exceptionalCount X := by
  intro X
  simp only [exceptionalCount, isExceptional]
  have h : (Finset.filter hasRoughNumberInGap (Finset.range X)).card +
    (Finset.filter (fun n => ¬hasRoughNumberInGap n) (Finset.range X)).card =
    (Finset.range X).card :=
    Finset.filter_card_add_filter_neg_card_eq_card
  simp only [Finset.card_range] at h
  omega

/-
## Part IX: Related Results
-/

/-
**Connection to Problem #680:**
Problem 680 asks about the maximum gap among p_n ≤ X without rough numbers.
-/

/-
**Connection to Problem #681:**
Problem 681 concerns a similar question with a different gap condition.
-/

/-
**Smooth vs Rough Numbers:**
k-smooth numbers (all prime factors ≤ k) are the complement of k-rough.
The distribution of smooth numbers is well-understood (de Bruijn).
-/

/-
**Bertrand's Postulate Connection:**
Bertrand: there exists a prime in (n, 2n).
This problem asks about composite numbers with large least prime factors.
-/

/-
## Part X: Summary
-/

/--
**Summary of Results:**
-/
theorem erdos_682_summary :
    -- Gafni-Tao bound: E(X) ≪ X/(log X)²
    (∃ C : ℝ, C > 0 ∧ ∀ X ≥ 3, (exceptionalCount X : ℝ) ≤ C * X / (Real.log X)^2) ∧
    -- Answer is YES: almost all n have the property
    erdos682Question := by
  constructor
  · exact gafni_tao_upper_bound
  · exact erdos682_answer

/--
**Erdős Problem #682: SOLVED**

Is it true that for almost all n there exists m ∈ (p_n, p_{n+1})
with p(m) ≥ p_{n+1} - p_n?

Answer: YES (Gafni-Tao 2025)

The number of exceptional n ≤ X is O(X/(log X)²).
Conditionally, it is asymptotic to c·X/(log X)² for explicit c > 0.
-/
theorem erdos_682 : erdos682Question := erdos682_answer

end

end Erdos682
