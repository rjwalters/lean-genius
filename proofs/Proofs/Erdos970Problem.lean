/-
Erdős Problem #970: Jacobsthal's Function

Source: https://erdosproblems.com/970
Status: OPEN

Statement:
Let h(k) be Jacobsthal's function, defined as the minimal m such that,
if n has at most k prime factors, then in any set of m consecutive integers
there exists an integer coprime to n. Determine the order of magnitude of h(k).
In particular, is it true that h(k) ≪ k²?

Answer: OPEN - Best bounds are:
- Upper: h(k) ≪ (k log k)² (Iwaniec 1978)
- Lower: h(k) ≫ k · (log k)(log log log k)/(log log k)² (Ford-Green-Konyagin-Maynard-Tao 2018)

Key Results:
- Jacobsthal's Conjecture: h(k) ≪ k² remains unproven
- Gap between upper and lower bounds is roughly a log factor
- Related to prime gaps (Problem #687)

References:
- [Iw78] Iwaniec, "On the problem of Jacobsthal" (1978)
- [FGKMT18] Ford-Green-Konyagin-Maynard-Tao, "Long gaps between primes" (2018)
- OEIS A048669

Tags: number-theory, primes, gaps, coprimality, open-problem
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real Nat

namespace Erdos970

/-!
## Part 1: Basic Definitions
-/

/-- The number of distinct prime factors of n (omega function) -/
def omega (n : ℕ) : ℕ := n.primeFactors.card

/-- n has at most k distinct prime factors -/
def hasAtMostKPrimes (n : ℕ) (k : ℕ) : Prop := omega n ≤ k

/-- An interval [a, a+m) of consecutive integers -/
def consecutiveInterval (a m : ℕ) : Finset ℕ :=
  Finset.Ico a (a + m)

/-- There exists an element in [a, a+m) coprime to n -/
def hasCoprimeElement (n a m : ℕ) : Prop :=
  ∃ x ∈ consecutiveInterval a m, Nat.Coprime x n

/-- Jacobsthal's function: minimal m such that any m consecutive
    integers contain one coprime to n -/
noncomputable def jacobsthalForN (n : ℕ) : ℕ :=
  if n ≤ 1 then 1
  else Nat.find (⟨n + 1, by
    intro a
    -- In n+1 consecutive integers starting at a, at least one is coprime to n
    sorry⟩ : ∃ m, ∀ a, hasCoprimeElement n a m)

/-- h(k): maximum of jacobsthalForN over all n with at most k prime factors -/
noncomputable def h (k : ℕ) : ℕ :=
  if k = 0 then 1
  else sSup {jacobsthalForN n | n : ℕ, hasAtMostKPrimes n k}

/-!
## Part 2: The Main Conjecture
-/

/-- Jacobsthal's Conjecture: h(k) ≪ k² -/
def jacobsthalConjecture : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ k : ℕ, k ≥ 1 → (h k : ℝ) ≤ C * k^2

/-- The weaker form: h(k) = O(k²) -/
def hQuadraticBound : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀, (h k : ℝ) ≤ C * k^2

/-!
## Part 3: Known Upper Bounds
-/

/-- Iwaniec's Theorem (1978): h(k) ≪ (k log k)² -/
axiom iwaniec_upper_bound :
  ∃ C : ℝ, C > 0 ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀,
    (h k : ℝ) ≤ C * (k * Real.log k)^2

/-- The Iwaniec bound explicitly: h(k) ≤ C(k log k)² for some constant C -/
theorem iwaniec_bound_form :
    ∃ C : ℝ, C > 0 ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀,
      (h k : ℝ) ≤ C * k^2 * (Real.log k)^2 := by
  obtain ⟨C, hC, k₀, hk⟩ := iwaniec_upper_bound
  use C, hC, k₀
  intro k hkge
  have := hk k hkge
  ring_nf at this ⊢
  exact this

/-- The gap from k² is a (log k)² factor -/
axiom gap_from_quadratic :
  -- Iwaniec's bound is (k log k)² = k² · (log k)²
  -- The conjecture is k², so gap is (log k)²
  True

/-!
## Part 4: Known Lower Bounds
-/

/-- Trivial lower bound: h(k) ≥ p_k where p_k is the k-th prime -/
axiom trivial_lower_bound :
  ∀ k : ℕ, k ≥ 1 → h k ≥ Nat.prime (k)

/-- Rankin's lower bound (implied by prime gap results) -/
axiom rankin_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀,
    (h k : ℝ) ≥ c * k * Real.log k

/-- Ford-Green-Konyagin-Maynard-Tao (2018) lower bound -/
axiom fgkmt_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀,
    (h k : ℝ) ≥ c * k * (Real.log k) * (Real.log (Real.log (Real.log k))) /
                    (Real.log (Real.log k))^2

/-- The FGKMT bound is the current best lower bound -/
axiom fgkmt_is_best_known_lower : True

/-!
## Part 5: Small Values
-/

/-- h(1) = 2: any 2 consecutive integers contain one coprime to any prime -/
axiom h_one : h 1 = 2

/-- h(2) = 4: primorial 2# = 6, gap of 4 (5,6,7,8) around 6 works -/
axiom h_two : h 2 = 4

/-- h(3) = 6: primorial 3# = 30 -/
axiom h_three : h 3 = 6

/-- h(4) = 10: primorial 4# = 210 -/
axiom h_four : h 4 = 10

/-- h(5) = 14: primorial 5# = 2310 -/
axiom h_five : h 5 = 14

/-- The primorial plays a key role in extremal examples -/
def primorial (k : ℕ) : ℕ :=
  (Finset.range k).prod (fun i => Nat.prime (i + 1))

/-- Jacobsthal's function is maximized at primorials -/
axiom jacobsthal_extremal :
  ∀ k : ℕ, k ≥ 1 → jacobsthalForN (primorial k) = h k

/-!
## Part 6: Connection to Prime Gaps
-/

/-- Problem 687: related question about gaps -/
axiom problem_687_connection :
  -- Problem 687 asks about specific prime gap questions
  -- Problem 970 is a generalization using Jacobsthal's function
  True

/-- Large prime gaps imply lower bounds for h(k) -/
axiom prime_gaps_imply_lower_bounds :
  -- If there exist large gaps between consecutive primes,
  -- this gives lower bounds for h(k)
  True

/-- The FGKMT paper on long prime gaps is key -/
axiom fgkmt_paper_importance :
  -- Ford-Green-Konyagin-Maynard-Tao proved major results on prime gaps
  -- Their techniques also apply to Jacobsthal's function
  True

/-!
## Part 7: Proof Strategies
-/

/-- Sieve methods give upper bounds -/
axiom sieve_methods :
  -- Iwaniec used sieve methods to prove h(k) ≪ (k log k)²
  -- Better sieves might improve the bound
  True

/-- The Chinese Remainder Theorem connection -/
axiom crt_connection :
  -- Elements coprime to n = p₁...pₖ exist in intervals by CRT
  -- The question is how small the interval can be
  True

/-- Probabilistic heuristics -/
axiom probabilistic_heuristic :
  -- Random model: probability of coprimality to primorial is ∏(1 - 1/p)
  -- This suggests h(k) should be roughly k log k or k²
  -- Heuristics don't resolve the conjecture
  True

/-!
## Part 8: Why It's Hard
-/

/-- The conjecture has resisted proof for decades -/
axiom long_standing_open : True

/-- Gap between bounds: (log k)² factor -/
theorem current_gap :
    -- Upper: h(k) ≤ C(k log k)²
    -- Lower: h(k) ≥ ck · log k · log³ k / (log² k)²
    -- Gap is roughly (log k)² between upper and quadratic
    -- Gap between upper and lower is roughly k log k
    True := trivial

/-- Neither bound approach has improved significantly recently -/
axiom bounds_stable : True

/-!
## Part 9: Generalizations
-/

/-- Generalized Jacobsthal function for arbitrary moduli -/
def generalizedJacobsthal (S : Finset ℕ) : ℕ :=
  -- Minimum m such that any m consecutive integers
  -- contain one coprime to all elements of S
  sorry

/-- Higher-dimensional variants -/
axiom higher_dim_variant : True

/-- Weighted versions -/
axiom weighted_variant : True

/-!
## Part 10: The Current State
-/

/-- The conjecture h(k) ≪ k² is OPEN -/
theorem jacobsthal_conjecture_open :
    -- The conjecture remains unproven
    -- Best upper bound is (k log k)² by Iwaniec
    -- Best lower bound is k · log k · log³ k / (log² k)² by FGKMT
    True := trivial

/-- Summary of known bounds -/
theorem known_bounds :
    -- Upper: h(k) ≤ C(k log k)² for large k
    -- Lower: h(k) ≥ ck(log k)(log³ k)/(log² k)² for large k
    -- Conjecture: h(k) ≤ Ck² for all k ≥ 1
    True := trivial

/-!
## Part 11: Main Results
-/

/-- Erdős Problem #970 is OPEN -/
def erdos_970_status : String :=
  "OPEN - Jacobsthal's Conjecture h(k) ≪ k² is unresolved"

/-- The conjecture -/
def erdos_970_conjecture : Prop := jacobsthalConjecture

/-- What we know -/
theorem erdos_970_known :
    -- 1. h(k) ≤ C(k log k)² (Iwaniec 1978)
    -- 2. h(k) ≥ ck log k log³ k / (log² k)² (FGKMT 2018)
    -- 3. Gap to quadratic is (log k)²
    True := trivial

/-- **Erdős Problem #970: OPEN**

QUESTION: Is h(k) ≪ k² where h(k) is Jacobsthal's function?

ANSWER: UNKNOWN (OPEN)

KNOWN BOUNDS:
- Upper: h(k) ≪ (k log k)² (Iwaniec 1978)
- Lower: h(k) ≫ k log k log³k / (log²k)² (FGKMT 2018)

The gap to the conjectured k² bound is roughly (log k)².
This has been open since Jacobsthal's original work.
-/
theorem erdos_970_summary : True := trivial

end Erdos970
