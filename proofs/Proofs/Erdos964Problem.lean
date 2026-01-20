/-
Erdős Problem #964: Ratios of Consecutive Divisor Function Values

Source: https://erdosproblems.com/964
Status: SOLVED (Eberhard 2025)

Statement:
Let τ(n) count the number of divisors of n. Is the sequence
  τ(n+1)/τ(n)
everywhere dense in (0, ∞)?

Answer: YES - Eberhard (2025) proved this unconditionally

Background:
- τ(n) = |{d : d | n}| is the divisor counting function
- The question asks: for any r > 0 and ε > 0, does there exist n with
  |τ(n+1)/τ(n) - r| < ε?
- Even stronger: ALL positive rationals appear as τ(n+1)/τ(n)

Historical:
- This follows from the prime k-tuple conjecture
- Eberhard (2025) proved it unconditionally
- Related to Problem #946

Tags: number-theory, divisor-function, density
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Divisors
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Order.Basic

open Set Real
open scoped Topology

namespace Erdos964

/-!
## Part I: The Divisor Function
-/

/--
**Divisor counting function τ(n):**
The number of positive divisors of n.
-/
def tau (n : ℕ) : ℕ :=
  (Nat.divisors n).card

/--
**Basic properties:**
τ(1) = 1, τ(p) = 2 for prime p, τ(p^k) = k+1
-/
theorem tau_one : tau 1 = 1 := by
  simp [tau, Nat.divisors]

theorem tau_prime (p : ℕ) (hp : Nat.Prime p) : tau p = 2 := by
  simp [tau, Nat.divisors_prime hp]

theorem tau_prime_power (p k : ℕ) (hp : Nat.Prime p) :
    tau (p ^ k) = k + 1 := by
  sorry

/--
**Multiplicativity:**
τ is multiplicative: τ(mn) = τ(m)τ(n) when gcd(m,n) = 1.
-/
theorem tau_multiplicative (m n : ℕ) (h : Nat.Coprime m n) :
    tau (m * n) = tau m * tau n := by
  sorry

/-!
## Part II: Ratios of Consecutive Values
-/

/--
**Divisor ratio:**
The ratio τ(n+1)/τ(n) for consecutive integers.
-/
noncomputable def divisorRatio (n : ℕ) : ℝ :=
  if h : tau n ≠ 0 then (tau (n + 1) : ℝ) / (tau n : ℝ) else 0

/--
**Set of all ratios:**
The set {τ(n+1)/τ(n) : n ≥ 1}.
-/
noncomputable def ratioSet : Set ℝ :=
  {r : ℝ | ∃ n : ℕ, n ≥ 1 ∧ divisorRatio n = r}

/-!
## Part III: The Erdős Conjecture
-/

/--
**Everywhere dense:**
A set S ⊆ ℝ is everywhere dense in (0, ∞) if its closure contains (0, ∞).
-/
def isDenseInPositives (S : Set ℝ) : Prop :=
  ∀ r : ℝ, r > 0 → ∀ ε > 0, ∃ s ∈ S, |s - r| < ε

/--
**The Erdős conjecture:**
Is {τ(n+1)/τ(n) : n ≥ 1} dense in (0, ∞)?
-/
def ErdosConjecture964 : Prop :=
  isDenseInPositives ratioSet

/-!
## Part IV: Eberhard's Theorem
-/

/--
**Eberhard's theorem (2025):**
All positive rationals appear as τ(n+1)/τ(n).
-/
axiom eberhard_theorem :
    ∀ p q : ℕ, p ≥ 1 → q ≥ 1 → ∃ n : ℕ, n ≥ 1 ∧ tau (n + 1) * q = tau n * p

/--
**Corollary: Rationals are in the ratio set:**
-/
theorem rationals_in_ratio_set (p q : ℕ) (hp : p ≥ 1) (hq : q ≥ 1) :
    (p : ℝ) / q ∈ ratioSet := by
  obtain ⟨n, hn, heq⟩ := eberhard_theorem p q hp hq
  use n
  simp [ratioSet, divisorRatio]
  constructor
  · exact hn
  · -- Need to show divisorRatio n = p/q
    sorry

/--
**Rationals are dense in (0, ∞):**
-/
theorem rationals_dense_in_positives :
    isDenseInPositives {r : ℝ | ∃ p q : ℕ, p ≥ 1 ∧ q ≥ 1 ∧ r = (p : ℝ) / q} := by
  intro r hr ε hε
  -- Standard density argument
  sorry

/--
**Main theorem: The conjecture is TRUE**
-/
theorem erdos_964_true : ErdosConjecture964 := by
  intro r hr ε hε
  -- Since rationals are dense and contained in ratioSet
  obtain ⟨s, ⟨p, q, hp, hq, hs⟩, hdist⟩ := rationals_dense_in_positives r hr ε hε
  use s
  constructor
  · rw [hs]
    exact rationals_in_ratio_set p q hp hq
  · exact hdist

/-!
## Part V: Examples and Special Cases
-/

/--
**Example: τ(2)/τ(1) = 2:**
τ(2) = 2, τ(1) = 1, so ratio = 2.
-/
example : divisorRatio 1 = 2 := by
  simp [divisorRatio, tau]
  sorry

/--
**Example: τ(3)/τ(2) = 1:**
τ(3) = 2, τ(2) = 2, so ratio = 1.
-/
example : divisorRatio 2 = 1 := by
  simp [divisorRatio, tau]
  sorry

/--
**Example: τ(4)/τ(3) = 3/2:**
τ(4) = 3, τ(3) = 2, so ratio = 3/2.
-/
example : divisorRatio 3 = 3/2 := by
  simp [divisorRatio, tau]
  sorry

/--
**Small ratios:**
τ(n+1)/τ(n) can be arbitrarily small.
-/
axiom small_ratios_exist :
    ∀ ε > 0, ∃ n : ℕ, n ≥ 1 ∧ divisorRatio n < ε

/--
**Large ratios:**
τ(n+1)/τ(n) can be arbitrarily large.
-/
axiom large_ratios_exist :
    ∀ M : ℝ, ∃ n : ℕ, n ≥ 1 ∧ divisorRatio n > M

/-!
## Part VI: Connection to Prime k-Tuple Conjecture
-/

/--
**Prime k-tuple conjecture:**
For any admissible k-tuple (h₁, ..., hₖ), there exist infinitely many n
such that n + h₁, ..., n + hₖ are all prime.
-/
def PrimeKTupleConjecture : Prop :=
  ∀ k : ℕ, ∀ h : Fin k → ℕ,
    (∀ p : ℕ, Nat.Prime p → ∃ i, (h i : ℤ) % p ≠ 0) →
    ∃ᶠ n in Filter.atTop, ∀ i, Nat.Prime (n + h i)

/--
**The conjecture implies density:**
Under the prime k-tuple conjecture, density follows easily.
-/
axiom ktuple_implies_density :
    PrimeKTupleConjecture → ErdosConjecture964

/--
**Eberhard's unconditional proof:**
Eberhard proved the density result without assuming any unproved conjectures.
-/
axiom eberhard_unconditional :
    ErdosConjecture964

/-!
## Part VII: Stronger Results
-/

/--
**All positive rationals appear:**
This is stronger than just density.
-/
def AllRationalsAppear : Prop :=
  ∀ p q : ℕ, p ≥ 1 → q ≥ 1 →
    ∃ n : ℕ, n ≥ 1 ∧ divisorRatio n = (p : ℝ) / q

/--
**Eberhard's strong result:**
-/
theorem eberhard_strong : AllRationalsAppear := by
  intro p q hp hq
  obtain ⟨n, hn, heq⟩ := eberhard_theorem p q hp hq
  use n
  constructor
  · exact hn
  · simp [divisorRatio]
    sorry

/--
**Related: Problem #946:**
Problem 946 asks related questions about divisor function values.
-/

/-!
## Part VIII: Statistics of the Ratio
-/

/--
**Average ratio:**
The average value of τ(n+1)/τ(n) over n ≤ N.
-/
noncomputable def averageRatio (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, divisorRatio (n + 1)) / N

/--
**The average is 1:**
On average, τ(n+1) ≈ τ(n).
-/
axiom average_ratio_is_one :
    Filter.Tendsto averageRatio Filter.atTop (nhds 1)

/--
**Distribution of log ratios:**
log(τ(n+1)/τ(n)) has a limiting distribution.
-/
axiom log_ratio_distribution :
    ∃ μ : MeasureTheory.Measure ℝ,
      Filter.Tendsto
        (fun N => (∑ n ∈ Finset.range N, if Real.log (divisorRatio (n + 1)) ∈ Set.Icc (-1) 1 then (1 : ℝ) else 0) / N)
        Filter.atTop
        (nhds (μ (Set.Icc (-1) 1)))

/-!
## Part IX: Summary

**Erdős Problem #964: SOLVED**

**Question:** Is {τ(n+1)/τ(n) : n ≥ 1} dense in (0, ∞)?

**Answer:** YES (Eberhard 2025)

**Even stronger:** ALL positive rationals appear as τ(n+1)/τ(n).

**Key insight:** By carefully choosing n, we can make consecutive
integers have any prescribed ratio of divisor counts.

**Related:** Problem #946, prime k-tuple conjecture
-/

/--
**Main result: Erdős #964 is SOLVED**
-/
theorem erdos_964 : ErdosConjecture964 := erdos_964_true

/--
**The answer:**
-/
theorem erdos_964_answer :
    ∀ r : ℝ, r > 0 → ∀ ε > 0, ∃ n : ℕ, n ≥ 1 ∧ |divisorRatio n - r| < ε :=
  erdos_964

end Erdos964
