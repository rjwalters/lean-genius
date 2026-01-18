/-
Erdős Problem #858: Primitive-Like Sets and Logarithmic Density

Source: https://erdosproblems.com/858
Status: SOLVED

Statement:
Let A ⊆ {1,...,N} be such that there is no solution to at = b with a,b ∈ A
and the smallest prime factor of t is > a. Estimate the maximum of
  (1/log N) · ∑_{n∈A} 1/n

Answer:
Alexander (1966) and Erdős-Sárközy-Szemerédi (1968) proved this maximum is o(1)
as N → ∞.

Context:
The condition "smallest prime factor of t > a" defines a weaker form of primitive sets.
- A set is **primitive** if no element divides another
- This condition allows a | b only if t = b/a has smallest prime factor ≤ a

For primitive sets, Behrend (1935) proved:
  (1/log N) · ∑_{n∈A} 1/n ≪ 1/√(log log N)

An example of a set satisfying the weaker condition: all integers in [N^{1/2}, N]
divisible by some prime > N^{1/2}.

References:
- Alexander (1966): "Density and multiplicative structure of sets of integers"
- Behrend (1935): "On sequences of numbers not divisible by another"
- Erdős-Sárközy-Szemerédi (1968): "On the solvability of certain equations..."
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators Nat

namespace Erdos858

/-
## Part I: Smallest Prime Factor

The smallest prime factor of n > 1 is the minimum prime dividing n.
-/

/--
**Smallest Prime Factor:**
For n > 1, the smallest prime that divides n.
For n = 1, we define it as 0 (no prime divides 1).
-/
noncomputable def smallestPrimeFactor (n : ℕ) : ℕ :=
  if h : n > 1 then n.minFac else 0

/--
For n > 1, smallestPrimeFactor n is prime.
-/
theorem smallestPrimeFactor_prime {n : ℕ} (hn : n > 1) :
    (smallestPrimeFactor n).Prime := by
  simp only [smallestPrimeFactor, hn, dif_pos]
  exact Nat.minFac_prime (Nat.one_lt_iff_ne_one.mp hn)

/--
The smallest prime factor divides n.
-/
theorem smallestPrimeFactor_dvd {n : ℕ} (hn : n > 1) :
    smallestPrimeFactor n ∣ n := by
  simp only [smallestPrimeFactor, hn, dif_pos]
  exact Nat.minFac_dvd n

/--
Any prime dividing n is ≥ the smallest prime factor.
-/
theorem le_of_prime_dvd {n p : ℕ} (hn : n > 1) (hp : p.Prime) (hpn : p ∣ n) :
    smallestPrimeFactor n ≤ p := by
  simp only [smallestPrimeFactor, hn, dif_pos]
  exact Nat.minFac_le_of_dvd hp.two_le hpn

/-
## Part II: The Primitive-Like Condition

A set A satisfies the "primitive-like" condition if there's no solution to
at = b with a, b ∈ A and smallestPrimeFactor(t) > a.
-/

/--
**Primitive-Like Condition:**
A finite set A ⊆ ℕ⁺ is primitive-like if for all a, b ∈ A with a | b and a < b,
the smallest prime factor of t = b/a is ≤ a.

In other words: if at = b with a, b ∈ A and t > 1, then smallestPrimeFactor(t) ≤ a.
-/
def IsPrimitiveLike (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a < b → a ∣ b →
    let t := b / a
    smallestPrimeFactor t ≤ a

/--
**Alternative formulation:**
No solution to at = b with a, b ∈ A and smallestPrimeFactor(t) > a.
-/
def IsPrimitiveLike' (A : Finset ℕ) : Prop :=
  ¬∃ a ∈ A, ∃ b ∈ A, ∃ t : ℕ, t > 1 ∧ a * t = b ∧ smallestPrimeFactor t > a

/--
A standard primitive set: no element divides another distinct element.
-/
def IsPrimitive (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬(a ∣ b)

/--
Every primitive set is primitive-like.
-/
theorem primitive_implies_primitiveLike (A : Finset ℕ) :
    IsPrimitive A → IsPrimitiveLike A := by
  intro hprim a ha b hb hab hdiv
  -- In a primitive set, a ∤ b when a ≠ b
  exfalso
  have hne : a ≠ b := Nat.ne_of_lt hab
  exact hprim a ha b hb hne hdiv

/-
## Part III: Logarithmic Density

The logarithmic sum density of a set A ⊆ {1,...,N}.
-/

/--
**Range {1, ..., N}:**
-/
def rangeFrom1 (N : ℕ) : Finset ℕ := (Finset.range N).map ⟨(· + 1), fun _ _ h => by omega⟩

theorem mem_rangeFrom1 {N n : ℕ} : n ∈ rangeFrom1 N ↔ 1 ≤ n ∧ n ≤ N := by
  simp [rangeFrom1]
  constructor
  · intro ⟨a, ha, heq⟩
    constructor <;> omega
  · intro ⟨h1, h2⟩
    use n - 1
    constructor
    · simp [Finset.mem_range]; omega
    · omega

/--
**Logarithmic Sum:**
∑_{n ∈ A} 1/n for a finite set A of positive integers.
-/
noncomputable def logSum (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A.filter (· > 0), (1 : ℝ) / n

/--
**Normalized Logarithmic Density:**
(1/log N) · ∑_{n ∈ A} 1/n
-/
noncomputable def normalizedLogDensity (A : Finset ℕ) (N : ℕ) : ℝ :=
  if hN : N > 1 then logSum A / Real.log N else 0

/-
## Part IV: Behrend's Bound for Primitive Sets

For primitive sets, the normalized log density is O(1/√(log log N)).
-/

/--
**Behrend's Theorem (1935):**
For primitive sets A ⊆ {1,...,N}:
  (1/log N) · ∑_{n ∈ A} 1/n ≪ 1/√(log log N)

More precisely, there exists a constant C such that the normalized log
density is at most C/√(log log N) for all N ≥ 3.
-/
axiom behrend_primitive_bound : ∃ C : ℝ, C > 0 ∧
    ∀ N : ℕ, N ≥ 3 → ∀ A : Finset ℕ, A ⊆ rangeFrom1 N → IsPrimitive A →
    normalizedLogDensity A N ≤ C / Real.sqrt (Real.log (Real.log N))

/-
## Part V: Main Result - Alexander and Erdős-Sárközy-Szemerédi

For primitive-like sets, the normalized log density is o(1).
-/

/--
**Little-o Definition:**
A function f(N) is o(1) if for all ε > 0, there exists N₀ such that
|f(N)| < ε for all N ≥ N₀.
-/
def IsLittleO (f : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, |f N| < ε

/--
**Alexander's Theorem (1966):**
For sets A ⊆ {1,...,N} satisfying the primitive-like condition:
  (1/log N) · ∑_{n ∈ A} 1/n = o(1) as N → ∞

This is equivalent to saying the maximum normalized log density over
all primitive-like sets tends to 0.
-/
axiom alexander_theorem : ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ A : Finset ℕ, A ⊆ rangeFrom1 N → IsPrimitiveLike A →
    normalizedLogDensity A N < ε

/--
**Erdős-Sárközy-Szemerédi Theorem (1968):**
Same result as Alexander, proved independently. The maximum normalized
log density over primitive-like sets in {1,...,N} is o(1).
-/
axiom erdos_sarkozy_szemeredi_theorem : ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ A : Finset ℕ, A ⊆ rangeFrom1 N → IsPrimitiveLike A →
    normalizedLogDensity A N < ε

/-
## Part VI: Example Sets
-/

/--
**Example Construction:**
The set of all integers in [√N, N] divisible by some prime > √N.

This is an example of a set satisfying the primitive-like condition.
If a | b with a, b in this set, then t = b/a must have all prime
factors ≤ √N ≤ a (since a ≥ √N), so smallestPrimeFactor(t) ≤ a.
-/
def exampleSet (N : ℕ) : Finset ℕ :=
  (rangeFrom1 N).filter fun n =>
    n ≥ Nat.sqrt N ∧ ∃ p : ℕ, p.Prime ∧ p > Nat.sqrt N ∧ p ∣ n

/--
The example set satisfies the primitive-like condition.
-/
axiom exampleSet_isPrimitiveLike (N : ℕ) (hN : N ≥ 4) :
    IsPrimitiveLike (exampleSet N)

/-
## Part VII: Main Theorem
-/

/--
**Erdős Problem #858: SOLVED**

The main theorem: the maximum of (1/log N) · ∑_{n∈A} 1/n over all
primitive-like sets A ⊆ {1,...,N} is o(1) as N → ∞.
-/
theorem erdos_858 : ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ A : Finset ℕ, A ⊆ rangeFrom1 N → IsPrimitiveLike A →
    normalizedLogDensity A N < ε :=
  alexander_theorem

/--
Equivalent formulation using the o(1) definition.
-/
theorem erdos_858_alternative :
    IsLittleO (fun N =>
      if hN : N > 1 then
        sSup {normalizedLogDensity A N | A ∈ {B : Finset ℕ | B ⊆ rangeFrom1 N ∧ IsPrimitiveLike B}}
      else 0) := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := erdos_858 ε hε
  use max N₀ 2
  intro N hN
  by_cases hN' : N > 1
  · simp only [hN', dif_pos]
    -- The supremum of normalized log densities is < ε for N ≥ N₀
    -- This follows from erdos_858 applied to any A in the set
    sorry -- Would need Mathlib's sSup machinery
  · simp only [hN', dif_neg, not_lt]
    rw [abs_zero]
    exact hε

/--
**Summary:**
The primitive-like condition (no at = b with smallestPrimeFactor(t) > a)
is weaker than being primitive (no a | b at all), yet still forces
the normalized log density to be o(1).

Comparison:
- Primitive sets: density ≤ C/√(log log N) (Behrend 1935)
- Primitive-like sets: density = o(1) (Alexander 1966, ESS 1968)

The primitive-like condition captures the key structural property that
limits how dense a set can be in logarithmic measure.
-/
theorem erdos_858_summary :
    -- Main result
    (∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ A : Finset ℕ, A ⊆ rangeFrom1 N → IsPrimitiveLike A →
      normalizedLogDensity A N < ε) ∧
    -- Primitive implies primitive-like
    (∀ A : Finset ℕ, IsPrimitive A → IsPrimitiveLike A) ∧
    -- Stronger bound for primitive sets
    (∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 3 →
      ∀ A : Finset ℕ, A ⊆ rangeFrom1 N → IsPrimitive A →
      normalizedLogDensity A N ≤ C / Real.sqrt (Real.log (Real.log N))) :=
  ⟨erdos_858, primitive_implies_primitiveLike, behrend_primitive_bound⟩

end Erdos858
