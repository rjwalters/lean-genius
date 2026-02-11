import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
# The Riemann Hypothesis

## What This File Contains

This file formalizes the **Riemann Hypothesis** (RH), one of the seven Millennium Prize
Problems. The RH is an open conjecture about the location of the non-trivial zeros of
the Riemann zeta function.

## The Conjecture

**Riemann Hypothesis**: All non-trivial zeros of the Riemann zeta function ζ(s) have
real part equal to 1/2.

Formally: If ζ(s) = 0 and 0 < Re(s) < 1, then Re(s) = 1/2.

## Status: OPEN CONJECTURE

This file does NOT prove the Riemann Hypothesis. It provides:
1. A precise formal statement of RH using Mathlib's zeta function
2. Known equivalences that are proven to be equivalent to RH
3. Partial results about zeros on the critical line
4. Educational context about the significance of RH

## What Is Proven vs Conjectured

| Component | Status |
|-----------|--------|
| Trivial zeros at -2, -4, -6, ... | PROVEN (Mathlib) |
| Functional equation ζ(s) = ... ζ(1-s) | PROVEN (Mathlib) |
| ζ(s) ≠ 0 for Re(s) > 1 | PROVEN (Mathlib) |
| ζ(s) ≠ 0 for Re(s) = 1 | PROVEN (Prime Number Theorem) |
| All zeros in 0 < Re(s) < 1 have Re(s) = 1/2 | **CONJECTURE** |

## Historical Context

- **1859**: Riemann states the hypothesis in his paper "On the Number of Primes
  Less Than a Given Magnitude"
- **1896**: Hadamard and de la Vallée Poussin prove the Prime Number Theorem
  using ζ(s) ≠ 0 on Re(s) = 1
- **1914**: Hardy proves infinitely many zeros lie on the critical line Re(s) = 1/2
- **1942**: Selberg proves positive proportion of zeros on critical line
- **2000**: RH becomes one of the seven Millennium Prize Problems ($1M prize)

## Mathlib Dependencies

- `Mathlib.NumberTheory.LSeries.RiemannZeta` - Riemann zeta function
- `Mathlib.NumberTheory.ArithmeticFunction` - Arithmetic functions
- `Mathlib.NumberTheory.PrimeCounting` - Prime counting function

## References

- [Riemann's 1859 Paper](https://www.claymath.org/sites/default/files/ezeta.pdf)
- [Clay Mathematics Institute](https://www.claymath.org/millennium-problems/riemann-hypothesis)
- [Mathlib Zeta Function](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/RiemannZeta.html)
-/

set_option maxHeartbeats 400000

noncomputable section

open Complex Real Set Filter Topology Nat ArithmeticFunction
open scoped Topology BigOperators ComplexConjugate

namespace RiemannHypothesis

/-! ═══════════════════════════════════════════════════════════════════════════════
PART I: BASIC DEFINITIONS AND PROPERTIES
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The critical line Re(s) = 1/2 where non-trivial zeros are conjectured to lie -/
def criticalLine : Set ℂ := {s : ℂ | s.re = 1/2}

/-- The critical strip 0 < Re(s) < 1 where non-trivial zeros must lie -/
def criticalStrip : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < 1}

/-- A zero is trivial if it's a negative even integer -/
def isTrivialZero (s : ℂ) : Prop := ∃ n : ℕ, s = -2 * (n + 1)

/-- A zero is non-trivial if it's in the critical strip -/
def isNonTrivialZero (s : ℂ) : Prop := riemannZeta s = 0 ∧ s ∈ criticalStrip

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II: THE RIEMANN HYPOTHESIS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **THE RIEMANN HYPOTHESIS**

All non-trivial zeros of the Riemann zeta function lie on the critical line Re(s) = 1/2.

This is equivalent to: If ζ(s) = 0 and 0 < Re(s) < 1, then Re(s) = 1/2.

Constructing a proof of this type would resolve one of the Millennium Prize Problems.
As of 2025, this remains an open conjecture.
-/
def RiemannHypothesis : Prop :=
  ∀ s : ℂ, isNonTrivialZero s → s ∈ criticalLine

/-- Alternative formulation: all zeros in the critical strip have Re(s) = 1/2 -/
theorem RH_alt : RiemannHypothesis ↔
    ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1/2 := by
  unfold RiemannHypothesis isNonTrivialZero criticalStrip criticalLine
  simp only [mem_setOf_eq]
  constructor
  · intro h s hz hpos hlt
    exact h s ⟨hz, hpos, hlt⟩
  · intro h s ⟨hz, hpos, hlt⟩
    exact h s hz hpos hlt

/-- Symmetric formulation using distance from 1/2 -/
theorem RH_symmetric : RiemannHypothesis ↔
    ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → |s.re - 1/2| = 0 := by
  rw [RH_alt]
  constructor
  · intro h s hz hpos hlt
    simp only [abs_eq_zero, sub_eq_zero]
    exact h s hz hpos hlt
  · intro h s hz hpos hlt
    have := h s hz hpos hlt
    simp only [abs_eq_zero, sub_eq_zero] at this
    exact this

/-! ═══════════════════════════════════════════════════════════════════════════════
PART III: KNOWN FACTS ABOUT ZEROS (PROVEN)
═══════════════════════════════════════════════════════════════════════════════ -/

-- The Riemann zeta function: riemannZeta : ℂ → ℂ

/-- Trivial zeros: ζ(-2n) = 0 for all positive integers n

This is proven in Mathlib via the functional equation. -/
theorem trivial_zeros (n : ℕ) : riemannZeta (-2 * (n + 1)) = 0 :=
  riemannZeta_neg_two_mul_nat_add_one n

/-- ζ(0) = -1/2 (not a zero!) -/
theorem zeta_zero : riemannZeta 0 = -1/2 := riemannZeta_zero

/-- **Axiom: No Zeros for Re(s) > 1**

The Riemann zeta function has no zeros in the half-plane Re(s) > 1.

This follows from the Euler product representation:
  ζ(s) = ∏_p (1 - p^(-s))^(-1) for Re(s) > 1

Each factor is nonzero (since |p^(-s)| < 1 for Re(s) > 1), hence the product is nonzero.

**Status**: This is a proven theorem in analytic number theory, but requires the
Euler product formula which is not yet fully available in Mathlib for ζ(s) with s ∈ ℂ.
The Euler product is proven for the completed zeta function, but extracting this
result for the standard zeta function requires additional technical lemmas. -/
axiom no_zeros_re_gt_one (s : ℂ) (hs : 1 < s.re) : riemannZeta s ≠ 0

/-- The functional equation relates ζ(s) and ζ(1-s)

Mathlib has: completedRiemannZeta_one_sub -/
theorem functional_equation_completed (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s

/-- **Axiom: Zeros Symmetric About Critical Line**

Zeros in the critical strip come in symmetric pairs about Re(s) = 1/2.
If ζ(s) = 0 with 0 < Re(s) < 1, then ζ(1-s) = 0 as well.

**Proof sketch**: The functional equation for the completed zeta function gives
  Λ(s) = Λ(1-s) where Λ(s) = π^(-s/2) Γ(s/2) ζ(s)

If ζ(s) = 0, then Λ(s) = 0, so Λ(1-s) = 0. Since Γ has no zeros (only poles at
non-positive integers, which lie outside the critical strip), we must have ζ(1-s) = 0.

**Status**: This is a proven theorem, but extracting it requires careful analysis of
the Gamma function's behavior in the critical strip, specifically that Γ(s/2) ≠ 0
and Γ((1-s)/2) ≠ 0 when 0 < Re(s) < 1. -/
axiom zeros_symmetric (s : ℂ) (hs_strip : s ∈ criticalStrip)
    (hs_zero : riemannZeta s = 0) : riemannZeta (1 - s) = 0

/-- The critical strip is symmetric about Re(s) = 1/2 -/
theorem criticalStrip_symmetric (s : ℂ) :
    s ∈ criticalStrip ↔ (1 - s) ∈ criticalStrip := by
  simp only [criticalStrip, mem_setOf_eq, sub_re, one_re]
  constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> linarith

/-! ═══════════════════════════════════════════════════════════════════════════════
PART IV: EQUIVALENT FORMULATIONS OF RH
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Robin's Inequality

**Robin (1984)**: The Riemann Hypothesis is equivalent to:
  σ(n) < e^γ · n · log(log(n)) for all n > 5040

where σ(n) is the sum of divisors and γ is the Euler-Mascheroni constant.
-/

/-- The Euler-Mascheroni constant γ ≈ 0.5772 -/
def eulerMascheroni : ℝ := Real.eulerMascheroniConstant

/-- Sum of divisors function σ(n) -/
def sigma (n : ℕ) : ℕ := n.divisors.sum _root_.id

/-- Robin's upper bound function: e^γ · n · log(log(n)) -/
def robinBound (n : ℕ) : ℝ :=
  if h : n ≥ 3 then
    Real.exp eulerMascheroni * n * Real.log (Real.log n)
  else 0

/-- **Robin's Inequality** - equivalent to RH for n > 5040 -/
def RobinsInequality : Prop :=
  ∀ n : ℕ, n > 5040 → (sigma n : ℝ) < robinBound n

/-- **Axiom: Robin's Equivalence (1984)**

Robin's theorem states that the Riemann Hypothesis is equivalent to Robin's inequality:
  σ(n) < e^γ · n · log(log(n)) for all n > 5040

This deep result connects the analytic Riemann Hypothesis to a purely arithmetic
statement about divisor sums.

**References**:
- Robin, G. (1984). "Grandes valeurs de la fonction somme des diviseurs et hypothèse
  de Riemann". Journal de Mathématiques Pures et Appliquées, 63, 187-213.

**Proof complexity**: The proof requires:
1. Explicit bounds on ζ(s) near Re(s) = 1
2. Connection between σ(n) and ζ(s) via Dirichlet series: ζ(s)² = Σ σ(n)/n^s
3. Careful analysis of "colossally abundant numbers" (extremal cases for σ(n)/n)
4. Delicate calculations involving the prime number theorem with error terms

This is far beyond current Mathlib capabilities and would require a major
formalization effort. -/
axiom RH_iff_Robin : RiemannHypothesis ↔ RobinsInequality

/-!
### Mertens Function Bound

**Littlewood**: RH is equivalent to M(x) = O(x^(1/2 + ε)) for all ε > 0

where M(x) = Σ_{n≤x} μ(n) is the Mertens function.
-/

/-- The Möbius function μ(n) -/
def mobius : ℕ → ℤ := ArithmeticFunction.moebius

/-- The Mertens function M(x) = Σ_{n≤x} μ(n) -/
def mertens (x : ℝ) : ℤ :=
  ∑ n in Finset.filter (· ≤ ⌊x⌋₊) (Finset.range (⌊x⌋₊ + 1)), mobius n

/-- **Mertens bound equivalent to RH** -/
def MertensBound : Prop :=
  ∀ ε > 0, ∃ C > 0, ∀ x ≥ 1, |mertens x| ≤ C * x^((1:ℝ)/2 + ε)

/-- **Axiom: Mertens Equivalence (Littlewood, 1912)**

The Riemann Hypothesis is equivalent to the bound:
  M(x) = O(x^(1/2 + ε)) for all ε > 0

where M(x) = Σ_{n≤x} μ(n) is the Mertens function.

**Proof outline**:
1. The Dirichlet series 1/ζ(s) = Σ μ(n)/n^s converges for Re(s) > 1
2. Perron's formula relates M(x) to a contour integral involving 1/ζ(s)
3. The location of zeros of ζ(s) determines the growth rate of M(x)
4. RH implies zeros only at Re(s) = 1/2, giving M(x) = O(x^(1/2 + ε))
5. Conversely, M(x) = O(x^(1/2 + ε)) implies no zeros with Re(s) > 1/2

**References**:
- Littlewood, J.E. (1912). "Quelques conséquences de l'hypothèse que la fonction ζ(s)
  n'a pas de zéros dans le demi-plan Re(s) > 1/2"

**Status**: This requires Perron's formula and contour integration techniques not
yet available in Mathlib. -/
axiom RH_iff_Mertens : RiemannHypothesis ↔ MertensBound

/-!
### Prime Counting Error Term

**Koch (1901)**: RH is equivalent to:
  |π(x) - Li(x)| = O(√x log x)

where π(x) is the prime counting function and Li(x) is the logarithmic integral.
-/

/-- The prime counting function π(x) -/
def primeCounting (x : ℝ) : ℕ := Nat.primeCounting ⌊x⌋₊

/-- **Axiom: Logarithmic Integral Definition**

The logarithmic integral Li(x) = ∫₂ˣ dt/ln(t) is a fundamental function in
prime number theory that gives the main term in the prime counting approximation.

**Note**: The full definition requires measure theory integration:
  Li(x) = ∫_{t ∈ [2,x]} (1 / log t) dt

This could be defined using Mathlib's `MeasureTheory.integral` over `Set.Icc 2 x`,
but for simplicity we axiomatize the function here. The key properties used are:
- Li(x) ~ x/log(x) as x → ∞
- Li(x) approximates π(x) with the error term depending on zeta zeros -/
axiom logIntegral (x : ℝ) : ℝ

/-- **Prime counting error bound equivalent to RH** -/
def PrimeCountingBound : Prop :=
  ∃ C > 0, ∀ x ≥ 2, |(primeCounting x : ℝ) - logIntegral x| ≤ C * Real.sqrt x * Real.log x

/-- **Axiom: Prime Counting Equivalence (von Koch, 1901)**

The Riemann Hypothesis is equivalent to the prime counting error bound:
  |π(x) - Li(x)| = O(√x log x)

**Historical context**: This was one of the first equivalences of RH discovered.
It shows that RH is fundamentally about how well Li(x) approximates π(x).

**Proof outline**:
1. The explicit formula expresses π(x) as Li(x) minus contributions from zeta zeros
2. Each zero ρ contributes a term of size O(x^Re(ρ))
3. RH (all zeros have Re(ρ) = 1/2) gives error O(x^(1/2) log x)
4. Conversely, a zero with Re(ρ) > 1/2 would cause larger oscillations

**References**:
- von Koch, H. (1901). "Sur la distribution des nombres premiers"

**Status**: Requires the explicit formula for π(x), which involves complex analysis
and is not yet in Mathlib. -/
axiom RH_iff_PrimeCounting : RiemannHypothesis ↔ PrimeCountingBound

/-! ═══════════════════════════════════════════════════════════════════════════════
PART V: PARTIAL RESULTS (PROVEN WITHOUT RH)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Axiom: Hardy's Theorem (1914)**

Infinitely many zeros of the Riemann zeta function lie on the critical line Re(s) = 1/2.

This does NOT prove RH, but shows the critical line is special.

**Hardy's proof outline**:
1. Define the Hardy Z-function: Z(t) = exp(iθ(t)) ζ(1/2 + it) where θ(t) is the
   Riemann-Siegel theta function
2. Show Z(t) is real for real t (a remarkable property)
3. Prove Z(t) changes sign infinitely often as t → ∞
4. Each sign change corresponds to a zero on the critical line

**Historical significance**: This was the first proof that infinitely many zeros
lie exactly on the critical line, not just in the critical strip.

**References**:
- Hardy, G.H. (1914). "Sur les zéros de la fonction ζ(s) de Riemann"
  Comptes Rendus, 158, 1012-1014

**Status**: Requires the Hardy Z-function, Riemann-Siegel theta, and careful
asymptotic analysis not yet available in Mathlib. -/
axiom hardy_infinitely_many_on_critical_line :
    Set.Infinite {s : ℂ | riemannZeta s = 0 ∧ s.re = 1/2}

/-- **Axiom: Selberg's Positive Proportion (1942)**

A positive proportion of zeros are on the critical line.
Specifically, at least 40% of zeros (counted with multiplicity) lie on Re(s) = 1/2.

Let N₀(T) = number of zeros with Re(s) = 1/2 and 0 < Im(s) ≤ T
Let N(T) = total number of zeros in critical strip with 0 < Im(s) ≤ T

Then N₀(T) ≥ c · N(T) for some constant c > 0.

**Historical improvements**:
- Selberg (1942): c > 0 (some positive proportion)
- Levinson (1974): c > 1/3 (more than one third)
- Conrey (1989): c > 0.4 (more than 40%)
- Current best: c > 0.4088 (Bui, Conrey, Young, 2011)

**References**:
- Selberg, A. (1942). "On the zeros of Riemann's zeta-function"
- Conrey, J.B. (1989). "More than two fifths of the zeros of the Riemann zeta function
  are on the critical line"

**Status**: Deep analytic result requiring moment methods and the Riemann-Siegel
formula. Far beyond current Mathlib capabilities. -/
axiom selberg_positive_proportion :
    ∃ c > 0, ∀ T > 1,
      let N₀ := Set.ncard {s : ℂ | riemannZeta s = 0 ∧ s.re = 1/2 ∧ 0 < s.im ∧ s.im ≤ T}
      let N := Set.ncard {s : ℂ | riemannZeta s = 0 ∧ s ∈ criticalStrip ∧ 0 < s.im ∧ s.im ≤ T}
      (N₀ : ℝ) ≥ c * N

/-- **Axiom: Classical Zero-Free Region (de la Vallee Poussin, 1899)**

The Riemann zeta function has no zeros in the region:
  Re(s) ≥ 1 - c/log|Im(s)| for |Im(s)| ≥ t₀

This is the zero-free region used to prove the Prime Number Theorem.

**Proof idea**: Uses the fact that for real σ > 1:
  Re(3 + 4ζ'(σ)/ζ(σ) + ζ'(σ + 2it)/ζ(σ + 2it)) ≥ 0

Combined with bounds on log ζ(s) near Re(s) = 1, this gives the zero-free region.

**Applications**:
- Proves π(x) ~ x/log(x) (Prime Number Theorem)
- Gives error term π(x) = Li(x) + O(x exp(-c√log x))
- Essential for sieve methods and prime gap estimates

**References**:
- de la Vallee Poussin, C.J. (1896). "Recherches analytiques sur la theorie
  des nombres premiers"
- Hadamard, J. (1896). "Sur la distribution des zeros de la fonction ζ(s)
  et ses consequences arithmetiques"

**Status**: Proven in the literature but requires careful complex analysis
not yet available in Mathlib for ζ near Re(s) = 1. -/
axiom classical_zero_free_region :
    ∃ c > 0, ∃ t₀ > 0, ∀ s : ℂ,
      |s.im| ≥ t₀ → s.re ≥ 1 - c / Real.log |s.im| → riemannZeta s ≠ 0

/-! ═══════════════════════════════════════════════════════════════════════════════
PART VI: COMPUTATIONAL VERIFICATION
═══════════════════════════════════════════════════════════════════════════════ -/

/-- First few zeros on the critical line (imaginary parts)

The first zero is at s = 1/2 + 14.134725...i -/
def firstZeroImaginaryPart : ℝ := 14.134725141734693790

/-- **Computational verification**: All zeros up to height T have been verified
to lie on the critical line.

As of 2024, this has been verified for the first 10^13 zeros. -/
axiom computationally_verified_zeros (T : ℝ) (hT : T ≤ 10^13) :
    ∀ s : ℂ, riemannZeta s = 0 → s ∈ criticalStrip → |s.im| ≤ T → s.re = 1/2

/-! ═══════════════════════════════════════════════════════════════════════════════
PART VII: CONSEQUENCES OF RH
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Axiom: RH Implies Prime Gap Bounds**

Conditional on the Riemann Hypothesis, there are no extremely large gaps between primes.
Specifically, the gap between consecutive primes p_n and p_{n+1} satisfies:
  p_{n+1} - p_n = O(√p_n · (log p_n)²)

**Proof idea**: Under RH, the prime counting function satisfies:
  π(x) = Li(x) + O(√x log x)

This implies for any prime p, there is another prime in [p, p + C√p log²p].

**Unconditional results**: Without RH, the best known bound is:
  p_{n+1} - p_n ≤ p_n^(0.525) (Baker-Harman-Pintz, 2001)

**References**:
- Cramer, H. (1936). "On the order of magnitude of the difference between
  consecutive prime numbers"
- Conditional results follow from explicit forms of π(x) - Li(x) under RH

**Status**: Follows from RH via the prime counting error bound, but the full
derivation requires estimates not yet in Mathlib. -/
axiom RH_implies_prime_gaps (h : RiemannHypothesis) :
    ∃ C > 0, ∀ n : ℕ, Nat.Prime n →
      ∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p ≤ n + C * Real.sqrt n * (Real.log n)^2

/-- **Axiom: RH Gives Effective Ternary Goldbach**

Under the Riemann Hypothesis, the ternary Goldbach conjecture has an effective bound.
That is, there exists an explicit N₀ such that every odd n > N₀ is the sum of three primes.

**Background**: Vinogradov (1937) proved unconditionally that every sufficiently large
odd integer is the sum of three primes, but his proof was ineffective (did not give N₀).

**With RH**: The Riemann Hypothesis allows computation of an explicit N₀.
Without RH, the first effective bound was found by Helfgott (2013) who proved
the full ternary Goldbach: every odd n > 5 is the sum of three primes.

**Historical note**: Helfgott's proof completed the ternary Goldbach without assuming RH,
making this consequence of RH now unconditionally known. However, RH-based proofs
give better quantitative bounds and simpler arguments.

**References**:
- Vinogradov, I.M. (1937). "Representation of an odd number as a sum of three primes"
- Helfgott, H.A. (2013). "Major arcs for Goldbach's problem"

**Status**: The ternary Goldbach is now proven unconditionally (Helfgott 2013),
but RH-conditional proofs remain of theoretical interest. -/
axiom RH_implies_ternary_goldbach_effective (h : RiemannHypothesis) :
    ∃ N₀ : ℕ, ∀ n : ℕ, n > N₀ → Odd n →
      ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

/-! ═══════════════════════════════════════════════════════════════════════════════
PART VIII: SUMMARY AND SIGNIFICANCE
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Summary of what we know about the Riemann Hypothesis:

1. **Statement**: All non-trivial zeros of ζ(s) have Re(s) = 1/2

2. **Proven facts**:
   - Trivial zeros at -2, -4, -6, ...
   - No zeros for Re(s) > 1 or Re(s) = 1
   - Infinitely many zeros on Re(s) = 1/2 (Hardy)
   - >40% of zeros on Re(s) = 1/2 (Conrey)
   - First 10^13 zeros verified computationally

3. **Equivalent statements**:
   - Robin's inequality: σ(n) < e^γ n log log n for n > 5040
   - Mertens bound: M(x) = O(x^(1/2+ε))
   - Prime counting: |π(x) - Li(x)| = O(√x log x)

4. **Why it matters**:
   - Best possible error term in Prime Number Theorem
   - Bounds on prime gaps
   - Distribution of primes in arithmetic progressions
   - Connections to random matrix theory
   - Applications in cryptography and primality testing

5. **Status**: Open since 1859, $1M Millennium Prize
-/
theorem RH_summary : True := trivial

#check RiemannHypothesis
#check RH_iff_Robin
#check RH_iff_Mertens
#check hardy_infinitely_many_on_critical_line

end RiemannHypothesis
