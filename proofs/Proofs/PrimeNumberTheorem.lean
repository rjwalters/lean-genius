import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

/-!
# The Prime Number Theorem

## What This File Contains

This file formalizes the **Prime Number Theorem** (PNT), one of the most celebrated results
in analytic number theory. The PNT describes the asymptotic distribution of prime numbers.

## The Theorem

**Prime Number Theorem**: The prime counting function π(x) is asymptotically equivalent
to x/ln(x) as x → ∞.

$$\lim_{x \to \infty} \frac{\pi(x)}{x/\ln x} = 1$$

Equivalently: π(x) ~ x/ln(x), meaning the ratio approaches 1.

## Historical Context

- **1798**: Legendre conjectured that π(x) ≈ x/(ln(x) - 1.08366)
- **1849**: Gauss conjectured π(x) ~ Li(x), the logarithmic integral
- **1859**: Riemann's seminal paper connected primes to the zeta function
- **1896**: Hadamard and de la Vallée Poussin independently proved PNT
- **2004**: First formal proof in Isabelle by Avigad et al.
- **2024**: PrimeNumberTheoremAnd project formally proves PNT in Lean 4

## Equivalent Formulations

1. **Ratio form**: lim_{x→∞} π(x)·ln(x)/x = 1
2. **Logarithmic integral**: π(x) ~ Li(x) where Li(x) = ∫₂ˣ dt/ln(t)
3. **Chebyshev functions**: θ(x) ~ x and ψ(x) ~ x
4. **Asymptotic form**: π(x) = x/ln(x) + o(x/ln(x))

## Mathlib Dependencies

- `Mathlib.NumberTheory.PrimeCounting` - Prime counting function π(x)
- `Mathlib.Analysis.Asymptotics.Asymptotics` - Asymptotic notation (IsEquivalent, ~)
- `Mathlib.Analysis.SpecialFunctions.Log.Basic` - Natural logarithm

## References

- [PrimeNumberTheoremAnd Project](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
- [Mathlib Prime Counting](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/PrimeCounting.html)
- Hadamard, J. (1896). "Sur la distribution des zéros de la fonction ζ(s)"
- de la Vallée Poussin, C.-J. (1896). "Recherches analytiques sur la théorie des nombres premiers"

## Wiedijk's 100 Theorems: #5
-/

set_option maxHeartbeats 400000

noncomputable section

open Filter Topology Real Set Nat Asymptotics MeasureTheory
open scoped Topology BigOperators

namespace PrimeNumberTheorem

/-! ═══════════════════════════════════════════════════════════════════════════════
PART I: BASIC DEFINITIONS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The prime counting function π(x) counts primes ≤ x.

This uses Mathlib's `Nat.primeCounting` which is defined as the count of primes ≤ n. -/
def primePi (x : ℝ) : ℕ := Nat.primeCounting ⌊x⌋₊

/-- The approximation function x/ln(x) for the Prime Number Theorem -/
def primeApprox (x : ℝ) : ℝ :=
  if x > 1 then x / log x else 0

/-- The logarithmic integral Li(x) = ∫₂ˣ dt/ln(t)

This is actually a better approximation to π(x) than x/ln(x). -/
def logIntegral (x : ℝ) : ℝ :=
  if x ≤ 2 then 0
  else ∫ t in Icc 2 x, 1 / log t

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II: THE PRIME NUMBER THEOREM
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **THE PRIME NUMBER THEOREM (Ratio Form)**

The limit of π(x)·ln(x)/x as x → ∞ equals 1.

This is the classical formulation stating that π(x) is asymptotically x/ln(x). -/
def PrimeNumberTheorem_Ratio : Prop :=
  Tendsto (fun x : ℝ => (primePi x : ℝ) * log x / x) atTop (𝓝 1)

/-- **THE PRIME NUMBER THEOREM (Asymptotic Equivalence)**

π(x) ~ x/ln(x) as x → ∞.

Using Mathlib's asymptotic notation, the prime counting function is
equivalent to the prime approximation function. -/
def PrimeNumberTheorem_Equiv : Prop :=
  (fun x : ℝ => (primePi x : ℝ)) ~[atTop] primeApprox

/-- **THE PRIME NUMBER THEOREM (Error Term)**

π(x) = x/ln(x) + o(x/ln(x))

The prime counting function equals x/ln(x) plus a term that grows
slower than x/ln(x). -/
def PrimeNumberTheorem_Error : Prop :=
  (fun x : ℝ => (primePi x : ℝ) - primeApprox x) =o[atTop] primeApprox

/-- **THE PRIME NUMBER THEOREM (Logarithmic Integral)**

π(x) ~ Li(x) as x → ∞.

This is actually a more precise statement - the logarithmic integral
is a better approximation to π(x) than x/ln(x). -/
def PrimeNumberTheorem_Li : Prop :=
  (fun x : ℝ => (primePi x : ℝ)) ~[atTop] logIntegral

/-! ═══════════════════════════════════════════════════════════════════════════════
PART III: EQUIVALENCE OF FORMULATIONS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Proved: Ratio-Equivalence Correspondence**

The ratio formulation (π(x)·ln(x)/x → 1) is equivalent to asymptotic equivalence
(π(x) ~ x/ln(x)). Uses `isEquivalent_iff_tendsto_one` from Mathlib and the
algebraic identity π(x)/(x/ln(x)) = π(x)·ln(x)/x. -/
theorem ratio_iff_equiv : PrimeNumberTheorem_Ratio ↔ PrimeNumberTheorem_Equiv := by
  unfold PrimeNumberTheorem_Ratio PrimeNumberTheorem_Equiv
  have hpa : ∀ᶠ x : ℝ in atTop, primeApprox x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    simp only [primeApprox, if_pos hx]
    exact div_ne_zero (ne_of_gt (by linarith)) (ne_of_gt (Real.log_pos hx))
  rw [Asymptotics.isEquivalent_iff_tendsto_one hpa]
  constructor <;> intro h
  · -- Ratio → Quotient: show primePi/primeApprox = primePi*log/x eventually
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    simp only [Pi.div_apply, primeApprox, if_pos hx]
    have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
    have hx_ne : (x : ℝ) ≠ 0 := ne_of_gt (by linarith)
    field_simp
  · -- Quotient → Ratio: reverse direction, same algebra
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    simp only [Pi.div_apply, primeApprox, if_pos hx]
    have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
    have hx_ne : (x : ℝ) ≠ 0 := ne_of_gt (by linarith)
    field_simp

/-- **Proved: Equivalence-Error Correspondence**

`IsEquivalent l u v` is defined as `(u - v) =o[l] v`, which is exactly the
error term formulation. The two definitions are definitionally equal. -/
theorem equiv_iff_error : PrimeNumberTheorem_Equiv ↔ PrimeNumberTheorem_Error := by
  unfold PrimeNumberTheorem_Equiv PrimeNumberTheorem_Error Asymptotics.IsEquivalent
  rfl

/-- **Axiom: Logarithmic Integral Asymptotics**

The logarithmic integral Li(x) = integral from 2 to x of dt/ln(t) is asymptotically
equivalent to x/ln(x). This is established via integration by parts:

Li(x) = x/ln(x) + x/ln^2(x) + 2x/ln^3(x) + ... + O(x/ln^n(x))

The leading term dominates, giving Li(x) ~ x/ln(x).

A full proof requires careful analysis of the integral and asymptotic expansion. -/
axiom li_equiv_approx_axiom : logIntegral ~[atTop] primeApprox

/-- Li(x) and x/ln(x) are asymptotically equivalent -/
theorem li_equiv_approx : logIntegral ~[atTop] primeApprox :=
  li_equiv_approx_axiom

/-- **Proved: Li-Equiv Correspondence**

The Li formulation (π(x) ~ Li(x)) is equivalent to the basic asymptotic
formulation (π(x) ~ x/ln(x)), because Li(x) ~ x/ln(x) (axiomatized as
`li_equiv_approx_axiom`). Uses transitivity and symmetry of `~[l]`. -/
theorem li_iff_equiv : PrimeNumberTheorem_Li ↔ PrimeNumberTheorem_Equiv :=
  ⟨fun h => h.trans li_equiv_approx_axiom, fun h => h.trans li_equiv_approx_axiom.symm⟩

/-- All formulations of PNT are equivalent -/
theorem all_formulations_equiv :
    (PrimeNumberTheorem_Ratio ↔ PrimeNumberTheorem_Equiv) ∧
    (PrimeNumberTheorem_Equiv ↔ PrimeNumberTheorem_Error) ∧
    (PrimeNumberTheorem_Li ↔ PrimeNumberTheorem_Equiv) :=
  ⟨ratio_iff_equiv, equiv_iff_error, li_iff_equiv⟩

/-! ═══════════════════════════════════════════════════════════════════════════════
PART IV: THE MAIN THEOREM (AXIOMATIZED)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The Prime Number Theorem**

This is the main statement, axiomatized based on the formal proof in the
PrimeNumberTheoremAnd project by Kontorovich, Tao, et al.

The theorem states that as x → ∞, π(x)·ln(x)/x → 1.

A complete formal proof requires:
1. Complex analysis (Cauchy's theorem, residue calculus)
2. Properties of the Riemann zeta function
3. Zero-free region for ζ(s) on Re(s) = 1
4. Tauberian theorems (Wiener-Ikehara or Newman)

See: https://github.com/AlexKontorovich/PrimeNumberTheoremAnd -/
axiom primeNumberTheorem : PrimeNumberTheorem_Ratio

/-- Corollary: π(x) ~ x/ln(x) -/
theorem prime_asymptotic : PrimeNumberTheorem_Equiv :=
  ratio_iff_equiv.mp primeNumberTheorem

/-- Corollary: π(x) ~ Li(x) -/
theorem prime_li_asymptotic : PrimeNumberTheorem_Li :=
  li_iff_equiv.mpr prime_asymptotic

/-! ═══════════════════════════════════════════════════════════════════════════════
PART V: CONSEQUENCES OF PNT
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Proved: Prime Density Limit**

The density of primes π(x)/x tends to zero as x tends to infinity.
Proved from the axiomatized PNT: π(x)·ln(x)/x → 1 implies
π(x)/x = (π(x)·ln(x)/x) · (1/ln(x)) → 1 · 0 = 0, since ln(x) → ∞. -/
theorem prime_density_tends_to_zero :
    Tendsto (fun x : ℝ => (primePi x : ℝ) / x) atTop (𝓝 0) := by
  -- Strategy: π(x)/x = (π(x)·log(x)/x) · (1/log(x))
  -- The first factor → 1 (PNT), the second → 0 (log → ∞)
  suffices h : Tendsto (fun x : ℝ => (primePi x : ℝ) * log x / x * (1 / log x)) atTop (𝓝 0) by
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
    have hx_ne : (x : ℝ) ≠ 0 := ne_of_gt (by linarith)
    field_simp
  rw [show (0 : ℝ) = 1 * 0 from by ring]
  exact primeNumberTheorem.mul (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop)

/-- **Axiom: Nth Prime Asymptotics**

The nth prime pₙ satisfies pₙ ~ n·ln(n) as n → ∞.

This is the "inverse" of the Prime Number Theorem. If π(x) ~ x/ln(x),
then inverting the function gives pₙ ~ n·ln(n).

A full proof requires careful analysis of the inverse of the prime counting
function using asymptotic inversion techniques. -/
axiom nth_prime_asymptotic_axiom :
    Tendsto (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) / (n * Real.log n)) atTop (𝓝 1)

/-- **The nth prime is approximately n·ln(n)**

If pₙ denotes the nth prime, then pₙ ~ n·ln(n) as n → ∞. -/
theorem nth_prime_asymptotic :
    Tendsto (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) / (n * Real.log n)) atTop (𝓝 1) :=
  nth_prime_asymptotic_axiom

/-- **Axiom: Mertens' Sum of Prime Reciprocals**

The sum of reciprocals of primes up to x satisfies:
∑_{p ≤ x} 1/p = ln(ln(x)) + M + o(1)

where M is the Meissel-Mertens constant (approximately 0.2614972...).

Proved by Mertens (1874). The proof uses partial summation and PNT-type
estimates on the prime counting function. -/
axiom mertens_sum_primes_axiom :
    ∃ c : ℝ, Tendsto (fun x : ℝ =>
      (∑ p in Finset.filter (fun p => Nat.Prime p ∧ p ≤ ⌊x⌋₊) (Finset.range (⌊x⌋₊ + 1)),
        (1 : ℝ) / p) - log (log x)) atTop (𝓝 c)

/-- **Sum of reciprocals of primes diverges logarithmically**

∑_{p ≤ x} 1/p ~ ln(ln(x)) as x → ∞

Proved by Mertens (1874) as a consequence of PNT-type estimates. -/
theorem mertens_sum_primes :
    ∃ c : ℝ, Tendsto (fun x : ℝ =>
      (∑ p in Finset.filter (fun p => Nat.Prime p ∧ p ≤ ⌊x⌋₊) (Finset.range (⌊x⌋₊ + 1)),
        (1 : ℝ) / p) - log (log x)) atTop (𝓝 c) :=
  mertens_sum_primes_axiom

/-- **Axiom: Prime Gaps Are Sublinear**

For large x, the gap between consecutive primes near x is o(x).
This follows from the Prime Number Theorem: there are approximately x/ln(x)
primes up to x, so the average gap is about ln(x), which is o(x).

For any epsilon > 0, there exists X such that for all x >= X and any prime p <= x,
there exists a prime q with p < q <= x + epsilon*x.

A full proof requires showing that π(x + εx) - π(x) > 0 for large x,
using the PNT to estimate the difference. -/
axiom prime_gaps_sublinear_axiom :
    ∀ ε > 0, ∃ X : ℝ, ∀ x ≥ X, ∀ p : ℕ, Nat.Prime p → (p : ℝ) ≤ x →
      ∃ q : ℕ, Nat.Prime q ∧ p < q ∧ (q : ℝ) ≤ x + ε * x

/-- **Prime gaps bound**

For large x, the gap between consecutive primes near x is o(x).
Specifically, if p is the largest prime ≤ x, then the next prime is at most x + o(x). -/
theorem prime_gaps_sublinear :
    ∀ ε > 0, ∃ X : ℝ, ∀ x ≥ X, ∀ p : ℕ, Nat.Prime p → (p : ℝ) ≤ x →
      ∃ q : ℕ, Nat.Prime q ∧ p < q ∧ (q : ℝ) ≤ x + ε * x :=
  prime_gaps_sublinear_axiom

/-! ═══════════════════════════════════════════════════════════════════════════════
PART VI: STRONGER VERSIONS (CONDITIONAL ON RH)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Axiom: Riemann Hypothesis Statement**

The Riemann Hypothesis states that all non-trivial zeros of the Riemann zeta
function have real part equal to 1/2.

This is one of the most important unsolved problems in mathematics. It is
axiomatized here as this formalization focuses on the Prime Number Theorem,
and RH is only used to state a conditional result about error bounds.

A proper definition would require the Riemann zeta function for complex arguments
and its analytic continuation. -/
axiom RiemannHypothesis_statement : Prop

/-- The Riemann Hypothesis implies a stronger error bound for PNT -/
def RiemannHypothesis : Prop := RiemannHypothesis_statement

/-- **Axiom: Von Koch's Theorem (Conditional on RH)**

Under the Riemann Hypothesis, the error in the Prime Number Theorem is bounded:
|π(x) - Li(x)| = O(√x log x)

This was proved by von Koch in 1901. The proof uses the explicit formula relating
π(x) to the zeros of the zeta function, and the constraint that all non-trivial
zeros have real part 1/2.

This is one of the main motivations for studying the Riemann Hypothesis:
it would give much stronger control over the distribution of primes. -/
axiom pnt_rh_error_axiom :
    RiemannHypothesis →
    ∃ C > 0, ∀ x ≥ 2, |(primePi x : ℝ) - logIntegral x| ≤ C * Real.sqrt x * Real.log x

/-- **PNT with RH error bound**

Under the Riemann Hypothesis:
|π(x) - Li(x)| = O(√x log x)

This is von Koch's theorem (1901). -/
theorem pnt_rh_error (h : RiemannHypothesis) :
    ∃ C > 0, ∀ x ≥ 2, |(primePi x : ℝ) - logIntegral x| ≤ C * Real.sqrt x * Real.log x :=
  pnt_rh_error_axiom h

/-! ═══════════════════════════════════════════════════════════════════════════════
PART VII: ELEMENTARY BOUNDS (PROVEN WITHOUT FULL PNT)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Axiom: Chebyshev's Bounds**

Chebyshev (1852) showed that for sufficiently large x:
0.92129 < π(x)·ln(x)/x < 1.10555

These bounds were obtained using clever analysis of the central binomial
coefficient (2n choose n) and its prime factorization. Chebyshev's work
demonstrated that if the limit π(x)·ln(x)/x exists, it must equal 1.

This was a major step toward the Prime Number Theorem, proved 44 years later. -/
axiom chebyshev_bounds_axiom :
    ∃ X : ℝ, ∀ x ≥ X, x > 1 →
      0.92 < (primePi x : ℝ) * log x / x ∧ (primePi x : ℝ) * log x / x < 1.11

/-- **Chebyshev's bounds (1852)**

Before PNT was proved, Chebyshev showed:
0.92129 < π(x)·ln(x)/x < 1.10555 for sufficiently large x

These bounds demonstrate that if the limit exists, it must equal 1. -/
theorem chebyshev_bounds :
    ∃ X : ℝ, ∀ x ≥ X, x > 1 →
      0.92 < (primePi x : ℝ) * log x / x ∧ (primePi x : ℝ) * log x / x < 1.11 :=
  chebyshev_bounds_axiom

/-- **Proved: Prime Counting Tends to Infinity**

The prime counting function π(x) tends to infinity as x tends to infinity.
Proved by composing three Mathlib results:
1. `tendsto_nat_floor_atTop`: ⌊x⌋₊ → ∞ as x → ∞
2. `Nat.tendsto_primeCounting`: π(n) → ∞ as n → ∞
3. `tendsto_natCast_atTop_iff`: ℕ → ℝ cast preserves atTop -/
theorem prime_counting_tendsto_top : Tendsto (fun x : ℝ => (primePi x : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_iff.mpr (Nat.tendsto_primeCounting.comp tendsto_nat_floor_atTop)

/- euler_product_connection: **Euler's product formula connection**

The Euler product ζ(s) = ∏_p (1 - p^(-s))^(-1) connects PNT to the zeta function.
Taking logarithms: log ζ(s) = ∑_p p^(-s) + O(1) for Re(s) > 1.
The behavior of ζ(s) near s = 1 determines the distribution of primes. -/


/-! ═══════════════════════════════════════════════════════════════════════════════
PART VIII: NUMERICAL EVIDENCE
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Numerical values of π(x)**

| x          | π(x)        | x/ln(x)      | Li(x)        |
|------------|-------------|--------------|--------------|
| 10         | 4           | 4.34...      | 6.16...      |
| 100        | 25          | 21.71...     | 30.13...     |
| 1000       | 168         | 144.76...    | 177.61...    |
| 10⁶        | 78,498      | 72,382...    | 78,628...    |
| 10⁹        | 50,847,534  | 48,254,942...| 50,849,235...|
| 10¹²       | 37,607,912,018 | ...       | ...          |

Note: Li(x) is consistently a better approximation than x/ln(x). -/
def numericalEvidence : (1 : ℕ) + 1 = 2 := rfl

/-! ═══════════════════════════════════════════════════════════════════════════════
PART IX: SUMMARY
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Summary of the Prime Number Theorem**

1. **Statement**: π(x) ~ x/ln(x), i.e., lim_{x→∞} π(x)·ln(x)/x = 1

2. **Meaning**: Among numbers up to x, roughly 1/ln(x) are prime

3. **Better approximation**: π(x) ~ Li(x) = ∫₂ˣ dt/ln(t)

4. **Error terms**:
   - Unconditional: π(x) = Li(x) + O(x·exp(-c√(ln x)))
   - Under RH: π(x) = Li(x) + O(√x·ln x)

5. **Key techniques in proof**:
   - Complex analysis of ζ(s)
   - Zero-free region on Re(s) = 1
   - Tauberian theorems

6. **Historical significance**:
   - Conjectured by Gauss/Legendre (~1800)
   - Proved by Hadamard and de la Vallée Poussin (1896)
   - One of the crowning achievements of 19th century mathematics
-/
theorem pnt_summary : (1 : ℕ) + 1 = 2 := rfl

#check primeNumberTheorem
#check prime_asymptotic
#check prime_density_tends_to_zero
#check nth_prime_asymptotic

end PrimeNumberTheorem
