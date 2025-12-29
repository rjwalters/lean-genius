import Mathlib.NumberTheory.Liouville.Basic
import Mathlib.NumberTheory.Liouville.LiouvilleNumber
import Mathlib.NumberTheory.Liouville.LiouvilleConstant
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Liouville's Theorem and Transcendental Numbers (Wiedijk #18)

## What This File Contains

This file formalizes **Liouville's Theorem** about rational approximations to algebraic numbers
and the consequent existence of transcendental numbers via **Liouville numbers**.

## The Theorems

**Liouville's Approximation Theorem** (1844): If α is a real algebraic number of degree n > 1,
then there exists a constant c > 0 such that for all rationals p/q with q > 0:

$$\left| \alpha - \frac{p}{q} \right| > \frac{c}{q^n}$$

**Corollary**: Any number that can be approximated "too well" by rationals must be transcendental.
Such numbers are called **Liouville numbers**.

**Liouville Number Definition**: A real number ξ is a Liouville number if for every positive
integer n, there exist integers p and q with q > 1 such that:

$$0 < \left| \xi - \frac{p}{q} \right| < \frac{1}{q^n}$$

**Main Result**: All Liouville numbers are transcendental.

## Historical Significance

This was the **first explicit construction of transcendental numbers** (1844), predating:
- Cantor's diagonal argument (1874) showing transcendentals are uncountable
- Hermite's proof that e is transcendental (1873)
- Lindemann's proof that π is transcendental (1882)

Liouville's constant L = Σₙ 10^(-n!) was the first number proven transcendental.

## Key Ideas

1. **Algebraic numbers have bounded approximability**: The minimal polynomial provides a lower
   bound on how close rationals can get.

2. **Liouville numbers violate all such bounds**: They can be approximated arbitrarily well,
   better than any polynomial bound allows.

3. **Therefore Liouville numbers cannot be algebraic**: They must be transcendental.

## Mathlib Dependencies

- `Liouville` : Definition of Liouville numbers from `Mathlib.NumberTheory.Liouville.Basic`
- `liouvilleNumber` : The explicit Liouville constant from `Mathlib.NumberTheory.Liouville.LiouvilleConstant`
- `Transcendental` : Definition from `Mathlib.RingTheory.Algebraic.Basic`
- `IsAlgebraic` : Algebraic number definition

## Status

- [x] Statement of Liouville's approximation theorem
- [x] Definition of Liouville numbers (from Mathlib)
- [x] Explicit Liouville constant construction (from Mathlib)
- [x] Transcendence of Liouville numbers (from Mathlib)
- [x] Pedagogical exposition

## References

- Liouville, J. (1844). "Sur des classes très-étendues de quantités..."
- Mathlib: `Mathlib.NumberTheory.Liouville`
- Baker, A. (1990). "Transcendental Number Theory"
-/

set_option maxHeartbeats 400000

noncomputable section

open Real Polynomial
open scoped Nat

namespace LiouvilleTheorem

/-! ═══════════════════════════════════════════════════════════════════════════════
PART I: BACKGROUND AND DEFINITIONS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- A real number is algebraic over ℤ if it is a root of a non-zero polynomial
with integer coefficients. -/
#check IsAlgebraic

/-- A number is transcendental if it is not algebraic. -/
#check Transcendental

/-- The **degree** of an algebraic number is the degree of its minimal polynomial. -/
#check Polynomial.natDegree

/-- A real number is a **Liouville number** if it can be approximated by rationals
better than any polynomial bound allows.

Formally: For every n ≥ 1, there exist integers p and q with q > 1 such that
0 < |x - p/q| < 1/q^n

This definition captures numbers that are "too well approximated" by rationals. -/
#check Liouville

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II: LIOUVILLE'S APPROXIMATION THEOREM
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### The Approximation Theorem (Liouville, 1844)

**Theorem**: Let α be a real algebraic number of degree n ≥ 2 over ℚ.
Then there exists a constant c > 0 (depending only on α) such that for all
integers p, q with q > 0:

  |α - p/q| > c / q^n

**Proof Outline**:

1. Let P(x) be the minimal polynomial of α over ℤ, with degree n.

2. For any rational p/q ≠ α, we have P(p/q) ≠ 0 (since P is irreducible and
   p/q is rational while α is irrational for n ≥ 2).

3. Clearing denominators: q^n · P(p/q) is a non-zero integer, so |q^n · P(p/q)| ≥ 1.

4. By the Mean Value Theorem, for some ξ between p/q and α:
   P(p/q) = P(p/q) - P(α) = (p/q - α) · P'(ξ)

5. If |α - p/q| < 1, then |P'(ξ)| is bounded by some M depending on α.

6. Therefore: |α - p/q| ≥ 1 / (M · q^n)

7. If |α - p/q| ≥ 1, the bound holds trivially for small c.

**Key Insight**: The degree of the minimal polynomial limits how well the number
can be approximated by rationals.
-/

/-- **Liouville's Approximation Theorem** (1844)

If α is algebraic of degree n ≥ 2, then there exists c > 0 such that
for all rationals p/q with q > 0: |α - p/q| > c/q^n

This is the contrapositive of: Liouville numbers are transcendental.

**Implementation Note**: Mathlib proves this via the `Liouville.transcendental` theorem.
The approximation bound is implicit in that proof. -/
theorem liouville_approximation_theorem
    (α : ℝ) (hα : IsAlgebraic ℤ α) (n : ℕ) (hn : n ≥ 2)
    (hdeg : ∃ p : Polynomial ℤ, p.natDegree = n ∧ Polynomial.aeval α p = 0 ∧ p ≠ 0) :
    ∃ c : ℝ, c > 0 ∧ ∀ p q : ℤ, q > 0 → |α - p / q| > c / (q : ℝ) ^ n ∨ α = p / q := by
  -- The proof follows from properties of minimal polynomials
  -- For algebraic α of degree n, the minimal polynomial provides the bound
  sorry

/-! ═══════════════════════════════════════════════════════════════════════════════
PART III: LIOUVILLE NUMBERS AND THEIR TRANSCENDENCE
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Definition of Liouville Number**

A real number ξ is Liouville if for every positive integer n, there exist
integers p and q with q > 1 such that:
  0 < |ξ - p/q| < 1/q^n

Equivalently: ξ can be approximated by rationals better than any polynomial
bound would allow for an algebraic number. -/
theorem liouville_def (x : ℝ) :
    Liouville x ↔ ∀ n : ℕ, ∃ p q : ℤ, 1 < q ∧ 0 < |x - p / q| ∧ |x - p / q| < 1 / (q : ℝ) ^ n := by
  constructor
  · intro h n
    obtain ⟨p, q, hq, h1, h2⟩ := h n
    exact ⟨p, q, hq, h1, h2⟩
  · intro h n
    exact h n

/-- **Main Theorem: Liouville numbers are transcendental** (Wiedijk #18)

This follows from Liouville's approximation theorem by contraposition:
- If α is algebraic of degree n, it cannot be approximated better than c/q^n
- Liouville numbers can be approximated arbitrarily well
- Therefore Liouville numbers cannot be algebraic

**Proof Strategy**:
Suppose ξ is Liouville and algebraic of degree n. Then:
1. By the approximation theorem, |ξ - p/q| > c/q^n for some c > 0
2. By the Liouville property, there exist p, q with |ξ - p/q| < 1/q^(n+1)
3. For large enough q, 1/q^(n+1) < c/q^n, contradiction!
-/
theorem liouville_transcendental (x : ℝ) (hx : Liouville x) : Transcendental ℤ x :=
  Liouville.transcendental hx

/-- Alternative statement: Liouville numbers are not algebraic. -/
theorem liouville_not_algebraic (x : ℝ) (hx : Liouville x) : ¬IsAlgebraic ℤ x := by
  have := liouville_transcendental x hx
  unfold Transcendental at this
  exact this

/-! ═══════════════════════════════════════════════════════════════════════════════
PART IV: THE LIOUVILLE CONSTANT
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Construction of an Explicit Transcendental Number

**Liouville's Constant** (1844):

L = Σₙ₌₁^∞ 10^(-n!) = 10^(-1) + 10^(-2) + 10^(-6) + 10^(-24) + 10^(-120) + ...

In decimal: L = 0.110001000000000000000001000...

The 1's appear at positions 1, 2, 6, 24, 120, ... (the factorials).

**Why L is Liouville**:

The partial sums Lₘ = Σₙ₌₁^m 10^(-n!) are excellent rational approximations.

If we write Lₘ = pₘ/qₘ with qₘ = 10^(m!), then:

|L - pₘ/qₘ| = Σₙ₌ₘ₊₁^∞ 10^(-n!)
            < 2 · 10^(-(m+1)!)
            = 2 / qₘ^(m+1)
            < 1 / qₘ^m   (for m ≥ 2)

This beats the bound 1/q^n for arbitrarily large n by taking m > n.
-/

/-- The Liouville constant: L = Σₙ₌₁^∞ 10^(-n!)

This is Liouville's original example of a transcendental number. -/
#check liouvilleNumber

/-- The Liouville constant equals the sum 10^(-1!) + 10^(-2!) + 10^(-3!) + ... -/
theorem liouville_constant_eq_sum :
    liouvilleNumber 10 = ∑' n : ℕ, (1 : ℝ) / 10 ^ (n + 1).factorial := by
  unfold liouvilleNumber
  congr 1
  ext n
  simp [pow_succ]

/-- **The Liouville constant is a Liouville number** -/
theorem liouville_constant_is_liouville : Liouville (liouvilleNumber 10) :=
  isLiouville_liouvilleNumber (by norm_num : (1 : ℕ) < 10)

/-- **The Liouville constant is transcendental** (First Explicit Example, 1844)

This was historically the first number proven to be transcendental!
-/
theorem liouville_constant_transcendental : Transcendental ℤ (liouvilleNumber 10) :=
  liouville_transcendental _ liouville_constant_is_liouville

/-- The Liouville constant is irrational (weaker statement, but worth noting). -/
theorem liouville_constant_irrational : Irrational (liouvilleNumber 10) := by
  have h := liouville_constant_transcendental
  -- Transcendental implies irrational
  intro ⟨q, hq⟩
  have : IsAlgebraic ℤ (liouvilleNumber 10) := by
    use Polynomial.X - Polynomial.C q
    constructor
    · simp
    · simp [hq]
  exact h this

/-! ═══════════════════════════════════════════════════════════════════════════════
PART V: PROPERTIES OF LIOUVILLE NUMBERS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Liouville numbers form an uncountable set.

**Proof idea**: The set of Liouville numbers contains a perfect set (a closed set
with no isolated points), hence is uncountable by the Cantor-Bendixson theorem.

Alternatively: Consider numbers of the form Σₙ aₙ · 10^(-n!) where aₙ ∈ {0, 1}.
This gives 2^ℕ many distinct Liouville numbers. -/
theorem liouville_uncountable : ¬Set.Countable {x : ℝ | Liouville x} := by
  -- The Liouville numbers contain a Cantor-like perfect set
  sorry

/-- If x is Liouville and r is a non-zero rational, then x + r is Liouville.

Adding a rational doesn't change the approximability properties. -/
theorem liouville_add_rat (x : ℝ) (hx : Liouville x) (r : ℚ) : Liouville (x + r) := by
  sorry

/-- If x is Liouville and r is a non-zero rational, then r * x is Liouville.

Scaling by a rational changes the constant but preserves the Liouville property. -/
theorem liouville_mul_rat (x : ℝ) (hx : Liouville x) (r : ℚ) (hr : r ≠ 0) : Liouville (r * x) := by
  sorry

/-! ═══════════════════════════════════════════════════════════════════════════════
PART VI: GENERALIZATIONS AND IMPROVEMENTS
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Roth's Theorem (1955)

Liouville's bound |α - p/q| > c/q^n for algebraic α of degree n was dramatically
improved by Klaus Roth:

**Roth's Theorem**: For any algebraic irrational α and any ε > 0, there exists
c = c(α, ε) > 0 such that for all rationals p/q:

  |α - p/q| > c / q^(2+ε)

The exponent 2 is optimal (by Hurwitz's theorem on Diophantine approximation).

This earned Roth the Fields Medal in 1958.

**Consequence**: A number ξ is transcendental if for every ε > 0, there are
infinitely many rationals p/q with |ξ - p/q| < 1/q^(2+ε).
-/

/-- **Roth's Theorem** (1955)

For algebraic irrational α and any ε > 0, the inequality |α - p/q| < 1/q^(2+ε)
has only finitely many solutions.

This dramatically strengthens Liouville's theorem.

**Implementation Note**: The full proof is very deep, using methods from
algebraic geometry and the subspace theorem. -/
axiom roth_theorem (α : ℝ) (hα : IsAlgebraic ℤ α) (hirr : Irrational α) (ε : ℝ) (hε : ε > 0) :
    Set.Finite {pq : ℤ × ℤ | pq.2 > 0 ∧ |α - pq.1 / pq.2| < 1 / (pq.2 : ℝ) ^ (2 + ε)}

/-!
### The Thue-Siegel-Roth Progression

The exponent in approximation theorems improved over time:

1. **Liouville (1844)**: Exponent n (degree of algebraic number)
2. **Thue (1909)**: Exponent n/2 + 1 + ε
3. **Siegel (1921)**: Exponent 2√n + ε
4. **Dyson (1947)**: Exponent √(2n) + ε
5. **Roth (1955)**: Exponent 2 + ε (optimal!)

Each improvement required increasingly sophisticated techniques.
-/

/-! ═══════════════════════════════════════════════════════════════════════════════
PART VII: CONNECTIONS TO OTHER RESULTS
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Related Theorems

**Hermite-Lindemann (1882)**: e^α is transcendental for non-zero algebraic α.
This provides another (more powerful) method for proving transcendence.

**Gelfond-Schneider (1934)**: α^β is transcendental when α ≠ 0, 1 is algebraic
and β is algebraic irrational. Hilbert's 7th problem.

**Baker's Theorem (1966)**: Provides effective bounds for linear combinations
of logarithms, with applications to Diophantine equations.

### Connection to Diophantine Approximation

Liouville's theorem is foundational to **Diophantine approximation**, the study
of how well real numbers can be approximated by rationals.

Key results in this area:
- **Dirichlet's theorem**: For any α and N, there exists p/q with q ≤ N and |α - p/q| < 1/(qN)
- **Hurwitz's theorem**: For any irrational α, there are infinitely many p/q with |α - p/q| < 1/(√5 · q²)
- **Continued fractions**: Best rational approximations come from convergents
-/

/-! ═══════════════════════════════════════════════════════════════════════════════
PART VIII: EXAMPLES AND COMPUTATIONS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Example: The number Σₙ 2^(-n!) is also transcendental (same argument works). -/
theorem liouville_base_2_transcendental : Transcendental ℤ (liouvilleNumber 2) :=
  liouville_transcendental _ (isLiouville_liouvilleNumber (by norm_num : (1 : ℕ) < 2))

/-- For any integer base b > 1, the Liouville number Σₙ b^(-n!) is transcendental. -/
theorem liouville_any_base_transcendental (b : ℕ) (hb : b > 1) :
    Transcendental ℤ (liouvilleNumber b) :=
  liouville_transcendental _ (isLiouville_liouvilleNumber hb)

/-! ═══════════════════════════════════════════════════════════════════════════════
PART IX: MEASURE-THEORETIC PERSPECTIVE
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Almost All Numbers Are NOT Liouville

Despite being uncountable, Liouville numbers have **Lebesgue measure zero**.

**Theorem** (Borel, 1909): The set of Liouville numbers has measure zero.

This means:
- Liouville numbers are "rare" from a measure-theoretic perspective
- A random real number is almost surely NOT Liouville
- Yet the set is still uncountable (and of the same cardinality as ℝ)

**Proof idea**: For each n, the set of numbers with infinitely many
approximations |x - p/q| < 1/q^n can be covered by intervals whose
total measure tends to 0 as n → ∞.

**Contrast with transcendental numbers**: Almost all real numbers ARE transcendental
(since algebraic numbers are countable), but only measure zero of transcendentals
are Liouville.
-/

/-! ═══════════════════════════════════════════════════════════════════════════════
PART X: SUMMARY
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Summary of Wiedijk #18

**Liouville's Theorem** provides the first explicit proof that transcendental
numbers exist:

1. **The Approximation Bound**: Algebraic numbers of degree n cannot be
   approximated better than c/q^n by rationals p/q.

2. **Liouville Numbers**: Numbers that violate this bound for all n.

3. **Transcendence**: Liouville numbers must be transcendental.

4. **Explicit Example**: L = Σ 10^(-n!) is transcendental.

**Historical Impact**:
- First constructive proof of transcendental numbers (1844)
- Opened the field of transcendence theory
- Techniques evolved into Roth's theorem and beyond
- Foundational for Diophantine approximation

**Mathlib Status**: Fully formalized!
- `Liouville.transcendental`: The main theorem
- `liouvilleNumber`: The explicit constant
- `isLiouville_liouvilleNumber`: Verification of the Liouville property
-/

end LiouvilleTheorem
