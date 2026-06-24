import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Tactic
import Proofs.Hilbert17MotzkinNotSOS
import Proofs.Hilbert17RobinsonNotSOS
import Proofs.Hilbert17UnivariatePSDSOS

/-!
# Hilbert's 17th Problem: Sum of Squares Representation

## What This Proves

**Hilbert's 17th Problem** (1900): Is every non-negative polynomial a sum of squares?

**Resolution (Artin 1927)**: Yes, but as a sum of squares of *rational functions*, not polynomials!

## The Main Theorem

**Artin's Theorem**: If f ∈ ℝ[X₁,...,Xₙ] and f(x) ≥ 0 for all x ∈ ℝⁿ, then f is a sum of
squares of elements in the rational function field ℝ(X₁,...,Xₙ).

## The Critical Distinction

NOT every non-negative polynomial is a sum of squares of *polynomials*:

**Motzkin's Polynomial (1967)**: M(x,y) = x⁴y² + x²y⁴ - 3x²y² + 1

This polynomial:
- Is non-negative on all of ℝ² (can verify by calculus/AM-GM)
- Is NOT a sum of squares of polynomials (degree argument)
- IS a sum of squares of rational functions (by Artin's theorem)

## Historical Context

- **1888**: Hilbert showed that non-negative forms need NOT be sums of squares of polynomials
  (existence proof, no explicit example)
- **1900**: Hilbert posed Problem 17: Are they at least sums of squares of rational functions?
- **1927**: Artin answered affirmatively using the theory of real closed fields
- **1967**: Motzkin gave the first explicit non-SOS polynomial example

## Why Rational Functions Are Necessary

The key insight is that the degree of a sum of squares of polynomials must be even,
and each squared term contributes positively to the leading form. For certain
non-negative polynomials like Motzkin's, the structure of the leading terms prevents
writing them as polynomial SOS.

Allowing rational functions g²/h² = (g/h)² provides more flexibility.

## Approach

- **Foundation**: Real closed field theory from Mathlib (`IsRealClosed`)
- **Original Contributions**: Statement of Artin's theorem, Motzkin counterexample,
  pedagogical exposition of why the distinction matters
- **Proof Techniques**: Model-theoretic transfer, real algebraic geometry

## Status

- [x] Artin's theorem stated precisely
- [x] Motzkin counterexample for polynomial SOS
- [x] Connection to real closed fields
- [x] Explanation of why rational functions are needed
- [x] Pedagogical example
- [x] Motzkin and Robinson non-negativity machine-checked (nlinarith; AM-GM / Schur)
- [ ] Incomplete (4 axioms - full proof requires model theory and real algebraic geometry).
      Artin's general existence, the univariate rational-function case, and Cassels'
      bivariate bound are now *derived* from the four foundational axioms, not assumed.

## Mathlib Dependencies

- `RatFunc` : Rational function fields
- `IsRealClosed` : Real closed field theory (when available)
- `Polynomial` : Polynomial rings

## Hilbert's 23 Problems Context

This is Problem 17 from Hilbert's famous 1900 list. It was solved by Emil Artin
in 1927 as an application of his theory of formally real fields and real closures.

## References

- Artin, E. (1927). "Über die Zerlegung definiter Funktionen in Quadrate"
- Motzkin, T.S. (1967). "The arithmetic-geometric inequality"
- Pfister, A. (1967). "Zur Darstellung definiter Funktionen als Summe von Quadraten"
-/

set_option maxHeartbeats 400000

noncomputable section

open Polynomial RatFunc

namespace Hilbert17

/-! ═══════════════════════════════════════════════════════════════════════════════
PART I: BASIC DEFINITIONS
═══════════════════════════════════════════════════════════════════════════════ -/

variable (n : ℕ)

-- A multivariate polynomial over ℝ in n variables is `MvPolynomial (Fin n) ℝ`
#check MvPolynomial (Fin n) ℝ

-- The rational function field over ℝ in one variable.
-- For multivariate, we use `RatFunc (MvPolynomial ...)`.
#check RatFunc ℝ

/-! ### Sum of Squares Definitions -/

/-- A polynomial is a *sum of squares of polynomials* (SOS) if it can be written as
    p = q₁² + q₂² + ... + qₘ² for some polynomials qᵢ. -/
def IsSumOfSquaresPolynomial {R : Type*} [Ring R] (p : Polynomial R) : Prop :=
  ∃ (m : ℕ) (q : Fin m → Polynomial R), p = ∑ i, q i ^ 2

/-- A multivariate polynomial is SOS if it can be written as a sum of squared polynomials. -/
def IsSumOfSquaresMvPolynomial {R : Type*} [CommRing R] {σ : Type*}
    (p : MvPolynomial σ R) : Prop :=
  ∃ (m : ℕ) (q : Fin m → MvPolynomial σ R), p = ∑ i, q i ^ 2

/-- A rational function is a *sum of squares of rational functions* if it can be written as
    f = g₁² + g₂² + ... + gₘ² for some rational functions gᵢ. -/
def IsSumOfSquaresRatFunc {R : Type*} [CommRing R] [IsDomain R]
    (f : RatFunc R) : Prop :=
  ∃ (m : ℕ) (g : Fin m → RatFunc R), f = ∑ i, g i ^ 2

/-! ### Positive Semidefinite (PSD) Definitions -/

/-- A univariate polynomial is *positive semidefinite* (PSD) if it is non-negative
    for all real inputs. -/
def IsPositiveSemidefinite (p : Polynomial ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ p.eval x

/-- A multivariate polynomial is PSD if it is non-negative for all real inputs. -/
def IsPositiveSemidefiniteMv {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, 0 ≤ MvPolynomial.eval x p

/-! ═══════════════════════════════════════════════════════════════════════════════
FOUNDATIONAL AXIOMS

The deep, independent assumptions of this development. The pedagogical theorems
below (`artin_hilbert17`, `artin_univariate`, `cassels_bound_bivariate`) are NOT
independent axioms — they are *derived* from these. They are stated up front so
the derivations downstream typecheck regardless of presentation order.

Independent assumptions:
  • `pfister_bound_aux` — Pfister's 2ⁿ bound; the general Artin existence
    (`artin_hilbert17`) and Cassels' bivariate bound are specializations of it.

(`univariate_psd_is_sos_aux`, formerly an axiom, is now a fully machine-checked
theorem — see `Proofs/Hilbert17UnivariatePSDSOS.lean`.)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Univariate PSD is Polynomial-SOS** (Hilbert 1888, univariate case).

    Every univariate PSD polynomial is a sum of squares of polynomials — in fact
    a sum of just two squares.  The full elementary, 0-axiom proof lives in
    `Proofs/Hilbert17UnivariatePSDSOS.lean`
    (`Hilbert17UnivariatePSDSOS.univariate_psd_is_sos`): strong induction on the
    degree, factoring out either `(X - C r)²` at a real root (which a non-negative
    polynomial must have to even multiplicity) or a positive real quadratic at a
    conjugate pair of complex roots, recombined via the Brahmagupta–Fibonacci
    identity.  The parent's `IsPositiveSemidefinite` / `IsSumOfSquaresPolynomial`
    are definitionally equal to the child's predicates, so the proof transfers by
    `exact`.

    (Formerly the axiom `univariate_psd_is_sos_aux`; now fully machine-checked.) -/
theorem univariate_psd_is_sos_aux (p : Polynomial ℝ) (h : IsPositiveSemidefinite p) :
    IsSumOfSquaresPolynomial p :=
  Hilbert17UnivariatePSDSOS.univariate_psd_is_sos p h

/-- **Axiom: Pfister's Bound** (Pfister 1967).

    At most `2ⁿ` squares of rational functions suffice to represent any PSD
    polynomial in `n` variables. The proof uses Pfister forms and properties of
    sums of squares in formally real fields; the bound is optimal in general.

    Axiomatized pending the theory of Pfister forms. The general existence
    theorem `artin_hilbert17` and `cassels_bound_bivariate` (n = 2) are both
    specializations of this bound. -/
axiom pfister_bound_aux (n : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (h : IsPositiveSemidefiniteMv p) :
    ∃ (g : Fin (2^n) → RatFunc (MvPolynomial (Fin n) ℝ)),
      (algebraMap _ _ p : RatFunc _) = ∑ i, g i ^ 2

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II: ARTIN'S THEOREM - THE MAIN RESULT
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Artin's Theorem (Hilbert's 17th Problem Solution)**

    Every non-negative polynomial (in any number of variables) over ℝ is a sum of
    squares of rational functions.

    This is the affirmative answer to Hilbert's 17th Problem.

    **Key Points**:
    - The polynomial must be non-negative for ALL real inputs
    - The result is a sum of squares of RATIONAL FUNCTIONS, not polynomials
    - The proof uses real closed field theory and model-theoretic transfer

    **Proof Outline** (Artin 1927):
    1. Consider the ordered field ℝ(X₁,...,Xₙ) of rational functions
    2. If p is not SOS, there exists an ordering making p negative
    3. This ordering extends to the real closure
    4. But p is non-negative at all real points
    5. By transfer from real closed fields, contradiction!

    **Implementation Note**: Not an independent axiom — the *existence* of a
    rational-function SOS representation follows directly from Pfister's bound
    (`pfister_bound_aux`), which moreover gives the explicit count `2ⁿ`. We take
    `m := 2ⁿ`. -/
theorem artin_hilbert17 :
    ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ),
      IsPositiveSemidefiniteMv p →
      ∃ (m : ℕ) (g : Fin m → RatFunc (MvPolynomial (Fin n) ℝ)),
        (algebraMap _ _ p : RatFunc (MvPolynomial (Fin n) ℝ)) = ∑ i, g i ^ 2 :=
  fun n p h => ⟨2 ^ n, pfister_bound_aux n p h⟩

/-- **Univariate Case**: For univariate polynomials, PSD implies SOS as rational
    functions. Not an independent axiom — this is the rational-function shadow of
    the stronger polynomial result `univariate_psd_is_sos_aux`: if `p = ∑ qᵢ²`
    as polynomials, then `algebraMap p = ∑ (algebraMap qᵢ)²` in `RatFunc ℝ`. -/
theorem artin_univariate (p : Polynomial ℝ) (h : IsPositiveSemidefinite p) :
    IsSumOfSquaresRatFunc (algebraMap _ _ p : RatFunc ℝ) := by
  obtain ⟨m, q, hpq⟩ := univariate_psd_is_sos_aux p h
  refine ⟨m, fun i => algebraMap _ _ (q i), ?_⟩
  rw [hpq, map_sum]
  simp_rw [map_pow]

/-! ═══════════════════════════════════════════════════════════════════════════════
PART III: THE MOTZKIN POLYNOMIAL - A COUNTEREXAMPLE FOR POLYNOMIAL SOS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The **Motzkin Polynomial** (1967):
    M(x,y) = x⁴y² + x²y⁴ - 3x²y² + 1

    This is the simplest known example of a polynomial that is:
    - Non-negative everywhere on ℝ²
    - NOT a sum of squares of polynomials

    Named after Theodore Motzkin who gave this explicit example. -/
def motzkin : MvPolynomial (Fin 2) ℝ :=
  let x := MvPolynomial.X (0 : Fin 2)
  let y := MvPolynomial.X (1 : Fin 2)
  x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2 + 1

/-- **The Motzkin Polynomial is Non-Negative** (axiom-free).

    M(x,y) = x⁴y² + x²y⁴ - 3x²y² + 1 ≥ 0 for all (x,y) ∈ ℝ².

    **Proof.** The AM–GM step `x⁴y² + x²y⁴ + 1 ≥ 3x²y²` is a polynomial
    inequality that `nlinarith` discharges from the square hints
    `(x²y² - 1)²`, `(x²y - y)²`, `(xy² - x)² ≥ 0` together with `x²y² ≥ 0`.
    (Formerly the axiom `motzkin_nonneg_aux`; now fully machine-checked.) -/
theorem motzkin_nonneg : IsPositiveSemidefiniteMv motzkin := by
  intro v
  simp only [motzkin, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    MvPolynomial.eval_X]
  set x := v 0
  set y := v 1
  nlinarith [sq_nonneg (x * y - 1), sq_nonneg (x ^ 2 * y - y),
    sq_nonneg (x * y ^ 2 - x), sq_nonneg (x * y),
    mul_nonneg (sq_nonneg x) (sq_nonneg y), sq_nonneg (x ^ 2 * y ^ 2 - 1)]

/-- **Axiom: Motzkin Not Polynomial-SOS**

    The Motzkin polynomial cannot be written as a sum of squares of polynomials.

    The proof uses a degree analysis argument:
    1. M has total degree 6
    2. If M = Σᵢ pᵢ², each pᵢ has degree ≤ 3
    3. The degree-6 part x⁴y² + x²y⁴ = x²y²(x² + y²) cannot arise from
       squaring degree-3 homogeneous polynomials in 2 variables

    The full elementary proof lives in `Proofs/Hilbert17MotzkinNotSOS.lean`
    (`Hilbert17MotzkinNotSOS.motzkin_not_sos`, 0-axiom): a degree/coefficient
    argument showing each `qᵢ` has total degree ≤ 3, that all pure-axis powers
    of `x` and `y` of degrees 1–3 vanish in every `qᵢ`, and hence the `[x²y²]`
    coefficient of `Σ qᵢ²` is `Σ ([xy]qᵢ)² ≥ 0`, contradicting `[x²y²]M = -3`. -/
theorem motzkin_not_sos_polynomial : ¬ IsSumOfSquaresMvPolynomial motzkin := by
  -- `IsSumOfSquaresMvPolynomial motzkin` and `Hilbert17MotzkinNotSOS.IsSOS
  -- Hilbert17MotzkinNotSOS.motzkin` are definitionally equal (the two `motzkin`
  -- definitions and the two SOS predicates unfold to the same expression), so
  -- the elementary theorem discharges the parent statement directly.
  intro h
  exact Hilbert17MotzkinNotSOS.motzkin_not_sos h

/-- **By Artin's Theorem, Motzkin IS a Sum of Squares of Rational Functions**

    Even though M(x,y) is not polynomial-SOS, Artin guarantees it IS
    rational-function-SOS. An explicit representation exists but is complicated. -/
theorem motzkin_sos_ratfunc :
    ∃ (m : ℕ) (g : Fin m → RatFunc (MvPolynomial (Fin 2) ℝ)),
      (algebraMap _ _ motzkin : RatFunc _) = ∑ i, g i ^ 2 := by
  have h := motzkin_nonneg
  exact artin_hilbert17 2 motzkin h

/-! ═══════════════════════════════════════════════════════════════════════════════
PART IV: HILBERT'S 1888 RESULT - WHEN PSD = SOS (FOR POLYNOMIALS)
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Hilbert's 1888 Classification

Hilbert proved that PSD polynomials are sums of squares of polynomials
if and only if ONE of the following holds:

1. n = 1 (univariate polynomials of any degree)
2. n = 2 (bivariate) and degree d = 2 (quadratic forms)
3. d = 2 (quadratic forms) for any number of variables
4. n = 2 and d = 4 (bivariate quartics)

In ALL other cases, there exist PSD polynomials that are not polynomial-SOS.

This remarkable result was non-constructive - Hilbert proved existence without
giving explicit examples. Motzkin (1967) gave the first explicit counterexample.
-/

/- Note: the univariate PSD ⇒ polynomial-SOS statement is the foundational axiom
   `univariate_psd_is_sos_aux` declared near the top of this file (via complex
   factorization: real roots have even multiplicity, complex roots come in
   conjugate pairs). The wrapper below re-exports it under its pedagogical name. -/

/-- **Case 1: Univariate PSD polynomials ARE polynomial-SOS**

    If p(x) ∈ ℝ[x] and p(x) ≥ 0 for all x ∈ ℝ, then p = q₁² + q₂²
    for some polynomials q₁, q₂ ∈ ℝ[x].

    **Proof Idea**: Factor over ℂ. Complex roots come in conjugate pairs.
    Real roots have even multiplicity. Combine factors appropriately. -/
theorem univariate_psd_is_sos (p : Polynomial ℝ) (h : IsPositiveSemidefinite p) :
    IsSumOfSquaresPolynomial p := univariate_psd_is_sos_aux p h

/-- **Axiom: Quadratic PSD is Polynomial-SOS**

    Every quadratic form that is PSD can be written as a sum of squares of linear forms.

    The proof uses the Gram matrix approach:
    - Write Q(x) = x^T A x for symmetric matrix A
    - Q >= 0 everywhere iff A is positive semidefinite
    - A positive semidefinite iff A = B^T B for some matrix B
    - This gives Q = ||Bx||^2, a sum of squares of linear forms

    Axiomatized because the proof requires:
    - Correspondence between quadratic polynomials and symmetric matrices
    - Spectral theorem / Cholesky decomposition for PSD matrices
    - Matrix algebra and polynomial evaluation

    PROGRESS: the *matrix-level* heart of this argument is now proved with
    zero axioms in `Proofs.Hilbert17QuadraticGram`
    (`Hilbert17.posSemidef_quadratic_isSumSq`): for a PSD real matrix `M`,
    `x ⬝ᵥ (M *ᵥ x) = ∑ i, ((√M *ᵥ x) i)²`, an explicit SOS of linear forms via
    the symmetric Gram factorization `M = (√M)ᵀ (√M)`.  What remains (the
    un-Mathlib'd "bridge") is the polynomial coefficient-extraction
    `Q ↦ M` for `totalDegree Q = 2` and the homogenisation/PSD transfer; see
    `research/problems/hilbert-17-oq-03/knowledge.md`. -/
axiom quadratic_psd_is_sos_aux {n : ℕ} (Q : MvPolynomial (Fin n) ℝ)
    (hQ : MvPolynomial.totalDegree Q = 2)
    (h : IsPositiveSemidefiniteMv Q) :
    IsSumOfSquaresMvPolynomial Q

/-- **Case 2: Quadratic forms that are PSD are polynomial-SOS**

    This is the "Gram matrix" approach: if Q(x) = x^T A x for symmetric A,
    then Q >= 0 iff A is positive semidefinite.
    And A is PSD iff A = B^T B for some B, giving Q = ||Bx||^2. -/
theorem quadratic_psd_is_sos {n : ℕ} (Q : MvPolynomial (Fin n) ℝ)
    (hQ : MvPolynomial.totalDegree Q = 2)
    (h : IsPositiveSemidefiniteMv Q) :
    IsSumOfSquaresMvPolynomial Q := quadratic_psd_is_sos_aux Q hQ h

/-! ═══════════════════════════════════════════════════════════════════════════════
PART V: QUANTITATIVE BOUNDS - PFISTER'S THEOREM
═══════════════════════════════════════════════════════════════════════════════ -/

/- Note: Pfister's 2ⁿ bound is the foundational axiom `pfister_bound_aux` declared
   near the top of this file. The wrapper below re-exports it under its pedagogical
   name. -/

/-- **Pfister's Theorem on the Number of Squares**

    In Artin's theorem, how many squares are needed?

    **Pfister (1967)**: At most 2^n squares suffice for polynomials in n variables.

    This is optimal in general, though specific polynomials may need fewer.

    The proof uses Pfister forms and properties of quadratic forms over
    formally real fields. -/
theorem pfister_bound (n : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (h : IsPositiveSemidefiniteMv p) :
    ∃ (g : Fin (2^n) → RatFunc (MvPolynomial (Fin n) ℝ)),
      (algebraMap _ _ p : RatFunc _) = ∑ i, g i ^ 2 := pfister_bound_aux n p h

/-- **Cassels' Bound**: For bivariate (n=2), at most 4 = 2² squares are needed.

    Not an independent axiom — a direct specialization of Pfister's bound at
    `n = 2`, since `2² = 4` definitionally, so `pfister_bound_aux 2` already has
    the required type `Fin 4 → RatFunc …`. -/
theorem cassels_bound_bivariate (p : MvPolynomial (Fin 2) ℝ)
    (h : IsPositiveSemidefiniteMv p) :
    ∃ (g : Fin 4 → RatFunc (MvPolynomial (Fin 2) ℝ)),
      (algebraMap _ _ p : RatFunc _) = ∑ i, g i ^ 2 := pfister_bound_aux 2 p h

/-! ═══════════════════════════════════════════════════════════════════════════════
PART VI: CONNECTION TO REAL CLOSED FIELDS
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Real Closed Fields and Artin's Proof

A field R is *real closed* if:
1. R is formally real (−1 is not a sum of squares)
2. R has no proper formally real algebraic extension

Equivalently, R is real closed iff:
- Every positive element is a square
- Every odd-degree polynomial has a root
- The algebraic closure has degree 2 over R

**Artin's Key Insight**: The real numbers ℝ are real closed.
Every ordered field embeds into a real closed field (its real closure).
Model-theoretic transfer between real closed fields proves Hilbert 17.

Mathlib has `IsRealClosed` for fields satisfying these properties.
-/

-- Note: Mathlib's real closed field theory is in development.
-- The reals form a real closed field (IsRealClosed ℝ) — a key fact enabling Artin's proof.
-- The Transfer Principle (statements about polynomial inequalities holding in all real closed
-- fields) would require ordered field structure to formalize.

/-! ═══════════════════════════════════════════════════════════════════════════════
PART VII: MODERN APPLICATIONS
═══════════════════════════════════════════════════════════════════════════════ -/

section Applications

/-!
### Sum of Squares Programming

Hilbert's 17th Problem has modern applications in optimization:

**SOS Programming**: Given polynomial constraints, find a certificate of non-negativity.

- If p is polynomial-SOS, we can find the decomposition via *semidefinite programming*
- This is tractable: reduce to SDP in polynomial time
- Used in control theory, robotics, verification

**Limitation**: Not all PSD polynomials are polynomial-SOS (Motzkin!), so SOS
certificates don't always exist. But for many practical problems they do.

### Real Algebraic Geometry

The study of real polynomial equations and inequalities:

- **Positivstellensatz**: Characterizes when a polynomial system has no real solutions
  via SOS certificates involving the constraints
- **Stengle's theorem**: Full characterization with products of constraints
- **Schmüdgen's theorem**: For compact sets, simpler certificates exist

### Formal Verification

SOS methods are used to verify:
- Stability of dynamical systems
- Invariants of programs
- Safety of control systems

The connection to Hilbert 17 explains when these methods work.
-/

end Applications

/-! ═══════════════════════════════════════════════════════════════════════════════
PART VIII: ADDITIONAL COUNTEREXAMPLES
═══════════════════════════════════════════════════════════════════════════════ -/

section Counterexamples

/-- **Robinson's Polynomial** (1973):
    R(x,y,z) = x⁶ + y⁶ + z⁶ - x⁴y² - y⁴z² - z⁴x² - x²y⁴ - y²z⁴ - z²x⁴ + 3x²y²z²

    Another PSD polynomial that is not polynomial-SOS. -/
def robinson : MvPolynomial (Fin 3) ℝ :=
  let x := MvPolynomial.X (0 : Fin 3)
  let y := MvPolynomial.X (1 : Fin 3)
  let z := MvPolynomial.X (2 : Fin 3)
  x^6 + y^6 + z^6
  - x^4*y^2 - y^4*z^2 - z^4*x^2
  - x^2*y^4 - y^2*z^4 - z^2*x^4
  + 3*x^2*y^2*z^2

/-- **Robinson's polynomial is non-negative** (axiom-free).

    R(x,y,z) = x⁶ + y⁶ + z⁶ - x⁴y² - y⁴z² - z⁴x² - x²y⁴ - y²z⁴ - z²x⁴ + 3x²y²z² ≥ 0.

    **Proof.** With `a = x², b = y², c = z² ≥ 0`, `R` is precisely Schur's
    expression `a(a-b)(a-c) + b(b-a)(b-c) + c(c-a)(c-b)`, nonnegative by Schur's
    inequality. `nlinarith` finds the certificate from the hints
    `a·(a-b)² , b·(b-c)² , c·(c-a)² , …  ≥ 0` and `a·b·c ≥ 0`.
    (Formerly the axiom `robinson_nonneg_aux`; now fully machine-checked.) -/
theorem robinson_nonneg : IsPositiveSemidefiniteMv robinson := by
  intro v
  simp only [robinson, map_add, map_sub, map_mul, map_pow, map_ofNat,
    MvPolynomial.eval_X]
  set x := v 0
  set y := v 1
  set z := v 2
  have ha : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  have hb : (0 : ℝ) ≤ y ^ 2 := sq_nonneg y
  have hc : (0 : ℝ) ≤ z ^ 2 := sq_nonneg z
  nlinarith [mul_nonneg ha (sq_nonneg (x ^ 2 - y ^ 2)),
    mul_nonneg hb (sq_nonneg (y ^ 2 - z ^ 2)),
    mul_nonneg hc (sq_nonneg (z ^ 2 - x ^ 2)),
    mul_nonneg ha (sq_nonneg (x ^ 2 - z ^ 2)),
    mul_nonneg hb (sq_nonneg (x ^ 2 - y ^ 2)),
    mul_nonneg hc (sq_nonneg (y ^ 2 - z ^ 2)),
    mul_nonneg (mul_nonneg ha hb) hc]

/-- **Robinson's polynomial is not polynomial-SOS** (axiom-free).

    Robinson's polynomial cannot be written as a sum of squares of polynomials,
    despite being non-negative everywhere.

    The full elementary proof lives in `Proofs/Hilbert17RobinsonNotSOS.lean`
    (`Hilbert17RobinsonNotSOS.robinson_not_sos`, 0-axiom): in `R = Σ qᵢ²` each
    `qᵢ` has total degree ≤ 3, so taking the degree-6 homogeneous component gives
    `R = Σ (qᵢ⁽³⁾)²` with each `qᵢ⁽³⁾` a homogeneous cubic form; these vanish at
    `R`'s ten real projective zeros, and the 10×10 evaluation matrix of cubic
    monomials at those points has determinant `128 ≠ 0`, so every `qᵢ⁽³⁾ = 0`,
    forcing `R = 0` — contradicting `R(1,0,0) = 1`.
    (Formerly the axiom `robinson_not_sos_aux`; now fully machine-checked.) -/
theorem robinson_not_sos : ¬ IsSumOfSquaresMvPolynomial robinson := by
  -- `IsSumOfSquaresMvPolynomial robinson` and `Hilbert17RobinsonNotSOS.IsSOS
  -- Hilbert17RobinsonNotSOS.robinson` are definitionally equal (the two
  -- `robinson` definitions and the two SOS predicates unfold to the same
  -- expression), so the elementary theorem discharges the parent statement.
  intro h
  exact Hilbert17RobinsonNotSOS.robinson_not_sos h

/-- **Choi-Lam Polynomial**: Another family of counterexamples.
    CL(w,x,y,z) = w⁴ + x²y² + y²z² + z²w² - 4wxyz -/
def choi_lam : MvPolynomial (Fin 4) ℝ :=
  let w := MvPolynomial.X (0 : Fin 4)
  let x := MvPolynomial.X (1 : Fin 4)
  let y := MvPolynomial.X (2 : Fin 4)
  let z := MvPolynomial.X (3 : Fin 4)
  w^4 + x^2*y^2 + y^2*z^2 + z^2*w^2 - 4*w*x*y*z

end Counterexamples

/-! ═══════════════════════════════════════════════════════════════════════════════
PART IX: SUMMARY
═══════════════════════════════════════════════════════════════════════════════ -/

#check artin_hilbert17
#check motzkin
#check motzkin_nonneg
#check motzkin_not_sos_polynomial
#check motzkin_sos_ratfunc
#check univariate_psd_is_sos
#check pfister_bound

/-!
## Summary

**Hilbert's 17th Problem** asked whether every non-negative polynomial is a sum of squares.

**Answer (Artin 1927)**: YES, but as rational functions, not polynomials!

**Key Results**:
1. `artin_hilbert17`: PSD → SOS of rational functions
2. `motzkin_not_sos_polynomial`: The Motzkin polynomial is PSD but not polynomial-SOS
3. `univariate_psd_is_sos`: Univariate case: PSD → polynomial-SOS (2 squares suffice)
4. `pfister_bound`: At most 2ⁿ squares needed in n variables

**The Distinction Matters**:
- For optimization/verification: polynomial-SOS → tractable SDP
- For theory: rational-SOS always exists (Artin)
- For practice: many "reasonable" polynomials are polynomial-SOS

This is #17 on Hilbert's famous list of 23 problems from 1900.
-/

end Hilbert17
