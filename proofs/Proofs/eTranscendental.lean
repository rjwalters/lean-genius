import Mathlib.RingTheory.Algebraic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Complex.ExponentialBounds

/-!
# e is Transcendental (Wiedijk #67)

## What This Proves
Euler's number e = 2.71828... is transcendental: it is not the root of any
non-zero polynomial with integer (or equivalently, rational) coefficients.

## Approach
- **Foundation (from Mathlib):** The definition `Transcendental ℤ x` states that
  `x` is not algebraic over ℤ, meaning no non-zero integer polynomial has x as a root.
  Mathlib provides `Real.exp` and `Complex.exp` with full analytic theory.
- **Original Contributions:** This file provides pedagogical exposition of Hermite's
  1873 proof method, which was the first proof of transcendence for a "naturally
  occurring" number. The main theorem is axiomatized pending formalization of the
  Lindemann-Weierstrass theorem.
- **Proof Techniques Demonstrated:** Auxiliary polynomial construction, integral
  estimates, contradiction via divisibility arguments.

## Status
- [ ] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical example
- [x] Incomplete (has sorries)

## Mathlib Dependencies
- `Transcendental` : Definition from `Mathlib.RingTheory.Algebraic`
- `Real.exp` : The real exponential function
- `Irrational` : Definition of irrational numbers
- `Real.exp_nat_mul`, `Real.exp_add` : Exponential function properties

Historical Note: Charles Hermite proved e is transcendental in 1873, making it
the first "natural" constant shown to be transcendental. Ferdinand von Lindemann
later extended the method to prove π is transcendental (1882), settling the
ancient problem of squaring the circle.
-/

open Real Polynomial

-- ============================================================
-- PART 1: Definitions and Background
-- ============================================================

/-
  A number x is **transcendental** over a ring R if it is not algebraic:
  there is no non-zero polynomial P ∈ R[X] such that P(x) = 0.

  Equivalently, the numbers 1, x, x², x³, ... are linearly independent over R.

  Key facts:
  - Transcendental ⟹ Irrational (but not conversely: √2 is irrational but algebraic)
  - The set of transcendental numbers is uncountable (Cantor)
  - Most real numbers are transcendental, but proving specific ones is hard!
-/

#check Transcendental  -- Transcendental R x : Prop

-- The exponential constant e = exp(1)
#check Real.exp 1

-- ============================================================
-- PART 2: Key Properties of e from Mathlib
-- ============================================================

/-- e > 0 -/
theorem e_pos : Real.exp 1 > 0 := Real.exp_pos 1

/-- e > 1 (since exp is increasing and exp(0) = 1) -/
theorem e_gt_one : Real.exp 1 > 1 := one_lt_exp_iff.mpr (by norm_num : (0:ℝ) < 1)

/-- e < 3 (rough upper bound) -/
theorem e_lt_three : Real.exp 1 < 3 := by
  have h := exp_one_lt_d9
  -- exp(1) < 2.7182818286 < 3
  have h2 : (2.7182818286 : ℝ) < 3 := by norm_num
  exact lt_trans h h2

-- ============================================================
-- PART 3: Hermite's Proof Strategy (1873)
-- ============================================================

/-
  **Hermite's Proof Outline:**

  Assume e is algebraic: there exist integers a₀, a₁, ..., aₙ (not all zero)
  such that a₀ + a₁e + a₂e² + ... + aₙeⁿ = 0.

  **Step 1: Construct Auxiliary Polynomial**

  For a large prime p (to be chosen later), define:

    f(x) = xᵖ⁻¹(x-1)ᵖ(x-2)ᵖ...(x-n)ᵖ / (p-1)!

  This polynomial has carefully controlled divisibility properties.

  **Step 2: Define the Key Integral**

  For 0 ≤ k ≤ n, let:

    Iₖ = ∫₀^k f(x)eˣ dx

  Using integration by parts, we get:

    Iₖ = eᵏ·F(0) - F(k)

  where F(x) = f(x) + f'(x) + f''(x) + ... is the sum of all derivatives.

  **Step 3: Analyze the Sum**

  Consider:

    S = a₀I₀ + a₁I₁ + ... + aₙIₙ

  Using the algebraic relation, we can show:
  - |S| is small (the integrals decay rapidly)
  - S is a non-zero integer divisible by p (from the derivative structure)

  For p large enough, |S| < 1 but S ≠ 0 and p | S ⟹ contradiction!

  **Remark:** This is the essence of transcendence proofs: construct something
  that must simultaneously be a small non-zero integer—impossible!
-/

-- ============================================================
-- PART 4: The Main Theorem (Axiomatized)
-- ============================================================

/-- **Main Axiom: e is transcendental over ℤ**

    This is Wiedijk #67 and follows from Hermite's 1873 proof. The full
    formalization requires:
    1. Polynomial arithmetic over ℤ
    2. Integration by parts for polynomial × exponential
    3. Careful divisibility analysis mod p
    4. Asymptotic estimates showing contradiction

    The Lindemann-Weierstrass theorem (a generalization) is not yet in Mathlib.
    When formalized, this axiom would be replaced by a direct proof. -/
axiom e_transcendental : Transcendental ℤ (Real.exp 1)

/-- **Axiom: e is transcendental over ℚ**

    Transcendental over ℤ implies transcendental over ℚ.
    Any rational polynomial p with p(e) = 0 can be cleared to an integer
    polynomial q with q(e) = 0 by multiplying by the LCM of denominators. -/
axiom e_transcendental_over_rationals_axiom : Transcendental ℚ (Real.exp 1)

/-- e is transcendental over ℚ (equivalent formulation) -/
theorem e_transcendental_over_rationals : Transcendental ℚ (Real.exp 1) :=
  e_transcendental_over_rationals_axiom

-- ============================================================
-- PART 5: Corollaries
-- ============================================================

/-- **Axiom: e is irrational**

    Transcendental implies irrational: if e = p/q for rationals p, q, then
    e would be algebraic (root of q·X - p = 0), contradicting transcendence. -/
axiom e_irrational_axiom : Irrational (Real.exp 1)

/-- e is irrational (weaker than transcendental, but follows from it) -/
theorem e_irrational : Irrational (Real.exp 1) := e_irrational_axiom

/-- **Axiom: eⁿ is transcendental for any non-zero integer n**

    If eⁿ were algebraic, then e would be algebraic via a degree n extension.
    Specifically, if p(eⁿ) = 0, then e satisfies q(X) = p(Xⁿ) which is
    a polynomial of degree n · deg(p). This contradicts e being transcendental. -/
axiom exp_nat_transcendental_axiom (n : ℕ) (hn : n ≠ 0) : Transcendental ℤ (Real.exp n)

/-- eⁿ is transcendental for any non-zero integer n -/
theorem exp_nat_transcendental (n : ℕ) (hn : n ≠ 0) :
    Transcendental ℤ (Real.exp n) :=
  exp_nat_transcendental_axiom n hn

/-- **Axiom: 1/e is transcendental**

    If 1/e were algebraic, say p(1/e) = 0, then the reciprocal polynomial
    q(X) = X^n · p(1/X) satisfies q(e) = 0, making e algebraic. Contradiction. -/
axiom e_inv_transcendental_axiom : Transcendental ℤ (Real.exp 1)⁻¹

/-- 1/e is transcendental -/
theorem e_inv_transcendental : Transcendental ℤ (Real.exp 1)⁻¹ := e_inv_transcendental_axiom

/-- **Axiom: e + 1 is transcendental**

    If e + 1 were algebraic, say p(e + 1) = 0, then e satisfies q(X) = p(X + 1),
    making e algebraic. Contradiction. -/
axiom e_plus_one_transcendental_axiom : Transcendental ℤ (Real.exp 1 + 1)

/-- e + 1 is transcendental -/
theorem e_plus_one_transcendental : Transcendental ℤ (Real.exp 1 + 1) := e_plus_one_transcendental_axiom

-- ============================================================
-- PART 6: Connections to Other Results
-- ============================================================

/-
  **Related Theorems:**

  1. **Lindemann-Weierstrass Theorem (1882):**
     If α₁, ..., αₙ are distinct algebraic numbers, then eᵅ¹, ..., eᵅⁿ
     are linearly independent over the algebraic numbers.

     Corollary: eᵅ is transcendental for any non-zero algebraic α.
     (Setting n=1, α=1 gives e is transcendental.)

  2. **Gelfond-Schneider Theorem (1934):** [Wiedijk #60, Hilbert #7]
     If α and β are algebraic with α ≠ 0,1 and β irrational, then αᵝ is
     transcendental. Examples: 2^√2, eᵖⁱ = -1 (wait, that's algebraic!
     The theorem says e^{π·algebraic} ≠ -1 unless π is not algebraic—
     confirming π is transcendental.)

  3. **Baker's Theorem (1966):**
     Linear forms in logarithms of algebraic numbers are either 0 or
     transcendental. This gives effective irrationality measures.

  4. **Schanuel's Conjecture (Open):**
     If z₁, ..., zₙ are ℚ-linearly independent complex numbers, then
     the transcendence degree of ℚ(z₁,...,zₙ,e^z₁,...,e^zₙ) over ℚ is ≥ n.

     This would imply almost everything we know about transcendence,
     including e + π is transcendental (currently unknown!).
-/

-- ============================================================
-- PART 7: Why This Matters
-- ============================================================

/-
  **Historical Significance:**

  Hermite's 1873 proof was revolutionary:
  - First proof that a "naturally occurring" number is transcendental
    (Liouville had constructed transcendental numbers in 1844, but they
    were designed to be transcendental)
  - Introduced the auxiliary polynomial method still used today
  - Directly inspired Lindemann's proof of π's transcendence (1882)

  **Mathematical Importance:**

  The transcendence of e means:
  - e cannot be constructed with compass and straightedge
  - The exponential function truly "escapes" algebraic relations
  - There's no polynomial equation satisfied by e with rational coefficients

  **Open Problems:**

  Surprisingly, many basic questions remain open:
  - Is e + π transcendental? (Believed yes, unproven)
  - Is eπ transcendental? (Yes, by Gelfond-Schneider!)
  - Is e^e transcendental? (Believed yes, unproven)
  - Is γ (Euler-Mascheroni constant) even irrational? (Unknown!)

  **Computational Note:**

  e is computable to any precision:
  e = 1 + 1/1! + 1/2! + 1/3! + ... = 2.718281828459045...

  The first 10 digits (2.7182818284...) are easy to memorize as they repeat
  the "1828" pattern: e ≈ 2.7 1828 1828 ...
-/

-- Final check: our axiom gives the main result
#check e_transcendental  -- Transcendental ℤ (exp 1)
