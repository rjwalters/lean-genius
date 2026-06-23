import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Complex.ExponentialBounds
import Proofs.HermiteLindemann

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
-- PART 4: The Main Theorem (derived from Hermite-Lindemann)
-- ============================================================

/-- **Main Theorem: e is transcendental over ℤ** (Wiedijk #67).

    Derived from `HermiteLindemann.hermite_lindemann` at α = 1: since 1 ≠ 0
    is algebraic over ℚ, `Complex.exp 1` is transcendental over ℤ; transfer
    along the embedding ℝ ↪ ℂ gives `Transcendental ℤ (Real.exp 1)`.

    The underlying assumption is now `axiom hermite_lindemann` in
    `Proofs.HermiteLindemann`; this slug no longer carries an independent axiom. -/
theorem e_transcendental : Transcendental ℤ (Real.exp 1) :=
  HermiteLindemann.e_transcendental_int

/-- e is transcendental over ℚ.
    Derived from e_transcendental (over ℤ) via IsFractionRing.isAlgebraic_iff:
    IsAlgebraic ℚ x ↔ IsAlgebraic ℤ x for the fraction ring ℤ ⊂ ℚ. -/
theorem e_transcendental_over_rationals : Transcendental ℚ (Real.exp 1) :=
  fun halg => e_transcendental ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr halg)

-- ============================================================
-- PART 5: Corollaries
-- ============================================================

/-- **e is irrational** (formerly axiom, now proved)

    Transcendental implies irrational: if e = p/q for rationals p, q, then
    e would be algebraic (root of q·X - p = 0), contradicting transcendence. -/
theorem e_irrational_axiom : Irrational (Real.exp 1) := by
  intro ⟨q, hq⟩
  exact e_transcendental
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr (by rw [← hq]; exact isAlgebraic_algebraMap q))

/-- e is irrational (weaker than transcendental, but follows from it) -/
theorem e_irrational : Irrational (Real.exp 1) := e_irrational_axiom

/-- **eⁿ is transcendental for any non-zero integer n** (formerly axiom, now proved)

    If eⁿ were algebraic, then e would be algebraic via polynomial composition.
    Specifically, if p(eⁿ) = 0, then e satisfies q(X) = p(Xⁿ) which is
    a polynomial of degree n · deg(p). This contradicts e being transcendental.

    We use exp(n) = (exp 1)^n and polynomial composition. -/
theorem exp_nat_transcendental_axiom (n : ℕ) (hn : n ≠ 0) : Transcendental ℤ (Real.exp n) := by
  -- exp(n) = (exp 1)^n
  have hexp : Real.exp (n : ℝ) = (Real.exp 1) ^ n := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [hexp]
  intro halg
  have hq : IsAlgebraic ℚ ((Real.exp 1) ^ n) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp halg
  obtain ⟨p, hp_ne, hp_eval⟩ := hq
  have he : IsAlgebraic ℚ (Real.exp 1) := by
    refine ⟨p.comp (Polynomial.X ^ n), ?_, ?_⟩
    · intro h
      rcases Nat.eq_zero_or_pos p.natDegree with hd | hd
      · have heq := Polynomial.eq_C_of_natDegree_eq_zero hd
        rw [heq, Polynomial.C_comp] at h
        rw [heq] at hp_ne; exact hp_ne h
      · have hpos : 0 < (p.comp (Polynomial.X ^ n)).natDegree := by
          rw [Polynomial.natDegree_comp]
          simp only [Polynomial.natDegree_X_pow]
          exact Nat.mul_pos hd (Nat.pos_of_ne_zero hn)
        simp [h] at hpos
    · rw [Polynomial.aeval_comp, map_pow, Polynomial.aeval_X]; exact hp_eval
  exact e_transcendental ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr he)

/-- eⁿ is transcendental for any non-zero integer n -/
theorem exp_nat_transcendental (n : ℕ) (hn : n ≠ 0) :
    Transcendental ℤ (Real.exp n) :=
  exp_nat_transcendental_axiom n hn

/-- **1/e is transcendental** (formerly axiom, now proved)

    If 1/e were algebraic over ℤ, then algebraic over ℚ. Since algebraic
    elements over a field are closed under inversion, e = (1/e)⁻¹ would be
    algebraic over ℚ, contradicting transcendence. -/
theorem e_inv_transcendental_axiom : Transcendental ℤ (Real.exp 1)⁻¹ := by
  intro halg
  have hq : IsAlgebraic ℚ (Real.exp 1)⁻¹ := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp halg
  have he : IsAlgebraic ℚ (Real.exp 1) := IsAlgebraic.inv_iff.mp hq
  exact e_transcendental ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr he)

/-- 1/e is transcendental -/
theorem e_inv_transcendental : Transcendental ℤ (Real.exp 1)⁻¹ := e_inv_transcendental_axiom

/-- **e + 1 is transcendental**: if e + 1 were algebraic over ℤ, then
    e = (e + 1) − 1 would be algebraic (algebraic elements over ℚ are closed
    under subtraction of rationals). This contradicts e being transcendental. -/
theorem e_plus_one_transcendental_axiom : Transcendental ℤ (Real.exp 1 + 1) := by
  intro halg
  have hq : IsAlgebraic ℚ (Real.exp 1 + 1) := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp halg
  have h1 : IsAlgebraic ℚ (1 : ℝ) := isAlgebraic_one
  have he : IsAlgebraic ℚ (Real.exp 1) := by
    have := hq.sub h1; rwa [add_sub_cancel_right] at this
  exact e_transcendental ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr he)

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
