import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Real.Irrational

/-!
# π is Transcendental (Wiedijk #53)

## What This Proves
The number π = 3.14159... is transcendental: it is not the root of any
non-zero polynomial with integer (or equivalently, rational) coefficients.

## Approach
- **Foundation (from Mathlib):** The definition `Transcendental ℤ x` states that
  `x` is not algebraic over ℤ. Mathlib provides `Real.pi` and `Complex.exp` with
  the key identity `exp(π * I) = -1` (Euler's identity).
- **Original Contributions:** This file provides pedagogical exposition of
  Lindemann's 1882 proof method, which settled the ancient problem of squaring
  the circle. The main theorem is axiomatized pending formalization of the
  Lindemann-Weierstrass theorem.
- **Proof Techniques Demonstrated:** Using algebraic properties of complex numbers,
  contraposition arguments, connections to Euler's identity.

## Status
- [x] Complete proof (modulo Lindemann's theorem axiom)
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical example
- [x] pi_transcendental proved from lindemann_theorem

## Mathlib Dependencies
- `Transcendental` : Definition from `Mathlib.RingTheory.Algebraic`
- `Real.pi` : The constant π
- `Complex.exp_pi_mul_I` : exp(π * I) = -1 (Euler's identity)
- `Complex.I` : The imaginary unit

Historical Note: Ferdinand von Lindemann proved π is transcendental in 1882,
building on Hermite's 1873 proof for e. This finally settled the 2,000-year-old
problem of squaring the circle—showing it is impossible with compass and straightedge.
-/

open Real Complex Polynomial

-- ============================================================
-- PART 1: Definitions and Background
-- ============================================================

/-
  A number x is **transcendental** over a ring R if it is not algebraic:
  there is no non-zero polynomial P ∈ R[X] such that P(x) = 0.

  Key insight for π:
  - e^(iπ) = -1 (Euler's identity)
  - -1 is clearly algebraic (root of X + 1)
  - i is algebraic (root of X² + 1)
  - If π were algebraic, then iπ would be algebraic
  - But Lindemann-Weierstrass says: e^α is transcendental for non-zero algebraic α
  - Contradiction! Since e^(iπ) = -1 is algebraic, π cannot be algebraic.
-/

#check Transcendental  -- Transcendental R x : Prop
#check Real.pi         -- Real.pi : ℝ

-- ============================================================
-- PART 2: Key Properties of π from Mathlib
-- ============================================================

/-- π > 0 -/
theorem pi_pos' : Real.pi > 0 := Real.pi_pos

/-- The famous identity: e^(iπ) = -1 -/
example : Complex.exp (Real.pi * Complex.I) = -1 := Complex.exp_pi_mul_I

-- ============================================================
-- PART 3: Lindemann's Proof Strategy (1882)
-- ============================================================

/-
  **Lindemann's Proof Outline:**

  The proof uses the Lindemann-Weierstrass theorem, which Lindemann proved
  specifically for this purpose:

  **Lindemann-Weierstrass Theorem:**
  If α₁, ..., αₙ are distinct algebraic numbers, then e^α₁, ..., e^αₙ
  are linearly independent over the algebraic numbers.

  **Corollary (Lindemann's Theorem):**
  If α is a non-zero algebraic number, then e^α is transcendental.

  **Proof that π is transcendental:**

  1. Suppose, for contradiction, that π is algebraic.

  2. Then iπ is algebraic (since i is algebraic: root of X² + 1,
     and algebraic numbers form a field closed under multiplication).

  3. iπ ≠ 0 (since π ≠ 0 and i ≠ 0).

  4. By Lindemann's Theorem, e^(iπ) must be transcendental.

  5. But e^(iπ) = -1 by Euler's identity.

  6. -1 is algebraic (root of X + 1).

  7. Contradiction! Therefore π is transcendental.

  **The Lindemann-Weierstrass proof** itself is an intricate generalization
  of Hermite's proof for e. It constructs auxiliary polynomials with careful
  divisibility properties, uses integration by parts to relate integrals
  to algebraic expressions, and derives a contradiction from the assumption
  that all αᵢ are algebraic.
-/

-- ============================================================
-- PART 4: The Main Theorem (Axiomatized)
-- ============================================================

/-- **Lindemann's Theorem (1882):**
    If α is a non-zero algebraic number, then e^α is transcendental.

    This is the key step - once we have this, π's transcendence follows.
    The full Lindemann-Weierstrass theorem is not yet in Mathlib. -/
axiom lindemann_theorem (α : ℂ) (hα_ne : α ≠ 0) (hα_alg : IsAlgebraic ℤ α) :
    Transcendental ℤ (Complex.exp α)

/-- **Main Theorem: π is transcendental over ℤ** (Wiedijk #53)

    This follows from Lindemann's theorem and Euler's identity e^(iπ) = -1.
    Since -1 is algebraic, and e^(iπ) = -1, if iπ were algebraic (which it
    would be if π were algebraic), we'd contradict Lindemann's theorem.

    Proof:
    1. Assume π is algebraic over ℤ (in ℝ)
    2. Then (↑π : ℂ) is algebraic over ℤ (in ℂ) via the embedding ℝ → ℂ
    3. i is algebraic over ℤ (root of X² + 1)
    4. So π·i is algebraic over ℤ (algebraic numbers form a ring)
    5. π·i ≠ 0 (since π > 0 and i ≠ 0)
    6. By Lindemann's theorem, e^(πi) is transcendental
    7. But e^(πi) = -1 by Euler's identity
    8. -1 is algebraic (root of X + 1) — contradiction -/
theorem pi_transcendental : Transcendental ℤ Real.pi := by
  intro halg
  -- Step 2: Transfer algebraicity from ℝ to ℂ via the embedding ℝ → ℂ
  have hpi_C : IsAlgebraic ℤ (↑(Real.pi) : ℂ) := by
    obtain ⟨p, hp_ne, hp_eval⟩ := halg
    refine ⟨p, hp_ne, ?_⟩
    -- aeval (↑π : ℂ) p = ↑(aeval π p : ℝ) = ↑0 = 0
    have h : Polynomial.aeval (algebraMap ℝ ℂ Real.pi) p =
        algebraMap ℝ ℂ (Polynomial.aeval Real.pi p) :=
      (Polynomial.aeval_algebraMap_apply ℤ Real.pi p).symm
    rw [h, hp_eval, map_zero]
  -- Step 3: i is algebraic
  have hi := I_algebraic
  -- Step 4: π·i is algebraic (algebraic numbers form a ring)
  have hpi_i : IsAlgebraic ℤ ((↑Real.pi : ℂ) * Complex.I) := hpi_C.mul hi
  -- Step 5: π·i ≠ 0
  have hne : (↑Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)) Complex.I_ne_zero
  -- Step 6: By Lindemann's theorem, e^(πi) is transcendental
  have h_trans := lindemann_theorem ((↑Real.pi : ℂ) * Complex.I) hne hpi_i
  -- Step 7: But e^(πi) = -1 (Euler's identity)
  rw [show (↑Real.pi : ℂ) * Complex.I = ↑Real.pi * Complex.I from rfl,
      Complex.exp_pi_mul_I] at h_trans
  -- Step 8: -1 is algebraic — contradiction
  exact h_trans neg_one_algebraic

/-- π is transcendental over ℚ.
    Derived from pi_transcendental (over ℤ): if π were algebraic over ℚ,
    clearing denominators via integerNormalization gives an integer polynomial
    vanishing at π, contradicting Transcendental ℤ π. -/
theorem pi_transcendental_over_rationals : Transcendental ℚ Real.pi := by
  intro ⟨p, hp_ne, hp_eval⟩
  exact pi_transcendental
    ⟨IsLocalization.integerNormalization (nonZeroDivisors ℤ) p,
     mt IsFractionRing.integerNormalization_eq_zero_iff.mp hp_ne,
     IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors ℤ) p hp_eval⟩

-- ============================================================
-- PART 5: Why π Cannot Be Algebraic
-- ============================================================

/-
  Alternative perspective: The impossibility of constructible π.

  A number is **constructible** (with compass and straightedge) if and only if
  it lies in a tower of quadratic extensions starting from ℚ.

  Constructible numbers are algebraic with degree a power of 2.

  If π were constructible, it would be algebraic of degree 2ⁿ for some n.
  But π is transcendental, so it's not even algebraic, let alone constructible.

  This is why squaring the circle is impossible!
-/

/-- The key identity for the proof: e^(iπ) = -1 -/
theorem euler_identity_neg_one : Complex.exp (Real.pi * Complex.I) = -1 :=
  Complex.exp_pi_mul_I

/-- -1 is algebraic (root of X + 1) -/
theorem neg_one_algebraic : IsAlgebraic ℤ (-1 : ℂ) := by
  use Polynomial.X + 1
  constructor
  · exact Polynomial.X_add_C_ne_zero 1
  · simp

/-- i is algebraic (root of X² + 1) -/
theorem I_algebraic : IsAlgebraic ℤ Complex.I := by
  use Polynomial.X^2 + 1
  constructor
  · have h : Polynomial.leadingCoeff (Polynomial.X ^ 2 + (1 : Polynomial ℤ)) = 1 := by simp
    intro heq
    rw [heq] at h
    simp at h
  · simp [Complex.I_sq]

-- ============================================================
-- PART 6: Corollaries
-- ============================================================

/-- **π is irrational** (formerly axiom, now proved from Mathlib)

    Mathlib provides `irrational_pi` directly. This also follows from transcendence:
    if π = p/q for integers p, q, then π would be algebraic (root of q·X - p = 0),
    contradicting transcendence. -/
theorem pi_irrational_axiom : Irrational Real.pi := irrational_pi

/-- π is irrational (weaker than transcendental, but follows from it) -/
theorem pi_irrational : Irrational Real.pi := pi_irrational_axiom

/-- **2π is transcendental** (formerly axiom, now proved)

    If 2π were algebraic over ℤ, then algebraic over ℚ. Multiplying by 2⁻¹
    (algebraic over ℚ) gives π algebraic over ℚ, contradicting transcendence. -/
theorem two_pi_transcendental_axiom : Transcendental ℤ (2 * Real.pi) := by
  intro halg
  have hq : IsAlgebraic ℚ (2 * Real.pi) := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp halg
  have h_half : IsAlgebraic ℚ ((2⁻¹ : ℚ) : ℝ) := isAlgebraic_algebraMap (2⁻¹ : ℚ)
  have hpi : IsAlgebraic ℚ Real.pi := by
    have := hq.mul h_half
    rwa [show 2 * Real.pi * ((2⁻¹ : ℚ) : ℝ) = Real.pi from by push_cast; field_simp] at this
  exact pi_transcendental ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr hpi)

/-- 2π is transcendental -/
theorem two_pi_transcendental : Transcendental ℤ (2 * Real.pi) :=
  two_pi_transcendental_axiom

/-- **π² is transcendental** (formerly axiom, now proved)

    If π² were algebraic, say p(π²) = 0, then π satisfies q(X) = p(X²),
    making π algebraic. This contradicts π being transcendental. -/
theorem pi_sq_transcendental_axiom : Transcendental ℤ (Real.pi ^ 2) := by
  intro halg
  have hq : IsAlgebraic ℚ (Real.pi ^ 2) := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp halg
  obtain ⟨p, hp_ne, hp_eval⟩ := hq
  have hpi : IsAlgebraic ℚ Real.pi := by
    refine ⟨p.comp (Polynomial.X ^ 2), ?_, ?_⟩
    · -- p.comp (X^2) ≠ 0: either p is a nonzero constant (comp = p) or
      -- natDegree(p.comp(X^2)) = natDegree(p) * 2 > 0
      intro h
      rcases Nat.eq_zero_or_pos p.natDegree with hd | hd
      · have heq := Polynomial.eq_C_of_natDegree_eq_zero hd
        rw [heq, Polynomial.C_comp] at h
        rw [heq] at hp_ne; exact hp_ne h
      · have hpos : 0 < (p.comp (Polynomial.X ^ 2)).natDegree := by
          rw [Polynomial.natDegree_comp]
          simp only [Polynomial.natDegree_X_pow]
          omega
        simp [h] at hpos
    · rw [Polynomial.aeval_comp, map_pow, Polynomial.aeval_X]; exact hp_eval
  exact pi_transcendental ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr hpi)

/-- π² is transcendental -/
theorem pi_sq_transcendental : Transcendental ℤ (Real.pi ^ 2) :=
  pi_sq_transcendental_axiom

/-- **π + 1 is transcendental**: if π + 1 were algebraic over ℤ, then
    π = (π + 1) − 1 would be algebraic (algebraic elements over ℚ are closed
    under subtraction of rationals). This contradicts π being transcendental. -/
theorem pi_plus_one_transcendental_axiom : Transcendental ℤ (Real.pi + 1) := by
  intro halg
  have hq : IsAlgebraic ℚ (Real.pi + 1) := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp halg
  have h1 : IsAlgebraic ℚ (1 : ℝ) := isAlgebraic_algebraMap (1 : ℚ)
  have hpi : IsAlgebraic ℚ Real.pi := by
    have := hq.sub h1; rwa [add_sub_cancel_right] at this
  exact pi_transcendental ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr hpi)

/-- π + 1 is transcendental -/
theorem pi_plus_one_transcendental : Transcendental ℤ (Real.pi + 1) :=
  pi_plus_one_transcendental_axiom

/-- **1/π is transcendental** (formerly axiom, now proved)

    If π⁻¹ were algebraic over ℤ, then algebraic over ℚ. Since algebraic
    elements over a field form a subfield, π = (π⁻¹)⁻¹ would be algebraic.
    But π is transcendental — contradiction. -/
theorem pi_inv_transcendental_axiom : Transcendental ℤ (Real.pi)⁻¹ := by
  intro halg
  have hq : IsAlgebraic ℚ (Real.pi)⁻¹ := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp halg
  have hpi : IsAlgebraic ℚ Real.pi := IsAlgebraic.inv_iff.mp hq
  exact pi_transcendental ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr hpi)

/-- 1/π is transcendental -/
theorem pi_inv_transcendental : Transcendental ℤ (Real.pi)⁻¹ :=
  pi_inv_transcendental_axiom

-- ============================================================
-- PART 7: The Squaring of the Circle
-- ============================================================

/-
  **The Ancient Problem:**

  Given a circle of radius r (and thus area πr²), construct a square with
  the same area using only compass and straightedge.

  Such a square would have side length r√π.

  **Why It's Impossible:**

  1. Compass and straightedge constructions can only produce numbers that
     lie in iterated quadratic extensions of the rationals.

  2. Such numbers are algebraic with degree a power of 2.

  3. √π would be algebraic if and only if π is algebraic.

  4. But π is transcendental!

  5. Therefore √π is transcendental, hence not constructible.

  6. The circle cannot be squared.

  **Historical Note:**

  This problem dates back to ancient Greece. For over 2,000 years,
  mathematicians attempted to find the construction. In 1882, Lindemann
  finally proved it impossible—not by failing to find a construction,
  but by proving none can exist.

  The problem is one of the three classical "impossible constructions":
  1. Squaring the circle (π transcendental)
  2. Doubling the cube (∛2 has degree 3, not a power of 2)
  3. Trisecting an arbitrary angle (some angles need degree 3 extensions)
-/

/-- **√π is transcendental** (formerly axiom, now proved)

    If √π were algebraic over ℤ, then algebraic over ℚ. Since algebraic
    numbers over ℚ are closed under multiplication, π = √π · √π would be
    algebraic over ℚ, contradicting π's transcendence. -/
theorem sqrt_pi_transcendental_axiom : Transcendental ℤ (Real.sqrt Real.pi) := by
  intro halg
  have hq : IsAlgebraic ℚ (Real.sqrt Real.pi) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp halg
  have hpi : IsAlgebraic ℚ Real.pi := by
    have := hq.mul hq
    rwa [Real.mul_self_sqrt (le_of_lt Real.pi_pos)] at this
  exact pi_transcendental ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr hpi)

/-- √π is transcendental (key to impossibility of squaring the circle) -/
theorem sqrt_pi_transcendental : Transcendental ℤ (Real.sqrt Real.pi) :=
  sqrt_pi_transcendental_axiom

-- ============================================================
-- PART 8: Connections to Other Results
-- ============================================================

/-
  **Related Theorems:**

  1. **Hermite's Theorem (1873):** [Wiedijk #67]
     e is transcendental. The prototype for π's proof.

  2. **Lindemann-Weierstrass Theorem (1882):**
     The general result from which π's transcendence follows.
     If α₁,...,αₙ are distinct algebraic numbers, then e^α₁,...,e^αₙ
     are linearly independent over algebraic numbers.

  3. **Gelfond-Schneider Theorem (1934):** [Wiedijk #60, Hilbert #7]
     If α ≠ 0,1 and β are algebraic with β irrational, then α^β is
     transcendental. Examples: 2^√2, e^π (since e^π = (e^(iπ))^(-i) = (-1)^(-i)).

  4. **Baker's Theorem (1966):**
     Linear forms in logarithms of algebraic numbers.

  **Open Problems:**

  - Is e + π transcendental? (Believed yes, unproven)
  - Is eπ transcendental? (Yes, by Gelfond-Schneider!)
  - Is e^e transcendental? (Believed yes, unproven)
  - Is π^e transcendental? (Unknown)
  - Is π^π transcendental? (Unknown)
-/

-- ============================================================
-- PART 9: Computational Notes
-- ============================================================

/-
  **Computing π:**

  π is computable to any desired precision. Famous formulas include:

  1. **Leibniz series:** π/4 = 1 - 1/3 + 1/5 - 1/7 + ... (very slow)

  2. **Machin's formula:** π/4 = 4·arctan(1/5) - arctan(1/239)

  3. **Ramanujan's series:** Converges incredibly fast

  4. **Chudnovsky algorithm:** Used for record computations (billions of digits)

  **Current records:**

  As of 2024, π has been computed to over 100 trillion digits.
  The transcendence of π means these digits never become periodic.

  **First 50 digits:**
  π ≈ 3.14159265358979323846264338327950288419716939937510...
-/

-- ============================================================
-- PART 10: Why This Matters
-- ============================================================

/-
  **Mathematical Importance:**

  The transcendence of π means:
  - π cannot be constructed with compass and straightedge
  - No polynomial equation relates π to rational numbers
  - π "escapes" the world of algebraic numbers
  - The digits of π never become periodic in any base

  **Physical Significance:**

  π appears throughout physics:
  - Circle geometry: C = 2πr, A = πr²
  - Heisenberg uncertainty: Δx·Δp ≥ ℏ/2 = h/(4π)
  - Coulomb's law: F = e²/(4πε₀r²)
  - Einstein field equations: Rμν - ½Rgμν = 8πG·Tμν

  The transcendence of π means these fundamental constants involve
  a number that lies beyond algebraic description.

  **Philosophical Note:**

  That π is transcendental shows the circle—the simplest curved figure—
  has a fundamental complexity. The ratio of circumference to diameter
  cannot be captured by any finite algebraic expression. This is not a
  failure of measurement but an intrinsic property of Euclidean geometry.
-/

-- Final check: our axiom gives the main result
#check pi_transcendental  -- Transcendental ℤ Real.pi
