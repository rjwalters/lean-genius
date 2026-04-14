import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.UniqueFactorizationDomain
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Polynomial.RingDivision
import Mathlib.Tactic

/-
# Gauss's Lemma for ℤ[x]: Does `linear_combination` Scale? (OQ-02-OQ-04)

## The Open Question (bezout-identity-oq-02-oq-04)

Does the `linear_combination` tactic approach — used in BezoutIdentityOQ02 to prove
Euclid's lemma for ℤ via explicit Bézout coefficients — scale to Gauss's lemma for
polynomial rings: *if f ∈ ℤ[x] is primitive and irreducible, does f | g·h imply
f | g or f | h*?

## Answer: No direct scaling — but UFD theory gives the result

**Why Bézout/linear_combination worked for ℤ:**
- ℤ is a PID: gcd(a,b) = 1 ↔ ∃ x y, a*x + b*y = 1 (Bézout's identity)
- `linear_combination` closes the proof goal using this explicit witness
- Euclid's lemma follows in one algebraic step

**Why it fails for ℤ[x]:**
- ℤ[x] is NOT a PID (it is a UFD but not a PID)
- Example: gcd(2, X) = 1 in ℤ[x] but ¬∃ f g : ℤ[x], 2·f + X·g = 1
  (evaluate at 0: 2·f(0) = 1 has no solution in ℤ since 2 ∤ 1)
- No polynomial Bézout coefficients → `linear_combination` has no witness

**What works instead:**
- ℤ[x] is a UFD (Gauss's theorem: UFD base ring → polynomial ring is UFD)
- In a UFD: irreducible ↔ prime → (f | g*h → f | g ∨ f | h)
- This requires abstract ring theory, NOT explicit linear combination witnesses

## Where linear_combination still plays a role

At the coefficient level: checking primitivity of a specific polynomial requires showing
gcd of its coefficients is 1. For integer coefficients, Bézout witnesses exist, and
`norm_num` finds them automatically. So `linear_combination`-style reasoning appears
inside primitive checks, but NOT in the global divisibility argument.

## Status
- [x] No Bézout in ℤ[x] for (2, X) — proved by evaluation at 0 (0 sorries)
- [x] Gauss's lemma: primitive + irreducible → prime in ℤ[x] (0 sorries)
- [x] X + 1 is primitive in ℤ[x] (0 sorries)
- [x] X + 1 is irreducible in ℤ[x] (0 sorries)
- [x] Euclid's lemma for X+1: (X+1) | g*h → (X+1) | g or (X+1) | h (0 sorries)
- [x] Integer Bézout witnesses (the level where linear_combination applies) (0 sorries)
-/

namespace GaussLemmaPolynomial

open Polynomial

/-! ## Part I: No Bézout Identity in ℤ[x] — Why linear_combination Has No Witness -/

/-- **No Bézout for (2, X) in ℤ[x]**: no f, g : ℤ[x] satisfy 2*f + X*g = 1.

    **Proof**: Evaluate at 0. LHS = 2*f(0), so 2*f(0) = 1. But 2 ∤ 1 in ℤ. -/
theorem no_bezout_2_X : ¬ ∃ f g : ℤ[X], 2 * f + X * g = 1 := by
  intro ⟨f, g, hfg⟩
  have h : (2 * f + X * g).eval 0 = (1 : ℤ[X]).eval 0 := congrArg (eval 0) hfg
  simp only [eval_add, eval_mul, eval_ofNat, eval_X, eval_one, mul_zero, add_zero] at h
  omega

/-! ## Part II: Gauss's Lemma via UFD Theory -/

/-- **Gauss's Lemma** (prime divisibility): A primitive irreducible f ∈ ℤ[x] is prime.

    **Proof strategy** (NO linear combinations used):
    - ℤ[x] is a UFD (Gauss's theorem, available in Mathlib)
    - In a UFD, irreducible ↔ prime (`UniqueFactorizationMonoid.irreducible_iff_prime`)
    - Prime elements satisfy p ∣ a*b → p ∣ a ∨ p ∣ b by definition -/
theorem gauss_lemma_prime {f g h : ℤ[X]}
    (_hf_prim : f.IsPrimitive)
    (hf_irred : Irreducible f)
    (hdvd : f ∣ g * h) :
    f ∣ g ∨ f ∣ h :=
  (UniqueFactorizationMonoid.irreducible_iff_prime.mp hf_irred).dvd_or_dvd hdvd

/-! ## Part III: Concrete Example — X + 1 -/

/-- **X + 1 is primitive in ℤ[x]**: its constant coefficient is 1 (a unit). -/
theorem X_add_one_primitive : (X + 1 : ℤ[X]).IsPrimitive := by
  intro r hr
  -- The constant coefficient of X + 1 is 1
  have h0 : r ∣ (X + 1 : ℤ[X]).coeff 0 := hr 0
  simp only [coeff_add, coeff_X_zero, coeff_one_zero, zero_add] at h0
  exact isUnit_of_dvd_one h0

/-- **X + 1 is irreducible in ℤ[x]**: X + C(1) is irreducible over any nontrivial
    integral domain since degree(f*g) = 1 forces one factor to have degree 0 (a unit). -/
theorem X_add_one_irreducible : Irreducible (X + 1 : ℤ[X]) := by
  have : (X + 1 : ℤ[X]) = X + C 1 := by simp
  rw [this]
  exact Polynomial.irreducible_X_add_C 1

/-- **Euclid's lemma for X+1 in ℤ[x]**: (X+1) | g*h → (X+1) | g ∨ (X+1) | h. -/
theorem X_add_one_dvd_of_dvd_mul {g h : ℤ[X]} (hdvd : (X + 1 : ℤ[X]) ∣ g * h) :
    (X + 1 : ℤ[X]) ∣ g ∨ (X + 1 : ℤ[X]) ∣ h :=
  gauss_lemma_prime X_add_one_primitive X_add_one_irreducible hdvd

/-! ## Part IV: Where linear_combination CAN Help — Integer Level -/

/-- **Integer Bézout witnesses exist** (this is the level where linear_combination applies):
    For coprime integers like 3 and 2, explicit witnesses prove gcd = 1. This is used
    when checking primitivity of polynomials with integer coefficients. -/
theorem int_bezout_3_2 : ∃ x y : ℤ, 3 * x + 2 * y = 1 :=
  ⟨-1, 2, by norm_num⟩

/-- **Contrast**: no such witnesses exist at the polynomial level for 2 and X. -/
theorem poly_no_bezout : ¬ ∃ x y : ℤ[X], 2 * x + X * y = 1 :=
  no_bezout_2_X

/-- **Primitivity check using integer Bézout**: the polynomial 3·X + 2 is primitive.
    Proof: any common divisor r of all coefficients (3 and 2) satisfies r ∣ gcd(3,2) = 1.
    The Bézout witness 3·(-1) + 2·2 = 1 shows gcd(3,2) = 1 — this is where
    integer Bézout (and `linear_combination`-style reasoning) plays its role. -/
theorem three_X_add_two_primitive : (C 3 * X + C 2 : ℤ[X]).IsPrimitive := by
  intro r hr
  -- Coefficient at degree 1 is 3 (from C 3 * X)
  have h1 : r ∣ (3 : ℤ) := by
    have := hr 1
    simp only [coeff_add, coeff_C_mul, coeff_X_one, mul_one, coeff_C, if_false, add_zero] at this
    exact this
  -- Coefficient at degree 0 is 2 (from C 2)
  have h0 : r ∣ (2 : ℤ) := by
    have := hr 0
    simp only [coeff_add, coeff_C_mul, coeff_X_zero, mul_zero, coeff_C, if_true] at this
    exact this
  -- Integer Bézout: 3*(-1) + 2*2 = 1 → r ∣ 1
  -- (This is where linear_combination-style reasoning applies)
  have hbez : r ∣ (3 : ℤ) * (-1) + 2 * 2 :=
    dvd_add (h1.mul_right (-1)) (h0.mul_right 2)
  rwa [show (3 : ℤ) * (-1) + 2 * 2 = 1 from by norm_num] at hbez

/-- **Summary**: The linear_combination approach from bezout-identity-oq-02 does NOT scale
    to Gauss's lemma because:
    1. ℤ[x] lacks Bézout coefficients (not a PID) → no witness for linear_combination
    2. The prime divisibility property requires abstract UFD theory, not explicit witnesses

    However, linear_combination DOES apply at the coefficient level:
    - Checking a polynomial's primitivity uses integer Bézout witnesses (findable by norm_num)
    - This is a partial, local role — not the global Gauss's lemma -/
theorem answer_summary :
    -- Part 1: No polynomial Bézout witnesses exist
    (¬ ∃ f g : ℤ[X], 2 * f + X * g = 1) ∧
    -- Part 2: Gauss's lemma holds via UFD (not via linear_combination)
    (∀ {f g h : ℤ[X]}, f.IsPrimitive → Irreducible f → f ∣ g * h → f ∣ g ∨ f ∣ h) ∧
    -- Part 3: Integer Bézout witnesses exist at coefficient level
    (∃ x y : ℤ, 3 * x + 2 * y = 1) :=
  ⟨no_bezout_2_X, fun hp hi hd => gauss_lemma_prime hp hi hd, int_bezout_3_2⟩

end GaussLemmaPolynomial
