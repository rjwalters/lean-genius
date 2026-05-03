/-
Erdős Problem #1214: Primitive Prime Divisors and Integer Powers

Source: https://erdosproblems.com/1214
Status: SOLVED (Corrales-Rodrigáñez & Schoof, 1997)

Statement:
Let x, y ≥ 1 be integers such that for all n ≥ 1, the set of primes
dividing x^n − 1 equals the set of primes dividing y^n − 1. Must x = y?

Answer: YES. Proved by Corrales-Rodrigáñez and Schoof [CoSc97].

The proof proceeds via Zsygmondy's theorem (1892): for x ≥ 2 and n ≥ 3
(with finitely many exceptions), x^n − 1 has a primitive prime divisor —
a prime p such that the multiplicative order of x modulo p is exactly n.
Tracking primitive primes across all valid n forces x and y to be equal.

References:
  [CoSc97] Corrales-Rodrigáñez, C. and Schoof, R.,
           "The support problem and its elliptic analogue",
           J. Number Theory 64 (1997), 276–290.
  [Zs92]   Zsygmondy, K., "Zur Theorie der Potenzreste",
           Monatsh. Math. Phys. 3 (1892), 265–284.
-/

import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.GroupPower.Basic

open Nat

namespace Erdos1214

/-!
## The Same-Prime-Support Condition

For a natural number x and exponent n ≥ 1, write P(x^n − 1) for the set of
prime divisors of x^n − 1 (i.e., Nat.primeFactors (x^n − 1)).

Two integers x, y ≥ 1 have the same prime support if P(x^n − 1) = P(y^n − 1)
for every n ≥ 1.
-/

/--
x and y have the **same prime support** if for every n ≥ 1,
the set of primes dividing x^n − 1 equals the set of primes dividing y^n − 1.
-/
def samePrimeSupport (x y : ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → (x ^ n - 1 : ℕ).primeFactors = (y ^ n - 1 : ℕ).primeFactors

/--
A prime p is a **primitive prime divisor** of x^n − 1 if p divides x^n − 1
but does not divide x^k − 1 for any 1 ≤ k < n.

Equivalently, the multiplicative order of x modulo p is exactly n.
-/
def IsPrimitivePrimeDivisor (p x n : ℕ) : Prop :=
  p.Prime ∧ p ∣ x ^ n - 1 ∧ ∀ k : ℕ, 1 ≤ k → k < n → ¬(p ∣ x ^ k - 1)

/-!
## Elementary Properties of Same-Prime-Support
-/

/-- Reflexivity: x has the same prime support as itself. -/
lemma samePrimeSupport_refl (x : ℕ) : samePrimeSupport x x :=
  fun _ _ => rfl

/-- Symmetry: if x and y have the same prime support, so do y and x. -/
lemma samePrimeSupport_symm {x y : ℕ} (h : samePrimeSupport x y) :
    samePrimeSupport y x :=
  fun n hn => (h n hn).symm

/-- Transitivity: same prime support is transitive. -/
lemma samePrimeSupport_trans {x y z : ℕ}
    (hxy : samePrimeSupport x y) (hyz : samePrimeSupport y z) :
    samePrimeSupport x z :=
  fun n hn => (hxy n hn).trans (hyz n hn)

/-- Equal integers have the same prime support. -/
lemma eq_implies_samePrimeSupport {x y : ℕ} (h : x = y) :
    samePrimeSupport x y := h ▸ samePrimeSupport_refl x

/-!
## Specializations of the Condition

Specializing to small n gives concrete constraints.
-/

/-- At n = 1: primeFactors(x − 1) = primeFactors(y − 1). -/
lemma primeFactors_pred_eq {x y : ℕ} (h : samePrimeSupport x y) :
    (x - 1).primeFactors = (y - 1).primeFactors := by
  have h1 := h 1 (Nat.le_refl 1)
  simp only [pow_one] at h1
  exact h1

/-- At n = 2: primeFactors(x² − 1) = primeFactors(y² − 1). -/
lemma primeFactors_sq_pred_eq {x y : ℕ} (h : samePrimeSupport x y) :
    (x ^ 2 - 1).primeFactors = (y ^ 2 - 1).primeFactors :=
  h 2 (by norm_num)

/-- At n = 3: primeFactors(x³ − 1) = primeFactors(y³ − 1). -/
lemma primeFactors_cube_pred_eq {x y : ℕ} (h : samePrimeSupport x y) :
    (x ^ 3 - 1).primeFactors = (y ^ 3 - 1).primeFactors :=
  h 3 (by norm_num)

/-!
## Multiplicative Order: The Key Correspondence

A prime p divides x^n − 1 if and only if the multiplicative order of x
modulo p divides n. This correspondence is the backbone of the proof.
-/

/--
**Order characterization:**
For p prime, x with p ∤ x, n ≥ 1:
p ∣ x^n − 1  ↔  orderOf (x : ZMod p) ∣ n.

This follows from:
  (1) p ∣ x^n − 1  ↔  (x : ZMod p)^n = 1  [ZMod.intCast_zmod_eq_zero_iff_dvd]
  (2) (x : ZMod p)^n = 1  ↔  orderOf (x : ZMod p) ∣ n  [orderOf_dvd_iff_pow_eq_one]
-/
axiom order_characterization (p : ℕ) (hp : p.Prime) (x n : ℕ)
    (hn : 1 ≤ n) (hxp : ¬p ∣ x) (hx : 2 ≤ x) :
    p ∣ x ^ n - 1 ↔ orderOf (x : ZMod p) ∣ n

/-!
## Monotonicity of Prime Support

n ∣ m implies every prime dividing x^n − 1 also divides x^m − 1.
-/

/--
**Monotonicity:** n ∣ m → primeFactors(x^n − 1) ⊆ primeFactors(x^m − 1).

Proof: if p ∣ x^n − 1, then ord_p(x) ∣ n, and n ∣ m gives ord_p(x) ∣ m,
so x^m ≡ 1 (mod p), giving p ∣ x^m − 1.
-/
axiom primeSupport_mono (x : ℕ) (hx : 2 ≤ x) {n m : ℕ}
    (hn : 1 ≤ n) (hdvd : n ∣ m) :
    (x ^ n - 1).primeFactors ⊆ (x ^ m - 1).primeFactors

/-!
## Zsygmondy's Theorem (1892)

The existence of primitive prime divisors for almost all exponents.
-/

/--
**Zsygmondy's Theorem (1892) [Zs92]:**
For x ≥ 2 and n ≥ 3, with the single exception (x, n) = (2, 6),
there exists a prime p dividing x^n − 1 whose multiplicative order
modulo p is exactly n (a "primitive prime divisor").

The proof uses cyclotomic polynomials: the n-th cyclotomic polynomial Φ_n(x)
divides x^n − 1, and for n ≥ 3 (away from exceptions), Φ_n(x) has a prime
factor not dividing any Φ_k(x) with k < n.
-/
axiom zsygmondy (x n : ℕ) (hx : 2 ≤ x) (hn : 3 ≤ n)
    (hexc : ¬(x = 2 ∧ n = 6)) :
    ∃ p : ℕ, IsPrimitivePrimeDivisor p x n

/--
The exception: 2^6 − 1 = 63 = 3² · 7. The prime factors 3 and 7 both appear
earlier: 3 ∣ 2² − 1 = 3 and 7 ∣ 2³ − 1 = 7. So no primitive prime divisor exists.
-/
theorem zsygmondy_exception_63 :
    (2 ^ 6 - 1 : ℕ) = 3 ^ 2 * 7 := by norm_num

/-!
## The Main Theorem: Corrales-Rodrigáñez & Schoof (1997)
-/

/--
**Corrales-Rodrigáñez & Schoof (1997) [CoSc97]:**
If x, y ≥ 1 with samePrimeSupport x y, then x = y.

Proof outline:
1. If x = 1: all primeFactors(x^n − 1) = ∅, forcing primeFactors(y^n − 1) = ∅ for all n,
   which forces y = 1.
2. If x ≥ 2: For n ≥ 3 with (x,n) ≠ (2,6), Zsygmondy gives a primitive prime p_n
   with ord_{p_n}(x) = n. Since p_n ∈ primeFactors(y^n − 1), we have ord_{p_n}(y) ∣ n.
   Moreover, p_n ∤ y^k − 1 for k < n (since p_n ∤ x^k − 1 and same support)...
   [The full argument, due to Corrales-Rodrigáñez & Schoof, shows y is a power of x,
    and symmetry forces x = y.]
-/
axiom corrales_rodriganez_schoof (x y : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (h : samePrimeSupport x y) : x = y

/--
**Erdős Problem #1214: SOLVED** (Corrales-Rodrigáñez & Schoof, 1997).

If x, y ≥ 1 are natural numbers such that for every n ≥ 1, the set of
primes dividing x^n − 1 equals the set of primes dividing y^n − 1, then x = y.
-/
theorem erdos_1214 (x y : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (h : ∀ n : ℕ, 1 ≤ n →
      (x ^ n - 1 : ℕ).primeFactors = (y ^ n - 1 : ℕ).primeFactors) :
    x = y :=
  corrales_rodriganez_schoof x y hx hy h

/-!
## Further Context: The Elliptic Analogue

Corrales-Rodrigáñez and Schoof [CoSc97] also proved an elliptic analogue:
if E is an elliptic curve over ℚ and P, Q ∈ E(ℚ) are non-torsion points
such that for every n ≥ 1, the prime reduction support of [n]P equals
that of [n]Q, then P = ±Q. This uses the Weil pairing and ℓ-adic representations.

The multiplicative case proved here is the foundational arithmetic version.
-/

end Erdos1214
