import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.EuclideanDomain.Defs
import Mathlib.Tactic

/-!
# Greatest Common Divisor Algorithm

## What This Proves
The Euclidean algorithm correctly computes the greatest common divisor (GCD):

$$\gcd(a, b) = \gcd(b, a \mod b)$$

with base case $\gcd(a, 0) = a$.

This ancient algorithm, described in Euclid's *Elements* (c. 300 BCE), is one of the
oldest algorithms still in common use today. It terminates and produces the unique
greatest common divisor of any two natural numbers.

## Approach
- **Foundation (from Mathlib):** We use `Mathlib.Data.Nat.GCD.Basic` which provides
  the complete GCD infrastructure including `Nat.gcd`, `Nat.gcd_rec`, and
  related divisibility theorems.
- **Original Contributions:** Pedagogical wrapper theorems with explicit
  documentation explaining the algorithm's history and correctness.
- **Proof Techniques Demonstrated:** Working with divisibility, well-founded
  recursion, and the Euclidean domain structure.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical examples
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Mathlib.Data.Nat.GCD.Basic` : GCD definition and properties
- `Nat.gcd` : The GCD function itself
- `Nat.gcd_rec` : The recursive property gcd(a, b) = gcd(b, a % b)
- `Nat.gcd_dvd_left`, `Nat.gcd_dvd_right` : GCD divides both arguments
- `Nat.dvd_gcd` : Characterization as greatest common divisor

## Historical Note
The Euclidean algorithm appears in Book VII of Euclid's *Elements* (c. 300 BCE),
making it over 2,300 years old. It was originally stated in terms of repeated
subtraction rather than the modulo operation, but the principle is the same.
The algorithm is also described in ancient Chinese and Indian mathematics.

## Why This Works
The algorithm exploits the key insight that:
- If d divides both a and b, then d also divides (a mod b)
- If d divides both b and (a mod b), then d divides a

Thus gcd(a, b) and gcd(b, a mod b) have exactly the same set of common divisors,
and hence the same greatest common divisor.

Termination is guaranteed because (a mod b) < b, so the second argument
strictly decreases in each recursive call.

## Wiedijk's 100 Theorems: #69
-/

namespace GCDAlgorithm

/-! ## The Core Algorithm -/

/-- **The Euclidean Algorithm**: The GCD satisfies the fundamental recurrence.

    This is the heart of the Euclidean algorithm:
    gcd(a, b) = gcd(b, a mod b) when b ≠ 0

    The algorithm terminates because (a mod b) < b, providing a
    strictly decreasing sequence of second arguments. -/
theorem euclidean_recurrence (a : ℕ) {b : ℕ} (hb : b ≠ 0) :
    Nat.gcd a b = Nat.gcd b (a % b) := by
  conv_lhs => rw [Nat.gcd_comm]
  rw [Nat.gcd_rec]
  rw [Nat.gcd_comm]

/-- **Base Case**: The GCD of any number with 0 is that number.

    gcd(a, 0) = a

    This is the base case of the Euclidean algorithm. When the second
    argument reaches 0, we've found our answer. -/
theorem gcd_zero_right (a : ℕ) : Nat.gcd a 0 = a :=
  Nat.gcd_zero_right a

/-- **Symmetry**: GCD is commutative.

    gcd(a, b) = gcd(b, a)

    The order of arguments doesn't matter for GCD. -/
theorem gcd_comm (a b : ℕ) : Nat.gcd a b = Nat.gcd b a :=
  Nat.gcd_comm a b

/-! ## Correctness: GCD Divides Both Arguments -/

/-- **Left Divisibility**: gcd(a, b) divides a. -/
theorem gcd_divides_left (a b : ℕ) : Nat.gcd a b ∣ a :=
  Nat.gcd_dvd_left a b

/-- **Right Divisibility**: gcd(a, b) divides b. -/
theorem gcd_divides_right (a b : ℕ) : Nat.gcd a b ∣ b :=
  Nat.gcd_dvd_right a b

/-! ## Correctness: GCD is the Greatest -/

/-- **Greatest Property**: If d divides both a and b, then d divides gcd(a, b).

    This shows that gcd(a, b) is the *greatest* common divisor:
    any other common divisor must divide it, so it's at least as large. -/
theorem gcd_is_greatest {a b d : ℕ} (ha : d ∣ a) (hb : d ∣ b) :
    d ∣ Nat.gcd a b :=
  Nat.dvd_gcd ha hb

/-- **Complete Characterization**: d is gcd(a, b) iff it divides both
    and every common divisor divides d.

    This is the universal property of GCD. -/
theorem gcd_characterization (a b d : ℕ) :
    d = Nat.gcd a b ↔
    (d ∣ a ∧ d ∣ b ∧ ∀ e, e ∣ a → e ∣ b → e ∣ d) := by
  constructor
  · intro h
    rw [h]
    exact ⟨Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b,
           fun e ha hb => Nat.dvd_gcd ha hb⟩
  · intro ⟨hda, hdb, hmax⟩
    apply Nat.dvd_antisymm
    · exact Nat.dvd_gcd hda hdb
    · exact hmax (Nat.gcd a b) (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)

/-! ## Key Properties -/

/-- **Associativity**: GCD is associative.

    gcd(gcd(a, b), c) = gcd(a, gcd(b, c)) -/
theorem gcd_assoc (a b c : ℕ) :
    Nat.gcd (Nat.gcd a b) c = Nat.gcd a (Nat.gcd b c) :=
  Nat.gcd_assoc a b c

/-- **Identity Element**: gcd(a, 0) = a and gcd(0, a) = a.

    Zero is the identity element for GCD. -/
theorem gcd_zero_left (a : ℕ) : Nat.gcd 0 a = a :=
  Nat.gcd_zero_left a

/-- **Self GCD**: gcd(a, a) = a. -/
theorem gcd_self (a : ℕ) : Nat.gcd a a = a :=
  Nat.gcd_self a

/-- **GCD with 1**: gcd(a, 1) = 1 for any a. -/
theorem gcd_one_right (a : ℕ) : Nat.gcd a 1 = 1 :=
  Nat.gcd_one_right a

/-! ## Coprimality -/

/-- **Coprime Definition**: a and b are coprime iff gcd(a, b) = 1. -/
theorem coprime_iff_gcd_one (a b : ℕ) : Nat.Coprime a b ↔ Nat.gcd a b = 1 :=
  Iff.rfl

/-- **Coprime Example**: Consecutive integers are coprime. -/
theorem consecutive_coprime (n : ℕ) : Nat.Coprime n (n + 1) :=
  Nat.coprime_self_add_right n 1

/-! ## The Extended Euclidean Algorithm (Bézout's Identity) -/

/-- **Bézout's Identity**: For any a and b, there exist integers x and y
    such that gcd(a, b) = a * x + b * y.

    This is computed by the extended Euclidean algorithm, which tracks
    the linear combination as it computes the GCD.

    Note: We use integers here since x and y may be negative. -/
theorem bezout_identity (a b : ℕ) :
    ∃ x y : ℤ, (Nat.gcd a b : ℤ) = a * x + b * y :=
  ⟨Nat.gcdA a b, Nat.gcdB a b, Nat.gcd_eq_gcd_ab a b⟩

/-- **Bézout Coefficients**: Mathlib provides explicit Bézout coefficients. -/
theorem bezout_equation (a b : ℕ) :
    (Nat.gcd a b : ℤ) = a * Nat.gcdA a b + b * Nat.gcdB a b :=
  Nat.gcd_eq_gcd_ab a b

/-! ## Worked Examples -/

/-- Example: gcd(48, 18) = 6 -/
example : Nat.gcd 48 18 = 6 := by native_decide

/-- Example: gcd(17, 5) = 1 (17 and 5 are coprime) -/
example : Nat.gcd 17 5 = 1 := by native_decide

/-- Example: gcd(100, 35) = 5 -/
example : Nat.gcd 100 35 = 5 := by native_decide

/-- Example: Tracing the Euclidean algorithm for gcd(48, 18):
    gcd(48, 18) = gcd(18, 48 mod 18) = gcd(18, 12)
    gcd(18, 12) = gcd(12, 18 mod 12) = gcd(12, 6)
    gcd(12, 6)  = gcd(6, 12 mod 6)   = gcd(6, 0)
    gcd(6, 0)   = 6 -/
example : Nat.gcd 48 18 = Nat.gcd 18 12 := by native_decide
example : Nat.gcd 18 12 = Nat.gcd 12 6 := by native_decide
example : Nat.gcd 12 6 = Nat.gcd 6 0 := by native_decide
example : Nat.gcd 6 0 = 6 := by native_decide

/-! ## Connection to Euclidean Domains

The natural numbers form a Euclidean domain, which generalizes the
Euclidean algorithm to other algebraic structures like polynomial rings.

In a Euclidean domain, we have:
- A Euclidean function φ (for ℕ, this is just the identity)
- Division with remainder: a = q * b + r where φ(r) < φ(b) or r = 0
- The Euclidean algorithm works for computing GCDs

This abstraction allows the same algorithm to work for:
- Integers (ℤ)
- Polynomials over a field (F[x])
- Gaussian integers (ℤ[i])
- And many other rings
-/

/-! ## Complexity Analysis

**Time Complexity**: O(log(min(a, b)))

The Euclidean algorithm is remarkably efficient. In the worst case
(consecutive Fibonacci numbers), it takes about log_φ(n) steps,
where φ is the golden ratio ≈ 1.618.

**Gabriel Lamé's Theorem (1844)**:
The number of steps in the Euclidean algorithm is at most
5 times the number of digits in the smaller input.

This makes the Euclidean algorithm one of the most efficient
algorithms known for computing GCDs.
-/

#check euclidean_recurrence
#check gcd_zero_right
#check gcd_divides_left
#check gcd_divides_right
#check gcd_is_greatest
#check gcd_characterization
#check bezout_identity

end GCDAlgorithm
