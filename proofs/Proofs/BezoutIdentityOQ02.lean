import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-
# Euclid's Lemma via coprime_iff_linear_combination

## Open Question (bezout-identity-oq-02)
Can Euclid's lemma be proved formally using the coprime_iff_linear_combination theorem?

## Answer: Yes!

The coprime_iff_linear_combination theorem characterizes coprimality as the existence
of a linear combination equaling 1. This characterization is exactly what's needed to
prove Euclid's lemma constructively.

## The Key Proof Idea

**Euclid's Lemma**: If gcd(a, b) = 1 and a | b*c, then a | c.

**Proof via Bézout coefficients**:
1. From `coprime_iff_linear_combination`: ∃ x y : ℤ, a*x + b*y = 1
2. Get k : ℤ with b*c = a*k (from divisibility)
3. Compute: c = (a*x + b*y)*c = a*(x*c) + (b*c)*y = a*(x*c) + a*k*y = a*(x*c + y*k)
4. So a | c with witness x*c + y*k

**Algebraically**: `linear_combination y * hk - c * hbez` closes the goal.

## Status
- [x] Complete proof (0 sorries)
- [x] Euclid's lemma for integers (IsCoprime version, direct)
- [x] Euclid's lemma for naturals (via coprime_iff_linear_combination)
- [x] Prime version of Euclid's lemma
- [x] Worked examples
-/

namespace BezoutIdentityOQ02

/-! ## Core Tool: coprime_iff_linear_combination

For natural numbers a, b:
  Nat.Coprime a b ↔ ∃ x y : ℤ, a * x + b * y = 1
-/

/-- **coprime_iff_linear_combination** (re-stated for self-containment):
    Two natural numbers are coprime iff there exist integers x, y with a*x + b*y = 1.

    This characterization is the bridge between the arithmetic notion of coprimality
    (gcd = 1) and the algebraic property (Bézout linear combination = 1) that makes
    Euclid's lemma work. -/
theorem coprime_iff_linear_combination (a b : ℕ) :
    Nat.Coprime a b ↔ ∃ x y : ℤ, (a : ℤ) * x + (b : ℤ) * y = 1 := by
  constructor
  · intro h
    rw [Nat.Coprime] at h
    refine ⟨Nat.gcdA a b, Nat.gcdB a b, ?_⟩
    have := Nat.gcd_eq_gcd_ab a b
    rw [h] at this
    push_cast at this ⊢
    linarith
  · intro ⟨x, y, heq⟩
    rw [Nat.Coprime]
    have hdvd : (Nat.gcd a b : ℤ) ∣ (1 : ℤ) := by
      have ha : (Nat.gcd a b : ℤ) ∣ (a : ℤ) :=
        Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left a b)
      have hb : (Nat.gcd a b : ℤ) ∣ (b : ℤ) :=
        Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right a b)
      rw [← heq]
      exact dvd_add (dvd_mul_of_dvd_left ha x) (dvd_mul_of_dvd_left hb y)
    have hdvd' : Nat.gcd a b ∣ 1 := by exact_mod_cast hdvd
    exact Nat.eq_one_of_dvd_one hdvd'

/-! ## Euclid's Lemma: Integer Version via IsCoprime

In Lean 4, `IsCoprime a b` is *defined* as `∃ u v, u * a + v * b = 1`.
This is exactly Bézout's identity with gcd = 1, so the proof is a direct
application of the Bézout witness.
-/

/-- **Euclid's Lemma for Integers** (via IsCoprime / Bézout coefficients):
    If IsCoprime a b and a divides b*c, then a divides c.

    **Proof**: From IsCoprime, get u, v with u*a + v*b = 1.
    From divisibility, get k with b*c = a*k.
    **Witness**: u*c + v*k, since c = a*(u*c + v*k) follows by
    linear_combination (verified by ring): v*(b*c - a*k) - c*(u*a + v*b - 1) = 0. -/
theorem euclids_lemma_int (a b c : ℤ)
    (hcop : IsCoprime a b) (hdvd : a ∣ b * c) : a ∣ c := by
  obtain ⟨u, v, huv⟩ := hcop  -- huv : u * a + v * b = 1
  obtain ⟨k, hk⟩ := hdvd      -- hk  : b * c = a * k
  -- c = (u*a + v*b)*c = a*(u*c) + b*c*v = a*(u*c) + a*k*v = a*(u*c + v*k)
  exact ⟨u * c + v * k, by linear_combination v * hk - c * huv⟩

/-! ## Euclid's Lemma: Natural Number Version via coprime_iff_linear_combination

This is the main answer to the open question: YES, Euclid's lemma can be proved
formally using `coprime_iff_linear_combination`.

The proof uses `coprime_iff_linear_combination` to extract integers x, y with
a*x + b*y = 1, then constructs the divisibility witness over ℤ and casts back.
-/

/-- **Euclid's Lemma via coprime_iff_linear_combination** (main result):
    If Nat.Coprime a b and a | b*c, then a | c.

    **Key tool**: `coprime_iff_linear_combination` gives integers x, y with a*x + b*y = 1.
    **Proof**: Over ℤ, get k with b*c = a*k, construct witness x*c + y*k for c = a*(...).
    The `linear_combination` tactic checks: y*(b*c - a*k) - c*(a*x + b*y - 1) = 0. -/
theorem euclids_lemma_nat (a b c : ℕ)
    (hcop : Nat.Coprime a b) (hdvd : a ∣ b * c) : a ∣ c := by
  -- Extract Bézout coefficients via coprime_iff_linear_combination
  rw [coprime_iff_linear_combination] at hcop
  obtain ⟨x, y, hbez⟩ := hcop  -- hbez : (a : ℤ) * x + (b : ℤ) * y = 1
  -- Prove divisibility in ℤ (avoids subtraction issues in ℕ)
  rw [← Int.natCast_dvd_natCast]
  -- Cast: a | b*c in ℕ → (a:ℤ) | (b:ℤ)*(c:ℤ)
  obtain ⟨k, hk⟩ : (a : ℤ) ∣ (b : ℤ) * (c : ℤ) := by exact_mod_cast hdvd
  -- Witness: x*c + y*k, proved by linear_combination
  exact ⟨x * c + y * k, by linear_combination y * hk - (c : ℤ) * hbez⟩

/-! ## Prime Version of Euclid's Lemma

The classic form: if p is prime and p | a*b, then p | a or p | b.
-/

/-- **Euclid's Lemma (Prime Version)**:
    If p is prime and p | a*b, then p | a or p | b.

    **Proof**: If p ∤ a, then gcd(p, a) = 1 (p prime means only divisors are 1 and p,
    and p ∤ a excludes p). Apply euclids_lemma_nat to get p | b. -/
theorem euclids_lemma_prime (p a b : ℕ) (hp : Nat.Prime p)
    (hdvd : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  by_cases ha : p ∣ a
  · exact Or.inl ha
  · right
    -- If p ∤ a, then gcd(p, a) = 1
    have hcop : Nat.Coprime p a :=
      (hp.coprime_iff_not_dvd).mpr ha
    -- Apply Euclid's lemma: p | b*a and Coprime p a implies p | b
    exact euclids_lemma_nat p a b hcop hdvd

/-! ## Worked Examples -/

/-- Example: gcd(3, 7) = 1, 3 | 7 * 6 = 42, so 3 | 6. -/
example : (3 : ℕ) ∣ 6 := by
  exact euclids_lemma_nat 3 7 6 (by decide) (by norm_num)

/-- Example: gcd(5, 8) = 1, 5 | 8 * 15 = 120, so 5 | 15. -/
example : (5 : ℕ) ∣ 15 := by
  exact euclids_lemma_nat 5 8 15 (by decide) (by norm_num)

/-- Example: 7 is prime and 7 | 14 * 3 = 42, so 7 | 14 or 7 | 3. -/
example : (7 : ℕ) ∣ 14 ∨ (7 : ℕ) ∣ 3 :=
  euclids_lemma_prime 7 14 3 (by norm_num) (by norm_num)

/-- Direct verification of the Bézout witness:
    3 * 5 + 7 * (-2) = 15 - 14 = 1, confirming gcd(3,7) = 1 by linear combination. -/
example : (3 : ℤ) * 5 + 7 * (-2) = 1 := by norm_num

/-- The coprime_iff_linear_combination theorem applied concretely for a = 3, b = 7. -/
example : Nat.Coprime 3 7 ↔ ∃ x y : ℤ, 3 * x + 7 * y = 1 :=
  coprime_iff_linear_combination 3 7

/-- Verification of the Euclid's lemma witness directly:
    For 3 * 5 + 7 * (-2) = 1 and 7 * 6 = 3 * 14:
    witness = x * c + y * k = 5 * 6 + (-2) * 14 = 30 - 28 = 2
    and indeed 3 * 2 = 6. -/
example : (3 : ℤ) * (5 * 6 + (-2) * 14) = 6 := by norm_num

/-! ## Why coprime_iff_linear_combination Is the Right Tool

The key insight: Euclid's lemma is fundamentally an algebraic identity.

Given a*x + b*y = 1 and b*c = a*k, we have:
  c = 1 * c = (a*x + b*y) * c = a*(x*c) + (b*c)*y = a*(x*c) + (a*k)*y = a*(x*c + y*k)

The `linear_combination` tactic makes this algebraic argument formal and checkable:
  c - a*(x*c + y*k) = y*(b*c - a*k) - c*(a*x + b*y - 1) = y*0 - c*0 = 0

This is why `coprime_iff_linear_combination` is the natural tool:
it converts the arithmetic fact "gcd = 1" into the algebraic witness that
makes the linear combination argument work.
-/

#check euclids_lemma_int
#check euclids_lemma_nat
#check euclids_lemma_prime
#check coprime_iff_linear_combination

end BezoutIdentityOQ02
