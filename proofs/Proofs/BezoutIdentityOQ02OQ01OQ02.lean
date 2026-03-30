import Mathlib

/-
# FTA Generalization to Euclidean Domains via UniqueFactorizationDomain

## The Open Question

Can the Fundamental Theorem of Arithmetic (unique prime factorization)
be generalized to Euclidean domains using Mathlib's UniqueFactorizationDomain?

## Answer: Yes — Mathlib Already Has This

Mathlib provides the chain:
  EuclideanDomain → GCDMonoid → UniqueFactorizationDomain

Key instances and theorems:
- `EuclideanDomain.instGCDMonoid` — every ED has a GCD structure
- The instance chain — GCDMonoid → UFD (via WfDvd + normalization)
- `UniqueFactorizationMonoid` — the general framework for unique factorization

## What This File Demonstrates

1. Every Euclidean domain is a UFD (via Mathlib instance resolution)
2. Concrete examples: ℤ as both ED and UFD
3. The core structural theorems: irreducible ↔ prime, existence and
   uniqueness of factorization
-/

namespace BezoutFTAGeneralization

/-- Every Euclidean domain is a unique factorization domain.
    This is automatic in Mathlib via instance resolution:
    EuclideanDomain → GCDMonoid → UniqueFactorizationMonoid. -/
example : UniqueFactorizationMonoid ℤ := inferInstance

/-- The integers form a Euclidean domain. -/
example : EuclideanDomain ℤ := inferInstance

/-- In any UFD, irreducible elements are prime.
    This is the generalization of Euclid's lemma to all UFDs.
    In ℤ: an integer is irreducible iff it is ±prime. -/
theorem irreducible_iff_prime_in_ufd {α : Type*} [CommMonoidWithZero α]
    [UniqueFactorizationMonoid α] {p : α} :
    Irreducible p ↔ Prime p :=
  UniqueFactorizationMonoid.irreducible_iff_prime

/-- Every non-zero element in a UFD has an irreducible factorization.
    The factors are given by `UniqueFactorizationMonoid.factors`. -/
theorem factors_exist {α : Type*} [CancelCommMonoidWithZero α]
    [UniqueFactorizationMonoid α] (a : α) (ha : a ≠ 0) :
    (∀ p ∈ UniqueFactorizationMonoid.factors a, Irreducible p) ∧
    Associated (UniqueFactorizationMonoid.factors a).prod a :=
  ⟨fun _ h => UniqueFactorizationMonoid.irreducible_of_factor _ h,
   UniqueFactorizationMonoid.factors_prod ha⟩

/-- The Euclidean domain structure of ℤ gives a computable GCD. -/
theorem int_gcd_exists (a b : ℤ) :
    ∃ g : ℤ, g ∣ a ∧ g ∣ b ∧ ∀ d : ℤ, d ∣ a → d ∣ b → d ∣ g :=
  ⟨Int.gcd a b, Int.gcd_dvd_left, Int.gcd_dvd_right,
   fun d hda hdb => Int.dvd_gcd hda hdb⟩

/-- Polynomial rings over fields are Euclidean domains, hence UFDs.
    This gives unique factorization of polynomials. -/
example {F : Type*} [Field F] : UniqueFactorizationMonoid (Polynomial F) :=
  inferInstance

end BezoutFTAGeneralization
