import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Nilpotent

/-
# Burnside's p^a q^b Theorem (Abel-Ruffini OQ-07)

## Open Question (abel-ruffini-galois-extensions-oq-07)

**Burnside's p^a q^b theorem in Lean**: Every group of order p^a q^b
(where p, q are primes and a, b ∈ ℕ) is solvable.

## Status: SCAFFOLD (Session 2 of OBSERVE)

This file establishes the file structure and proves the trivial cases:
- p = q  (collapses to a single prime, hence p-group)
- a = 0  (the group is a q-power, hence q-group)
- b = 0  (the group is a p-power, hence p-group)

The non-degenerate case (a ≥ 1, b ≥ 1, p ≠ q) remains as `sorry` and is
the substance of Burnside's 1904 theorem. Two routes are documented in
the parent JSON (`abel-ruffini-galois-extensions-oq-07.json`):
  (i)  original Burnside via character theory + algebraic integers;
  (ii) Goldschmidt-Matsuyama character-free via transfer / focal subgroup.

## Sharpness

|A₅| = 60 = 2² · 3 · 5 has *three* distinct primes, exactly one more
than Burnside's bound, and A₅ is non-solvable. The parent gallery entry
`abel-ruffini-galois-extensions` proves A₅ non-solvable; together they
pin the solvability threshold at "≤ 2 distinct primes".

## Mathlib Infrastructure Used

- `IsPGroup.of_card`        — from `Nat.card G = p^n` build an `IsPGroup p G`
- `IsPGroup.isNilpotent`    — finite p-groups are nilpotent (`Mathlib.GroupTheory.Nilpotent`)
- `IsNilpotent.to_isSolvable` — nilpotent ⟹ solvable (instance, priority 100)

The trivial-case proofs go through the chain
  card = p^k  ⟶  IsPGroup p G  ⟶  IsNilpotent G  ⟶  IsSolvable G.
-/

namespace AbelRuffiniGaloisExtensionsOQ07

-- `IsNilpotent` for groups lives in the `Group` namespace; the root-level
-- `IsNilpotent` is the predicate on ring elements.
open Group

/-! ## Trivial reductions (single-prime cases)

When the two prime factors collapse into one (`p = q`) or when one of
the exponents is zero, the group is a p-group, and existing Mathlib
infrastructure shows it is nilpotent and hence solvable. These cases
are mathematically uninteresting but useful as sanity checks and as
clean Aristotle targets. -/

/-- Single-prime case: if `|G| = p^a · p^b`, then `G` is a p-group, hence solvable. -/
theorem burnside_pq_eq_prime
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {a b : ℕ} (hG : Nat.card G = p ^ a * p ^ b) : IsSolvable G := by
  have hcard : Nat.card G = p ^ (a + b) := by rw [hG, ← pow_add]
  have hpG : IsPGroup p G := IsPGroup.of_card hcard
  haveI : IsNilpotent G := hpG.isNilpotent
  infer_instance

/-- Trivial exponent case: if `|G| = p^0 · q^b = q^b`, then `G` is a q-group. -/
theorem burnside_pq_a_zero
    {G : Type*} [Group G] [Finite G] {p q : ℕ} [Fact q.Prime]
    {b : ℕ} (hG : Nat.card G = p ^ 0 * q ^ b) : IsSolvable G := by
  have hcard : Nat.card G = q ^ b := by rw [hG, pow_zero, one_mul]
  have hqG : IsPGroup q G := IsPGroup.of_card hcard
  haveI : IsNilpotent G := hqG.isNilpotent
  infer_instance

/-- Trivial exponent case: if `|G| = p^a · q^0 = p^a`, then `G` is a p-group. -/
theorem burnside_pq_b_zero
    {G : Type*} [Group G] [Finite G] {p q : ℕ} [Fact p.Prime]
    {a : ℕ} (hG : Nat.card G = p ^ a * q ^ 0) : IsSolvable G := by
  have hcard : Nat.card G = p ^ a := by rw [hG, pow_zero, mul_one]
  have hpG : IsPGroup p G := IsPGroup.of_card hcard
  haveI : IsNilpotent G := hpG.isNilpotent
  infer_instance

/-! ## Direct p-group bridge

Phrased without the multiplicative factorisation, this is the building
block used in every reduction: a finite group whose order is a prime
power is solvable. -/

/-- A finite group of prime-power order is solvable. -/
theorem isSolvable_of_card_eq_prime_pow
    {G : Type*} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime]
    (hG : Nat.card G = p ^ n) : IsSolvable G := by
  have hpG : IsPGroup p G := IsPGroup.of_card hG
  haveI : IsNilpotent G := hpG.isNilpotent
  infer_instance

/-! ## Main theorem (non-trivial direction)

The substantive content of Burnside (1904): a finite group whose order
has exactly two distinct prime factors is solvable. Currently scaffolded
as `sorry`; future sessions will choose between the character-theoretic
and Goldschmidt-Matsuyama proof routes. -/

/-- **Burnside's p^a q^b theorem** (OPEN — non-trivial case).

If `|G| = p^a · q^b` for primes `p`, `q` and natural numbers `a`, `b`,
then `G` is solvable.

The trivial cases `p = q`, `a = 0`, `b = 0` are dispatched by the
lemmas above. The non-degenerate case `a ≥ 1`, `b ≥ 1`, `p ≠ q` is
the subject of Burnside (1904) and remains `sorry` here. -/
theorem burnside_pq
    {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {a b : ℕ} (hG : Nat.card G = p ^ a * q ^ b) : IsSolvable G := by
  sorry

end AbelRuffiniGaloisExtensionsOQ07
