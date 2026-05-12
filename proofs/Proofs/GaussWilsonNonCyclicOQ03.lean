import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic
import Proofs.GaussWilsonNonCyclic

/-
# Exact Count of Square Roots of Unity in ZMod n (OQ-03)

The parent `GaussWilsonNonCyclic.lean` proves the qualitative lower bound
(`#{x : ZMod n // x² = 1} ≥ 3` whenever `(ZMod n)ˣ` is non-cyclic).
OQ-03 upgrades this to the exact closed-form count:

```
  #{x ∈ ZMod n : x² = 1}  =  2 ^ (ω_odd(n) + ε₂(n))
```

where `ω_odd(n)` is the number of distinct odd prime factors of `n`, and
`ε₂(n) ∈ {0, 1, 2}` is the two-adic correction:

```
  ε₂(n) = 0  if v₂(n) ≤ 1,
          1  if v₂(n) = 2,
          2  if v₂(n) ≥ 3.
```

The formula has been verified numerically for `n = 1..120` (see
`research/problems/gauss-wilson-non-cyclic-oq-03/knowledge.md`).

## This file (S3)

* Defines the closed-form count `numSqrtsOne` (computable, via
  `Nat.primeFactors` — note the contrast with `Nat.factorization`, which is
  `noncomputable` in Mathlib because of `multiplicity`).
* Verifies the formula at a handful of small `n` via `decide`.
* States the main theorem `card_sqrts_one_eq_numSqrtsOne` with `sorry`.
* **S3 NEW**: ring↔unit bridge `card_sqrts_one_eq_card_units_sqrts_one`
  reducing the ZMod-side count to a unit-group count, so that subsequent
  sessions can work entirely inside `(ZMod n)ˣ` where the cyclic-group
  structure (`ZMod.isCyclic_units_of_prime_pow` etc.) applies.

## Subsequent sessions

* **S4**: prime-power count `card_sqrts_one_unit_prime_pow_odd`
  via `IsCyclic.card_orderOf_eq_totient` (~70 lines).
* **S5**: CRT multiplicativity (~50 lines).
* **S6**: assembly by induction on `n.primeFactors.card` (~40 lines).

## Status

1 sorry (`card_sqrts_one_eq_numSqrtsOne`), 0 axioms.
-/

namespace GaussWilsonNonCyclicOQ03

open Nat Finset

-- ============================================================================
-- Section 1: Closed-form count
-- ============================================================================

/-- Two-adic correction factor for the square-root count of `x² = 1` in
`ZMod n`.  Encodes the well-known case split:

```
  (ZMod 2^a)ˣ  has   1 sqrt of 1   if a ≤ 1   (groups of order ≤ 1 or 2)
                     2 sqrts        if a = 2   (cyclic of order 2)
                     4 sqrts        if a ≥ 3   (≅ ℤ/2 × ℤ/2^{a-2})
```
-/
def epsTwo (n : ℕ) : ℕ :=
  if n % 8 = 0 then 2 else if n % 4 = 0 then 1 else 0

/-- The number of distinct **odd** prime factors of `n`. -/
def omegaOdd (n : ℕ) : ℕ :=
  (n.primeFactors.filter (· ≠ 2)).card

/-- Closed-form prediction for `#{x ∈ ZMod n : x² = 1}`.

For `n = 2^a · m` with `m` odd and `m` having `k` distinct odd prime factors,
the count is `2^(k + ε₂(n))`. -/
def numSqrtsOne (n : ℕ) : ℕ := 2 ^ (omegaOdd n + epsTwo n)

theorem numSqrtsOne_pos (n : ℕ) : 0 < numSqrtsOne n := by
  unfold numSqrtsOne
  positivity

-- ============================================================================
-- Section 2: Small-case verification (the formula is decidable)
-- ============================================================================

-- Powers of 2: should give epsTwo correction only.
example : numSqrtsOne 1 = 1 := by native_decide
example : numSqrtsOne 2 = 1 := by native_decide
example : numSqrtsOne 4 = 2 := by native_decide
example : numSqrtsOne 8 = 4 := by native_decide
example : numSqrtsOne 16 = 4 := by native_decide

-- Odd: pure ω_odd contribution.
example : numSqrtsOne 3 = 2 := by native_decide
example : numSqrtsOne 15 = 4 := by native_decide
example : numSqrtsOne 105 = 8 := by native_decide

-- Mixed: both factors contribute.
example : numSqrtsOne 12 = 4 := by native_decide      -- 2² · 3:  ω_odd=1, ε₂=1
example : numSqrtsOne 24 = 8 := by native_decide      -- 2³ · 3:  ω_odd=1, ε₂=2
example : numSqrtsOne 60 = 8 := by native_decide      -- 2² · 15: ω_odd=2, ε₂=1
example : numSqrtsOne 120 = 16 := by native_decide    -- 2³ · 15: ω_odd=2, ε₂=2

-- ============================================================================
-- Section 3: Main theorem (target of S3..S5)
-- ============================================================================

/-- **Main theorem (OQ-03, statement only in S2).**

The number of solutions of `x² = 1` in `ZMod n` equals the closed-form count
`numSqrtsOne n = 2 ^ (ω_odd(n) + ε₂(n))`.

This is the quantitative upgrade of the parent's qualitative `≥ 3` bound
(`GaussWilsonNonCyclic.card_sq_eq_one_ge_three`).  The proof strategy
(deferred to S3..S5) factors through:

* CRT to reduce to prime-power moduli (S4);
* Cyclicity of `(ZMod p^a)ˣ` for odd `p` (and the explicit `ℤ/2 × ℤ/2^{a-2}`
  structure of `(ZMod 2^a)ˣ` for `a ≥ 3`) to count at prime-power level (S3);
* Induction on `n.primeFactors.card` to assemble (S5).
-/
theorem card_sqrts_one_eq_numSqrtsOne (n : ℕ) [NeZero n] :
    (Finset.univ.filter (fun x : ZMod n => x ^ 2 = 1)).card = numSqrtsOne n := by
  sorry

-- ============================================================================
-- Section 4: Ring ↔ unit bridge (S3)
-- ============================================================================

/-- **Ring ↔ unit bridge for square roots of unity.**

Every `x : ZMod n` satisfying `x² = 1` is automatically a unit (its inverse is
itself), so counting solutions inside `ZMod n` is the same as counting
solutions inside `(ZMod n)ˣ`.

This is the key reduction that lets subsequent sessions (S4 onward) work
entirely inside the unit group `(ZMod n)ˣ`, where the cyclic-group structure
(`ZMod.isCyclic_units_of_prime_pow`, the order-`p^{k-1}(p-1)` totient
formula, etc.) applies cleanly. The ring `ZMod n` itself is not even an
integral domain when `n` is composite, so polynomial-roots arguments do
not directly count `x² = 1`; the bridge sidesteps this by lifting to units.

The bijection is the parent file's `unitOfSqEqOne` in one direction and
`Units.val` in the other. We prove the equality of cardinalities by showing
the image of the unit-side filter under `Units.val` is exactly the
ring-side filter, then applying `Finset.card_image_of_injective` to the
injection `Units.val_injective`. -/
theorem card_sqrts_one_eq_card_units_sqrts_one (n : ℕ) [NeZero n] :
    (Finset.univ.filter (fun x : ZMod n => x ^ 2 = 1)).card =
    (Finset.univ.filter (fun u : (ZMod n)ˣ => u ^ 2 = 1)).card := by
  classical
  -- Image of the unit-side filter under `Units.val` is the ring-side filter.
  have himg :
      (Finset.univ.filter (fun u : (ZMod n)ˣ => u ^ 2 = 1)).image
          (Units.val : (ZMod n)ˣ → ZMod n) =
      Finset.univ.filter (fun x : ZMod n => x ^ 2 = 1) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · rintro ⟨u, hu_sq, rfl⟩
      -- `u² = 1` in the unit group transports to `(u : ZMod n)² = 1` in the ring.
      have h : ((u ^ 2 : (ZMod n)ˣ) : ZMod n) = ((1 : (ZMod n)ˣ) : ZMod n) := by
        rw [hu_sq]
      rw [Units.val_pow_eq_pow_val, Units.val_one] at h
      exact h
    · intro hx_sq
      -- Conversely, `unitOfSqEqOne x` lifts `x² = 1` to the unit group.
      exact ⟨GaussWilsonNonCyclic.unitOfSqEqOne x hx_sq,
             GaussWilsonNonCyclic.unitOfSqEqOne_sq x hx_sq,
             GaussWilsonNonCyclic.unitOfSqEqOne_val x hx_sq⟩
  -- Cardinality of the image equals cardinality of the original (val is injective).
  rw [← himg, Finset.card_image_of_injective _ Units.val_injective]

end GaussWilsonNonCyclicOQ03
