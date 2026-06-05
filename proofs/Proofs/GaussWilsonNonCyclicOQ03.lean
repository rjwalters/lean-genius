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

-- ============================================================================
-- Section 5: Order-2 decomposition of the square-root filter (S4 prep)
-- ============================================================================

/-! ### S4 preparation — generic group-theoretic decomposition

The S3 ring↔unit bridge reduces the ring-side count to a unit-group count
`#{u : (ZMod n)ˣ // u^2 = 1}`. The S4 strategy is then: at each prime power
`p^k`, use the cyclic structure of `(ZMod p^k)ˣ` (for odd `p`, or `p^k ∈
{1, 2, 4}`) and the `ℤ/2 × ℤ/2^{k-2}` structure for `p = 2, k ≥ 3` to count.

This subsection packages the **order-theoretic** half of that argument
generically (no `ZMod`/`Cyclic`/`Units` baggage): the count of `u² = 1`
in any finite group splits as the sum of the order-1 and order-2 counts.
The cyclic / specific-structure step is then a one-line totient lookup on
`#{u | orderOf u = 1} = φ(1) = 1` and `#{u | orderOf u = 2} = φ(2) = 1`
(both via `IsCyclic.card_orderOf_eq_totient`).

Three lemmas:

* `filter_sq_eq_one_eq_filter_orderOf_dvd_two` — `u^2 = 1 ↔ orderOf u ∣ 2`
  (immediate from `orderOf_dvd_iff_pow_eq_one`).
* `filter_orderOf_dvd_two_eq_union` — `orderOf u ∣ 2` decomposes as the
  union `{orderOf = 1} ∪ {orderOf = 2}` (Nat.dvd_prime on 2).
* `card_filter_sq_eq_one_decomp` — cardinality split using disjoint union
  on the previous decomposition. -/

/-- **Filter equality**: `u^2 = 1` iff `orderOf u ∣ 2`. -/
theorem filter_sq_eq_one_eq_filter_orderOf_dvd_two
    (G : Type*) [Group G] [DecidableEq G] [Fintype G] :
    Finset.univ.filter (fun u : G => u ^ 2 = 1) =
      Finset.univ.filter (fun u : G => orderOf u ∣ 2) := by
  ext u
  simp [orderOf_dvd_iff_pow_eq_one]

/-- **Union decomposition** of the order-divides-2 filter: every unit
of order dividing the prime `2` has order exactly `1` or `2`
(`Nat.dvd_prime` on `2`). -/
theorem filter_orderOf_dvd_two_eq_union
    (G : Type*) [Group G] [DecidableEq G] [Fintype G] :
    Finset.univ.filter (fun u : G => orderOf u ∣ 2) =
      (Finset.univ.filter (fun u : G => orderOf u = 1)) ∪
      (Finset.univ.filter (fun u : G => orderOf u = 2)) := by
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  refine ⟨?_, ?_⟩
  · intro hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · rw [h]; exact one_dvd _
    · rw [h]

/-- **Cardinality split**: `#{u | u^2 = 1} = #{u | orderOf u = 1} +
#{u | orderOf u = 2}`. The two components are disjoint (`1 ≠ 2`) so
cardinality is additive on the union.

For `IsCyclic` groups, `IsCyclic.card_orderOf_eq_totient` further
reduces each component to a `Nat.totient` value (`φ(1) = 1`,
`φ(2) = 1`); this is the entry point for S4's odd-prime-power count
once cyclicity has been established. -/
theorem card_filter_sq_eq_one_decomp
    (G : Type*) [Group G] [DecidableEq G] [Fintype G] :
    (Finset.univ.filter (fun u : G => u ^ 2 = 1)).card =
      (Finset.univ.filter (fun u : G => orderOf u = 1)).card +
      (Finset.univ.filter (fun u : G => orderOf u = 2)).card := by
  rw [filter_sq_eq_one_eq_filter_orderOf_dvd_two,
      filter_orderOf_dvd_two_eq_union]
  apply Finset.card_union_of_disjoint
  rw [Finset.disjoint_left]
  intro u hu1 hu2
  have h1 : orderOf u = 1 := (Finset.mem_filter.mp hu1).2
  have h2 : orderOf u = 2 := (Finset.mem_filter.mp hu2).2
  omega

-- ============================================================================
-- Section 6: Cyclic-group count of u^2 = 1 (S4)
-- ============================================================================

/-! ### S4 — `card = 2` for cyclic groups of even order

For an IsCyclic group `G` whose order is divisible by `2`,
`#{u : G | u^2 = 1} = 2`. The two solutions are the identity and the
unique element of order `2` (whose existence is guaranteed by
`2 ∣ |G|` together with cyclicity).

This is the order-theoretic endpoint of the S4-prep decomposition
(`card_filter_sq_eq_one_decomp` above): combining the order-1 and
order-2 components via `IsCyclic.card_orderOf_eq_totient` gives
`Nat.totient 1 + Nat.totient 2 = 1 + 1 = 2`. -/

/-- **Cyclic, even order ⇒ exactly two square roots of 1.**

For any cyclic group of even order, the count of solutions of
`u^2 = 1` is exactly `2`: the identity (the unique order-1 element)
and the unique element of order `2` (which exists by cyclicity +
`2 ∣ |G|`).

Specialising to `(ZMod p^k)ˣ` for an odd prime `p` (cyclic by
`ZMod.isCyclic_units_of_prime_pow`, even by `2 ∣ p - 1`) yields
the S4 deliverable mentioned in `state.md` §"Next Action": the
odd-prime-power unit-side count is `2`. -/
theorem card_filter_sq_eq_one_cyclic_even
    (G : Type*) [Group G] [DecidableEq G] [Fintype G] [IsCyclic G]
    (heven : 2 ∣ Fintype.card G) :
    (Finset.univ.filter (fun u : G => u ^ 2 = 1)).card = 2 := by
  rw [card_filter_sq_eq_one_decomp]
  have h1 :=
    IsCyclic.card_orderOf_eq_totient (α := G) (one_dvd (Fintype.card G))
  have h2 := IsCyclic.card_orderOf_eq_totient (α := G) heven
  rw [h1, h2]
  -- Nat.totient 1 = 1, Nat.totient 2 = 1, so 1 + 1 = 2.
  decide

-- ============================================================================
-- Section 7: Odd-prime-power specialisation (S5)
-- ============================================================================

/-! ### S5 — odd prime power unit count

For an odd prime `p` and `k ≥ 1`, instantiate the generic
`card_filter_sq_eq_one_cyclic_even` at `G = (ZMod (p^k))ˣ`.

* `ZMod.isCyclic_units_of_prime_pow` supplies cyclicity for `(ZMod (p^k))ˣ`.
* The order is `φ(p^k) = p^{k-1}(p-1)` (via `ZMod.card_units_eq_totient` +
  `Nat.totient_prime_pow`), which is even because `p` odd ⇒ `p - 1` even
  (via `Nat.Prime.even_sub_one`).

This is the per-prime-power count input that the subsequent CRT
multiplicativity step (S6, currently scheduled) consumes when assembling
the closed-form `numSqrtsOne(n) = 2^(ω_odd(n) + ε₂(n))` formula. -/

/-- **S5 ACT — odd prime power unit count.**

For any odd prime `p` and any `k ≥ 1`, the number of square roots of unity
in `(ZMod (p^k))ˣ` equals exactly `2` (the identity and the unique element
of order `2`). The proof composes `card_filter_sq_eq_one_cyclic_even` (the
S4 generic theorem) with `ZMod.isCyclic_units_of_prime_pow` and the
`p` odd ⇒ `2 ∣ (p - 1)` ⇒ `2 ∣ φ(p^k)` chain.

This closes the *unit-side* count at odd prime powers. The CRT
multiplicativity step (S6) then assembles per-prime-power counts into the
full closed-form `numSqrtsOne` formula. -/
theorem card_filter_sq_eq_one_units_zmod_prime_pow_odd
    {p k : ℕ} (hp : p.Prime) (hp_odd : p ≠ 2) (hk : 0 < k) [NeZero (p ^ k)] :
    (Finset.univ.filter (fun u : (ZMod (p ^ k))ˣ => u ^ 2 = 1)).card = 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := ZMod.isCyclic_units_of_prime_pow p hp hp_odd k
  apply card_filter_sq_eq_one_cyclic_even
  rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow hp hk]
  -- 2 ∣ p^(k-1) * (p-1) because p odd ⇒ 2 ∣ (p - 1).
  exact dvd_mul_of_dvd_right (hp.even_sub_one hp_odd).two_dvd _

-- ============================================================================
-- Section 8: Power-of-2 small prime-power cases (S5b.1, S5b.2)
-- ============================================================================

/-! ### S5b — small power-of-2 unit counts

Companion to S5: handles the even prime `p = 2` case at small exponents
`k ∈ {1, 2}`. The structural `k ≥ 3` case (`(ZMod 2^k)ˣ ≅ ℤ/2 × ℤ/2^(k-2)`,
count = 4) is deferred to S5b.3.

The mathematical content (verified numerically in `knowledge.md` and proved
here for `k ≤ 2`):

```
  k = 1 : (ZMod 2)ˣ trivial               → count = 1
  k = 2 : (ZMod 4)ˣ cyclic order 2        → count = 2
  k ≥ 3 : (ZMod 2^k)ˣ ≅ ℤ/2 × ℤ/2^(k-2)   → count = 4   [S5b.3]
```

Both proofs here are `decide`-based: the unit groups have decidable
equality and computable Fintype instances (via `ZMod.card_units_eq_totient`
and `Nat.totient_prime_pow`), so the filter cardinality reduces to a
concrete natural-number equality at elaboration time.

These per-prime-power facts, together with S5
(`card_filter_sq_eq_one_units_zmod_prime_pow_odd`), are the base-case
inputs that the eventual CRT multiplicativity step (S6) consumes when
assembling the closed-form `numSqrtsOne(n) = 2^(ω_odd(n) + ε₂(n))`
formula. -/

/-- **S5b.1 — `(ZMod 2)ˣ` has exactly one square root of `1`.**

The unit group `(ZMod 2)ˣ` is trivial: only the residue `1` is coprime
to `2`, so `|(ZMod 2)ˣ| = φ(2) = 1`. The unique element is the identity,
which satisfies `1^2 = 1`. Count = `1`.

This is the `ε₂(n) = 0` half of the two-adic correction: when `2 ∥ n`
(i.e. `v₂(n) = 1`), the power-of-2 factor contributes no extra square
roots beyond the trivial one. -/
theorem card_filter_sq_eq_one_units_zmod_two :
    (Finset.univ.filter (fun u : (ZMod 2)ˣ => u ^ 2 = 1)).card = 1 := by
  decide

/-- **S5b.2 — `(ZMod 4)ˣ` has exactly two square roots of `1`.**

The unit group `(ZMod 4)ˣ = {1, 3}` is cyclic of order 2 (cardinality
`φ(4) = 2`). Both elements satisfy `u^2 = 1`: `1^2 = 1` directly, and
`3^2 = 9 ≡ 1 (mod 4)`. Count = `2`.

This is the `ε₂(n) = 1` case of the two-adic correction: when `4 ∥ n`
(i.e. `v₂(n) = 2`), the power-of-2 factor contributes a single extra
square root (`-1 ≡ 3 (mod 4)`), doubling the count.

Alternative proof (not used here, for reference): `(ZMod 4)ˣ` is cyclic
of even order, so the S4 generic `card_filter_sq_eq_one_cyclic_even`
applies directly. The `decide` route is shorter (no `IsCyclic` instance
plumbing) and equally robust at this small size. -/
theorem card_filter_sq_eq_one_units_zmod_four :
    (Finset.univ.filter (fun u : (ZMod 4)ˣ => u ^ 2 = 1)).card = 2 := by
  decide

end GaussWilsonNonCyclicOQ03
