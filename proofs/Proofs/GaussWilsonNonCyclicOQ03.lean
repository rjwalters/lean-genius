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
* Originally stated the main theorem `card_sqrts_one_eq_numSqrtsOne` as an
  open target (closed in S7 — see Section 12; no open targets remain).
* **S3 NEW**: ring↔unit bridge `card_sqrts_one_eq_card_units_sqrts_one`
  reducing the ZMod-side count to a unit-group count, so that subsequent
  sessions can work entirely inside `(ZMod n)ˣ` where the cyclic-group
  structure (`ZMod.isCyclic_units_of_prime_pow` etc.) applies.

## Session history

* **S4/S4-prep**: order-2 decomposition + generic cyclic-even count = 2.
* **S5**: odd-prime-power unit count = 2.
* **S5b.1/2/3**: power-of-2 unit counts (1, 2, 4 for k = 1, 2, ≥ 3).
* **S6**: CRT multiplicativity of the count across coprime moduli
  (Section 10), via `ZMod.chineseRemainder` + `MulEquiv.prodUnits`,
  following the `Nat.totient_mul` template.
* **S7**: closed-form bookkeeping (Section 11) and the final induction via
  `Nat.recOnPosPrimePosCoprime` (Section 12), closing the main theorem
  `card_sqrts_one_eq_numSqrtsOne`.

## Status

**0 sorries, 0 axioms — main theorem fully proved (S6+S7).**
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
-- Section 3: Main theorem (statement moved to Section 12)
-- ============================================================================

/- **Main theorem (OQ-03).**

The number of solutions of `x² = 1` in `ZMod n` equals the closed-form count
`numSqrtsOne n = 2 ^ (ω_odd(n) + ε₂(n))`.

This is the quantitative upgrade of the parent's qualitative `≥ 3` bound
(`GaussWilsonNonCyclic.card_sq_eq_one_ge_three`).

From S2 through S5b.3 the theorem `card_sqrts_one_eq_numSqrtsOne` was *stated*
here with `sorry` while the supporting sections below were built up.  S6/S7
closed the proof; since Lean requires dependencies to precede their use, the
theorem now lives at the **end of the file** (Section 12), where it is proved
from the S3 bridge (Section 4) and the unit-side assembly
`card_filter_sq_eq_one_units_eq_numSqrtsOne` (Section 12). -/

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

-- ============================================================================
-- Section 9: Structural power-of-2 case k ≥ 3 (S5b.3)
-- ============================================================================

/-! ### S5b.3 — `(ZMod 2^k)ˣ` has exactly four square roots of `1` for `k ≥ 3`

This is the structural (`ε₂(n) = 2`) leg of the two-adic correction. Unlike
the `k ∈ {1, 2}` cases (`decide` over a fixed finite group), the count here
must be established uniformly in `k`, because `(ZMod 2^k)ˣ` is **non-cyclic**
for `k ≥ 3` (`ZMod.isCyclic_units_two_pow_iff : IsCyclic (ZMod 2^n)ˣ ↔ n ≤ 2`)
— it is `ℤ/2 × ℤ/2^(k-2)`, generated by `-1` (order `2`) and `5`
(order `2^(k-2)`, via `ZMod.orderOf_five`).

The four square roots of `1` are exactly `{1, -1, s, -s}` with
`s = 2^(k-1) - 1`; note `-s = 1 + 2^(k-1)` because `-2^(k-1) = 2^(k-1)` in
`ZMod 2^k` (as `2 · 2^(k-1) = 2^k = 0`). Each squares to `1`:
`s² = 2^(2k-2) - 2^k + 1 = 1` since both `2^(2k-2)` (as `2k-2 ≥ k`) and `2^k`
vanish in `ZMod 2^k`. They are the *only* roots: `x² = 1` gives
`2^k ∣ (x-1)(x+1)`, and since consecutive even numbers `x∓1` share exactly
one factor of `2`, one of `x∓1` is divisible by `2^(k-1)`, pinning `x` to one
of the four residues.
-/

/-- Number-theoretic core of S5b.3. For `k ≥ 2`, an odd `a` with
`2^k ∣ a² - 1` has `2^(k-1) ∣ a - 1` or `2^(k-1) ∣ a + 1`.

Writing `a = 2m+1`, we get `a² - 1 = 4·m·(m+1)`, hence
`2^(k-2) ∣ m·(m+1)`. Since `m` and `m+1` are coprime, the prime power
`2^(k-2)` divides whichever of them is even, and multiplying by the
factor `2` from `a∓1 = 2·m` (resp. `2·(m+1)`) yields `2^(k-1)`. -/
private theorem two_pow_dvd_split (k : ℕ) (hk : 2 ≤ k) {a : ℕ}
    (hodd : Odd a) (hdvd : 2 ^ k ∣ a ^ 2 - 1) :
    2 ^ (k - 1) ∣ a - 1 ∨ 2 ^ (k - 1) ∣ a + 1 := by
  obtain ⟨m, rfl⟩ := hodd
  have hsq : (2 * m + 1) ^ 2 - 1 = 2 ^ 2 * (m * (m + 1)) := by
    have h : (2 * m + 1) ^ 2 = 2 ^ 2 * (m * (m + 1)) + 1 := by ring
    omega
  rw [hsq] at hdvd
  have hk2 : 2 ^ k = 2 ^ 2 * 2 ^ (k - 2) := by rw [← pow_add]; congr 1; omega
  rw [hk2] at hdvd
  have hdvd' : 2 ^ (k - 2) ∣ m * (m + 1) :=
    (mul_dvd_mul_iff_left (by norm_num : ((2 : ℕ) ^ 2) ≠ 0)).mp hdvd
  have hk1 : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by rw [← pow_succ']; congr 1; omega
  rcases Nat.even_or_odd m with hm | hm
  · -- `m` even ⇒ `m+1` odd ⇒ `2^(k-2) ∣ m`
    have hndvd : ¬ (2 ∣ (m + 1)) := by have := Nat.even_iff.mp hm; omega
    have hco : Nat.Coprime (2 ^ (k - 2)) (m + 1) :=
      Nat.Coprime.pow_left _ ((Nat.prime_two.coprime_iff_not_dvd).mpr hndvd)
    have hdm : 2 ^ (k - 2) ∣ m := hco.dvd_of_dvd_mul_right hdvd'
    left
    rw [show 2 * m + 1 - 1 = 2 * m from by omega, hk1]
    exact Nat.mul_dvd_mul_left 2 hdm
  · -- `m` odd ⇒ `2^(k-2) ∣ m+1`
    have hndvd : ¬ (2 ∣ m) := by have := Nat.odd_iff.mp hm; omega
    have hco : Nat.Coprime (2 ^ (k - 2)) m :=
      Nat.Coprime.pow_left _ ((Nat.prime_two.coprime_iff_not_dvd).mpr hndvd)
    have hdm : 2 ^ (k - 2) ∣ (m + 1) := hco.dvd_of_dvd_mul_left hdvd'
    right
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) from by omega, hk1]
    exact Nat.mul_dvd_mul_left 2 hdm

/-- **S5b.3 ACT — power-of-2 (`k ≥ 3`) unit count.**

For any `k ≥ 3`, the number of square roots of unity in `(ZMod 2^k)ˣ` equals
exactly `4`. This is the structural even-prime endpoint: `(ZMod 2^k)ˣ` is
non-cyclic (`≅ ℤ/2 × ℤ/2^(k-2)`), so its `2`-torsion has rank `2`, giving
`2² = 4` solutions of `u² = 1` — namely the units lifting
`{1, -1, 2^(k-1)-1, 2^(k-1)+1}`.

Together with `card_filter_sq_eq_one_units_zmod_prime_pow_odd` (S5, odd
prime powers, count `2`), `card_filter_sq_eq_one_units_zmod_two` (`k=1`,
count `1`) and `card_filter_sq_eq_one_units_zmod_four` (`k=2`, count `2`),
this closes all per-prime-power unit-side counts feeding the CRT
multiplicativity step (S6). -/
theorem card_filter_sq_eq_one_units_zmod_two_pow_ge_three
    (k : ℕ) (hk : 3 ≤ k) [NeZero (2 ^ k)] :
    (Finset.univ.filter (fun u : (ZMod (2 ^ k))ˣ => u ^ 2 = 1)).card = 4 := by
  classical
  -- Reduce the unit-side count to the ring-side count via the S3 bridge.
  rw [← card_sqrts_one_eq_card_units_sqrts_one (2 ^ k)]
  -- Useful arithmetic facts about powers of two.
  have hpow : 4 ≤ 2 ^ (k - 1) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hkeq : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  haveI hfact : Fact (1 < 2 ^ k) := ⟨by omega⟩
  -- The four roots, as natural numbers below `2^k`.
  set S : Finset ℕ := {1, 2 ^ (k - 1) - 1, 2 ^ (k - 1) + 1, 2 ^ k - 1} with hS
  -- `t = 2^(k-1)` in the ring, with `t² = 0` and `2t = 0`.
  set t : ZMod (2 ^ k) := (2 : ZMod (2 ^ k)) ^ (k - 1) with ht
  have h2k : (2 : ZMod (2 ^ k)) ^ k = 0 := by
    have h : ((2 ^ k : ℕ) : ZMod (2 ^ k)) = 0 := ZMod.natCast_self _
    push_cast at h; exact h
  have ht2 : t ^ 2 = 0 := by
    rw [ht, ← pow_mul, show (k - 1) * 2 = k + (k - 2) from by omega, pow_add, h2k,
      zero_mul]
  have h2t : (2 : ZMod (2 ^ k)) * t = 0 := by
    rw [ht, mul_comm, ← pow_succ, show k - 1 + 1 = k from by omega]; exact h2k
  -- Cast bridges relating the natural-number roots to ring expressions.
  have hone : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have hone' : 1 ≤ 2 ^ (k - 1) := by omega
  have e1 : ((2 ^ (k - 1) - 1 : ℕ) : ZMod (2 ^ k)) = t - 1 := by
    rw [Nat.cast_sub hone']; push_cast; rw [ht]
  have e2 : ((2 ^ (k - 1) + 1 : ℕ) : ZMod (2 ^ k)) = t + 1 := by
    push_cast; rw [ht]
  have e3 : ((2 ^ k - 1 : ℕ) : ZMod (2 ^ k)) = -1 := by
    rw [Nat.cast_sub hone, ZMod.natCast_self]; push_cast; ring
  -- The square-root filter equals the image of `S` under `Nat.cast`.
  have hfilter : Finset.univ.filter (fun x : ZMod (2 ^ k) => x ^ 2 = 1)
      = S.image (Nat.cast) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hS,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · -- Forward: `x² = 1` forces `x.val` into `S`.
      intro hx
      have hxval_lt : x.val < 2 ^ k := ZMod.val_lt x
      have hxne : x.val ≠ 0 := by
        intro h0
        rw [ZMod.val_eq_zero] at h0
        rw [h0] at hx; simp at hx
      have hcast : ((x.val ^ 2 : ℕ) : ZMod (2 ^ k)) = ((1 : ℕ) : ZMod (2 ^ k)) := by
        push_cast; rw [ZMod.natCast_rightInverse x]; exact hx
      have hmod : x.val ^ 2 ≡ 1 [MOD 2 ^ k] :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
      have hge : 1 ≤ x.val ^ 2 := Nat.one_le_pow _ _ (by omega)
      have hdvd : 2 ^ k ∣ x.val ^ 2 - 1 :=
        (Nat.modEq_iff_dvd' hge).mp hmod.symm
      have hodd : Odd x.val := by
        rcases Nat.even_or_odd x.val with he | ho
        · exfalso
          have h2 : (2 : ℕ) ∣ x.val ^ 2 - 1 :=
            dvd_trans (dvd_pow_self 2 (by omega : k ≠ 0)) hdvd
          have hev : Even (x.val ^ 2) := by rw [pow_two]; exact he.mul_right _
          rw [Nat.even_iff] at hev
          omega
        · exact ho
      have hsplit := two_pow_dvd_split k (by omega) hodd hdvd
      refine ⟨x.val, ?_, ZMod.natCast_rightInverse x⟩
      rcases hsplit with hL | hR
      · obtain ⟨c, hc⟩ := hL
        have hclt : c < 2 := by
          by_contra h
          have : 2 ^ (k - 1) * 2 ≤ x.val - 1 := by
            rw [hc]; exact Nat.mul_le_mul (le_refl _) (by omega)
          omega
        interval_cases c <;> omega
      · obtain ⟨c, hc⟩ := hR
        have hclt : c ≤ 2 := by
          by_contra h
          have : 2 ^ (k - 1) * 3 ≤ x.val + 1 := by
            rw [hc]; exact Nat.mul_le_mul (le_refl _) (by omega)
          omega
        interval_cases c <;> omega
    · -- Reverse: each element of `S` squares to `1`.
      rintro ⟨a, ha, rfl⟩
      rcases ha with rfl | rfl | rfl | rfl
      · simp
      · rw [e1]
        calc (t - 1) ^ 2 = t ^ 2 - 2 * t + 1 := by ring
          _ = 0 - 0 + 1 := by rw [ht2, h2t]
          _ = 1 := by ring
      · rw [e2]
        calc (t + 1) ^ 2 = t ^ 2 + 2 * t + 1 := by ring
          _ = 0 + 0 + 1 := by rw [ht2, h2t]
          _ = 1 := by ring
      · rw [e3]; ring
  -- `Nat.cast` is injective on `S` (all elements are `< 2^k`).
  have hInj : Set.InjOn (Nat.cast : ℕ → ZMod (2 ^ k)) ↑S := by
    intro a ha b hb hab
    simp only [hS, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rw [ZMod.natCast_eq_natCast_iff] at hab
    unfold Nat.ModEq at hab
    have halt : a < 2 ^ k := by omega
    have hblt : b < 2 ^ k := by omega
    rwa [Nat.mod_eq_of_lt halt, Nat.mod_eq_of_lt hblt] at hab
  -- The four naturals are pairwise distinct.
  have hd1 : (1 : ℕ) ∉ ({2 ^ (k - 1) - 1, 2 ^ (k - 1) + 1, 2 ^ k - 1} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hd2 : (2 ^ (k - 1) - 1 : ℕ) ∉ ({2 ^ (k - 1) + 1, 2 ^ k - 1} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hd3 : (2 ^ (k - 1) + 1 : ℕ) ∉ ({2 ^ k - 1} : Finset ℕ) := by
    simp only [Finset.mem_singleton]; omega
  -- Conclude: `card filter = card (image) = card S = 4`.
  rw [hfilter, Finset.card_image_of_injOn hInj, hS,
    Finset.card_insert_of_notMem hd1, Finset.card_insert_of_notMem hd2,
    Finset.card_insert_of_notMem hd3, Finset.card_singleton]

-- ============================================================================
-- Section 10: CRT multiplicativity (S6)
-- ============================================================================

/-! ### S6 — the square-root count is multiplicative across coprime moduli

Following the `Nat.totient_mul` template
(`Mathlib/Data/Nat/Totient.lean`), the unit group of `ZMod (m * n)` for
coprime `m, n` decomposes as

```
  (ZMod (m * n))ˣ  ≃*  (ZMod m × ZMod n)ˣ  ≃*  (ZMod m)ˣ × (ZMod n)ˣ
```

via `ZMod.chineseRemainder` (lifted to units by `Units.mapEquiv`) and
`MulEquiv.prodUnits`.  Since a `MulEquiv` preserves the predicate
`u² = 1`, and 2-torsion of a direct product splits componentwise
(`(g, h)² = 1 ↔ g² = 1 ∧ h² = 1`), the solution count is multiplicative.

Two generic helper lemmas package the transport and the product split;
`card_filter_sq_eq_one_units_mul_coprime` specialises to `ZMod`. -/

/-- **Transport of the square-root-of-unity count across a `MulEquiv`.**

A multiplicative equivalence `e : G ≃* H` maps `{g | g² = 1}` bijectively
onto `{h | h² = 1}` (its image under the injective map `e` is exactly the
target filter), so the two counts agree. -/
theorem card_filter_sq_eq_one_of_mulEquiv {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H] (e : G ≃* H) :
    (Finset.univ.filter (fun g : G => g ^ 2 = 1)).card =
      (Finset.univ.filter (fun h : H => h ^ 2 = 1)).card := by
  have himg : (Finset.univ.filter (fun g : G => g ^ 2 = 1)).image e =
      Finset.univ.filter (fun h : H => h ^ 2 = 1) := by
    ext h
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [← map_pow, hg, map_one]
    · intro hh
      exact ⟨e.symm h, by rw [← map_pow, hh, map_one], e.apply_symm_apply h⟩
  rw [← himg, Finset.card_image_of_injective _ e.injective]

/-- **2-torsion of a direct product splits componentwise.**

`(g, h)² = 1` iff `g² = 1` and `h² = 1`, so the solution filter of the
product group is the `Finset` product of the component filters and the
count factors. -/
theorem card_filter_sq_eq_one_prod {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H] :
    (Finset.univ.filter (fun w : G × H => w ^ 2 = 1)).card =
      (Finset.univ.filter (fun g : G => g ^ 2 = 1)).card *
        (Finset.univ.filter (fun h : H => h ^ 2 = 1)).card := by
  rw [← Finset.card_product]
  congr 1
  ext ⟨g, h⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
    Prod.pow_mk, Prod.mk_eq_one]

/-- **S6 ACT — CRT multiplicativity of the 2-torsion count.**

For coprime moduli `m, n`, the number of square roots of unity in
`(ZMod (m * n))ˣ` is the product of the counts for `(ZMod m)ˣ` and
`(ZMod n)ˣ`.  The proof composes the CRT ring isomorphism
`ZMod.chineseRemainder h : ZMod (m * n) ≃+* ZMod m × ZMod n` (lifted to
unit groups via `Units.mapEquiv`) with `MulEquiv.prodUnits`, then applies
the two generic lemmas above — exactly the rewrite chain of Mathlib's
`Nat.totient_mul`. -/
theorem card_filter_sq_eq_one_units_mul_coprime {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) :
    (Finset.univ.filter (fun u : (ZMod (m * n))ˣ => u ^ 2 = 1)).card =
      (Finset.univ.filter (fun u : (ZMod m)ˣ => u ^ 2 = 1)).card *
        (Finset.univ.filter (fun u : (ZMod n)ˣ => u ^ 2 = 1)).card := by
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  rw [card_filter_sq_eq_one_of_mulEquiv
      ((Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans
        MulEquiv.prodUnits)]
  exact card_filter_sq_eq_one_prod

-- ============================================================================
-- Section 11: Closed-form bookkeeping (S7 helpers)
-- ============================================================================

/-! ### S7 bookkeeping — `numSqrtsOne` matches the per-prime-power counts

The induction in Section 12 needs the closed form `numSqrtsOne` to mirror
the behaviour of the actual count: multiplicative across coprime factors
(matching S6) and evaluating to `2` at odd prime powers, `1 / 2 / 4` at
`2^1 / 2^2 / 2^(k≥3)` (matching S5/S5b).  Both `omegaOdd` and `epsTwo`
are additive across coprime products — `omegaOdd` because prime-factor
sets of coprime numbers are disjoint, `epsTwo` because at most one
coprime factor is even, so the two-adic data lives entirely in that
factor. -/

/-- `epsTwo` vanishes on odd numbers (no two-adic correction). -/
theorem epsTwo_of_odd {n : ℕ} (hn : Odd n) : epsTwo n = 0 := by
  have h2 : n % 2 = 1 := Nat.odd_iff.mp hn
  unfold epsTwo
  split_ifs with h8 h4 <;> omega

/-- Multiplying by an odd factor does not change `epsTwo`: an odd `n` is
coprime to every power of `2`, so `2^j ∣ m * n ↔ 2^j ∣ m`. -/
theorem epsTwo_mul_of_odd_right {m n : ℕ} (hn : Odd n) :
    epsTwo (m * n) = epsTwo m := by
  have h2 : n % 2 = 1 := Nat.odd_iff.mp hn
  have hnd : ¬ (2 : ℕ) ∣ n := by omega
  have hco : ∀ j : ℕ, 2 ^ j ∣ m * n ↔ 2 ^ j ∣ m := fun j =>
    ⟨fun hd => (Nat.Coprime.pow_left j
        ((Nat.prime_two.coprime_iff_not_dvd).mpr hnd)).dvd_of_dvd_mul_right hd,
      fun hd => Dvd.dvd.mul_right hd n⟩
  have hd8 := hco 3
  have hd4 := hco 2
  norm_num at hd8 hd4
  unfold epsTwo
  split_ifs <;> omega

/-- `epsTwo` is additive across coprime products: coprimality forces at
least one factor to be odd, and an odd factor contributes `0`. -/
theorem epsTwo_mul_of_coprime {m n : ℕ} (h : m.Coprime n) :
    epsTwo (m * n) = epsTwo m + epsTwo n := by
  rcases Nat.even_or_odd n with hn | hn
  · rcases Nat.even_or_odd m with hm | hm
    · -- both even contradicts coprimality
      exfalso
      have hg : (2 : ℕ) ∣ Nat.gcd m n := Nat.dvd_gcd hm.two_dvd hn.two_dvd
      have h1 : Nat.gcd m n = 1 := h
      omega
    · rw [mul_comm, epsTwo_mul_of_odd_right hm, epsTwo_of_odd hm]
      omega
  · rw [epsTwo_mul_of_odd_right hn, epsTwo_of_odd hn]
    omega

/-- `omegaOdd` is additive across coprime products: the prime-factor sets
are disjoint (`Nat.Coprime.disjoint_primeFactors`), so the odd-prime
filters partition the union. -/
theorem omegaOdd_mul_of_coprime {m n : ℕ} (h : m.Coprime n) :
    omegaOdd (m * n) = omegaOdd m + omegaOdd n := by
  unfold omegaOdd
  rw [Nat.Coprime.primeFactors_mul h, Finset.filter_union,
    Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter (Nat.Coprime.disjoint_primeFactors h))]

/-- `numSqrtsOne` is multiplicative across coprime products — the
closed-form mirror of the S6 CRT multiplicativity. -/
theorem numSqrtsOne_mul_of_coprime {m n : ℕ} (h : m.Coprime n) :
    numSqrtsOne (m * n) = numSqrtsOne m * numSqrtsOne n := by
  unfold numSqrtsOne
  rw [omegaOdd_mul_of_coprime h, epsTwo_mul_of_coprime h, ← pow_add]
  congr 1
  omega

/-- The closed form evaluates to `2` at odd prime powers, matching the S5
unit-side count: one odd prime factor, no two-adic correction. -/
theorem numSqrtsOne_prime_pow_odd {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : 0 < k) :
    numSqrtsOne (p ^ k) = 2 := by
  unfold numSqrtsOne omegaOdd
  rw [Nat.primeFactors_prime_pow (by omega : k ≠ 0) hp,
    epsTwo_of_odd ((hp.odd_of_ne_two hp2).pow), Finset.filter_singleton]
  simp [hp2]

/-- Powers of `2` have no odd prime factors. -/
theorem omegaOdd_two_pow {k : ℕ} (hk : k ≠ 0) : omegaOdd (2 ^ k) = 0 := by
  unfold omegaOdd
  rw [Nat.primeFactors_prime_pow hk Nat.prime_two, Finset.filter_singleton]
  simp

/-- The two-adic correction saturates at `2` once `8 ∣ 2^k`, i.e. `k ≥ 3`. -/
theorem epsTwo_two_pow_ge_three {k : ℕ} (hk : 3 ≤ k) : epsTwo (2 ^ k) = 2 := by
  have h8 : (8 : ℕ) ∣ 2 ^ k := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
    _ ∣ 2 ^ k := pow_dvd_pow 2 hk
  unfold epsTwo
  have hm : (2 : ℕ) ^ k % 8 = 0 := by omega
  simp [hm]

/-- Closed form at modulus `2`: count `1`, matching S5b.1. -/
theorem numSqrtsOne_two : numSqrtsOne 2 = 1 := by
  have h := omegaOdd_two_pow (k := 1) one_ne_zero
  norm_num at h
  simp [numSqrtsOne, h, epsTwo]

/-- Closed form at modulus `4`: count `2`, matching S5b.2. -/
theorem numSqrtsOne_four : numSqrtsOne 4 = 2 := by
  have h := omegaOdd_two_pow (k := 2) two_ne_zero
  norm_num at h
  simp [numSqrtsOne, h, epsTwo]

-- ============================================================================
-- Section 12: Induction assembly and the main theorem (S7)
-- ============================================================================

/-! ### S7 — assembling the closed form by `Nat.recOnPosPrimePosCoprime`

The four induction cases are exactly the four ingredient groups built in
S4–S6:

* `zero` — vacuous under `NeZero`.
* `one` — the trivial unit group `(ZMod 1)ˣ` has count `1 = numSqrtsOne 1`.
* `prime_pow` — `p = 2` splits into `k = 1 / k = 2 / k ≥ 3`
  (S5b.1/S5b.2/S5b.3, counts `1 / 2 / 4`); odd `p` is S5 (count `2`).
* `coprime` — S6 multiplicativity plus the Section-11 closed-form
  multiplicativity `numSqrtsOne_mul_of_coprime`. -/

/-- **S7 — unit-side assembly.**  For every `n ≠ 0`, the number of square
roots of unity in `(ZMod n)ˣ` equals the closed form
`numSqrtsOne n = 2 ^ (ω_odd(n) + ε₂(n))`.  Proved by induction on the
prime factorisation via `Nat.recOnPosPrimePosCoprime`. -/
theorem card_filter_sq_eq_one_units_eq_numSqrtsOne :
    ∀ (n : ℕ) [NeZero n],
      (Finset.univ.filter (fun u : (ZMod n)ˣ => u ^ 2 = 1)).card =
        numSqrtsOne n := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro _
    rcases eq_or_ne p 2 with rfl | hp2
    · -- p = 2: the three S5b regimes
      rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | hk3
      · show (Finset.univ.filter (fun u : (ZMod 2)ˣ => u ^ 2 = 1)).card =
          numSqrtsOne 2
        rw [card_filter_sq_eq_one_units_zmod_two, numSqrtsOne_two]
      · show (Finset.univ.filter (fun u : (ZMod 4)ˣ => u ^ 2 = 1)).card =
          numSqrtsOne 4
        rw [card_filter_sq_eq_one_units_zmod_four, numSqrtsOne_four]
      · rw [card_filter_sq_eq_one_units_zmod_two_pow_ge_three k hk3]
        unfold numSqrtsOne
        rw [omegaOdd_two_pow (by omega), epsTwo_two_pow_ge_three hk3]
        norm_num
    · -- p odd: S5
      rw [card_filter_sq_eq_one_units_zmod_prime_pow_odd hp hp2 hk,
        numSqrtsOne_prime_pow_odd hp hp2 hk]
  | zero =>
    intro h
    exact absurd rfl h.out
  | one =>
    intro inst
    have hall : ∀ u : (ZMod (1 : ℕ))ˣ, u ^ 2 = 1 := fun u =>
      Units.ext (Subsingleton.elim _ _)
    rw [Finset.filter_true_of_mem (fun u _ => hall u), Finset.card_univ,
      ZMod.card_units_eq_totient, Nat.totient_one]
    simp [numSqrtsOne, omegaOdd, epsTwo]
  | coprime a b ha hb hab iha ihb =>
    intro _
    haveI ha0 : NeZero a := ⟨by omega⟩
    haveI hb0 : NeZero b := ⟨by omega⟩
    rw [card_filter_sq_eq_one_units_mul_coprime hab, iha, ihb,
      numSqrtsOne_mul_of_coprime hab]

/-- **Main theorem (OQ-03) — exact count of square roots of unity.**

The number of solutions of `x² = 1` in `ZMod n` equals the closed-form
count `numSqrtsOne n = 2 ^ (ω_odd(n) + ε₂(n))`, where `ω_odd(n)` is the
number of distinct odd prime factors of `n` and `ε₂(n) ∈ {0, 1, 2}` is
the two-adic correction.

This is the quantitative upgrade of the parent's qualitative `≥ 3` bound
(`GaussWilsonNonCyclic.card_sq_eq_one_ge_three`): CRT reduces the count
to prime-power moduli (S6, Section 10), the per-prime-power counts are
`2` at odd prime powers and `1 / 2 / 4` at `2^1 / 2^2 / 2^(k≥3)`
(S5/S5b, Sections 7–9), and induction on the prime factorisation
assembles the closed form (S7, this section).  The ring-side count
reduces to the unit-side count through the S3 bridge (Section 4). -/
theorem card_sqrts_one_eq_numSqrtsOne (n : ℕ) [NeZero n] :
    (Finset.univ.filter (fun x : ZMod n => x ^ 2 = 1)).card = numSqrtsOne n := by
  rw [card_sqrts_one_eq_card_units_sqrts_one n,
    card_filter_sq_eq_one_units_eq_numSqrtsOne n]

end GaussWilsonNonCyclicOQ03
