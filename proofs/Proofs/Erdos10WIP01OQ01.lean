import Proofs.Erdos10WIP01

/-
# Erdős #10 — WIP-01 / OQ-01: bounded-offset certification of Granville–Soundararajan witnesses

## Context (parent Erdős Problem #10: sums of a prime and powers of 2)

`Erdos10WIP01` proved the characterization

> `IsPrimePlusKPowers k n ↔ ∃ p prime, p ≤ n ∧ popcount (n − p) ≤ k`     (`isPrimePlusKPowers_iff_popcount`)

which still phrases membership as a search over **all primes `p ≤ n`** — an `O(n / log n)`
sweep, far out of kernel reach for the 10-digit Granville–Soundararajan witnesses.

This file supplies the dual, **bounded** form. Substituting `m = n − p` turns the prime sweep
into a search over **offsets**:

> `IsPrimePlusKPowers k n ↔ ∃ m ≤ n, popcount m ≤ k ∧ (n − m) prime`     (`isPrimePlusKPowers_iff_offset`)

The offsets with `popcount m ≤ k` number only `∑_{j≤k} C(⌊log₂ n⌋+1, j) = O((log n)^k)` — a few
thousand for `k = 3, n ≈ 2³⁰`, versus tens of millions of primes. **This is the reformulation that
makes a witness checkable at all without enumerating primes.**

## Concrete certification (no `native_decide`)

We then *use* the bounded form to settle the smallest concrete witness of the Granville–
Soundararajan phenomenon, the smallest even integer that genuinely needs three powers of two:

> **`906` is a prime plus three powers of two, but not a prime plus at most two.**
> (`need_exactly_three_906`)

`906 = 887 + 2⁰ + 2¹ + 2⁴` gives the upper witness. For the lower bound, the bounded form
collapses `¬ IsPrimePlusKPowers 2 906` to the finite statement "no offset `2^a` or `2^a + 2^b`
(`a, b < 10`, since `2¹⁰ = 1024 > 906`) makes `906 − offset` prime" — `56` candidates, all
composite — which the **kernel** decides (`decide`, not `native_decide`): the result is genuinely
`0`-axiom (`propext / Quot.sound / Classical.choice` only, no `Lean.ofReduceBool`).

The 10-digit witness `1117175146` is the same shape with `~4500` offsets; the kernel primality
checks there are individually feasible but the aggregate is heavy, and the honest route to it is a
covering-congruence certificate (a fixed finite set of primes dividing `n − 2^a − 2^b − 2^c` for
every exponent triple). See the closing assessment.

Tags: number-theory, primes, powers-of-two, binary, popcount, additive-combinatorics, erdos
-/

namespace Erdos10WIP01OQ01

open Erdos10OQ02 Erdos10WIP01

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: THE BOUNDED-OFFSET REFORMULATION

Substitute `m = n − p`: searching primes `p ≤ n` ⟺ searching offsets `m ≤ n`.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- **Bounded-offset form of the Erdős #10 predicate.** `n` is a prime plus at most `k` powers of
    two iff some offset `m ≤ n` of binary popcount `≤ k` has `n − m` prime.

    This is `isPrimePlusKPowers_iff_popcount` after the involution `p ↦ n − p`: the unbounded prime
    sweep becomes a search over the `O((log n)^k)` offsets with `popcount ≤ k`. It is the form a
    witness certificate actually consumes — only finitely many `m` need be inspected. -/
theorem isPrimePlusKPowers_iff_offset (k n : ℕ) :
    IsPrimePlusKPowers k n ↔ ∃ m, m ≤ n ∧ popcount m ≤ k ∧ (n - m).Prime := by
  rw [isPrimePlusKPowers_iff_popcount]
  constructor
  · rintro ⟨p, hp, hpn, hpc⟩
    exact ⟨n - p, Nat.sub_le _ _, hpc, by rwa [Nat.sub_sub_self hpn]⟩
  · rintro ⟨m, hmn, hmc, hp⟩
    exact ⟨n - m, hp, Nat.sub_le _ _, by rwa [Nat.sub_sub_self hmn]⟩

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: STRUCTURE OF `≤ 2`-POWER OFFSETS

A sum of at most two powers of two is `0`, a single power, or a pair — read straight off the
exponent multiset (card `≤ 2`). Exponents are bounded by the value.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- A sum of **at most two** powers of two is `0`, a single power `2^a`, or `2^a + 2^b`.
    Direct from the exponent multiset `s` (`s.card ≤ 2`): split on `card ∈ {0, 1, 2}`. -/
theorem repWithAtMost_two_shape {m : ℕ} (h : RepWithAtMost 2 m) :
    m = 0 ∨ (∃ a, m = 2 ^ a) ∨ (∃ a b, m = 2 ^ a + 2 ^ b) := by
  obtain ⟨s, hcard, hsum⟩ := h
  subst hsum
  interval_cases hc : s.card
  · -- card 0
    rw [Multiset.card_eq_zero] at hc; subst hc; simp
  · -- card 1
    obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp hc
    refine Or.inr (Or.inl ⟨a, ?_⟩); simp [powSum]
  · -- card 2
    obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp hc
    refine Or.inr (Or.inr ⟨a, b, ?_⟩)
    simp [powSum, Multiset.insert_eq_cons]

/-- If `2 ^ a ≤ 906` then `a < 10` (as `2¹⁰ = 1024 > 906`). -/
theorem exp_lt_ten {a : ℕ} (h : 2 ^ a ≤ 906) : a < 10 := by
  by_contra hge
  push_neg at hge
  have : (2 : ℕ) ^ 10 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hge
  norm_num at this
  omega

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: CERTIFYING THE WITNESS `906` WITHOUT `native_decide`

`906` is the smallest even integer needing three powers of two.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- The finite, kernel-decidable search underlying `¬ IsPrimePlusKPowers 2 906`: `906` itself,
    or some `906 − 2^a` (`a < 10`), or some `906 − 2^a − 2^b` (`a, b < 10`), is prime. All `56`
    candidates are composite, so this is `False` — by the **kernel** `decide`, not `native_decide`. -/
def search906 : Prop :=
  (906 : ℕ).Prime ∨
    (∃ a : Fin 10, ((906 - 2 ^ (a : ℕ)) : ℕ).Prime) ∨
    (∃ a b : Fin 10, ((906 - 2 ^ (a : ℕ) - 2 ^ (b : ℕ)) : ℕ).Prime)

/-- Membership of `906` in `prime + ≤ 2 powers` would force one of the finitely many bounded
    offsets to land on a prime. -/
theorem isPrimePlus2_906_imp_search (h : IsPrimePlusKPowers 2 906) : search906 := by
  obtain ⟨p, hp, m, hm, hnm⟩ := h            -- 906 = p + m, p prime, RepWithAtMost 2 m
  have hm906 : m ≤ 906 := by omega
  rcases repWithAtMost_two_shape hm with h0 | ⟨a, ha⟩ | ⟨a, b, hab⟩
  · -- m = 0 ⇒ 906 = p prime
    refine Or.inl ?_
    have : p = 906 := by omega
    rwa [this] at hp
  · -- m = 2^a ⇒ 906 − 2^a = p prime, a < 10
    refine Or.inr (Or.inl ⟨⟨a, exp_lt_ten (ha ▸ hm906)⟩, ?_⟩)
    have hpe : (906 : ℕ) - 2 ^ a = p := by omega
    simpa [hpe] using hp
  · -- m = 2^a + 2^b ⇒ 906 − 2^a − 2^b = p prime, a,b < 10
    have hmle : 2 ^ a + 2 ^ b ≤ 906 := hab ▸ hm906
    have h2a : 2 ^ a ≤ 906 := le_trans (Nat.le_add_right _ _) hmle
    have h2b : 2 ^ b ≤ 906 := le_trans (Nat.le_add_left _ _) hmle
    refine Or.inr (Or.inr ⟨⟨a, exp_lt_ten h2a⟩, ⟨b, exp_lt_ten h2b⟩, ?_⟩)
    have hpe : (906 : ℕ) - 2 ^ a - 2 ^ b = p := by omega
    simpa [hpe] using hp

set_option maxRecDepth 100000 in
/-- **Lower bound.** `906` is *not* a prime plus at most two powers of two.
    The bounded search `search906` is refuted by the kernel `decide` (all `56` offsets composite);
    `isPrimePlus2_906_imp_search` then closes the contrapositive. No `native_decide`. -/
theorem not_isPrimePlusKPowers_two_906 : ¬ IsPrimePlusKPowers 2 906 := by
  have hsearch : ¬ search906 := by
    unfold search906
    decide
  exact fun h => hsearch (isPrimePlus2_906_imp_search h)

/-- **Upper witness.** `906 = 887 + 2⁰ + 2¹ + 2⁴` is a prime plus three powers of two. -/
theorem isPrimePlusKPowers_three_906 : IsPrimePlusKPowers 3 906 := by
  refine ⟨887, by norm_num, 19, ⟨{0, 1, 4}, by decide, by decide⟩, by norm_num⟩

/-- **`906` is a Granville–Soundararajan witness needing exactly three powers of two**: a prime
    plus three powers of two, but not a prime plus at most two. Fully certified, `0`-axiom, with no
    `native_decide` — the smallest even integer exhibiting the Erdős #10 "three powers" phenomenon. -/
theorem need_exactly_three_906 :
    IsPrimePlusKPowers 3 906 ∧ ¬ IsPrimePlusKPowers 2 906 :=
  ⟨isPrimePlusKPowers_three_906, not_isPrimePlusKPowers_two_906⟩

#check @isPrimePlusKPowers_iff_offset
#check @need_exactly_three_906

end Erdos10WIP01OQ01

/-
## Summary

- `isPrimePlusKPowers_iff_offset`: the **bounded-offset reformulation** of the Erdős #10 predicate
  — `IsPrimePlusKPowers k n ↔ ∃ m ≤ n, popcount m ≤ k ∧ (n − m) prime`. Converts the unbounded
  "search all primes `p ≤ n`" of `isPrimePlusKPowers_iff_popcount` into a search over the
  `O((log n)^k)` offsets of popcount `≤ k`. This is what makes any concrete witness checkable.
- `repWithAtMost_two_shape`: a `≤ 2`-power sum is `0`, `2^a`, or `2^a + 2^b` (exponent multiset of
  card `≤ 2`); `exp_lt_ten` bounds the exponents from the value.
- `need_exactly_three_906`: **`906` needs exactly three powers of two** (`= 887 + 1 + 2 + 16`, and
  not a prime plus `≤ 2`). The lower bound runs the bounded search `search906` through the **kernel**
  `decide` over its `56` composite offsets — `0`-axiom, **no `native_decide`** (no `Lean.ofReduceBool`).

## Infrastructure assessment: the 10-digit witness `1117175146`

**Needed**: `¬ IsPrimePlusKPowers 3 1117175146`. Via `isPrimePlusKPowers_iff_offset` this is the finite
claim "`1117175146 − m` is composite for every `m` with `popcount m ≤ 3`" — `≈ 4526` offsets
(`m = 0, 2^a, 2^a+2^b, 2^a+2^b+2^c`, exponents `< 31` since `2³¹ > 1117175146`).

**Size estimate / decision**: BUILD (offset reduction) done here; the *aggregate* compositeness check
is the remaining work. Two honest routes, both substantial:
- **Kernel `decide`**: each `Nat.Prime` test on a 10-digit number is kernel-feasible, but `~4526` of
  them in one `decide` is heavy (minutes–hours, large memory) — and any `native_decide` shortcut would
  forfeit the `0`-axiom status (it pulls in `Lean.ofReduceBool`).
- **Covering certificate** (the mathematically faithful route): a fixed finite prime set
  `{3, 5, 7, 13, 17, 241, …}` such that some member divides `1117175146 − 2^a − 2^b − 2^c` for *every*
  exponent triple (a covering system on the exponents mod `lcm` of the orders of `2`). This replaces
  `4526` primality tests by a finite residue computation, but formalizing the covering system is a
  multi-session build. `need_exactly_three_906` is the same statement at a scale where the kernel can
  close it directly — the working template for the covering build.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/
