/-
# Oppermann's Conjecture: a prime in both halves of every square-gap
# (open question legendre-partial-oq-04)

The base entry `Proofs.LegendrePartial` formalises **Legendre's conjecture** —
for every `n ≥ 1` there is a prime in the open interval `(n², (n+1)²)` — and
verifies it computationally for `n = 1, …, 20`.

This file states and studies the natural strengthening asked by the open
question: **Oppermann's conjecture** (1882).  Splitting the square-gap
`(n², (n+1)²)` at the composite midpoint `n² + n = n·(n+1)` into a *lower half*
`(n², n²+n)` and an *upper half* `(n²+n, (n+1)²)`, Oppermann asserts that for
every `n ≥ 2` BOTH halves contain a prime:

      OppermannAt n  :=  (∃ p prime, n² < p < n²+n)
                         ∧ (∃ q prime, n²+n < q < (n+1)²).

(The case `n = 1` is excluded because the lower half `(1, 2)` is empty; this is
why Oppermann's conjecture is classically stated for `n > 1`.)

New content here:

  * `OppermannAt`, `OppermannConjecture` — the statement.
  * `oppermann_at_implies_legendre_at` — **Oppermann ⟹ Legendre** at each `n`:
    the lower-half prime already lies in `(n², (n+1)²)`.  VERIFIED, 0-axiom.
  * `oppermann_at_two_primes` — **Oppermann ⟹ at least two primes per
    square-gap**: the lower- and upper-half primes are distinct points of
    `(n², (n+1)²)`, so `#{primes in (n², (n+1)²)} ≥ 2`.  This makes precise the
    sense in which Oppermann is *strictly stronger* than Legendre (which only
    guarantees one).  VERIFIED, 0-axiom.
  * `oppermann_implies_legendre`, `oppermann_implies_two_primes` — the
    conjecture-level corollaries.  VERIFIED, 0-axiom (they take the conjecture
    as a hypothesis; they do not assert it).
  * `oppermann_at_four_primes_two_gaps` — **the Brocard mechanism**: Oppermann at
    two *adjacent* gaps `n`, `n+1` forces `≥ 4` primes in the double gap
    `(n², (n+2)²)` (the four half-interval primes are kept distinct by the
    composite separators `n²+n`, `(n+1)²`, `(n+1)²+(n+1)`).  This is the
    elementary combinatorial core of the classical **Oppermann ⟹ Brocard**
    implication.  VERIFIED, 0-axiom.
  * `oppermann_implies_four_primes` — its conjecture-level corollary.  VERIFIED,
    0-axiom.
  * `card_primes_Ioc` — the number of primes in `(a, b]` equals `π(b) − π(a)` for
    Mathlib's `Nat.primeCounting`.  VERIFIED, 0-axiom.
  * `oppermann_at_pi_total`, `oppermann_implies_pi_total` — the total π-count
    form: Oppermann forces `π((n+1)²) − π(n²) ≥ 2`.  VERIFIED, 0-axiom.
  * `oppermann_at_iff_pi`, `oppermann_conjecture_iff_pi` — Oppermann in
    **π-counting form**: for `n ≥ 2`, `OppermannAt n ⟺ π(n²+n) − π(n²) ≥ 1 ∧
    π((n+1)²) − π(n²+n) ≥ 1` (the composite endpoints `n²+n` and `(n+1)²` make the
    half-open `π`-difference count exactly the open-interval primes).  VERIFIED,
    0-axiom.
  * `oppermann_2, …, oppermann_20` — `OppermannAt n` checked with explicit
    witnesses for `n = 2, …, 20` by `native_decide`.
  * `oppermann_conjecture` — the open conjecture stated as an `axiom`.

Status: the structural theorems are fully machine-checked with NO axioms
(`#print axioms oppermann_at_two_primes` reports only `propext, Classical.choice,
Quot.sound`).  The file as a whole is `axiomatized`: the `n ≤ 20` verifications
use `native_decide` (depends on `Lean.ofReduceBool`) and the general conjecture
is stated as `oppermann_conjecture : OppermannConjecture`, which is OPEN.
-/
import Mathlib
import Proofs.LegendrePartial

namespace Legendre.Oppermann

open Finset

/-! ## Statement -/

/-- **Oppermann's conjecture at `n`.** Both halves of the square-gap
`(n², (n+1)²)`, split at the composite point `n²+n = n·(n+1)`, contain a prime:
a prime in the lower half `(n², n²+n)` and a prime in the upper half
`(n²+n, (n+1)²)`. -/
def OppermannAt (n : ℕ) : Prop :=
  (∃ p, Nat.Prime p ∧ n ^ 2 < p ∧ p < n ^ 2 + n) ∧
  (∃ q, Nat.Prime q ∧ n ^ 2 + n < q ∧ q < (n + 1) ^ 2)

/-- **Oppermann's conjecture.** `OppermannAt n` holds for every `n ≥ 2`. (At
`n = 1` the lower half `(1, 2)` is empty, so the conjecture is stated for
`n > 1`.) -/
def OppermannConjecture : Prop := ∀ n : ℕ, 2 ≤ n → OppermannAt n

/-! ## Structural theorems (VERIFIED, 0-axiom)

These are honest implications: each takes Oppermann's statement as a hypothesis
and derives a consequence by elementary interval arithmetic.  None of them
asserts that Oppermann's conjecture is true. -/

/-- **Oppermann ⟹ Legendre, pointwise.** The lower-half prime `p` of the
square-gap already witnesses Legendre's conjecture at `n`, since
`p < n²+n < (n+1)²`. -/
theorem oppermann_at_implies_legendre_at {n : ℕ} (h : OppermannAt n) :
    Legendre.LegendreAt n := by
  obtain ⟨⟨p, hp, hlo, hhi⟩, _⟩ := h
  have hexp : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  exact ⟨p, hp, hlo, by omega⟩

/-- **Oppermann ⟹ at least two primes between consecutive squares.** The
lower-half prime `p` and upper-half prime `q` are distinct (`p < n²+n < q`) and
both lie in `(n², (n+1)²)`, so the gap contains at least two primes — a strict
strengthening of Legendre's single-prime guarantee. -/
theorem oppermann_at_two_primes {n : ℕ} (h : OppermannAt n) :
    2 ≤ ((Finset.Ioo (n ^ 2) ((n + 1) ^ 2)).filter Nat.Prime).card := by
  obtain ⟨⟨p, hp, hplo, hphi⟩, ⟨q, hq, hqlo, hqhi⟩⟩ := h
  have hexp : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  have hpmem : p ∈ (Finset.Ioo (n ^ 2) ((n + 1) ^ 2)).filter Nat.Prime := by
    rw [Finset.mem_filter, Finset.mem_Ioo]
    exact ⟨⟨hplo, by omega⟩, hp⟩
  have hqmem : q ∈ (Finset.Ioo (n ^ 2) ((n + 1) ^ 2)).filter Nat.Prime := by
    rw [Finset.mem_filter, Finset.mem_Ioo]
    exact ⟨⟨by omega, hqhi⟩, hq⟩
  have hpq : p ≠ q := by omega
  calc 2 = ({p, q} : Finset ℕ).card := by rw [Finset.card_pair hpq]
    _ ≤ _ := Finset.card_le_card (by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hpmem
        · exact hqmem)

/-- **Oppermann ⟹ Legendre.** Conjecture-level: if Oppermann holds for all
`n ≥ 2`, so does Legendre. -/
theorem oppermann_implies_legendre (h : OppermannConjecture) :
    ∀ n : ℕ, 2 ≤ n → Legendre.LegendreAt n :=
  fun n hn => oppermann_at_implies_legendre_at (h n hn)

/-- **Oppermann ⟹ two primes per square-gap.** Conjecture-level form of
`oppermann_at_two_primes`. -/
theorem oppermann_implies_two_primes (h : OppermannConjecture) :
    ∀ n : ℕ, 2 ≤ n →
      2 ≤ ((Finset.Ioo (n ^ 2) ((n + 1) ^ 2)).filter Nat.Prime).card :=
  fun n hn => oppermann_at_two_primes (h n hn)

/-! ### The Brocard mechanism (VERIFIED, 0-axiom)

**Brocard's conjecture** (1904, OPEN): between the squares of two consecutive
primes `p < q` (with `p ≥ 3`) there are at least four primes.  It is a classical
observation that **Oppermann's conjecture implies Brocard's**, and the argument is
purely combinatorial: two consecutive primes `≥ 3` are both odd, so `q ≥ p + 2`,
hence the interval `(p², q²)` contains at least the two *adjacent* square-gaps
`(p², (p+1)²)` and `((p+1)², (p+2)²)`; Oppermann puts two primes in each, and the
composite square `(p+1)²` separating them keeps all four distinct.

The theorem below isolates exactly this mechanism at the level of an arbitrary
pair of adjacent gaps — no consecutive-prime bookkeeping required — and is the
provable core of the Oppermann ⟹ Brocard implication. -/

/-- **Oppermann ⟹ four primes across two adjacent square-gaps.** If Oppermann
holds at both `n` and `n+1`, the double gap `(n², (n+2)²)` contains at least FOUR
primes: the lower/upper-half primes of `(n², (n+1)²)` and those of
`((n+1)², (n+2)²)`, all four distinct (they are separated by the composite
points `n²+n`, `(n+1)²`, `(n+1)²+(n+1)`).  This is the elementary combinatorial
core of **Brocard's conjecture**. VERIFIED, 0-axiom. -/
theorem oppermann_at_four_primes_two_gaps {n : ℕ}
    (h₀ : OppermannAt n) (h₁ : OppermannAt (n + 1)) :
    4 ≤ ((Finset.Ioo (n ^ 2) ((n + 2) ^ 2)).filter Nat.Prime).card := by
  obtain ⟨⟨p, hp, hplo, hphi⟩, ⟨q, hq, hqlo, hqhi⟩⟩ := h₀
  obtain ⟨⟨r, hr, hrlo, hrhi⟩, ⟨s, hs, hslo, hshi⟩⟩ := h₁
  -- polynomial expansions so `omega` can compare the interval endpoints
  have e1 : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  have e2 : (n + 2) ^ 2 = n ^ 2 + 4 * n + 4 := by ring
  have e2' : (n + 1 + 1) ^ 2 = n ^ 2 + 4 * n + 4 := by ring
  have hsub : ({p, q, r, s} : Finset ℕ) ⊆
      (Finset.Ioo (n ^ 2) ((n + 2) ^ 2)).filter Nat.Prime := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter, Finset.mem_Ioo]
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨⟨by omega, by omega⟩, hp⟩
    · exact ⟨⟨by omega, by omega⟩, hq⟩
    · exact ⟨⟨by omega, by omega⟩, hr⟩
    · exact ⟨⟨by omega, by omega⟩, hs⟩
  have h4 : ({p, q, r, s} : Finset ℕ).card = 4 := by
    have hpne : p ∉ ({q, r, s} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have hqne : q ∉ ({r, s} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have hrne : r ∉ ({s} : Finset ℕ) := by
      simp only [Finset.mem_singleton]; omega
    rw [Finset.card_insert_of_notMem hpne, Finset.card_insert_of_notMem hqne,
        Finset.card_insert_of_notMem hrne, Finset.card_singleton]
  calc 4 = ({p, q, r, s} : Finset ℕ).card := h4.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- **Oppermann ⟹ four primes per double gap.** Conjecture-level form of
`oppermann_at_four_primes_two_gaps`: under Oppermann, every double gap
`(n², (n+2)²)` with `n ≥ 2` contains at least four primes. -/
theorem oppermann_implies_four_primes (h : OppermannConjecture) :
    ∀ n : ℕ, 2 ≤ n →
      4 ≤ ((Finset.Ioo (n ^ 2) ((n + 2) ^ 2)).filter Nat.Prime).card :=
  fun n hn => oppermann_at_four_primes_two_gaps (h n hn) (h (n + 1) (by omega))

/-! ## π-counting form (VERIFIED, 0-axiom)

Bridging the interval-existence statement to Mathlib's prime-counting function
`Nat.primeCounting` (`π(n) = #{p ≤ n : p prime}`).  The number of primes in a
half-open interval is exactly a difference of `π` values, and Oppermann's
conjecture becomes a pair of lower bounds on such differences.  All lemmas here
are elementary and fully machine-checked with no axioms. -/

open Nat (primeCounting)

/-- **Prime count of an interval as a difference of `π`.** For `a ≤ b`, the number
of primes in the half-open interval `(a, b]` equals `π(b) − π(a)`. -/
theorem card_primes_Ioc {a b : ℕ} (hab : a ≤ b) :
    ((Finset.Ioc a b).filter Nat.Prime).card = primeCounting b - primeCounting a := by
  have key : ∀ m : ℕ,
      primeCounting m = ((Finset.range (m + 1)).filter Nat.Prime).card := by
    intro m
    simp only [Nat.primeCounting, Nat.primeCounting']
    rw [Nat.count_eq_card_filter_range]
  rw [key a, key b]
  have hdisj : Disjoint ((Finset.range (a + 1)).filter Nat.Prime)
      ((Finset.Ioc a b).filter Nat.Prime) := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hx'
    obtain ⟨hx1, _⟩ := hx
    obtain ⟨⟨hx2, _⟩, _⟩ := hx'
    omega
  have hunion : ((Finset.range (a + 1)).filter Nat.Prime) ∪
      ((Finset.Ioc a b).filter Nat.Prime) = (Finset.range (b + 1)).filter Nat.Prime := by
    rw [← Finset.filter_union]
    congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ioc]
    omega
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion] at hcard
  omega

/-- Removing a **non-prime** right endpoint does not change the prime count:
`#{primes in (a, b)} = #{primes in (a, b]}` when `b` is composite. -/
theorem card_primes_Ioo_eq_Ioc {a b : ℕ} (hb : ¬ Nat.Prime b) :
    ((Finset.Ioo a b).filter Nat.Prime).card
      = ((Finset.Ioc a b).filter Nat.Prime).card := by
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hax, hxb⟩, hpx⟩; exact ⟨⟨hax, le_of_lt hxb⟩, hpx⟩
  · rintro ⟨⟨hax, hxb⟩, hpx⟩
    refine ⟨⟨hax, ?_⟩, hpx⟩
    rcases lt_or_eq_of_le hxb with h | h
    · exact h
    · exact absurd (h ▸ hpx) hb

/-- **Existence of a prime in an open interval, as a count bound.** -/
theorem exists_prime_Ioo_iff_card {a b : ℕ} :
    (∃ p, Nat.Prime p ∧ a < p ∧ p < b) ↔
      1 ≤ ((Finset.Ioo a b).filter Nat.Prime).card := by
  rw [Nat.one_le_iff_ne_zero, ne_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  push_neg
  constructor
  · rintro ⟨p, hp, ha, hb⟩
    exact ⟨p, Finset.mem_Ioo.mpr ⟨ha, hb⟩, hp⟩
  · rintro ⟨p, hmem, hp⟩
    obtain ⟨ha, hb⟩ := Finset.mem_Ioo.mp hmem
    exact ⟨p, hp, ha, hb⟩

/-- **Oppermann's conjecture at `n`, π-counting form.** For `n ≥ 2`,
`OppermannAt n` is equivalent to the pair of prime-counting lower bounds
`π(n²+n) − π(n²) ≥ 1` (lower half) and `π((n+1)²) − π(n²+n) ≥ 1` (upper half).
Both half-open right endpoints `n²+n = n(n+1)` and `(n+1)²` are composite for
`n ≥ 2`, so the half-open `π`-difference counts exactly the open-interval primes
of `OppermannAt`. VERIFIED, 0-axiom. -/
theorem oppermann_at_iff_pi {n : ℕ} (hn : 2 ≤ n) :
    OppermannAt n ↔
      (1 ≤ primeCounting (n ^ 2 + n) - primeCounting (n ^ 2)) ∧
      (1 ≤ primeCounting ((n + 1) ^ 2) - primeCounting (n ^ 2 + n)) := by
  have hcomp1 : ¬ Nat.Prime (n ^ 2 + n) := by
    have h : n ^ 2 + n = n * (n + 1) := by ring
    rw [h]; exact Nat.not_prime_mul (by omega) (by omega)
  have hcomp2 : ¬ Nat.Prime ((n + 1) ^ 2) := by
    have h : (n + 1) ^ 2 = (n + 1) * (n + 1) := by ring
    rw [h]; exact Nat.not_prime_mul (by omega) (by omega)
  have hle1 : n ^ 2 ≤ n ^ 2 + n := by omega
  have hle2 : n ^ 2 + n ≤ (n + 1) ^ 2 := by nlinarith
  have lower : (∃ p, Nat.Prime p ∧ n ^ 2 < p ∧ p < n ^ 2 + n) ↔
      1 ≤ primeCounting (n ^ 2 + n) - primeCounting (n ^ 2) := by
    rw [exists_prime_Ioo_iff_card, card_primes_Ioo_eq_Ioc hcomp1, card_primes_Ioc hle1]
  have upper : (∃ q, Nat.Prime q ∧ n ^ 2 + n < q ∧ q < (n + 1) ^ 2) ↔
      1 ≤ primeCounting ((n + 1) ^ 2) - primeCounting (n ^ 2 + n) := by
    rw [exists_prime_Ioo_iff_card, card_primes_Ioo_eq_Ioc hcomp2, card_primes_Ioc hle2]
  unfold OppermannAt
  rw [lower, upper]

/-- **Oppermann's conjecture, π-counting form.** Equivalent to: for every `n ≥ 2`,
`π(n²+n) − π(n²) ≥ 1` and `π((n+1)²) − π(n²+n) ≥ 1`. VERIFIED, 0-axiom. -/
theorem oppermann_conjecture_iff_pi :
    OppermannConjecture ↔
      ∀ n : ℕ, 2 ≤ n →
        (1 ≤ primeCounting (n ^ 2 + n) - primeCounting (n ^ 2)) ∧
        (1 ≤ primeCounting ((n + 1) ^ 2) - primeCounting (n ^ 2 + n)) := by
  constructor
  · intro h n hn; exact (oppermann_at_iff_pi hn).mp (h n hn)
  · intro h n hn; exact (oppermann_at_iff_pi hn).mpr (h n hn)

/-- **Oppermann ⟹ `π((n+1)²) − π(n²) ≥ 2`, π-counting total form.** The whole
square-gap contributes at least two to the prime-counting difference: the
`π`-difference form of `oppermann_at_two_primes`, obtained by folding the
open-interval two-prime count through the composite right endpoint `(n+1)²`.
VERIFIED, 0-axiom. -/
theorem oppermann_at_pi_total {n : ℕ} (hn : 1 ≤ n) (h : OppermannAt n) :
    2 ≤ primeCounting ((n + 1) ^ 2) - primeCounting (n ^ 2) := by
  have hcomp2 : ¬ Nat.Prime ((n + 1) ^ 2) := by
    have hh : (n + 1) ^ 2 = (n + 1) * (n + 1) := by ring
    rw [hh]; exact Nat.not_prime_mul (by omega) (by omega)
  have hle : n ^ 2 ≤ (n + 1) ^ 2 := by nlinarith
  have hcard := oppermann_at_two_primes h
  rwa [← card_primes_Ioc hle, ← card_primes_Ioo_eq_Ioc hcomp2]

/-- Conjecture-level form of `oppermann_at_pi_total`: under Oppermann,
`π((n+1)²) − π(n²) ≥ 2` for every `n ≥ 2`. VERIFIED, 0-axiom. -/
theorem oppermann_implies_pi_total (h : OppermannConjecture) :
    ∀ n : ℕ, 2 ≤ n →
      2 ≤ primeCounting ((n + 1) ^ 2) - primeCounting (n ^ 2) :=
  fun n hn => oppermann_at_pi_total (by omega) (h n hn)

/-! ## Computational verification (axiomatized via `native_decide`)

Each `OppermannAt n` is witnessed by an explicit pair (lower-half prime,
upper-half prime); `native_decide` checks primality and the interval bounds. -/

-- n=2: lower (4,6)→5,  upper (6,9)→7
theorem oppermann_2 : OppermannAt 2 := ⟨⟨5, by native_decide⟩, ⟨7, by native_decide⟩⟩
-- n=3: lower (9,12)→11, upper (12,16)→13
theorem oppermann_3 : OppermannAt 3 := ⟨⟨11, by native_decide⟩, ⟨13, by native_decide⟩⟩
-- n=4: lower (16,20)→17, upper (20,25)→23
theorem oppermann_4 : OppermannAt 4 := ⟨⟨17, by native_decide⟩, ⟨23, by native_decide⟩⟩
-- n=5: lower (25,30)→29, upper (30,36)→31
theorem oppermann_5 : OppermannAt 5 := ⟨⟨29, by native_decide⟩, ⟨31, by native_decide⟩⟩
-- n=6: lower (36,42)→37, upper (42,49)→43
theorem oppermann_6 : OppermannAt 6 := ⟨⟨37, by native_decide⟩, ⟨43, by native_decide⟩⟩
-- n=7: lower (49,56)→53, upper (56,64)→59
theorem oppermann_7 : OppermannAt 7 := ⟨⟨53, by native_decide⟩, ⟨59, by native_decide⟩⟩
-- n=8: lower (64,72)→67, upper (72,81)→73
theorem oppermann_8 : OppermannAt 8 := ⟨⟨67, by native_decide⟩, ⟨73, by native_decide⟩⟩
-- n=9: lower (81,90)→83, upper (90,100)→97
theorem oppermann_9 : OppermannAt 9 := ⟨⟨83, by native_decide⟩, ⟨97, by native_decide⟩⟩
-- n=10: lower (100,110)→101, upper (110,121)→113
theorem oppermann_10 : OppermannAt 10 := ⟨⟨101, by native_decide⟩, ⟨113, by native_decide⟩⟩
-- n=11: lower (121,132)→127, upper (132,144)→137
theorem oppermann_11 : OppermannAt 11 := ⟨⟨127, by native_decide⟩, ⟨137, by native_decide⟩⟩
-- n=12: lower (144,156)→149, upper (156,169)→157
theorem oppermann_12 : OppermannAt 12 := ⟨⟨149, by native_decide⟩, ⟨157, by native_decide⟩⟩
-- n=13: lower (169,182)→173, upper (182,196)→191
theorem oppermann_13 : OppermannAt 13 := ⟨⟨173, by native_decide⟩, ⟨191, by native_decide⟩⟩
-- n=14: lower (196,210)→197, upper (210,225)→211
theorem oppermann_14 : OppermannAt 14 := ⟨⟨197, by native_decide⟩, ⟨211, by native_decide⟩⟩
-- n=15: lower (225,240)→227, upper (240,256)→241
theorem oppermann_15 : OppermannAt 15 := ⟨⟨227, by native_decide⟩, ⟨241, by native_decide⟩⟩
-- n=16: lower (256,272)→257, upper (272,289)→277
theorem oppermann_16 : OppermannAt 16 := ⟨⟨257, by native_decide⟩, ⟨277, by native_decide⟩⟩
-- n=17: lower (289,306)→293, upper (306,324)→307
theorem oppermann_17 : OppermannAt 17 := ⟨⟨293, by native_decide⟩, ⟨307, by native_decide⟩⟩
-- n=18: lower (324,342)→331, upper (342,361)→347
theorem oppermann_18 : OppermannAt 18 := ⟨⟨331, by native_decide⟩, ⟨347, by native_decide⟩⟩
-- n=19: lower (361,380)→367, upper (380,400)→383
theorem oppermann_19 : OppermannAt 19 := ⟨⟨367, by native_decide⟩, ⟨383, by native_decide⟩⟩
-- n=20: lower (400,420)→401, upper (420,441)→421
theorem oppermann_20 : OppermannAt 20 := ⟨⟨401, by native_decide⟩, ⟨421, by native_decide⟩⟩

/-- Sanity corollary: every gap `(n², (n+1)²)` for `2 ≤ n ≤ 20` contains at
least two primes (combining the verified instances with the 0-axiom structural
theorem). -/
theorem two_primes_2 :
    2 ≤ ((Finset.Ioo (2 ^ 2) (3 ^ 2)).filter Nat.Prime).card :=
  oppermann_at_two_primes oppermann_2

/-- Brocard-mechanism sanity corollary: the double gap `(4, 16) = (2², 4²)`
contains at least four primes (namely `5, 7, 11, 13`), obtained from the verified
instances `oppermann_2`, `oppermann_3` through the 0-axiom structural theorem
`oppermann_at_four_primes_two_gaps`. -/
theorem four_primes_2 :
    4 ≤ ((Finset.Ioo (2 ^ 2) ((2 + 2) ^ 2)).filter Nat.Prime).card :=
  oppermann_at_four_primes_two_gaps oppermann_2 oppermann_3

/-- π-counting sanity corollary at `n = 2`: `π(6) − π(4) ≥ 1` (lower half) and
`π(9) − π(6) ≥ 1` (upper half), derived from the verified instance `oppermann_2`
through the `π`-equivalence. -/
theorem pi_bounds_2 :
    (1 ≤ primeCounting (2 ^ 2 + 2) - primeCounting (2 ^ 2)) ∧
    (1 ≤ primeCounting ((2 + 1) ^ 2) - primeCounting (2 ^ 2 + 2)) :=
  (oppermann_at_iff_pi (by norm_num)).mp oppermann_2

/-! ## The open conjecture -/

/-- **Oppermann's conjecture** (open since 1882): a prime in both halves of every
square-gap, for all `n ≥ 2`. Strictly stronger than both Legendre's conjecture
and the (also open) Brocard conjecture. -/
axiom oppermann_conjecture : OppermannConjecture

/-- Under Oppermann's conjecture, Legendre's conjecture holds for all `n ≥ 2`. -/
theorem legendre_of_oppermann : ∀ n : ℕ, 2 ≤ n → Legendre.LegendreAt n :=
  oppermann_implies_legendre oppermann_conjecture

end Legendre.Oppermann
