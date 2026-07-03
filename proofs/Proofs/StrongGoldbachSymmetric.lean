/-
# Strong Goldbach Conjecture — Symmetric (Midpoint) Reformulation

The **Strong (Binary) Goldbach Conjecture** states that every even integer `n > 2`
is the sum of two primes. It is one of the oldest **open** problems in number
theory; this file does **not** prove it.

What this file *does* prove — with **zero axioms and zero `sorry`** — is a clean
structural reformulation of the conjecture. A Goldbach partition `n = p + q`
(both prime) of an even number `n = 2m` is exactly a pair of primes placed
symmetrically about the midpoint `m`:

    p = m - k,   q = m + k     for some `0 ≤ k < m`.

Concretely we prove the per-`n` equivalence

    IsSumOfTwoPrimes (2 * m)  ↔  ∃ k < m, Prime (m - k) ∧ Prime (m + k)

and lift it to the conjecture level

    StrongGoldbachConjecture  ↔  SymmetricGoldbachConjecture.

This is the standard "Goldbach comet" viewpoint: it halves the search space
(one bounded parameter `k < n/2` instead of an unordered pair) and exposes the
symmetry underlying every Goldbach partition. We also give a decidable instance
for the symmetric predicate, so any concrete case is machine-checkable by `decide`.

**Status**: The reformulation is fully verified. The conjecture itself remains open.

**References**:
- Goldbach's letter to Euler (1742)
- The "Goldbach comet" / symmetric prime-pair picture of Goldbach partitions
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace StrongGoldbach

/-! ## Core Definitions -/

/-- `n` is a sum of two primes. -/
def IsSumOfTwoPrimes (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

/-- `m` has a **symmetric prime pair**: there is an offset `k < m` for which both
`m - k` and `m + k` are prime. This is a Goldbach partition of `2 * m` seen as a
pair symmetric about the midpoint `m`. -/
def HasSymmetricPrimePair (m : ℕ) : Prop :=
  ∃ k : ℕ, k < m ∧ Nat.Prime (m - k) ∧ Nat.Prime (m + k)

/-- Strong (Binary) Goldbach Conjecture: every even `n > 2` is a sum of two primes. -/
def StrongGoldbachConjecture : Prop :=
  ∀ n : ℕ, 2 < n → Even n → IsSumOfTwoPrimes n

/-- Symmetric form of the conjecture: every `m ≥ 2` has a symmetric prime pair. -/
def SymmetricGoldbachConjecture : Prop :=
  ∀ m : ℕ, 2 ≤ m → HasSymmetricPrimePair m

/-! ## The Per-`n` Equivalence

For any `m`, being a sum of two primes for `2 * m` is equivalent to having a
symmetric prime pair about the midpoint `m`. (No lower bound on `m` is needed:
for `m = 0` both sides are false, since primes are at least `2`.)
-/

/-- **Midpoint-symmetry equivalence.** `2 * m` is a sum of two primes iff there is
`k < m` with both `m - k` and `m + k` prime.

The forward direction takes a partition `2m = p + q`, orders the two primes, and
reads off the offset `k = m - min p q` from the midpoint; the reverse direction
sets `p = m - k`, `q = m + k` and observes `p + q = 2m`. -/
theorem sumTwoPrimes_iff_symmetric (m : ℕ) :
    IsSumOfTwoPrimes (2 * m) ↔ HasSymmetricPrimePair m := by
  constructor
  · rintro ⟨p, q, hp, hq, heq⟩
    -- `heq : 2 * m = p + q`.  Order the primes so the smaller sits at `m - k`.
    rcases le_total p q with hpq | hqp
    · refine ⟨m - p, ?_, ?_, ?_⟩
      · have := hp.two_le; omega
      · have hpm : m - (m - p) = p := by omega
        rwa [hpm]
      · have hqm : m + (m - p) = q := by omega
        rwa [hqm]
    · refine ⟨m - q, ?_, ?_, ?_⟩
      · have := hq.two_le; omega
      · have hqm : m - (m - q) = q := by omega
        rwa [hqm]
      · have hpm : m + (m - q) = p := by omega
        rwa [hpm]
  · rintro ⟨k, hk, hp1, hp2⟩
    exact ⟨m - k, m + k, hp1, hp2, by omega⟩

/-! ## The Conjecture-Level Equivalence -/

/-- **Strong Goldbach ⟺ its symmetric form.** The two statements are logically
equivalent; proving either proves both. -/
theorem strong_iff_symmetric :
    StrongGoldbachConjecture ↔ SymmetricGoldbachConjecture := by
  constructor
  · intro h m hm
    have h2 : (2 : ℕ) < 2 * m := by omega
    have heven : Even (2 * m) := ⟨m, by ring⟩
    exact (sumTwoPrimes_iff_symmetric m).mp (h (2 * m) h2 heven)
  · intro h n hn heven
    obtain ⟨r, hr⟩ := heven
    have hnr : n = 2 * r := by omega
    have hm2 : 2 ≤ r := by omega
    rw [hnr]
    exact (sumTwoPrimes_iff_symmetric r).mpr (h r hm2)

/-! ## Decidability and Verified Examples

The symmetric predicate is a bounded existential over a decidable primality test,
hence decidable. Any concrete case is therefore machine-checkable by `decide`
(kernel reduction, no `native_decide`, so these remain axiom-free). -/

instance decidableHasSymmetricPrimePair (m : ℕ) :
    Decidable (HasSymmetricPrimePair m) :=
  decidable_of_iff (∃ k ∈ Finset.range m, Nat.Prime (m - k) ∧ Nat.Prime (m + k)) <| by
    constructor
    · rintro ⟨k, hk, hp⟩
      exact ⟨k, Finset.mem_range.mp hk, hp⟩
    · rintro ⟨k, hk, hp⟩
      exact ⟨k, Finset.mem_range.mpr hk, hp⟩

-- Symmetric prime pairs for small even numbers, verified by `decide`.
example : HasSymmetricPrimePair 5 := by decide   -- 10 = 3 + 7   (k = 2)
example : HasSymmetricPrimePair 6 := by decide   -- 12 = 5 + 7   (k = 1)
example : HasSymmetricPrimePair 9 := by decide   -- 18 = 7 + 11  (k = 2)

-- `n = 2` (i.e. `m = 1`) has no symmetric prime pair, matching the exclusion `n > 2`.
example : ¬HasSymmetricPrimePair 1 := by decide

-- Sanity check that the equivalence transports a concrete partition.
example : IsSumOfTwoPrimes 10 :=
  (sumTwoPrimes_iff_symmetric 5).mpr (by decide)

/-! ## The Goldbach Comet Counting Function

Turning the existential predicate into a *quantitative* object: the number of
symmetric prime pairs about the midpoint `m`. This counts the offsets `k < m`
for which both `m - k` and `m + k` are prime — equivalently the number of
(ordered-by-size) Goldbach partitions of `2 * m`. Plotting this count against
`2 * m` produces the well-known **Goldbach comet**. The Strong Goldbach
Conjecture is exactly the statement that this count is *positive* for every
`m ≥ 2`. -/

/-- The **Goldbach comet count** at midpoint `m`: the number of offsets `k < m`
with both `m - k` and `m + k` prime. This equals the number of Goldbach
partitions `2 * m = p + q` with `p ≤ q` (via `p = m - k`, `q = m + k`). -/
def symmetricPairCount (m : ℕ) : ℕ :=
  ((Finset.range m).filter (fun k => Nat.Prime (m - k) ∧ Nat.Prime (m + k))).card

/-- The symmetric predicate holds iff the comet count is positive: existence of a
Goldbach partition is the same as the count being nonzero. -/
theorem hasSymmetricPrimePair_iff_count_pos (m : ℕ) :
    HasSymmetricPrimePair m ↔ 0 < symmetricPairCount m := by
  rw [symmetricPairCount, Finset.card_pos]
  constructor
  · rintro ⟨k, hk, hp1, hp2⟩
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hp1, hp2⟩⟩
  · rintro ⟨k, hk⟩
    rw [Finset.mem_filter, Finset.mem_range] at hk
    exact ⟨k, hk.1, hk.2.1, hk.2.2⟩

/-- **Strong Goldbach as a positivity statement about the comet.** The conjecture
is equivalent to: the Goldbach comet count is positive for every `m ≥ 2`. -/
theorem symmetricGoldbach_iff_count :
    SymmetricGoldbachConjecture ↔ ∀ m : ℕ, 2 ≤ m → 0 < symmetricPairCount m := by
  unfold SymmetricGoldbachConjecture
  exact forall_congr' fun m => imp_congr_right fun _ => hasSymmetricPrimePair_iff_count_pos m

/-! ## Structural Constraint: Both Summands Are Odd for `2 * m > 4`

Every Goldbach partition of an even number `> 4` consists of two **odd** primes.
In the symmetric picture, once `m > 2` the smaller prime `m - k` cannot be `2`:
if it were, the larger prime would be `m + k = 2 * (m - 1)`, which is even and
`> 2`, hence not prime. So `2` never participates, and both summands are odd. -/

/-- For `m > 2`, the smaller summand `m - k` of a symmetric prime pair is odd. -/
theorem symmetric_pair_odd {m k : ℕ} (hm : 2 < m) (hk : k < m)
    (hp1 : Nat.Prime (m - k)) (hp2 : Nat.Prime (m + k)) :
    Odd (m - k) := by
  rcases hp1.eq_two_or_odd' with h2 | hodd
  · -- If `m - k = 2`, then `m + k = 2 * (m - 1)` is an even prime `> 2`: impossible.
    exfalso
    have heven : Even (m + k) := ⟨m - 1, by omega⟩
    have : m + k = 2 := (Nat.Prime.even_iff hp2).mp heven
    omega
  · exact hodd

/-- For `m > 2`, **both** summands `m - k` and `m + k` of a symmetric prime pair
are odd primes. -/
theorem symmetric_pair_both_odd {m k : ℕ} (hm : 2 < m) (hk : k < m)
    (hp1 : Nat.Prime (m - k)) (hp2 : Nat.Prime (m + k)) :
    Odd (m - k) ∧ Odd (m + k) := by
  refine ⟨symmetric_pair_odd hm hk hp1 hp2, ?_⟩
  obtain ⟨j, hj⟩ := symmetric_pair_odd hm hk hp1 hp2
  exact ⟨j + k, by omega⟩

-- Concrete comet heights, verified by kernel `decide` (axiom-free).
-- `2 * 5 = 10 = 3 + 7 = 5 + 5`, so two symmetric pairs (`k = 0, 2`).
example : symmetricPairCount 5 = 2 := by decide
-- `2 * 6 = 12 = 5 + 7`, a single symmetric pair (`k = 1`).
example : symmetricPairCount 6 = 1 := by decide

-- Positivity of the comet at a few midpoints, routed through the equivalence.
example : 0 < symmetricPairCount 9 :=
  (hasSymmetricPrimePair_iff_count_pos 9).mp (by decide)

end StrongGoldbach
