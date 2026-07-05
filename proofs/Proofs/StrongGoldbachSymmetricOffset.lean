/-
# Strong Goldbach — the Minimal Symmetric Offset (Innermost Goldbach Partition)

This file is a follow-up to `Proofs.StrongGoldbachSymmetric`, which reformulates the
open **Strong (Binary) Goldbach Conjecture** in terms of prime pairs symmetric about
the midpoint `m`: a Goldbach partition of `2 * m` is a pair `(m - k, m + k)` of primes
with offset `k < m`. That file develops the *comet count* `symmetricPairCount m` — the
number of such offsets — and gives a battery of upper bounds on it (parity ceiling,
single-prime sieve, Euler-totient ceiling, half-totient at odd midpoints).

Here we study a complementary object that the count bounds do **not** see: the
**minimal offset**

    minimalSymmetricOffset m  =  least k with `m - k` and `m + k` both prime,

i.e. the *innermost* Goldbach partition of `2 * m` — the one whose two primes sit
closest to the midpoint. Where the comet count measures *how many* partitions exist,
the minimal offset measures *where the first one is*.

What we prove, with **zero axioms and zero `sorry`** (kernel `decide` only, no
`native_decide`):

* **Characterization** — the minimal offset is a genuine symmetric offset and is
  `≤` every other one (`minimalSymmetricOffset_le`), and it lies in range
  (`< m`) exactly when a Goldbach partition exists
  (`minimalSymmetricOffset_lt_iff`, tied to the parent's comet count).
* **Diagonal law** — `minimalSymmetricOffset m = 0 ↔ m` is prime
  (`minimalSymmetricOffset_eq_zero_iff`): the innermost partition is the diagonal
  `2 * m = m + m` precisely at prime midpoints.
* **Prime-gap connection** — the larger summand `m + minimalSymmetricOffset m` is the
  *smallest* prime `j ≥ m` whose reflection `2 * m - j` is also prime
  (`add_minimalSymmetricOffset_le`); dually the smaller summand is the *largest* prime
  `≤ m` with prime complement (`le_sub_minimalSymmetricOffset`). A large minimal offset
  therefore encodes a long run of primes near `m` whose Goldbach complements are all
  composite — this is the sense in which the minimal offset "relates to prime gaps".
* **Inherited structure** — at composite `m` the minimal offset is a nonzero
  **totative** of `m` (`minimalSymmetricOffset_coprime_of_not_prime`) and, for `m > 2`,
  of opposite parity to `m` (`minimalSymmetricOffset_parity`), by specializing the
  parent's coprimality and parity constraints to the innermost pair.
* **A new reformulation of Strong Goldbach** — the conjecture is *equivalent* to the
  statement that the minimal offset is always well-defined (in range) for every
  `m ≥ 2` (`symmetricGoldbach_iff_minimalSymmetricOffset_lt`), the minimal-offset analogue
  of the parent's comet-positivity reformulation `symmetricGoldbach_iff_count`.

**Status.** All results here are fully verified. The Strong Goldbach Conjecture itself
remains **open**; nothing here proves it. A general *upper* bound on the minimal offset
(that it is `< m` for every `m ≥ 2`) is by `symmetricGoldbach_iff_minimalSymmetricOffset_lt`
logically equivalent to the conjecture, and whether the minimal offset is unbounded (a
midpoint whose only partition is far off-diagonal) is an open sparsity question about
Goldbach partitions.

**References**:
- Goldbach's letter to Euler (1742); the "Goldbach comet" picture.
- `Proofs.StrongGoldbachSymmetric` (the parent reformulation and comet-count bounds).
-/

import Proofs.StrongGoldbachSymmetric
import Mathlib.Tactic

namespace StrongGoldbach

/-! ## Definition of the Minimal Symmetric Offset

We define `minimalSymmetricOffset m` as the least offset `k` for which both `m - k`
and `m + k` are prime, using `Nat.find` on the (decidable) symmetric-pair predicate.
When `m` has no Goldbach partition at all we return the sentinel value `m` (which lies
*outside* the valid range `[0, m)`, so `minimalSymmetricOffset m < m` cleanly detects
existence — see `minimalSymmetricOffset_lt_iff`).

The parent file provides `decidableHasSymmetricPrimePair`, making the `if h : …`
computable, so concrete values remain machine-checkable by kernel `decide`. -/

/-- The **minimal symmetric offset** at midpoint `m`: the least `k` with both `m - k`
and `m + k` prime — the offset of the *innermost* Goldbach partition of `2 * m`.
Returns the out-of-range sentinel `m` when `2 * m` has no Goldbach partition. -/
def minimalSymmetricOffset (m : ℕ) : ℕ :=
  if h : HasSymmetricPrimePair m then Nat.find h else m

/-- Unfolding lemma: when a symmetric prime pair exists, the minimal offset is the
`Nat.find` of the pair predicate. -/
theorem minimalSymmetricOffset_of_hasPair {m : ℕ} (h : HasSymmetricPrimePair m) :
    minimalSymmetricOffset m = Nat.find h := by
  simp only [minimalSymmetricOffset, dif_pos h]

/-! ## Characterization: it is a symmetric offset, and the least one -/

/-- The minimal offset is in range when a Goldbach partition exists. -/
theorem minimalSymmetricOffset_lt {m : ℕ} (h : HasSymmetricPrimePair m) :
    minimalSymmetricOffset m < m := by
  rw [minimalSymmetricOffset_of_hasPair h]; exact (Nat.find_spec h).1

/-- The smaller summand `m - minimalSymmetricOffset m` is prime. -/
theorem prime_sub_minimalSymmetricOffset {m : ℕ} (h : HasSymmetricPrimePair m) :
    Nat.Prime (m - minimalSymmetricOffset m) := by
  rw [minimalSymmetricOffset_of_hasPair h]; exact (Nat.find_spec h).2.1

/-- The larger summand `m + minimalSymmetricOffset m` is prime. -/
theorem prime_add_minimalSymmetricOffset {m : ℕ} (h : HasSymmetricPrimePair m) :
    Nat.Prime (m + minimalSymmetricOffset m) := by
  rw [minimalSymmetricOffset_of_hasPair h]; exact (Nat.find_spec h).2.2

/-- The two summands recover `2 * m`: `(m - off) + (m + off) = 2 * m`. -/
theorem sub_add_add_minimalSymmetricOffset {m : ℕ} (h : HasSymmetricPrimePair m) :
    (m - minimalSymmetricOffset m) + (m + minimalSymmetricOffset m) = 2 * m := by
  have := minimalSymmetricOffset_lt h; omega

/-- **Minimality.** Every symmetric offset `k` (both `m - k` and `m + k` prime) is at
least the minimal one. -/
theorem minimalSymmetricOffset_le {m k : ℕ} (h : HasSymmetricPrimePair m)
    (h1 : Nat.Prime (m - k)) (h2 : Nat.Prime (m + k)) :
    minimalSymmetricOffset m ≤ k := by
  rw [minimalSymmetricOffset_of_hasPair h]
  have hk : k < m := by have := h1.two_le; omega
  exact Nat.find_min' h ⟨hk, h1, h2⟩

/-! ## In-range ⟺ existence ⟺ positive comet count -/

/-- The minimal offset is in range (`< m`) **iff** `2 * m` has a Goldbach partition.
The sentinel value `m` for the empty case makes `< m` a clean existence test. -/
theorem minimalSymmetricOffset_lt_iff (m : ℕ) :
    minimalSymmetricOffset m < m ↔ HasSymmetricPrimePair m := by
  constructor
  · intro hlt
    by_contra h
    rw [minimalSymmetricOffset, dif_neg h] at hlt
    exact absurd hlt (lt_irrefl m)
  · exact minimalSymmetricOffset_lt

/-- Tie to the parent's Goldbach comet count: the minimal offset is in range iff the
comet height is positive. -/
theorem minimalSymmetricOffset_lt_iff_count_pos (m : ℕ) :
    minimalSymmetricOffset m < m ↔ 0 < symmetricPairCount m := by
  rw [minimalSymmetricOffset_lt_iff, hasSymmetricPrimePair_iff_count_pos]

/-! ## Diagonal law: minimal offset `0 ⟺ m` prime -/

/-- If the midpoint `m` is prime, the innermost Goldbach partition is the diagonal
`2 * m = m + m`, i.e. the minimal offset is `0`. -/
theorem minimalSymmetricOffset_eq_zero_of_prime {m : ℕ} (hm : Nat.Prime m) :
    minimalSymmetricOffset m = 0 := by
  have h : HasSymmetricPrimePair m := hasSymmetricPrimePair_of_prime hm
  rw [minimalSymmetricOffset_of_hasPair h, Nat.find_eq_zero]
  exact ⟨hm.pos, by simpa using hm, by simpa using hm⟩

/-- **Diagonal law.** When a Goldbach partition exists, its innermost offset is `0`
exactly when the midpoint is prime. -/
theorem minimalSymmetricOffset_eq_zero_iff {m : ℕ} (h : HasSymmetricPrimePair m) :
    minimalSymmetricOffset m = 0 ↔ Nat.Prime m := by
  rw [minimalSymmetricOffset_of_hasPair h, Nat.find_eq_zero]
  constructor
  · rintro ⟨_, hp, _⟩; simpa using hp
  · intro hm; exact ⟨hm.pos, by simpa using hm, by simpa using hm⟩

/-- At a composite midpoint (that still has some partition) the minimal offset is
strictly positive: the innermost pair is genuinely off-diagonal. -/
theorem minimalSymmetricOffset_pos_of_not_prime {m : ℕ}
    (h : HasSymmetricPrimePair m) (hm : ¬ Nat.Prime m) :
    0 < minimalSymmetricOffset m :=
  Nat.pos_of_ne_zero fun h0 => hm ((minimalSymmetricOffset_eq_zero_iff h).mp h0)

/-! ## Prime-gap connection: the summands are the extreme Goldbach primes

The minimality of the offset transports to the summands. Since `k ↦ m + k` is
increasing, the least offset gives the **smallest** larger prime `j = m + k` in the
upper arm `[m, 2 * m)` whose reflection `2 * m - j` is prime; dually the **largest**
smaller prime `p = m - k` in the lower arm `(0, m]` with prime complement. A large
minimal offset therefore means every prime `j` just above `m` has a *composite*
Goldbach complement `2 * m - j` — a structural link between the innermost partition
and the distribution (gaps) of primes near `m`. -/

/-- **The larger summand is the least Goldbach prime `≥ m`.** For any prime `j ≥ m`
whose reflection `2 * m - j` is also prime, the innermost larger summand does not
exceed `j`: `m + minimalSymmetricOffset m ≤ j`. -/
theorem add_minimalSymmetricOffset_le {m j : ℕ} (h : HasSymmetricPrimePair m)
    (hjm : m ≤ j) (hj : Nat.Prime j) (hcj : Nat.Prime (2 * m - j)) :
    m + minimalSymmetricOffset m ≤ j := by
  have hk : minimalSymmetricOffset m ≤ j - m := by
    apply minimalSymmetricOffset_le h
    · have e : m - (j - m) = 2 * m - j := by omega
      rw [e]; exact hcj
    · have e : m + (j - m) = j := by omega
      rw [e]; exact hj
  omega

/-- **The smaller summand is the greatest Goldbach prime `≤ m`.** For any prime `p ≤ m`
(with `p ≤ 2 * m`) whose complement `2 * m - p` is also prime, the innermost smaller
summand is at least `p`: `p ≤ m - minimalSymmetricOffset m`. -/
theorem le_sub_minimalSymmetricOffset {m p : ℕ} (h : HasSymmetricPrimePair m)
    (hpm : p ≤ m) (hp : Nat.Prime p) (hcp : Nat.Prime (2 * m - p)) :
    p ≤ m - minimalSymmetricOffset m := by
  have hk : minimalSymmetricOffset m ≤ m - p := by
    apply minimalSymmetricOffset_le h
    · have e : m - (m - p) = p := by omega
      rw [e]; exact hp
    · have e : m + (m - p) = 2 * m - p := by omega
      rw [e]; exact hcp
  omega

/-! ## Inherited structure at composite midpoints

Specializing the parent's structural constraints (`symmetric_pair_offset_coprime`,
`symmetric_pair_offset_parity`) to the innermost pair. -/

/-- At a composite midpoint the minimal offset is **coprime** to `m`: the innermost
off-diagonal offset shares no prime factor with the midpoint. -/
theorem minimalSymmetricOffset_coprime_of_not_prime {m : ℕ}
    (h : HasSymmetricPrimePair m) (hm : ¬ Nat.Prime m) :
    Nat.Coprime (minimalSymmetricOffset m) m :=
  symmetric_pair_offset_coprime
    (minimalSymmetricOffset_pos_of_not_prime h hm)
    (prime_sub_minimalSymmetricOffset h)
    (prime_add_minimalSymmetricOffset h)

/-- For `m > 2` the minimal offset has **opposite parity** to `m` (both summands odd). -/
theorem minimalSymmetricOffset_parity {m : ℕ} (hm : 2 < m)
    (h : HasSymmetricPrimePair m) :
    m % 2 ≠ minimalSymmetricOffset m % 2 :=
  symmetric_pair_offset_parity hm (minimalSymmetricOffset_lt h)
    (prime_sub_minimalSymmetricOffset h) (prime_add_minimalSymmetricOffset h)

/-! ## A new reformulation of Strong Goldbach via the minimal offset

The parent recast Strong Goldbach as positivity of the comet count
(`symmetricGoldbach_iff_count`). The minimal offset gives an equally clean equivalent
form: the conjecture holds iff the innermost offset is always well-defined (in range)
for every `m ≥ 2`. -/

/-- Under Strong Goldbach the minimal offset is well-defined (in range) at every
`m ≥ 2`. -/
theorem minimalSymmetricOffset_lt_of_symmetricGoldbach
    (H : SymmetricGoldbachConjecture) {m : ℕ} (hm : 2 ≤ m) :
    minimalSymmetricOffset m < m :=
  minimalSymmetricOffset_lt (H m hm)

/-- **Strong Goldbach as minimal-offset well-definedness.** The Symmetric (hence Strong)
Goldbach Conjecture is equivalent to: for every `m ≥ 2` the minimal symmetric offset is
in range (`< m`). The minimal-offset analogue of `symmetricGoldbach_iff_count`. -/
theorem symmetricGoldbach_iff_minimalSymmetricOffset_lt :
    SymmetricGoldbachConjecture ↔ ∀ m : ℕ, 2 ≤ m → minimalSymmetricOffset m < m := by
  constructor
  · intro H m hm; exact minimalSymmetricOffset_lt (H m hm)
  · intro H m hm; exact (minimalSymmetricOffset_lt_iff m).mp (H m hm)

/-! ## Verified concrete values (kernel `decide`, axiom-free)

Exact minimal offsets, pinned via `Nat.find_eq_iff` so the checks reduce to small
concrete primality facts (no heavy `Nat.find` kernel reduction). -/

-- `m = 5` is prime, so the innermost partition of `10` is the diagonal `5 + 5`.
example : minimalSymmetricOffset 5 = 0 := minimalSymmetricOffset_eq_zero_of_prime (by norm_num)

-- `m = 4` (composite): `8 = 3 + 5`, offset `1`; the diagonal `4 + 4` fails (`4` composite).
example : minimalSymmetricOffset 4 = 1 := by
  have h : HasSymmetricPrimePair 4 := ⟨1, by norm_num, by decide, by decide⟩
  rw [minimalSymmetricOffset_of_hasPair h, Nat.find_eq_iff]
  refine ⟨⟨by norm_num, by decide, by decide⟩, ?_⟩
  intro n hn; interval_cases n; decide

-- `m = 6` (composite): `12 = 5 + 7`, offset `1`.
example : minimalSymmetricOffset 6 = 1 := by
  have h : HasSymmetricPrimePair 6 := ⟨1, by norm_num, by decide, by decide⟩
  rw [minimalSymmetricOffset_of_hasPair h, Nat.find_eq_iff]
  refine ⟨⟨by norm_num, by decide, by decide⟩, ?_⟩
  intro n hn; interval_cases n; decide

-- `m = 9 = 3²` (odd composite): innermost partition `18 = 7 + 11`, offset `2`.
-- Illustrates the inherited structure — the offset `2` is even (opposite parity to the
-- odd `m`) and coprime to `9`.
example : minimalSymmetricOffset 9 = 2 := by
  have h : HasSymmetricPrimePair 9 := ⟨2, by norm_num, by decide, by decide⟩
  rw [minimalSymmetricOffset_of_hasPair h, Nat.find_eq_iff]
  refine ⟨⟨by norm_num, by decide, by decide⟩, ?_⟩
  intro n hn; interval_cases n <;> decide

-- A larger off-diagonal offset: `m = 34`, innermost partition `68 = 31 + 37`, offset `3`.
-- The nearer reflections fail — `33, 35` (offset 1) and `32, 36` (offset 2) are all
-- composite — so the smallest Goldbach prime above `34` with prime complement is `37`.
example : minimalSymmetricOffset 34 = 3 := by
  have h : HasSymmetricPrimePair 34 := ⟨3, by norm_num, by decide, by decide⟩
  rw [minimalSymmetricOffset_of_hasPair h, Nat.find_eq_iff]
  refine ⟨⟨by norm_num, by decide, by decide⟩, ?_⟩
  intro n hn; interval_cases n <;> decide

-- The minimal offset detects existence: `m = 1` (i.e. `2`) has no Goldbach partition,
-- so the sentinel makes it *not* in range.
example : ¬ minimalSymmetricOffset 1 < 1 := by
  rw [minimalSymmetricOffset_lt_iff]; decide

end StrongGoldbach
