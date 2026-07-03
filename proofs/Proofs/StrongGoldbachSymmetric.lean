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

/-! ## Sufficient Condition: Prime Midpoints

If the midpoint `m` is itself prime, then `2 * m = m + m` is already a Goldbach
partition — the `k = 0` "diagonal" of the comet, where the two summands coincide.
So the Strong Goldbach Conjecture holds *unconditionally* at every prime midpoint,
and the comet count is positive there. This is why the Goldbach comet has no zeros
at prime abscissae `m`: the trivial pair is always available. -/

/-- If `m` is prime then it has the trivial symmetric prime pair at offset `k = 0`
(both `m - 0 = m` and `m + 0 = m` are prime), i.e. `2 * m = m + m` is a Goldbach
partition. -/
theorem hasSymmetricPrimePair_of_prime {m : ℕ} (hm : Nat.Prime m) :
    HasSymmetricPrimePair m := by
  refine ⟨0, hm.pos, ?_, ?_⟩
  · simpa using hm
  · simpa using hm

/-- The comet count is positive at every prime midpoint. -/
theorem symmetricPairCount_pos_of_prime {m : ℕ} (hm : Nat.Prime m) :
    0 < symmetricPairCount m :=
  (hasSymmetricPrimePair_iff_count_pos m).mp (hasSymmetricPrimePair_of_prime hm)

-- `m = 7` is prime, so `14 = 7 + 7` is the diagonal Goldbach partition.
example : HasSymmetricPrimePair 7 := hasSymmetricPrimePair_of_prime (by decide)

/-! ## Upper Bound: Comet Height ≤ Primes in the Upper Arm

Each symmetric pair `(m - k, m + k)` with `k < m` contributes a *distinct* prime
`m + k` lying in the interval `[m, 2 * m)`. The map `k ↦ m + k` is injective, so
the comet count is bounded above by the number of primes in that upper-arm
interval. In particular the comet height never exceeds the prime-counting
increment `π(2m) − π(m)`, a purely density-theoretic ceiling on how many Goldbach
partitions `2 * m` can have. -/

/-- **Upper bound on the comet count.** The number of symmetric prime pairs about
`m` is at most the number of primes in the upper-arm interval `[m, 2 * m)`, via the
injection `k ↦ m + k` sending each pair to its larger prime. -/
theorem symmetricPairCount_le_primesInUpperArm (m : ℕ) :
    symmetricPairCount m ≤
      ((Finset.Ico m (2 * m)).filter (fun j => Nat.Prime j)).card := by
  rw [symmetricPairCount]
  apply Finset.card_le_card_of_injOn (fun k => m + k)
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkm, _, hpk⟩ := hk
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨Nat.le_add_right m k, by omega⟩, hpk⟩
  · intro a _ b _ hab
    simpa using hab

/-! ## Exact Identity: Comet Height = Goldbach Partition Count of `2 * m`

The upper bound above only injects each symmetric pair into the primes of the
upper arm `[m, 2 * m)`.  Keeping the *both-prime* condition on the image turns
that injection into a **bijection**: `k ↦ m + k` matches each symmetric pair
`(m - k, m + k)` about `m` with the prime `j = m + k ∈ [m, 2 * m)` whose complement
`2 * m - j = m - k` is *also* prime.  Its inverse is `j ↦ j - m`.  This makes the
docstring claim precise — the comet height is **exactly** the number of Goldbach
partitions `2 * m = j + (2 * m - j)` indexed by their larger prime `j`, not merely
bounded by the primes in the arm. -/

/-- **The comet count is an exact Goldbach-partition count.**  The number of
symmetric prime pairs about `m` equals the number of primes `j ∈ [m, 2 * m)` whose
complement `2 * m - j` is also prime — i.e. the number of Goldbach partitions of
`2 * m` indexed by their larger summand.  Refines
`symmetricPairCount_le_primesInUpperArm` from a bound to an equality by keeping the
complementary-prime condition on the image. -/
theorem symmetricPairCount_eq_upperArm_partitions (m : ℕ) :
    symmetricPairCount m
      = ((Finset.Ico m (2 * m)).filter
          (fun j => Nat.Prime j ∧ Nat.Prime (2 * m - j))).card := by
  have hinj : ∀ s : Finset ℕ, Set.InjOn (fun k => m + k) ↑s :=
    fun s a _ b _ hab => by simpa using hab
  rw [symmetricPairCount, ← Finset.card_image_of_injOn (hinj _)]
  congr 1
  ext j
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨k, ⟨hkm, hpmk, hpmpk⟩, rfl⟩
    refine ⟨⟨Nat.le_add_right m k, by omega⟩, hpmpk, ?_⟩
    have h : 2 * m - (m + k) = m - k := by omega
    rw [h]; exact hpmk
  · rintro ⟨⟨hjm, hj2m⟩, hpj, hp2mj⟩
    refine ⟨j - m, ⟨by omega, ?_, ?_⟩, by omega⟩
    · have h : m - (j - m) = 2 * m - j := by omega
      rw [h]; exact hp2mj
    · have h : m + (j - m) = j := by omega
      rw [h]; exact hpj

-- The exact identity, checked against the concrete comet heights above.
-- `2 * 5 = 10`: larger-summand primes in `[5, 10)` with prime complement are
-- `5 (= 5 + 5)` and `7 (= 3 + 7)`, matching `symmetricPairCount 5 = 2`.
example :
    ((Finset.Ico 5 10).filter (fun j => Nat.Prime j ∧ Nat.Prime (10 - j))).card = 2 := by
  decide

/-! ## Offset-Side Ceiling: the Comet is Bounded by Half the Offsets

The bounds above are all *prime-side*: they count admissible larger primes in the
upper arm `[m, 2 * m)`.  There is a complementary *offset-side* constraint that
needs no prime-counting input.  Once `m > 2` both summands `m - k` and `m + k` are
odd (proved in `symmetric_pair_both_odd`), and `m - k` odd forces `k` to have the
**opposite parity to `m`**.  So only offsets `k` with `k % 2 ≠ m % 2` can ever
contribute a Goldbach partition — exactly half of `{0, …, m - 1}`.  This halves the
offset search space and gives an elementary `≈ m/2` ceiling on the comet height,
orthogonal to the prime-arm identity `symmetricPairCount_eq_upperArm_partitions`. -/

/-- **Offset parity constraint.**  For `m > 2`, every offset `k` of a symmetric
prime pair has the opposite parity to `m` (equivalently `m - k` and `m + k` are both
odd).  Follows from `symmetric_pair_odd`: `m - k` odd means `m` and `k` differ in
parity. -/
theorem symmetric_pair_offset_parity {m k : ℕ} (hm : 2 < m) (hk : k < m)
    (hp1 : Nat.Prime (m - k)) (hp2 : Nat.Prime (m + k)) :
    m % 2 ≠ k % 2 := by
  obtain ⟨j, hj⟩ := symmetric_pair_odd hm hk hp1 hp2
  omega

-- `m = 5` (odd): the contributing offsets `0, 2` are both even — opposite parity.
example : (5 : ℕ) % 2 ≠ (2 : ℕ) % 2 :=
  symmetric_pair_offset_parity (by norm_num) (by norm_num) (by decide) (by decide)
-- `m = 6` (even): the contributing offset `1` is odd — opposite parity.
example : (6 : ℕ) % 2 ≠ (1 : ℕ) % 2 :=
  symmetric_pair_offset_parity (by norm_num) (by norm_num) (by decide) (by decide)

/-- **Offset-side upper bound on the comet count.**  For `m > 2` the comet count is
at most the number of offsets `k < m` of opposite parity to `m`.  Since exactly half
of `{0, …, m - 1}` have opposite parity to `m`, this is an elementary `≈ m/2` ceiling
on the Goldbach comet height that uses no density input, complementing the prime-arm
bound `symmetricPairCount_le_primesInUpperArm`. -/
theorem symmetricPairCount_le_oppositeParityOffsets {m : ℕ} (hm : 2 < m) :
    symmetricPairCount m ≤
      ((Finset.range m).filter (fun k => m % 2 ≠ k % 2)).card := by
  rw [symmetricPairCount]
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
  obtain ⟨hkm, hp1, hp2⟩ := hk
  exact ⟨hkm, symmetric_pair_offset_parity hm hkm hp1 hp2⟩

end StrongGoldbach
