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
import Mathlib.Data.Nat.Totient
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

/-! ## Diagonal / Off-Diagonal Decomposition of the Comet Height

The offset `k = 0` is special: the symmetric pair it produces is the **diagonal**
partition `2 * m = m + m`, present exactly when `m` itself is prime. Every other
contributing offset `k ≥ 1` gives a partition `2 * m = (m - k) + (m + k)` into two
**distinct** primes. Splitting the comet count at `k = 0` therefore separates the
single possible "square" representation from the genuinely distinct-prime ones:

    symmetricPairCount m  =  [m prime]  +  #{ 1 ≤ k < m : m - k, m + k both prime }.

This makes precise the `+ 1` that recurs in the totient ceilings
(`symmetricPairCount_le_totient_succ`, `symmetricPairCount_le_half_totient_succ_of_odd`):
that unit is exactly the diagonal term, contributed by `k = 0` only at a prime midpoint,
so on composite `m` it drops and the comet height counts *only* distinct-prime pairs. -/

/-- **Diagonal / off-diagonal decomposition of the comet height.** The Goldbach
partitions of `2 * m` split into the single diagonal `2 * m = m + m` (present iff `m`
is prime, the `k = 0` offset) and the distinct-prime pairs (offsets `1 ≤ k < m`):

    symmetricPairCount m = (if m prime then 1 else 0)
        + #{ k ∈ [1, m) : Prime (m - k) ∧ Prime (m + k) }.

Isolating the `k = 0` term via `Finset.filter_insert` and simplifying `m ± 0 = m`
(so the diagonal condition `Prime m ∧ Prime m` collapses to `Prime m`). -/
theorem symmetricPairCount_eq_diagonal_add_offDiagonal (m : ℕ) :
    symmetricPairCount m
      = (if Nat.Prime m then 1 else 0)
        + ((Finset.Ico 1 m).filter
            (fun k => Nat.Prime (m - k) ∧ Nat.Prime (m + k))).card := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [symmetricPairCount, Nat.not_prime_zero]
  · have hrange : Finset.range m = insert 0 (Finset.Ico 1 m) := by
      ext k
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [symmetricPairCount, hrange, Finset.filter_insert]
    simp only [Nat.sub_zero, Nat.add_zero, and_self]
    by_cases hp : Nat.Prime m
    · rw [if_pos hp, if_pos hp, Finset.card_insert_of_notMem (by simp)]
      omega
    · rw [if_neg hp, if_neg hp, Nat.zero_add]

/-- **On a composite midpoint the comet height counts only distinct-prime pairs.**
When `m` is not prime the diagonal `2 * m = m + m` is unavailable, so the comet
height equals exactly the number of Goldbach partitions of `2 * m` into two
*distinct* primes (offsets `1 ≤ k < m`). Corollary of the diagonal decomposition. -/
theorem symmetricPairCount_eq_offDiagonal_of_not_prime {m : ℕ} (hm : ¬ Nat.Prime m) :
    symmetricPairCount m
      = ((Finset.Ico 1 m).filter
          (fun k => Nat.Prime (m - k) ∧ Nat.Prime (m + k))).card := by
  rw [symmetricPairCount_eq_diagonal_add_offDiagonal, if_neg hm, Nat.zero_add]

-- `m = 5` is prime: the diagonal `10 = 5 + 5` plus one distinct-prime pair
-- (`k = 2`, `10 = 3 + 7`) gives comet height `2`.
example :
    ((Finset.Ico 1 5).filter (fun k => Nat.Prime (5 - k) ∧ Nat.Prime (5 + k))).card = 1 := by
  decide

-- `m = 6` is composite: no diagonal, and the lone distinct-prime pair is
-- `k = 1` (`12 = 5 + 7`), so the comet height `1` is purely off-diagonal.
example :
    symmetricPairCount 6
      = ((Finset.Ico 1 6).filter (fun k => Nat.Prime (6 - k) ∧ Nat.Prime (6 + k))).card :=
  symmetricPairCount_eq_offDiagonal_of_not_prime (by decide)

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

/-! ## Dual Identity: Comet Height = the Textbook Goldbach Partition Function `g(2m)`

`symmetricPairCount_eq_upperArm_partitions` indexes each Goldbach partition of `2 * m`
by its **larger** prime `j ∈ [m, 2 * m)`. The dual indexing is by the **smaller** prime
`p ∈ (0, m]`, and this is exactly the textbook **Goldbach partition function**

    g(2m) = #{ p ≤ m : p and 2m − p both prime },

the object plotted as the Goldbach comet in the literature. The reflection `k ↦ m − k`
(inverse `p ↦ m − p`) matches each symmetric pair `(m − k, m + k)` about `m` with its
smaller summand `p = m − k`, so the comet height equals this standard count as well.
Composing the two identities exhibits the reflection symmetry `x ↦ 2 * m − x` between the
lower arm `(0, m]` and the upper arm `[m, 2 * m)`. -/

/-- **The comet count is the Goldbach partition function `g(2m)`.** The number of
symmetric prime pairs about `m` equals the number of primes `p ∈ (0, m]` whose
complement `2 * m − p` is also prime — the standard count of Goldbach partitions of
`2 * m` indexed by their smaller summand `p ≤ m`. Dual to
`symmetricPairCount_eq_upperArm_partitions`, via the reflection `k ↦ m − k` sending each
pair to its smaller prime. -/
theorem symmetricPairCount_eq_lowerArm_partitions (m : ℕ) :
    symmetricPairCount m
      = ((Finset.Ioc 0 m).filter
          (fun p => Nat.Prime p ∧ Nat.Prime (2 * m - p))).card := by
  have hinj : Set.InjOn (fun k => m - k)
      ↑((Finset.range m).filter
        (fun k => Nat.Prime (m - k) ∧ Nat.Prime (m + k))) := by
    intro a ha b hb hab
    have hA : a < m := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).1
    have hB : b < m := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).1
    simp only at hab
    omega
  rw [symmetricPairCount, ← Finset.card_image_of_injOn hinj]
  congr 1
  ext p
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
  constructor
  · rintro ⟨k, ⟨hkm, hpmk, hpmpk⟩, rfl⟩
    refine ⟨⟨by omega, by omega⟩, hpmk, ?_⟩
    have h : 2 * m - (m - k) = m + k := by omega
    rw [h]; exact hpmpk
  · rintro ⟨⟨hp0, hpm⟩, hpp, hp2mp⟩
    refine ⟨m - p, ⟨by omega, ?_, ?_⟩, by omega⟩
    · have h : m - (m - p) = p := by omega
      rw [h]; exact hpp
    · have h : m + (m - p) = 2 * m - p := by omega
      rw [h]; exact hp2mp

/-- **Reflection symmetry of the two arm-indexings.** Indexing the Goldbach partitions
of `2 * m` by their larger prime (in `[m, 2 * m)`) or by their smaller prime (in
`(0, m]`) yields the same count — both equal the comet height `symmetricPairCount m`.
The underlying bijection is the reflection `x ↦ 2 * m − x` swapping the two arms. -/
theorem upperArm_partitions_eq_lowerArm_partitions (m : ℕ) :
    ((Finset.Ico m (2 * m)).filter
        (fun j => Nat.Prime j ∧ Nat.Prime (2 * m - j))).card
      = ((Finset.Ioc 0 m).filter
          (fun p => Nat.Prime p ∧ Nat.Prime (2 * m - p))).card := by
  rw [← symmetricPairCount_eq_upperArm_partitions,
    ← symmetricPairCount_eq_lowerArm_partitions]

-- The dual identity, checked against the concrete comet height `symmetricPairCount 5 = 2`.
-- `2 * 5 = 10`: smaller-summand primes in `(0, 5]` with prime complement are
-- `3 (= 3 + 7)` and `5 (= 5 + 5)`, matching the two upper-arm primes `7, 5`.
example :
    ((Finset.Ioc 0 5).filter (fun p => Nat.Prime p ∧ Nat.Prime (10 - p))).card = 2 := by
  decide

/-! ## Prime-Side Ceiling on the Lower Arm and the Two-Arm Minimum

`symmetricPairCount_le_primesInUpperArm` bounds the comet height by the number of
primes in the **upper** arm `[m, 2 * m)` — the possible larger summands.  Dually,
every Goldbach partition of `2 * m` is pinned by its **smaller** prime `p ∈ (0, m]`,
so the height is also bounded by the number of primes in the lower arm `(0, m]`,
i.e. by `π(m)`.  This drops the complementary-prime conjunct from the exact
lower-arm identity `symmetricPairCount_eq_lowerArm_partitions`.  Combining the two
arm bounds, the comet height is at most the *smaller* of the two prime counts —
a strictly sharper elementary ceiling than either arm alone. -/

/-- **Prime-side ceiling on the lower arm.**  The comet height is bounded by the
number of primes `p ∈ (0, m]` — the admissible *smaller* summands of a Goldbach
partition of `2 * m`.  Dual to `symmetricPairCount_le_primesInUpperArm`; obtained by
dropping the `Nat.Prime (2 * m - p)` conjunct from the exact identity
`symmetricPairCount_eq_lowerArm_partitions`. -/
theorem symmetricPairCount_le_primesInLowerArm (m : ℕ) :
    symmetricPairCount m ≤ ((Finset.Ioc 0 m).filter (fun p => Nat.Prime p)).card := by
  rw [symmetricPairCount_eq_lowerArm_partitions]
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1⟩

/-- **Two-arm minimum ceiling.**  The comet height is at most the *smaller* of the
prime counts in the two arms: the primes in the lower arm `(0, m]` (the possible
smaller summands) and the primes in the upper arm `[m, 2 * m)` (the possible larger
summands).  Combines `symmetricPairCount_le_primesInLowerArm` and
`symmetricPairCount_le_primesInUpperArm`; sharper than either bound in isolation. -/
theorem symmetricPairCount_le_min_primesInArms (m : ℕ) :
    symmetricPairCount m ≤
      min (((Finset.Ioc 0 m).filter (fun p => Nat.Prime p)).card)
          (((Finset.Ico m (2 * m)).filter (fun j => Nat.Prime j)).card) :=
  le_min (symmetricPairCount_le_primesInLowerArm m)
    (symmetricPairCount_le_primesInUpperArm m)

-- The lower-arm ceiling, checked against `symmetricPairCount 5 = 2`.
-- Primes in `(0, 5]` are `2, 3, 5` (three), so the comet height `2` is `≤ 3`.
example : ((Finset.Ioc 0 5).filter (fun p => Nat.Prime p)).card = 3 := by decide

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

/-! ## Closing the Offset Ceiling: an Explicit `⌈m/2⌉` Bound

The offset-side bound above is phrased against the *count* of opposite-parity
offsets.  That count has a closed form: among `{0, …, m - 1}` exactly `⌈m/2⌉`
residues have parity opposite to `m`.  Turning the bound into this explicit value
gives a fully elementary ceiling on the Goldbach comet height,

    symmetricPairCount m ≤ ⌈m / 2⌉  =  (m + 1) / 2,

i.e. the number of Goldbach partitions of `2 * m` is at most `≈ m / 2 ≈ n / 4`.
Unlike the prime-arm bound `symmetricPairCount_le_primesInUpperArm`, this uses **no
prime-counting input at all** — it is pure parity bookkeeping. -/

/-- **Residue count in `[0, m)` by parity.**  For a target residue `c < 2`, the
number of `k < m` with `k % 2 = c` is `(m + 1 - c) / 2`: `⌈m/2⌉` of the even
residues (`c = 0`) and `⌊m/2⌋` of the odd ones (`c = 1`).  Proved by a direct
induction on `m` (each new top element `n` contributes iff `n % 2 = c`). -/
theorem card_filter_mod2_range (c m : ℕ) (hc : c < 2) :
    ((Finset.range m).filter (fun k => k % 2 = c)).card = (m + 1 - c) / 2 := by
  induction m with
  | zero => simp only [Finset.range_zero, Finset.filter_empty, Finset.card_empty]; omega
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases h : n % 2 = c
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp), ih]; omega
    · rw [if_neg h, ih]; omega

/-- **Opposite-parity offsets number exactly `⌈m/2⌉`.**  The number of offsets
`k < m` whose parity differs from `m`'s is `(m + 1) / 2`.  These are the only
offsets that can index a symmetric prime pair once `m > 2`
(`symmetric_pair_offset_parity`). -/
theorem oppositeParityOffsets_card (m : ℕ) :
    ((Finset.range m).filter (fun k => m % 2 ≠ k % 2)).card = (m + 1) / 2 := by
  have heq : (Finset.range m).filter (fun k => m % 2 ≠ k % 2)
      = (Finset.range m).filter (fun k => k % 2 = 1 - m % 2) := by
    apply Finset.filter_congr
    intro k _
    omega
  rw [heq, card_filter_mod2_range (1 - m % 2) m (by omega)]
  omega

/-- **Explicit elementary ceiling on the Goldbach comet height.**  For `m > 2`,

    symmetricPairCount m ≤ (m + 1) / 2  =  ⌈m / 2⌉,

so `2 * m` has at most `⌈m/2⌉ ≈ n/4` Goldbach partitions.  This closes
`symmetricPairCount_le_oppositeParityOffsets` to a closed form and needs no
prime-density input — it follows purely from the parity constraint
`symmetric_pair_offset_parity` and the count `oppositeParityOffsets_card`. -/
theorem symmetricPairCount_le_half {m : ℕ} (hm : 2 < m) :
    symmetricPairCount m ≤ (m + 1) / 2 :=
  (symmetricPairCount_le_oppositeParityOffsets hm).trans
    (oppositeParityOffsets_card m).le

-- The explicit ceiling, checked against a concrete comet height: `2 * 5 = 10` has
-- two Goldbach partitions (`3 + 7`, `5 + 5`) and `⌈5/2⌉ = 3`, so `2 ≤ 3`.
example : symmetricPairCount 5 ≤ (5 + 1) / 2 := symmetricPairCount_le_half (by norm_num)

/-! ## Divisibility Sieve: Every Prime Factor of `m` Thins the Offsets

The parity ceiling above is the special case `p = 2` of a general phenomenon. If a
prime `p` divides the midpoint `m`, then any offset `k` that is *also* divisible by `p`
kills the pair: `p ∣ (m − k)` and `p ∣ (m + k)`, so for both to be prime we'd need
`m − k = p = m + k`, impossible once `k > 0`. Hence contributing offsets avoid the
multiples of every prime factor of `m`. This is the arithmetic behind the **rays of the
Goldbach comet**: a midpoint `m` divisible by many small primes has *more* admissible
offsets removed on the composite side, yet paradoxically tends to have a *higher* comet
count because the surviving summands `m ± k` are freed of those small factors — the
classic reason highly composite `m` sit on the comet's dense upper rays. -/

/-- **Prime-divisibility exclusion.** If a prime `p` divides `m` and also divides a
nonzero offset `k`, then `(m − k, m + k)` is *not* a symmetric prime pair: `p` divides
both `m − k` and `m + k`, so each — if prime — would have to equal `p`, forcing
`m − k = m + k`, impossible for `k > 0`. Generalizes `symmetric_pair_offset_parity` (the
`p = 2` case) to every prime factor of `m`. -/
theorem not_symmetric_pair_of_prime_dvd {m k p : ℕ} (hp : Nat.Prime p)
    (hpm : p ∣ m) (hk0 : 0 < k) (hpk : p ∣ k) :
    ¬(Nat.Prime (m - k) ∧ Nat.Prime (m + k)) := by
  rintro ⟨h1, h2⟩
  have hd1 : p ∣ (m - k) := Nat.dvd_sub hpm hpk
  have hd2 : p ∣ (m + k) := dvd_add hpm hpk
  have e1 : p = m - k := (h1.eq_one_or_self_of_dvd p hd1).resolve_left hp.ne_one
  have e2 : p = m + k := (h2.eq_one_or_self_of_dvd p hd2).resolve_left hp.ne_one
  omega

/-- **Sieve bound on the comet count from a proper prime factor of `m`.** If a prime `p`
divides `m` with `p < m` (so `m` is composite), then every contributing offset avoids the
multiples of `p`, hence the comet count is at most the number of offsets `k < m` that are
*not* divisible by `p`. For odd `p` this is an arithmetic constraint independent of the
parity ceiling `symmetricPairCount_le_half`. -/
theorem symmetricPairCount_le_notDvd {m p : ℕ} (hp : Nat.Prime p)
    (hpm : p ∣ m) (hpm' : p < m) :
    symmetricPairCount m ≤ ((Finset.range m).filter (fun k => ¬ p ∣ k)).card := by
  rw [symmetricPairCount]
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
  obtain ⟨hkm, hp1, hp2⟩ := hk
  refine ⟨hkm, ?_⟩
  intro hpk
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · -- `k = 0`: `m - 0 = m` is prime yet `p ∣ m` with `1 < p < m`, impossible.
    subst hk0
    simp only [Nat.sub_zero] at hp1
    rcases hp1.eq_one_or_self_of_dvd p hpm with h | h
    · exact hp.ne_one h
    · omega
  · exact not_symmetric_pair_of_prime_dvd hp hpm hk0 hpk ⟨hp1, hp2⟩

-- Concrete exclusion: `m = 15 = 3·5`, offset `k = 3` (a multiple of `3 ∣ 15`) gives
-- `(12, 18)` — neither prime — so it contributes no Goldbach partition of `30`.
example : ¬(Nat.Prime (15 - 3) ∧ Nat.Prime (15 + 3)) :=
  not_symmetric_pair_of_prime_dvd (p := 3) (by decide) (by decide) (by decide) (by decide)

/-! ## Closing the Sieve Bound: an Explicit `m − m / p` Ceiling

The divisibility sieve `symmetricPairCount_le_notDvd` bounds the comet height by the
number of offsets `k < m` *not* divisible by a prime factor `p` of `m`.  When `p ∣ m`
that count has a closed form: the offsets divisible by `p` are exactly
`p · 0, p · 1, …, p · (m / p − 1)`, so there are `m / p` of them and `m − m / p` remain.
This turns the sieve into an explicit density ceiling from any prime factor of `m`,

    symmetricPairCount m ≤ m − m / p  =  (1 − 1 / p) · m,

the closed-form analogue of `symmetricPairCount_le_half`.  Indeed the parity ceiling is
the `p = 2` case: for even `m`, `m − m / 2 = m / 2 = ⌈m / 2⌉`.  A midpoint divisible by a
*small* prime `p` has the most offsets removed (`1 / p` of them), tightening the ceiling. -/

/-- **Count of multiples of `p` in `[0, m)` when `p ∣ m`.**  The offsets `k < m` divisible
by `p` are exactly `p · 0, …, p · (m / p − 1)`, so there are `m / p` of them.  Proved by
identifying the filtered set with the image of `range (m / p)` under `j ↦ p · j`, an
injection since `p > 0`. -/
theorem card_range_filter_dvd {m p : ℕ} (hp : 0 < p) (hpm : p ∣ m) :
    ((Finset.range m).filter (fun k => p ∣ k)).card = m / p := by
  have hm : p * (m / p) = m := Nat.mul_div_cancel' hpm
  have hbij : (Finset.range m).filter (fun k => p ∣ k)
      = (Finset.range (m / p)).image (fun j => p * j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hkm, j, rfl⟩
      refine ⟨j, ?_, rfl⟩
      have hlt : p * j < p * (m / p) := by rw [hm]; exact hkm
      exact lt_of_mul_lt_mul_left hlt (Nat.zero_le p)
    · rintro ⟨j, hj, rfl⟩
      refine ⟨?_, dvd_mul_right p j⟩
      calc p * j < p * (m / p) := mul_lt_mul_of_pos_left hj hp
        _ = m := hm
  rw [hbij, Finset.card_image_of_injective _ (mul_right_injective₀ hp.ne'),
    Finset.card_range]

/-- **Explicit `m − m / p` ceiling on the Goldbach comet height.**  For a prime `p` dividing
the midpoint `m` with `p < m`,

    symmetricPairCount m ≤ m − m / p,

i.e. `2 * m` has at most `(1 − 1 / p) · m` Goldbach partitions.  This closes the sieve bound
`symmetricPairCount_le_notDvd` to a closed form (the count of non-multiples of `p` in `[0, m)`
being `m − m / p` by `card_range_filter_dvd`), the divisibility analogue of the parity ceiling
`symmetricPairCount_le_half`. -/
theorem symmetricPairCount_le_sub_div {m p : ℕ} (hp : Nat.Prime p)
    (hpm : p ∣ m) (hpm' : p < m) :
    symmetricPairCount m ≤ m - m / p := by
  refine (symmetricPairCount_le_notDvd hp hpm hpm').trans ?_
  have hsplit : ((Finset.range m).filter (fun k => p ∣ k)).card
      + ((Finset.range m).filter (fun k => ¬ p ∣ k)).card
      = (Finset.range m).card :=
    Finset.filter_card_add_filter_neg_card_eq_card _
  rw [Finset.card_range] at hsplit
  have hcount := card_range_filter_dvd hp.pos hpm
  omega

-- Concrete ceiling: `m = 15 = 3 · 5`, `p = 3` gives `15 − 15 / 3 = 10`, and the comet
-- height of `30` is `3` (`7+23, 11+19, 13+17`), so `3 ≤ 10`.
example : symmetricPairCount 15 ≤ 15 - 15 / 3 :=
  symmetricPairCount_le_sub_div (p := 3) (by decide) (by decide) (by decide)

/-! ## The Euler-Totient Ceiling: `symmetricPairCount m ≤ φ(m)`

The single-prime sieve `symmetricPairCount_le_sub_div` removes the multiples of *one*
prime factor `p ∣ m`.  But `not_symmetric_pair_of_prime_dvd` applies to **every** prime
factor of `m` simultaneously: a nonzero offset `k` contributing a symmetric prime pair
cannot share *any* prime factor with `m`, so it must be **coprime to `m`**.  The nonzero
part of the comet support therefore embeds into `{k < m : gcd(k, m) = 1}`, whose size is
Euler's totient `φ(m)`.  This gives the unified ceiling

    symmetricPairCount m ≤ φ(m) + 1,       and, for composite `m`,   ≤ φ(m).

Since `φ(m) = m · ∏_{p ∣ m} (1 − 1/p) ≤ m · (1 − 1/p) = m − m/p` for any prime factor `p`,
this **dominates every single-prime bound** `symmetricPairCount_le_sub_div`: the full
multiplicative sieve over *all* prime factors is strictly sharper than removing just one.
It also connects the comet height to a standard Mathlib object (`Nat.totient`). -/

/-- **A nonzero contributing offset is coprime to the midpoint.**  If `k > 0` and both
`m - k` and `m + k` are prime, then `gcd(k, m) = 1`: any common prime factor `p` of `k`
and `m` would divide both `m - k` and `m + k` (via `not_symmetric_pair_of_prime_dvd`),
which is impossible.  This is the simultaneous-over-all-primes form of the divisibility
exclusion, and it is what upgrades the single-prime sieve to the full totient ceiling. -/
theorem symmetric_pair_offset_coprime {m k : ℕ} (hk0 : 0 < k)
    (hp1 : Nat.Prime (m - k)) (hp2 : Nat.Prime (m + k)) :
    Nat.Coprime k m := by
  by_contra hnc
  obtain ⟨p, hp, hpk, hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  exact not_symmetric_pair_of_prime_dvd hp hpm hk0 hpk ⟨hp1, hp2⟩

/-- **Euler-totient ceiling (general form).**  For every midpoint `m`,

    symmetricPairCount m ≤ φ(m) + 1.

The comet support splits into the possible `k = 0` diagonal (present only when `m` is
prime) and the nonzero offsets, each of which is coprime to `m` by
`symmetric_pair_offset_coprime`; the latter inject into the `φ(m)` totatives of `m`. -/
theorem symmetricPairCount_le_totient_succ (m : ℕ) :
    symmetricPairCount m ≤ Nat.totient m + 1 := by
  rw [symmetricPairCount, Nat.totient_eq_card_coprime]
  refine (Finset.card_le_card ?_).trans (Finset.card_insert_le 0 _)
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_range] at hk
  obtain ⟨hkm, h1, h2⟩ := hk
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    exact Finset.mem_insert_self 0 _
  · refine Finset.mem_insert_of_mem ?_
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hkm, (symmetric_pair_offset_coprime hk0 h1 h2).symm⟩

/-- **Euler-totient ceiling (composite midpoint).**  When `m` is *not* prime the `k = 0`
diagonal cannot contribute (`m - 0 = m` would have to be prime), so the entire comet
support consists of offsets coprime to `m` and

    symmetricPairCount m ≤ φ(m).

This is the sharpest closed-form ceiling in this file: it dominates every single-prime
sieve bound `symmetricPairCount_le_sub_div`, since `φ(m) ≤ m − m/p` for each prime `p ∣ m`. -/
theorem symmetricPairCount_le_totient_of_not_prime {m : ℕ} (hm : ¬ Nat.Prime m) :
    symmetricPairCount m ≤ Nat.totient m := by
  rw [symmetricPairCount, Nat.totient_eq_card_coprime]
  refine Finset.card_le_card ?_
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
  obtain ⟨hkm, h1, h2⟩ := hk
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    rw [Nat.sub_zero] at h1
    exact absurd h1 hm
  · exact ⟨hkm, (symmetric_pair_offset_coprime hk0 h1 h2).symm⟩

-- Concrete totient ceiling: `m = 15 = 3 · 5` is composite, `φ(15) = 8`, and the comet
-- height of `30` is `3`, so `3 ≤ 8`.
example : symmetricPairCount 15 ≤ Nat.totient 15 :=
  symmetricPairCount_le_totient_of_not_prime (by decide)

-- The totient ceiling is strictly sharper than the single-prime `m − m/p` bound:
-- `φ(15) = 8 < 10 = 15 − 15/3`.  Removing the multiples of *both* `3` and `5` beats
-- removing the multiples of `3` alone.
example : Nat.totient 15 < 15 - 15 / 3 := by decide

/-- **The totient ceiling dominates every single-prime sieve ceiling.**  For any prime
`p ∣ m`,

    φ(m) ≤ m − m / p.

Every totative of `m` is coprime to `m`, hence — since `p ∣ m` — not divisible by `p`;
so the `φ(m)` totatives inject into the `m − m / p` residues of `[0, m)` that are not
multiples of `p` (counted by `card_range_filter_dvd`).  Combined with
`symmetricPairCount_le_totient_of_not_prime` this proves *in general* what the numeric
`example` above only checks at `m = 15`: the full-totient ceiling
`symmetricPairCount_le_totient_of_not_prime` is at least as sharp as the single-prime
ceiling `symmetricPairCount_le_sub_div` for **every** prime factor `p` of `m`.  (This is
the Lean form of `φ(m) = m · ∏_{q ∣ m}(1 − 1/q) ≤ m · (1 − 1/p) = m − m/p`, but proved
directly by the coprime-avoids-multiples inclusion rather than via the product formula.) -/
theorem totient_le_sub_div {m p : ℕ} (hp : Nat.Prime p) (hpm : p ∣ m) :
    Nat.totient m ≤ m - m / p := by
  rw [Nat.totient_eq_card_coprime]
  -- A totative of `m` is coprime to `m`, hence not divisible by the factor `p`.
  have hsub : ((Finset.range m).filter (fun k => m.Coprime k))
      ⊆ (Finset.range m).filter (fun k => ¬ p ∣ k) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    obtain ⟨hkm, hcop⟩ := hk
    refine ⟨hkm, fun hpk => ?_⟩
    have hcop' : Nat.gcd m k = 1 := hcop
    have hd : p ∣ 1 := by rw [← hcop']; exact Nat.dvd_gcd hpm hpk
    have hle := Nat.le_of_dvd Nat.one_pos hd
    have := hp.two_le
    omega
  refine (Finset.card_le_card hsub).trans ?_
  -- The non-multiples of `p` in `[0, m)` number `m − m / p`.
  have hsplit : ((Finset.range m).filter (fun k => p ∣ k)).card
      + ((Finset.range m).filter (fun k => ¬ p ∣ k)).card
      = (Finset.range m).card :=
    Finset.filter_card_add_filter_neg_card_eq_card _
  rw [Finset.card_range] at hsplit
  have hcount := card_range_filter_dvd hp.pos hpm
  omega

-- The general dominance, at `m = 15, p = 3`: `φ(15) = 8 ≤ 10 = 15 − 15/3`.
example : Nat.totient 15 ≤ 15 - 15 / 3 := totient_le_sub_div (p := 3) (by decide) (by decide)

/-! ## Sharper Ceiling at Odd Midpoints: Half the Totient

For an **odd** midpoint `m` the two independent structural constraints on a
contributing offset `k` — coprimality to `m` (`symmetric_pair_offset_coprime`) and
opposite parity to `m`, i.e. `k` **even** (`symmetric_pair_offset_parity`) — combine
into a genuine strengthening, because coprimality to an *odd* modulus says nothing
about parity.  A contributing offset is therefore an **even totative** of `m`.  The
involution `k ↦ m - k` maps the even totatives of `m` bijectively onto the odd ones:
it preserves coprimality (`Nat.coprime_self_sub_right`) and flips parity because `m`
is odd.  Hence exactly `φ(m) / 2` of the `φ(m)` totatives are even, giving for odd
composite `m`

    symmetricPairCount m ≤ φ(m) / 2,

a factor-of-two improvement over `symmetricPairCount_le_totient_of_not_prime` and the
sharpest closed-form ceiling in this file at odd midpoints.  No such gain exists for
*even* `m`: coprimality to an even `m` already forces the offset odd, so the parity
constraint is redundant there and `φ(m)` remains the right count. -/

/-- **Even and odd totatives of an odd modulus are equinumerous.**  For odd `m > 1`,
the involution `k ↦ m - k` is a bijection between the even totatives of `m` and the
odd ones: it preserves coprimality (`Nat.coprime_self_sub_right`) and, since `m` is
odd, sends an even `k` to an odd `m - k` and vice versa. -/
theorem card_even_totatives_eq_card_odd_totatives {m : ℕ} (hm : Odd m) (h1 : 1 < m) :
    ((Finset.range m).filter (fun k => m.Coprime k ∧ Even k)).card
      = ((Finset.range m).filter (fun k => m.Coprime k ∧ ¬ Even k)).card := by
  obtain ⟨j, hj⟩ := hm
  apply le_antisymm
  · apply Finset.card_le_card_of_injOn (fun k => m - k)
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Nat.even_iff] at hk ⊢
      obtain ⟨hkm, hcop, hev⟩ := hk
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · subst h; rw [Nat.coprime_zero_right] at hcop; omega
        · exact h
      exact ⟨by omega, (Nat.coprime_self_sub_right hkm.le).mpr hcop, by omega⟩
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
      obtain ⟨ha1, _⟩ := ha; obtain ⟨hb1, _⟩ := hb
      simp only at hab; omega
  · apply Finset.card_le_card_of_injOn (fun k => m - k)
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Nat.even_iff] at hk ⊢
      obtain ⟨hkm, hcop, hodd⟩ := hk
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · subst h; rw [Nat.coprime_zero_right] at hcop; omega
        · exact h
      exact ⟨by omega, (Nat.coprime_self_sub_right hkm.le).mpr hcop, by omega⟩
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
      obtain ⟨ha1, _⟩ := ha; obtain ⟨hb1, _⟩ := hb
      simp only at hab; omega

/-- **Exactly half of the totatives of an odd modulus are even.**  For odd `m > 1`,
`#{k < m : gcd(k, m) = 1 ∧ Even k} = φ(m) / 2`.  Splitting the `φ(m)` totatives by
parity and applying `card_even_totatives_eq_card_odd_totatives` gives two equal halves,
so `2 · (even totatives) = φ(m)`. -/
theorem card_even_totatives_eq_totient_div_two {m : ℕ} (hm : Odd m) (h1 : 1 < m) :
    ((Finset.range m).filter (fun k => m.Coprime k ∧ Even k)).card
      = Nat.totient m / 2 := by
  have hsplit :
      ((Finset.range m).filter (fun k => m.Coprime k ∧ Even k)).card
        + ((Finset.range m).filter (fun k => m.Coprime k ∧ ¬ Even k)).card
        = Nat.totient m := by
    rw [Nat.totient_eq_card_coprime, ← Finset.filter_filter, ← Finset.filter_filter]
    exact Finset.filter_card_add_filter_neg_card_eq_card _
  have heq := card_even_totatives_eq_card_odd_totatives hm h1
  omega

/-- **Half-totient ceiling at odd composite midpoints.**  For odd `m > 1` that is not
prime,

    symmetricPairCount m ≤ φ(m) / 2.

Every contributing offset `k` is a nonzero totative of `m` (coprimality:
`symmetric_pair_offset_coprime`; nonzero because `m - 0 = m` is composite) and is even
(opposite parity to the odd `m`: `symmetric_pair_offset_parity`), so the comet support
embeds into the `φ(m) / 2` even totatives of `m`.  This halves the totient ceiling
`symmetricPairCount_le_totient_of_not_prime` at odd midpoints. -/
theorem symmetricPairCount_le_half_totient_of_odd_not_prime {m : ℕ}
    (hm : Odd m) (h1 : 1 < m) (hcomp : ¬ Nat.Prime m) :
    symmetricPairCount m ≤ Nat.totient m / 2 := by
  obtain ⟨j, hj⟩ := hm
  rw [← card_even_totatives_eq_totient_div_two ⟨j, hj⟩ h1, symmetricPairCount]
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_range, Nat.even_iff] at hk ⊢
  obtain ⟨hkm, hp1, hp2⟩ := hk
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; rw [Nat.sub_zero] at hp1; exact absurd hp1 hcomp
    · exact h
  have hpar := symmetric_pair_offset_parity (by omega) hkm hp1 hp2
  exact ⟨hkm, (symmetric_pair_offset_coprime hk0 hp1 hp2).symm, by omega⟩

-- Concrete half-totient ceiling: `m = 9 = 3²` is odd composite, `φ(9) = 6`, so the
-- comet height of `18` is at most `φ(9)/2 = 3`.  (Actual height: `18 = 5 + 13 = 7 + 11`,
-- so `2 ≤ 3`.)  The full totient bound only gives `≤ 6`.
example : symmetricPairCount 9 ≤ Nat.totient 9 / 2 :=
  symmetricPairCount_le_half_totient_of_odd_not_prime (by decide) (by norm_num) (by decide)

-- The half-totient ceiling is strictly sharper than the totient ceiling at odd
-- composite midpoints: `φ(15)/2 = 4 < 8 = φ(15)`.
example : Nat.totient 15 / 2 < Nat.totient 15 := by decide

/-! ## Unified Half-Totient Ceiling at Every Odd Midpoint

`symmetricPairCount_le_half_totient_of_odd_not_prime` needs `m` composite: at an odd
*prime* midpoint the `k = 0` diagonal contributes (`m - 0 = m` is prime), so the
comet support is not contained in the even totatives alone.  Reinstating that single
diagonal offset — exactly as `symmetricPairCount_le_totient_succ` does for the general
totient ceiling — yields the odd-midpoint bound valid for **every** odd `m > 1`,
primes included:

    symmetricPairCount m ≤ φ(m) / 2 + 1.

This is the odd analog of the general `+1` ceiling `symmetricPairCount_le_totient_succ`
(`≤ φ(m) + 1`), and it strictly **halves** it at every odd midpoint, because the parity
constraint `symmetric_pair_offset_parity` (dead weight for even `m`, where coprimality
already forces the offset odd) becomes independent information at an odd modulus. -/

/-- **Unified half-totient ceiling at odd midpoints.**  For odd `m > 1` — with no
compositeness hypothesis, so odd primes are included —

    symmetricPairCount m ≤ φ(m) / 2 + 1.

Every nonzero contributing offset is an even totative of `m`
(`symmetric_pair_offset_coprime` + `symmetric_pair_offset_parity`), and the lone
possible `k = 0` diagonal is absorbed by the `+1` via `Finset.card_insert_le` — the
same device `symmetricPairCount_le_totient_succ` uses.  This is strictly sharper than
that general totient ceiling `≤ φ(m) + 1` at every odd `m > 1`. -/
theorem symmetricPairCount_le_half_totient_succ_of_odd {m : ℕ}
    (hm : Odd m) (h1 : 1 < m) :
    symmetricPairCount m ≤ Nat.totient m / 2 + 1 := by
  obtain ⟨j, hj⟩ := hm
  rw [← card_even_totatives_eq_totient_div_two ⟨j, hj⟩ h1, symmetricPairCount]
  refine (Finset.card_le_card ?_).trans (Finset.card_insert_le 0 _)
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_range] at hk
  obtain ⟨hkm, hp1, hp2⟩ := hk
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0; exact Finset.mem_insert_self 0 _
  · refine Finset.mem_insert_of_mem ?_
    simp only [Finset.mem_filter, Finset.mem_range, Nat.even_iff]
    have hpar := symmetric_pair_offset_parity (by omega) hkm hp1 hp2
    exact ⟨hkm, (symmetric_pair_offset_coprime hk0 hp1 hp2).symm, by omega⟩

-- Concrete unified ceiling at an odd *prime* midpoint, where the composite-only
-- `symmetricPairCount_le_half_totient_of_odd_not_prime` does not apply: `m = 7` is
-- prime, `φ(7) = 6`, so the comet height of `14` is at most `φ(7)/2 + 1 = 4`.
-- (Actual: `14 = 3 + 11 = 7 + 7`, height `2`.)
example : symmetricPairCount 7 ≤ Nat.totient 7 / 2 + 1 :=
  symmetricPairCount_le_half_totient_succ_of_odd (by decide) (by norm_num)

/-- **The unified half-totient ceiling dominates the parity `⌈m/2⌉` ceiling at odd
midpoints.**  For odd `m > 1`,

    φ(m) / 2 + 1 ≤ (m + 1) / 2  =  ⌈m / 2⌉.

Since `φ(m) < m` (`Nat.totient_lt`) and `φ(m)` is even for `m > 2` (`Nat.totient_even`),
we have `φ(m)/2 ≤ (m-1)/2`, and adding `1` lands exactly on `(m+1)/2` because `m` is
odd.  Composed with `symmetricPairCount_le_half_totient_succ_of_odd` this shows the
totient-based ceiling is at least as sharp as the elementary parity ceiling
`symmetricPairCount_le_half` at *every* odd midpoint (and strictly sharper whenever `m`
is composite, where `φ(m) < m - 1`). -/
theorem half_totient_succ_le_half_of_odd {m : ℕ} (hm : Odd m) (h1 : 1 < m) :
    Nat.totient m / 2 + 1 ≤ (m + 1) / 2 := by
  obtain ⟨s, hs⟩ := hm
  have hlt : Nat.totient m < m := Nat.totient_lt m h1
  obtain ⟨t, ht⟩ := Nat.totient_even (by omega : 2 < m)
  omega

end StrongGoldbach
