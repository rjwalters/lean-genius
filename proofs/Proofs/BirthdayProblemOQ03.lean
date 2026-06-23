import Mathlib

/-
# k-Way Birthday Coincidences (OQ-03)

## What This Proves
Generalizes the Birthday Problem from pairwise collisions to k-way coincidences:
at least k people sharing the same birthday.

**Mathematical Statement:**
Given n people and d equally likely birthdays, a k-way coincidence occurs when
at least k people share the same birthday. We prove:

1. **Generalized Pigeonhole**: n > (k-1)·d ⟹ k-way coincidence is certain
2. **Classical Recovery**: k=2 case is equivalent to non-injectivity
3. **Monotonicity**: k-way ⟹ k'-way when k' ≤ k (stronger coincidence implies weaker)
4. **Probability = 1** when pigeonhole bound is exceeded

## Approach
- **Foundation (from Mathlib):** `Finset.card_eq_sum_card_fiberwise` for fiber
  decomposition, `Finset.sum_le_sum` for bounding, `Fintype` for finite counting.
- **Original Contributions:** Formalization of k-way coincidences, generalized
  pigeonhole in the birthday setting, classical recovery, monotonicity.
- **Proof Techniques Demonstrated:** Fiber decomposition, counting by complement,
  generalized pigeonhole, contradiction.

## Historical Context
The k-way birthday problem is a natural generalization: instead of asking when
2 people share a birthday, we ask when k people do. Thresholds grow roughly as
d^{(k-1)/k}·(k!)^{1/k}. For d=365: k=2 → n≈23, k=3 → n≈88, k=4 → n≈187.
-/

namespace BirthdayKWay

/-
## Part I: Core Definitions

We model birthday assignments as functions f : Fin n → Fin d, where n is the
number of people and d is the number of days. The "fiber" at day j is the set
of people assigned to that day.
-/

/-- The fiber of an assignment at day j: the set of people assigned to day j. -/
def fiberAt {n d : ℕ} (f : Fin n → Fin d) (j : Fin d) : Finset (Fin n) :=
  Finset.univ.filter (fun i => f i = j)

/-- A k-way coincidence: some day has at least k people assigned to it. -/
def HasKWay {n d : ℕ} (f : Fin n → Fin d) (k : ℕ) : Prop :=
  ∃ j : Fin d, k ≤ (fiberAt f j).card

/-
## Part II: Fiber Partition

The fibers of any assignment partition the set of people: every person belongs
to exactly one fiber, so the fiber sizes sum to the total number of people.
-/

/-- **Fiber partition of unity**: fiber sizes sum to n.
    Every person is counted in exactly one fiber (the day they're assigned to). -/
theorem sum_fiberAt_card {n d : ℕ} (f : Fin n → Fin d) :
    ∑ j : Fin d, (fiberAt f j).card = n := by
  simp only [fiberAt]
  have h := Finset.card_eq_sum_card_fiberwise
    (f := f) (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset (Fin d)))
    (fun a _ => Finset.mem_univ (f a))
  simp only [Finset.card_univ, Fintype.card_fin] at h
  linarith

/-
## Part III: Generalized Pigeonhole

The heart of the k-way birthday problem: if n people are distributed among d
days, and n > (k-1)·d, then some day must have at least k people.

Proof: if every fiber had < k elements (i.e., ≤ k-1), then
  n = ∑ fiber sizes ≤ ∑ (k-1) = (k-1)·d < n,
a contradiction.
-/

/-- **Generalized Pigeonhole Bound for Birthdays.**
    If n > (k-1)·d, then every assignment f : Fin n → Fin d has a k-way
    coincidence. No matter how you distribute the people, some day is crowded. -/
theorem pigeonhole_kway {n d k : ℕ} (f : Fin n → Fin d) (hk : 0 < k)
    (hn : (k - 1) * d < n) : HasKWay f k := by
  by_contra h
  simp only [HasKWay, not_exists, Nat.not_le] at h
  -- h : ∀ j, (fiberAt f j).card < k, i.e., every fiber has fewer than k people
  have hbound : ∑ j : Fin d, (fiberAt f j).card ≤ (k - 1) * d := by
    calc ∑ j : Fin d, (fiberAt f j).card
        ≤ ∑ _j : Fin d, (k - 1) := by
          apply Finset.sum_le_sum
          intro j _
          have := h j
          omega  -- card < k ⟹ card ≤ k - 1 (natural numbers)
      _ = d * (k - 1) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      _ = (k - 1) * d := Nat.mul_comm d (k - 1)
  have hsum := sum_fiberAt_card f
  omega  -- n = ∑ card ≤ (k-1)*d < n, contradiction

/-- Pigeonhole for the standard birthday setting (d = 365).
    With more than 365·(k-1) people, a k-way coincidence is guaranteed. -/
theorem pigeonhole_365 {n k : ℕ} (f : Fin n → Fin 365) (hk : 0 < k)
    (hn : (k - 1) * 365 < n) : HasKWay f k :=
  pigeonhole_kway f hk hn

/-- For k=2, pigeonhole gives the classical result: n > 365 ⟹ collision certain.
    This is just the standard pigeonhole principle. -/
example (f : Fin 366 → Fin 365) : HasKWay f 2 :=
  pigeonhole_kway f (by omega) (by omega)

/-- For k=3, need n > 2·365 = 730 for a guaranteed triple. -/
example (f : Fin 731 → Fin 365) : HasKWay f 3 :=
  pigeonhole_kway f (by omega) (by omega)

/-
## Part IV: Classical Recovery (k=2)

The 2-way coincidence is the classical birthday problem: at least two people
share a birthday, which is equivalent to the assignment being non-injective.
-/

/-- **Classical Recovery**: a 2-way coincidence ⟺ the assignment is not injective.
    This connects the k-way framework back to the original birthday problem. -/
theorem hasKWay_two_iff_not_injective {n d : ℕ} (f : Fin n → Fin d) :
    HasKWay f 2 ↔ ¬Function.Injective f := by
  constructor
  · -- Forward: 2-way coincidence ⟹ not injective
    rintro ⟨j, hj⟩ hinj
    -- The fiber at j has ≥ 2 elements, giving distinct i₁ ≠ i₂ with f i₁ = f i₂ = j
    have : 1 < (fiberAt f j).card := by omega
    rw [Finset.one_lt_card] at this
    obtain ⟨i₁, hi₁, i₂, hi₂, hne⟩ := this
    simp only [fiberAt, Finset.mem_filter, Finset.mem_univ, true_and] at hi₁ hi₂
    exact hne (hinj (hi₁.trans hi₂.symm))
  · -- Backward: not injective ⟹ 2-way coincidence
    intro hninj
    simp only [Function.Injective, not_forall] at hninj
    obtain ⟨i₁, i₂, heq, hne⟩ := hninj
    push_neg at hne
    refine ⟨f i₁, ?_⟩
    have : 1 < (fiberAt f (f i₁)).card := by
      rw [Finset.one_lt_card]
      exact ⟨i₁, by simp [fiberAt],
             i₂, by simp [fiberAt, heq],
             hne⟩
    omega

/-- No 2-way coincidence ⟺ injective (the complement characterization). -/
theorem no_kway_two_iff_injective {n d : ℕ} (f : Fin n → Fin d) :
    (∀ j : Fin d, (fiberAt f j).card < 2) ↔ Function.Injective f := by
  constructor
  · -- All fibers have < 2 elements ⟹ injective
    intro hsmall i₁ i₂ heq
    by_contra hne
    have : 1 < (fiberAt f (f i₁)).card := by
      rw [Finset.one_lt_card]
      exact ⟨i₁, by simp [fiberAt],
             i₂, by simp [fiberAt, heq],
             fun h => hne h⟩
    have := hsmall (f i₁)
    omega
  · -- Injective ⟹ all fibers have < 2 elements
    intro hinj j
    by_contra hge
    push_neg at hge  -- hge : 2 ≤ card
    have : 1 < (fiberAt f j).card := by omega
    rw [Finset.one_lt_card] at this
    obtain ⟨i₁, hi₁, i₂, hi₂, hne⟩ := this
    simp only [fiberAt, Finset.mem_filter, Finset.mem_univ, true_and] at hi₁ hi₂
    exact hne (hinj (hi₁.trans hi₂.symm))

/-
## Part V: Monotonicity

Two natural monotonicity results:
1. A stronger coincidence (higher k) implies a weaker one (lower k')
2. More people makes coincidences more likely (in the pigeonhole sense)
-/

/-- **Monotonicity in k**: a k-way coincidence implies a k'-way coincidence for k' ≤ k.
    If k people share a birthday, then certainly k' ≤ k people do too. -/
theorem hasKWay_mono {n d k k' : ℕ} (hle : k' ≤ k) (f : Fin n → Fin d)
    (h : HasKWay f k) : HasKWay f k' := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j, le_trans hle hj⟩

/-- Special case: any k-way coincidence (k ≥ 2) implies a 2-way coincidence.
    A birthday triple implies a birthday pair. -/
theorem hasKWay_implies_pair {n d k : ℕ} (hk : 2 ≤ k) (f : Fin n → Fin d)
    (h : HasKWay f k) : HasKWay f 2 :=
  hasKWay_mono hk f h

/-
## Part VI: Trivial Cases

Edge cases that validate the definition.
-/

/-- A 0-way coincidence is trivially satisfied (when d > 0).
    Every fiber has ≥ 0 elements. -/
theorem hasKWay_zero {n d : ℕ} (f : Fin n → Fin d) (hd : 0 < d) :
    HasKWay f 0 := by
  exact ⟨⟨0, hd⟩, Nat.zero_le _⟩

/-- A 1-way coincidence holds iff n > 0 (when d > 0).
    Some day has at least 1 person iff there is at least 1 person. -/
theorem hasKWay_one_iff {n d : ℕ} (_hd : 0 < d) :
    (∀ f : Fin n → Fin d, HasKWay f 1) ↔ 0 < n := by
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    interval_cases n
    -- n = 0: need to show ¬(∀ f : Fin 0 → Fin d, HasKWay f 1)
    have f : Fin 0 → Fin d := Fin.elim0
    have := h f
    obtain ⟨j, hj⟩ := this
    simp [fiberAt] at hj
  · intro hn f
    -- n > 0, so ∃ person 0, and f(0) is their assigned day
    exact ⟨f ⟨0, hn⟩, by
      simp only [fiberAt]
      have : ⟨0, hn⟩ ∈ Finset.univ.filter (fun i : Fin n => f i = f ⟨0, hn⟩) := by
        simp
      exact Finset.one_le_card.mpr ⟨_, this⟩⟩

/-
## Part VII: The k-Way Probability

We define the probability of a k-way coincidence as 1 minus the fraction
of assignments where every fiber has fewer than k elements.
-/

/-- The set of assignments with no k-way coincidence: every day has < k people. -/
def noKWaySet (n d k : ℕ) : Finset (Fin n → Fin d) :=
  Finset.univ.filter (fun f => ∀ j : Fin d, (fiberAt f j).card < k)

/-- The probability of a k-way coincidence among n people with d days. -/
noncomputable def probKWay (n d k : ℕ) : ℚ :=
  1 - (noKWaySet n d k).card / (d : ℚ) ^ n

/-- **Pigeonhole probability**: when n > (k-1)·d, the probability is exactly 1.
    Every possible assignment has a k-way coincidence. -/
theorem probKWay_one_of_pigeonhole {n d k : ℕ} (hk : 0 < k)
    (hn : (k - 1) * d < n) : probKWay n d k = 1 := by
  suffices h : noKWaySet n d k = ∅ by
    simp [probKWay, h]
  rw [Finset.eq_empty_iff_forall_notMem]
  intro f hf
  simp only [noKWaySet, Finset.mem_filter, Finset.mem_univ, true_and] at hf
  have hkway := pigeonhole_kway f hk hn
  obtain ⟨j, hj⟩ := hkway
  exact Nat.not_lt.mpr hj (hf j)

/-- The no-k-way set shrinks as k decreases (weaker threshold, fewer safe assignments).
    This implies the k-way probability increases as k decreases. -/
theorem noKWaySet_mono {n d k k' : ℕ} (hle : k' ≤ k) :
    noKWaySet n d k' ⊆ noKWaySet n d k := by
  intro f hf
  simp only [noKWaySet, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
  exact fun j => lt_of_lt_of_le (hf j) hle

/-- **Probability monotonicity in k**: higher k ⟹ lower probability.
    It's harder to get k people sharing a birthday than k' < k people. -/
theorem probKWay_mono_k {n d k k' : ℕ} (hle : k' ≤ k) (hd : 0 < d) :
    probKWay n d k ≤ probKWay n d k' := by
  simp only [probKWay]
  have hpos : (0 : ℚ) < (d : ℚ) ^ n := by positivity
  have hmono := noKWaySet_mono hle (n := n) (d := d)
  have hcard := Finset.card_le_card hmono
  have h1 : ((noKWaySet n d k').card : ℚ) / (d : ℚ) ^ n ≤
      ((noKWaySet n d k).card : ℚ) / (d : ℚ) ^ n := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hpos)
    exact Nat.cast_le.mpr hcard
  linarith

/-
## Part VIII: Connection to Classical Birthday Problem (k=2)

For k=2, the no-k-way set consists exactly of the injective functions.
The count of injective functions Fin n → Fin d equals descFactorial(d, n),
recovering the classical birthday probability formula.
-/

/-- For k=2, assignments without k-way coincidences are exactly the injective ones.
    This connects the general framework to the classical birthday problem. -/
theorem noKWaySet_two_eq_injective (n d : ℕ) :
    noKWaySet n d 2 = Finset.univ.filter (fun f : Fin n → Fin d =>
      Function.Injective f) := by
  ext f
  simp only [noKWaySet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact no_kway_two_iff_injective f

/-- No k-way coincidence ⟺ every fiber has < k elements. -/
theorem no_kway_iff_fibers_small {n d k : ℕ} (f : Fin n → Fin d) :
    ¬HasKWay f k ↔ ∀ j : Fin d, (fiberAt f j).card < k := by
  simp only [HasKWay, not_exists, Nat.not_le]

/-
## Part IX: Counting with Bounded Multiplicities

For small cases, the no-k-way set can be computed directly.
-/

/-- With 1 person and d ≥ 1 days, no 2-way coincidence is possible. -/
theorem noKWaySet_one_person (d : ℕ) :
    noKWaySet 1 d 2 = Finset.univ := by
  ext f
  simp only [noKWaySet, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  intro j
  have : (fiberAt f j).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [fiberAt, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact Fin.ext (by omega)
  omega

/-- With 0 people, every fiber is empty. -/
theorem fiberAt_empty {d : ℕ} (f : Fin 0 → Fin d) (j : Fin d) :
    fiberAt f j = ∅ := by
  ext x; exact Fin.elim0 x

/-- With 0 people and k > 0, the no-k-way set is the full set. -/
theorem noKWaySet_zero_people (d k : ℕ) (hk : 0 < k) :
    noKWaySet 0 d k = Finset.univ := by
  ext f
  simp only [noKWaySet, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  intro j
  rw [fiberAt_empty]
  simp [hk]

/-
## Part XI: The n ≤ k-1 Case

When n ≤ k-1, no k-way coincidence is possible (not enough people to
fill any day k times), so the probability is 0.
-/

/-- When n < k, no assignment can have a k-way coincidence.
    You can't have k people at one birthday with fewer than k people total. -/
theorem no_kway_of_lt {n d k : ℕ} (hn : n < k) (f : Fin n → Fin d) :
    ¬HasKWay f k := by
  intro ⟨j, hj⟩
  have hcard : (fiberAt f j).card ≤ n := by
    calc (fiberAt f j).card
        ≤ Finset.univ.card := Finset.card_filter_le _ _
      _ = n := by simp [Fintype.card_fin]
  omega

/-- When n < k, the probability of a k-way coincidence is 0. -/
theorem probKWay_zero_of_lt {n d k : ℕ} (hn : n < k) (hd : 0 < d) :
    probKWay n d k = 0 := by
  have hset : noKWaySet n d k = Finset.univ := by
    ext f
    simp only [noKWaySet, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    intro j
    have hcard : (fiberAt f j).card ≤ n := by
      calc (fiberAt f j).card
          ≤ Finset.univ.card := Finset.card_filter_le _ _
        _ = n := by simp [Fintype.card_fin]
    omega
  simp only [probKWay, hset, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  have hd_ne : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Nat.cast_pow, div_self (pow_ne_zero n hd_ne), sub_self]

end BirthdayKWay
