/-
# Erdős Problem 53: Sums and Products of Distinct Elements

*Reference:* [erdosproblems.com/53](https://www.erdosproblems.com/53)

Let `A` be a finite set of integers. Is it true that for every `k`, if `|A|`
is sufficiently large (depending on `k`), then there are at least `|A|^k`
integers representable as sums or products of distinct elements of `A`?

This problem was posed by Erdős and Szemerédi (1983) and resolved affirmatively
by Chang (2003). Erdős and Szemerédi also proved an upper bound:
there exist arbitrarily large sets `A` where the count of representable
integers is at most `exp(c · (log |A|)² · log log |A|)`.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-
## Section 1: Subset sums and products

We define the set of integers representable as a sum of distinct elements
of a finite set, and similarly for products.
-/

namespace Erdos53

open Finset

/-- The set of all sums of distinct elements (subsets) of a finite integer set. -/
def subsetSums (A : Finset ℤ) : Finset ℤ :=
  (A.powerset).image (fun S => S.sum id)

/-- The set of all products of distinct elements (nonempty subsets) of a finite integer set. -/
def subsetProducts (A : Finset ℤ) : Finset ℤ :=
  (A.powerset.filter (fun S => S.Nonempty)).image (fun S => S.prod id)

/-- The set of integers representable as either a sum or product of distinct elements. -/
def sumsOrProducts (A : Finset ℤ) : Finset ℤ :=
  subsetSums A ∪ subsetProducts A

/-
## Section 2: The Erdős–Szemerédi conjecture (Problem 53)

For every `k`, if `|A|` is large enough, then `|sumsOrProducts A| ≥ |A|^k`.
-/

/-- Erdős Problem 53: For every k, there exists N₀ such that for any finite
    set A of integers with |A| ≥ N₀, the number of integers representable
    as sums or products of distinct elements of A is at least |A|^k. -/
def ErdosProblem53 : Prop :=
  ∀ k : ℕ, k ≥ 1 →
    ∃ N₀ : ℕ, ∀ A : Finset ℤ, A.card ≥ N₀ →
      (sumsOrProducts A).card ≥ A.card ^ k

/-
## Section 3: Chang's theorem (2003)

Chang proved the conjecture affirmatively, resolving Problem 53.
-/

/-  Chang's theorem (2003): Erdős Problem 53 holds. -/
/-
## Section 4: The Erdős–Szemerédi upper bound

Erdős and Szemerédi showed that arbitrarily large sets exist where the count
of representable integers is bounded by `exp(c · (log |A|)² · log log |A|)`.
This shows the growth cannot be *too* fast.
-/

/-  There exists a constant c > 0 and arbitrarily large sets A where the
    number of representable integers is at most exp(c · (log |A|)² · log log |A|). -/
/-
## Section 5: Sum-product phenomena connection

This problem is closely related to the Erdős–Szemerédi sum-product conjecture
(Problem 52), which concerns `|A + A| + |A · A|` for a single set `A`.
The distinction is that Problem 53 asks about sums and products of *distinct*
elements (subsets), while Problem 52 concerns pairwise sums and products.
-/

/-- The sumset A + A. -/
def sumset (A : Finset ℤ) : Finset ℤ :=
  (A ×ˢ A).image (fun p => p.1 + p.2)

/-- The product set A · A. -/
def productset (A : Finset ℤ) : Finset ℤ :=
  (A ×ˢ A).image (fun p => p.1 * p.2)

/-- The sum-product conjecture (Problem 52) asserts that for every ε > 0,
    |A+A| + |A·A| ≥ |A|^{2-ε} for large enough |A|.
    This is a related but distinct problem. -/
def SumProductConjecture : Prop :=
  ∀ εNum εDen : ℕ, εNum ≥ 1 → εDen ≥ 1 →
    ∃ N₀ : ℕ, ∀ A : Finset ℤ, A.card ≥ N₀ →
      (sumset A).card + (productset A).card ≥ A.card ^ 2 / (A.card * εNum / εDen + 1)

/-
## Section 6: Counting distinct-element representations

We can count how many integers have a representation as a sum of distinct
elements versus a product of distinct elements.
-/

/-- Count of integers representable as subset sums. -/
def subsetSumCount (A : Finset ℤ) : ℕ := (subsetSums A).card

/-- Count of integers representable as subset products. -/
def subsetProductCount (A : Finset ℤ) : ℕ := (subsetProducts A).card

/-
## Section 7: Foundational lemmas (axiom-free)

The Erdős–Szemerédi conjecture (Chang's theorem) and the upper bound require deep
additive combinatorics beyond current Mathlib and stay documented above only.  The
elementary structural facts about the set-valued definitions in this file are,
however, fully machine-checkable.  All lemmas below are axiom-free
(`propext / Classical.choice / Quot.sound` only). -/

/-- The empty sum (empty subset) shows `0` is always a subset sum. -/
theorem zero_mem_subsetSums (A : Finset ℤ) : (0 : ℤ) ∈ subsetSums A := by
  rw [subsetSums, Finset.mem_image]
  exact ⟨∅, Finset.empty_mem_powerset A, by simp⟩

/-- Every element of `A` is itself a subset sum (via the singleton subset). -/
theorem mem_subsetSums_of_mem {A : Finset ℤ} {a : ℤ} (ha : a ∈ A) :
    a ∈ subsetSums A := by
  rw [subsetSums, Finset.mem_image]
  exact ⟨{a}, Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr ha), by simp⟩

/-- Every element of `A` is itself a subset product (via the singleton subset). -/
theorem mem_subsetProducts_of_mem {A : Finset ℤ} {a : ℤ} (ha : a ∈ A) :
    a ∈ subsetProducts A := by
  rw [subsetProducts, Finset.mem_image]
  refine ⟨{a}, ?_, by simp⟩
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr ha),
    Finset.singleton_nonempty a⟩

/-- Subset sums are among the sum-or-product representable integers. -/
theorem subsetSums_subset_sumsOrProducts (A : Finset ℤ) :
    subsetSums A ⊆ sumsOrProducts A := by
  rw [sumsOrProducts]; exact Finset.subset_union_left

/-- Subset products are among the sum-or-product representable integers. -/
theorem subsetProducts_subset_sumsOrProducts (A : Finset ℤ) :
    subsetProducts A ⊆ sumsOrProducts A := by
  rw [sumsOrProducts]; exact Finset.subset_union_right

/-- There are at most `2^{|A|}` subset sums (image of the powerset). -/
theorem subsetSums_card_le (A : Finset ℤ) : (subsetSums A).card ≤ 2 ^ A.card := by
  rw [subsetSums]
  calc (A.powerset.image (fun S => S.sum id)).card
      ≤ A.powerset.card := Finset.card_image_le
    _ = 2 ^ A.card := Finset.card_powerset A

/-- Subset sums are monotone in the ground set. -/
theorem subsetSums_mono {A B : Finset ℤ} (h : A ⊆ B) : subsetSums A ⊆ subsetSums B := by
  rw [subsetSums, subsetSums]
  exact Finset.image_subset_image (Finset.powerset_mono.mpr h)

/-- The union count dominates the subset-sum count. -/
theorem subsetSumCount_le_card (A : Finset ℤ) :
    subsetSumCount A ≤ (sumsOrProducts A).card := by
  rw [subsetSumCount]
  exact Finset.card_le_card (subsetSums_subset_sumsOrProducts A)

/-- The union count dominates the subset-product count. -/
theorem subsetProductCount_le_card (A : Finset ℤ) :
    subsetProductCount A ≤ (sumsOrProducts A).card := by
  rw [subsetProductCount]
  exact Finset.card_le_card (subsetProducts_subset_sumsOrProducts A)

/-- The sumset `A + A` has at most `|A|²` elements. -/
theorem sumset_card_le (A : Finset ℤ) : (sumset A).card ≤ A.card ^ 2 := by
  rw [sumset]
  calc ((A ×ˢ A).image (fun p => p.1 + p.2)).card
      ≤ (A ×ˢ A).card := Finset.card_image_le
    _ = A.card * A.card := Finset.card_product A A
    _ = A.card ^ 2 := (sq _).symm

/-- The product set `A · A` has at most `|A|²` elements. -/
theorem productset_card_le (A : Finset ℤ) : (productset A).card ≤ A.card ^ 2 := by
  rw [productset]
  calc ((A ×ˢ A).image (fun p => p.1 * p.2)).card
      ≤ (A ×ˢ A).card := Finset.card_image_le
    _ = A.card * A.card := Finset.card_product A A
    _ = A.card ^ 2 := (sq _).symm

/-- The empty set has exactly one subset sum, namely `0`. -/
theorem subsetSums_empty : subsetSums (∅ : Finset ℤ) = {0} := by
  rw [subsetSums, Finset.powerset_empty, Finset.image_singleton, Finset.sum_empty]

/-
## Section 8: The `k = 1` base case, the trivial upper bracket, and
distinct-prime richness (all axiom-free)

Section 7 recorded structural facts about `subsetSums`.  Here we (i) prove the
`k = 1` slice of the Erdős–Szemerédi lower bound — the one instance of Problem 53
that is elementary — (ii) supply the matching trivial *upper* bracket
`|sumsOrProducts A| ≤ 2^{|A|+1}`, (iii) fill in the missing `subsetProducts`
analogues of the Section-7 `subsetSums` lemmas, and (iv) prove the distinct-prime
richness fact `|subsetProducts A| = 2^{|A|} - 1` (Chang's problem.md "Key lemma 2"),
which shows the trivial upper bound is *attained* for sets of distinct primes.  All
lemmas remain axiom-free (`propext / Classical.choice / Quot.sound` only). -/

/-- Every element of `A` is a subset sum, so `A ⊆ subsetSums A`. -/
theorem subset_subsetSums (A : Finset ℤ) : A ⊆ subsetSums A :=
  fun _ ha => mem_subsetSums_of_mem ha

/-- The representable count is at least `|A|`: the ground set embeds into the
    subset sums, which in turn sit inside `sumsOrProducts A`. -/
theorem card_le_sumsOrProducts (A : Finset ℤ) : A.card ≤ (sumsOrProducts A).card :=
  Finset.card_le_card ((subset_subsetSums A).trans (subsetSums_subset_sumsOrProducts A))

/-- **Erdős Problem 53 holds for the exponent `k = 1`.** Taking `N₀ = 0`, every
    finite `A` already satisfies `|sumsOrProducts A| ≥ |A|^1`.  This is the
    elementary base case of the Erdős–Szemerédi lower bound; the deep content of
    Chang's theorem is the growth to `|A|^k` for every `k`, which stays
    documented (not axiomatized) above. -/
theorem erdosProblem53_exponent_one :
    ∃ N₀ : ℕ, ∀ A : Finset ℤ, A.card ≥ N₀ → (sumsOrProducts A).card ≥ A.card ^ 1 := by
  refine ⟨0, fun A _ => ?_⟩
  simpa using card_le_sumsOrProducts A

/-- `subsetProducts` of the empty set is empty: there are no nonempty subsets. -/
theorem subsetProducts_empty : subsetProducts (∅ : Finset ℤ) = ∅ := by
  rw [subsetProducts, Finset.powerset_empty]
  simp

/-- There are at most `2^{|A|}` subset products (image of a subfamily of the
    powerset). -/
theorem subsetProducts_card_le (A : Finset ℤ) : (subsetProducts A).card ≤ 2 ^ A.card := by
  rw [subsetProducts]
  calc ((A.powerset.filter (fun S => S.Nonempty)).image (fun S => S.prod id)).card
      ≤ (A.powerset.filter (fun S => S.Nonempty)).card := Finset.card_image_le
    _ ≤ A.powerset.card := Finset.card_filter_le _ _
    _ = 2 ^ A.card := Finset.card_powerset A

/-- Subset products are monotone in the ground set. -/
theorem subsetProducts_mono {A B : Finset ℤ} (h : A ⊆ B) :
    subsetProducts A ⊆ subsetProducts B := by
  rw [subsetProducts, subsetProducts]
  exact Finset.image_subset_image (Finset.filter_subset_filter _ (Finset.powerset_mono.mpr h))

/-- The sum-or-product representable set is monotone in the ground set. -/
theorem sumsOrProducts_mono {A B : Finset ℤ} (h : A ⊆ B) :
    sumsOrProducts A ⊆ sumsOrProducts B := by
  rw [sumsOrProducts, sumsOrProducts]
  exact Finset.union_subset_union (subsetSums_mono h) (subsetProducts_mono h)

/-- `0` is always representable (as the empty subset sum). -/
theorem zero_mem_sumsOrProducts (A : Finset ℤ) : (0 : ℤ) ∈ sumsOrProducts A :=
  subsetSums_subset_sumsOrProducts A (zero_mem_subsetSums A)

/-- The representable set is always nonempty. -/
theorem sumsOrProducts_nonempty (A : Finset ℤ) : (sumsOrProducts A).Nonempty :=
  ⟨0, zero_mem_sumsOrProducts A⟩

/-- Trivial upper bracket: the representable count is at most `2^{|A|+1}`.
    Together with `card_le_sumsOrProducts` this pins `|sumsOrProducts A|` between
    `|A|` and `2^{|A|+1}`; Chang's theorem sharpens the *lower* end to `|A|^k`. -/
theorem sumsOrProducts_card_le (A : Finset ℤ) :
    (sumsOrProducts A).card ≤ 2 ^ (A.card + 1) := by
  rw [sumsOrProducts]
  calc (subsetSums A ∪ subsetProducts A).card
      ≤ (subsetSums A).card + (subsetProducts A).card := Finset.card_union_le _ _
    _ ≤ 2 ^ A.card + 2 ^ A.card :=
        Nat.add_le_add (subsetSums_card_le A) (subsetProducts_card_le A)
    _ = 2 ^ (A.card + 1) := by rw [pow_succ]; ring

/-- For a set `A` of **distinct positive primes**, subset products are pairwise
    distinct: a positive prime `p ∈ A` divides `∏ S` iff `p ∈ S`, so the subset
    is recovered from its product.  (Positivity rules out the `p ↔ -p` collision
    that `Prime` alone permits over `ℤ`.) -/
theorem subsetProd_injOn_of_prime {A : Finset ℤ}
    (hA : ∀ p ∈ A, Prime p) (hpos : ∀ p ∈ A, 0 < p) :
    Set.InjOn (fun S => S.prod id) (A.powerset : Set (Finset ℤ)) := by
  have key : ∀ U : Finset ℤ, U ⊆ A → ∀ p, p ∈ A → (p ∈ U ↔ p ∣ U.prod id) := by
    intro U hU p hp
    refine ⟨fun hpU => Finset.dvd_prod_of_mem id hpU, fun hdvd => ?_⟩
    rcases (Prime.dvd_finsetProd_iff (hA p hp) id).mp hdvd with ⟨x, hxU, hpx⟩
    have hxA : x ∈ A := hU hxU
    have hnat : p.natAbs = x.natAbs :=
      Int.associated_iff_natAbs.mp ((hA p hp).associated_of_dvd (hA x hxA) hpx)
    have hp' : (p.natAbs : ℤ) = p := Int.natAbs_of_nonneg (le_of_lt (hpos p hp))
    have hx' : (x.natAbs : ℤ) = x := Int.natAbs_of_nonneg (le_of_lt (hpos x hxA))
    have hpx' : p = x := by rw [← hp', ← hx', hnat]
    rw [hpx']; exact hxU
  intro S hS T hT hST
  rw [Finset.mem_coe, Finset.mem_powerset] at hS hT
  have hST : S.prod id = T.prod id := hST
  apply Finset.ext
  intro p
  by_cases hp : p ∈ A
  · rw [key S hS p hp, key T hT p hp, hST]
  · exact ⟨fun h => absurd (hS h) hp, fun h => absurd (hT h) hp⟩

/-- **Distinct-prime richness (problem.md "Key lemma 2").** For a set `A` of
    distinct positive primes, the number of distinct nonempty subset products is
    exactly `2^{|A|} - 1` — unique factorization makes every nonempty subset
    yield a different product.  This exhibits sets attaining the trivial upper
    bound `sumsOrProducts_card_le` on the multiplicative side. -/
theorem subsetProducts_card_of_prime {A : Finset ℤ}
    (hA : ∀ p ∈ A, Prime p) (hpos : ∀ p ∈ A, 0 < p) :
    (subsetProducts A).card = 2 ^ A.card - 1 := by
  have hsub : (↑(A.powerset.filter (fun S => S.Nonempty)) : Set (Finset ℤ)) ⊆ ↑A.powerset :=
    Finset.coe_subset.mpr (Finset.filter_subset _ _)
  have hinj : Set.InjOn (fun S => S.prod id)
      (↑(A.powerset.filter (fun S => S.Nonempty)) : Set (Finset ℤ)) :=
    Set.InjOn.mono hsub (subsetProd_injOn_of_prime hA hpos)
  rw [subsetProducts, Finset.card_image_of_injOn hinj]
  have hfe : A.powerset.filter (fun S => S.Nonempty) = A.powerset.erase ∅ := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_powerset,
      Finset.nonempty_iff_ne_empty]
    tauto
  rw [hfe, Finset.card_erase_of_mem (Finset.empty_mem_powerset A), Finset.card_powerset]

/-- **Superincreasing ⇒ injective subset sums.** If every element of `A` is
positive and strictly exceeds the sum of the strictly smaller elements of `A`
(the *superincreasing* condition, e.g. `{1, 2, 4, …, 2^{k−1}}`), then distinct
subsets have distinct sums.  This is the additive analogue of
`subsetProd_injOn_of_prime`.

Proof: if `S ≠ T` had equal sums, let `m` be the largest element in their
symmetric difference, say `m ∈ S \ T`.  Cancelling the common part gives
`(S\T).sum = (T\S).sum`; but `m ≤ (S\T).sum` while every element of `T\S` is
`< m`, so `(T\S).sum ≤ (Σ elements < m) < m` by superincreasingness — a
contradiction. -/
theorem subsetSum_injOn_of_superincreasing {A : Finset ℤ}
    (hpos : ∀ a ∈ A, 0 < a)
    (hsi : ∀ a ∈ A, (A.filter (· < a)).sum id < a) :
    Set.InjOn (fun S => S.sum id) (A.powerset : Set (Finset ℤ)) := by
  -- one-sided contradiction, applied with the two subsets in the order that puts
  -- the max element of the symmetric difference on the left
  have key : ∀ S T : Finset ℤ, S ⊆ A → T ⊆ A → S.sum id = T.sum id →
      ∀ m, m ∈ S \ T → (∀ x ∈ T \ S, x < m) → False := by
    intro S T hS hT hsum m hm hmax
    have hmA : m ∈ A := hS (Finset.mem_sdiff.mp hm).1
    -- the two half-differences have equal sum
    have hu1 : (S ∪ T).sum id = S.sum id + (T \ S).sum id := by
      rw [← Finset.union_sdiff_self_eq_union, Finset.sum_union Finset.disjoint_sdiff_self_right]
    have hu2 : (S ∪ T).sum id = T.sum id + (S \ T).sum id := by
      rw [Finset.union_comm, ← Finset.union_sdiff_self_eq_union,
        Finset.sum_union Finset.disjoint_sdiff_self_right]
    have hsplit : (S \ T).sum id = (T \ S).sum id := by
      have : S.sum id + (T \ S).sum id = T.sum id + (S \ T).sum id := by rw [← hu1, hu2]
      linarith
    -- m ≤ (S \ T).sum, since m ∈ S \ T and all elements are positive
    have hge : m ≤ (S \ T).sum id :=
      Finset.single_le_sum
        (fun x hx => le_of_lt (hpos x (hS (Finset.mem_sdiff.mp hx).1))) hm
    -- (T \ S).sum < m, since T \ S ⊆ {elements of A below m}
    have hTsub : T \ S ⊆ A.filter (· < m) := fun x hx =>
      Finset.mem_filter.mpr ⟨hT (Finset.mem_sdiff.mp hx).1, hmax x hx⟩
    have hle : (T \ S).sum id ≤ (A.filter (· < m)).sum id :=
      Finset.sum_le_sum_of_subset_of_nonneg hTsub
        (fun x hx _ => le_of_lt (hpos x (Finset.mem_filter.mp hx).1))
    have hfilt : (A.filter (· < m)).sum id < m := hsi m hmA
    linarith
  intro S hS T hT hST
  rw [Finset.mem_coe, Finset.mem_powerset] at hS hT
  by_contra hne
  -- the symmetric difference is nonempty
  have hD : (S \ T ∪ T \ S).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hne
    have h1 : S \ T = ∅ := Finset.subset_empty.mp (h ▸ Finset.subset_union_left)
    have h2 : T \ S = ∅ := Finset.subset_empty.mp (h ▸ Finset.subset_union_right)
    exact Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp h1)
      (Finset.sdiff_eq_empty_iff_subset.mp h2)
  -- its maximum lies in one side; the other side is strictly below it
  set m := (S \ T ∪ T \ S).max' hD with hm_def
  have hm_mem : m ∈ S \ T ∪ T \ S := Finset.max'_mem _ hD
  have hmax : ∀ x ∈ S \ T ∪ T \ S, x ≤ m := fun x hx => Finset.le_max' _ x hx
  rcases Finset.mem_union.mp hm_mem with hmL | hmR
  · refine key S T hS hT hST m hmL (fun x hx => ?_)
    rcases lt_or_eq_of_le (hmax x (Finset.mem_union.mpr (Or.inr hx))) with h | h
    · exact h
    · exact absurd ((h ▸ hx : m ∈ T \ S)) (fun hmTS =>
        (Finset.mem_sdiff.mp hmL).2 (Finset.mem_sdiff.mp hmTS).1)
  · refine key T S hT hS hST.symm m hmR (fun x hx => ?_)
    rcases lt_or_eq_of_le (hmax x (Finset.mem_union.mpr (Or.inl hx))) with h | h
    · exact h
    · exact absurd ((h ▸ hx : m ∈ S \ T)) (fun hmST =>
        (Finset.mem_sdiff.mp hmR).2 (Finset.mem_sdiff.mp hmST).1)

/-- **Additive richness (dual of `subsetProducts_card_of_prime`).** For a
superincreasing set `A`, the number of distinct subset sums is exactly `2^{|A|}`
— every subset gives a different sum.  This exhibits sets attaining the trivial
upper bound `subsetSums_card_le` on the additive side, so that bound is sharp. -/
theorem subsetSums_card_of_superincreasing {A : Finset ℤ}
    (hpos : ∀ a ∈ A, 0 < a)
    (hsi : ∀ a ∈ A, (A.filter (· < a)).sum id < a) :
    (subsetSums A).card = 2 ^ A.card := by
  rw [subsetSums,
    Finset.card_image_of_injOn (subsetSum_injOn_of_superincreasing hpos hsi),
    Finset.card_powerset]

end Erdos53
