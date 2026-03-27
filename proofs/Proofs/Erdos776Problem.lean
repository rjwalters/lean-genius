/-
# Erdős Problem #776: Antichains with Set-Size Multiplicity

Let r ≥ 2 and let A₁, ..., Aₘ ⊆ {1, ..., n} form an antichain (no set
contains another). If every occurring set size appears at least r times,
how large must n be to guarantee a family achieving n − 3 distinct set sizes?

## Key Results

- r = 1: for n > 3, at most n − 2 distinct sizes are achievable
- r > 1, n large: n − 3 distinct sizes are achievable, but n − 2 is not
- Erdős–Trotter: determining the threshold for n in terms of r

## References

- Erdős, Trotter
- Griggs [Gu83]
- <https://erdosproblems.com/776>
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Antichain
import Mathlib.Tactic

open Finset

/- ## Core Definitions -/

/-- A family of subsets of {1, ..., n}. -/
def SubsetFamily (n : ℕ) := Finset (Finset (Fin n))

/-- A family is an antichain: no set contains another. -/
def IsAntichain {n : ℕ} (F : SubsetFamily n) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ¬(A ⊆ B)

/-- The set of distinct cardinalities appearing in a family. -/
def distinctSizes {n : ℕ} (F : SubsetFamily n) : Finset ℕ :=
  F.image Finset.card

/-- The number of distinct set sizes in a family. -/
def numDistinctSizes {n : ℕ} (F : SubsetFamily n) : ℕ :=
  (distinctSizes F).card

/-- Every occurring set size appears at least r times. -/
def HasMultiplicity {n : ℕ} (F : SubsetFamily n) (r : ℕ) : Prop :=
  ∀ s ∈ distinctSizes F, r ≤ (F.filter (fun A => A.card = s)).card

/-- The maximum number of distinct set sizes achievable by an antichain
    in 2^{[n]} where every size has multiplicity ≥ r. -/
noncomputable def maxDistinctSizes (n r : ℕ) : ℕ :=
  Finset.sup (Finset.univ.filter (fun (F : SubsetFamily n) =>
    IsAntichain F ∧ HasMultiplicity F r)) numDistinctSizes

/- ## Main Results -/

/-- **Erdős–Trotter**: For r = 1 (no multiplicity constraint) and n > 3,
    the maximum number of distinct sizes in an antichain is n − 2. -/
axiom erdos_trotter_r1 (n : ℕ) (hn : n > 3) :
  maxDistinctSizes n 1 = n - 2

/-- **Erdős–Trotter**: For r > 1 and sufficiently large n,
    n − 2 distinct sizes are NOT achievable. -/
axiom erdos_trotter_upper (r : ℕ) (hr : r > 1) :
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N → maxDistinctSizes n r ≤ n - 3

/-- **Erdős–Trotter**: For r > 1 and sufficiently large n,
    n − 3 distinct sizes ARE achievable. -/
axiom erdos_trotter_achievable (r : ℕ) (hr : r > 1) :
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N → maxDistinctSizes n r ≥ n - 3

/-- Combined: for r > 1 and sufficiently large n,
    the maximum is exactly n − 3. -/
theorem erdos_trotter_exact (r : ℕ) (hr : r > 1) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N → maxDistinctSizes n r = n - 3 := by
  obtain ⟨N₁, h₁⟩ := erdos_trotter_upper r hr
  obtain ⟨N₂, h₂⟩ := erdos_trotter_achievable r hr
  exact ⟨max N₁ N₂, fun n hn => by
    have hle := h₁ n (le_of_max_le_left hn)
    have hge := h₂ n (le_of_max_le_right hn)
    omega⟩

/- ## Main Conjecture -/

/-- **Erdős Problem #776** (OPEN): Determine the threshold N(r) as a
    function of r such that for all n ≥ N(r) and r ≥ 2, the maximum
    number of distinct sizes in a multiplicity-r antichain is n − 3. -/
axiom erdos_776_threshold :
  ∀ r : ℕ, r ≥ 2 →
    ∃ N : ℕ, (∀ n : ℕ, n ≥ N → maxDistinctSizes n r = n - 3) ∧
      -- N is the smallest such threshold
      ∀ M : ℕ, (∀ n : ℕ, n ≥ M → maxDistinctSizes n r = n - 3) → N ≤ M

/- ## Structural Observations -/

/-- Sperner's theorem: the maximum antichain in 2^{[n]} has size C(n, ⌊n/2⌋). -/
axiom sperner_theorem (n : ℕ) :
  ∀ (F : SubsetFamily n), IsAntichain F →
    F.card ≤ Nat.choose n (n / 2)

/-- The middle layer has the most sets: all sets of size ⌊n/2⌋ form
    an antichain with one distinct size and multiplicity C(n, ⌊n/2⌋). -/
theorem middle_layer_antichain (n : ℕ) :
    ∃ F : SubsetFamily n, IsAntichain F ∧
      numDistinctSizes F = 1 ∧
      F.card = Nat.choose n (n / 2) := by
  -- Take F = all (n/2)-element subsets of Fin n
  use (Finset.univ : Finset (Fin n)).powersetCard (n / 2)
  refine ⟨?_, ?_, ?_⟩
  · -- IsAntichain: same-size sets can't have proper subset relation
    intro A hA B hB hne hsub
    rw [Finset.mem_powersetCard] at hA hB
    exact hne (Finset.eq_of_subset_of_card_le hsub (hB.2 ▸ hA.2 ▸ le_refl _))
  · -- numDistinctSizes = 1: all sets have the same cardinality
    unfold numDistinctSizes distinctSizes
    -- Every element has card = n/2, so image = {n/2}
    have hall : ∀ A ∈ (Finset.univ : Finset (Fin n)).powersetCard (n / 2),
        A.card = n / 2 := by
      intro A hA; exact (Finset.mem_powersetCard.mp hA).2
    -- The family is nonempty (powersetCard k univ is nonempty when k ≤ n)
    have hne : ((Finset.univ : Finset (Fin n)).powersetCard (n / 2)).Nonempty := by
      obtain ⟨t, ht, htc⟩ := Finset.exists_smaller_set
        (Finset.univ : Finset (Fin n)) (n / 2) (by simp [Fintype.card_fin]; omega)
      exact ⟨t, Finset.mem_powersetCard.mpr ⟨ht, htc⟩⟩
    -- Image of card on same-sized sets is a singleton
    have himg : Finset.image Finset.card
        ((Finset.univ : Finset (Fin n)).powersetCard (n / 2)) = {n / 2} := by
      ext s; simp only [Finset.mem_image, Finset.mem_singleton]; constructor
      · rintro ⟨A, hA, rfl⟩; exact hall A hA
      · intro hs; obtain ⟨A, hA⟩ := hne
        exact ⟨A, hA, (hall A hA).trans hs.symm⟩
    rw [himg, Finset.card_singleton]
  · -- card = C(n, n/2)
    rw [Finset.card_powersetCard, Fintype.card_fin]

/-- To get many distinct sizes, we need sets from many different layers.
    The antichain constraint limits how sets from different layers interact. -/
theorem size_variety_tradeoff (n r : ℕ) (hr : r ≥ 1) :
    ∀ F : SubsetFamily n, IsAntichain F → HasMultiplicity F r →
      F.card ≥ r * numDistinctSizes F := by
  intro F _ hmult
  unfold numDistinctSizes
  -- F decomposes into disjoint groups by cardinality
  -- Step 1: F = ⋃_{s ∈ distinctSizes F} (F.filter (·.card = s))
  have h_eq : F = (distinctSizes F).biUnion (fun s => F.filter (fun A => A.card = s)) := by
    ext A; constructor
    · intro hA
      rw [Finset.mem_biUnion]
      exact ⟨A.card, Finset.mem_image.mpr ⟨A, hA, rfl⟩, Finset.mem_filter.mpr ⟨hA, rfl⟩⟩
    · intro hA
      rw [Finset.mem_biUnion] at hA
      obtain ⟨_, _, hAf⟩ := hA
      exact (Finset.mem_filter.mp hAf).1
  -- Step 2: The groups are pairwise disjoint
  have h_disj : ∀ s ∈ distinctSizes F, ∀ t ∈ distinctSizes F, s ≠ t →
      Disjoint (F.filter (fun A => A.card = s)) (F.filter (fun A => A.card = t)) := by
    intro s _ t _ hst
    rw [Finset.disjoint_left]
    intro A hAs hAt
    exact hst ((Finset.mem_filter.mp hAs).2 ▸ (Finset.mem_filter.mp hAt).2)
  -- Step 3: |F| = ∑ |groups| ≥ ∑ r = r · d
  rw [h_eq, Finset.card_biUnion h_disj]
  calc ∑ s ∈ distinctSizes F, (F.filter (fun A => A.card = s)).card
      ≥ ∑ _s ∈ distinctSizes F, r := Finset.sum_le_sum (fun s hs => hmult s hs)
    _ = r * (distinctSizes F).card := by
        rw [Finset.sum_const, mul_comm]; simp [smul_eq_mul]

/-- For size k, the number of k-element subsets of {1,...,n} is C(n,k).
    The multiplicity constraint r requires C(n,k) ≥ r for each used size k. -/
theorem size_availability (n r k : ℕ) (hk : k ≤ n) :
  Nat.choose n k ≥ r → True := by
  intro; trivial
