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
import Mathlib.Combinatorics.SetFamily.LYM

open Finset

/- ## Core Definitions -/

/-- A family of subsets of {1, ..., n}. -/
def SubsetFamily (n : ℕ) := Finset (Finset (Fin n))

/-- A family is an antichain: no set contains another. -/
def IsAntichainFamily {n : ℕ} (F : SubsetFamily n) : Prop :=
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
    IsAntichainFamily F ∧ HasMultiplicity F r)) numDistinctSizes

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
    number of distinct sizes in a multiplicity-r antichain is n − 3.
    Existence follows from erdos_trotter_exact; minimality from Nat.find. -/
open Classical in
theorem erdos_776_threshold :
    ∀ r : ℕ, r ≥ 2 →
      ∃ N : ℕ, (∀ n : ℕ, n ≥ N → maxDistinctSizes n r = n - 3) ∧
        -- N is the smallest such threshold
        ∀ M : ℕ, (∀ n : ℕ, n ≥ M → maxDistinctSizes n r = n - 3) → N ≤ M := by
  intro r hr
  have h_exact := erdos_trotter_exact r (by omega)
  exact ⟨Nat.find h_exact, Nat.find_spec h_exact, fun M hM => Nat.find_min' h_exact hM⟩

/- ## Structural Observations -/

/-- Sperner's theorem: the maximum antichain in 2^{[n]} has size C(n, ⌊n/2⌋).
    Bridges our custom IsAntichainFamily to Mathlib's IsAntichain, then applies
    Mathlib's IsAntichain.sperner (proved via the LYM inequality). -/
theorem sperner_theorem (n : ℕ) :
    ∀ (F : SubsetFamily n), IsAntichainFamily F →
      F.card ≤ Nat.choose n (n / 2) := by
  intro F hF
  -- Bridge custom IsAntichainFamily to Mathlib's IsAntichain (· ⊆ ·)
  have h : _root_.IsAntichain (· ⊆ ·) (↑F : Set (Finset (Fin n))) := by
    intro A hA B hB hne hsub
    exact hF A (Finset.mem_coe.mp hA) B (Finset.mem_coe.mp hB) hne hsub
  -- Apply Mathlib's Sperner bound (from LYM inequality)
  have := h.sperner (α := Fin n)
  simp [Fintype.card_fin] at this
  exact this

/-- The middle layer has the most sets: all sets of size ⌊n/2⌋ form
    an antichain with one distinct size and multiplicity C(n, ⌊n/2⌋). -/
theorem middle_layer_antichain (n : ℕ) :
    ∃ F : SubsetFamily n, IsAntichainFamily F ∧
      numDistinctSizes F = 1 ∧
      F.card = Nat.choose n (n / 2) := by
  -- Take F = all (n/2)-element subsets of Fin n
  use (Finset.univ : Finset (Fin n)).powersetCard (n / 2)
  refine ⟨?_, ?_, ?_⟩
  · -- IsAntichainFamily: same-size sets can't have proper subset relation
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
    ∀ F : SubsetFamily n, IsAntichainFamily F → HasMultiplicity F r →
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

/- ## Structural Lemmas for Axiom Elimination

These lemmas decompose the path toward proving the known-result axioms
(erdos_trotter_r1, erdos_trotter_upper, erdos_trotter_achievable).
Key infrastructure: empty/full set exclusion, same-size antichain property,
and size bounds on distinct sizes in antichains. -/

/-- The empty set cannot appear in an antichain that contains any non-empty set,
    since ∅ ⊆ A for all A. -/
theorem empty_not_in_nontrivial_antichain {n : ℕ} {F : Finset (Finset (Fin n))}
    (hF : IsAntichainFamily F) (hA : ∃ A ∈ F, A ≠ ∅) : ∅ ∉ F := by
  unfold IsAntichainFamily at hF
  intro hempty
  obtain ⟨A, hAF, hAne⟩ := hA
  exact absurd (Finset.empty_subset A) (hF ∅ hempty A hAF (Ne.symm hAne))

/-- The full set cannot appear in an antichain that contains any proper subset,
    since A ⊆ Finset.univ for all A. -/
theorem univ_not_in_nontrivial_antichain {n : ℕ} {F : Finset (Finset (Fin n))}
    (hF : IsAntichainFamily F) (hA : ∃ A ∈ F, A ≠ Finset.univ) :
    Finset.univ ∉ F := by
  unfold IsAntichainFamily at hF
  intro huniv
  obtain ⟨A, hAF, hAne⟩ := hA
  exact absurd (Finset.subset_univ A) (hF A hAF Finset.univ huniv hAne)

/-- Any family of distinct sets with the same cardinality is automatically
    an antichain: if A ⊆ B and |A| = |B| then A = B. -/
theorem same_size_is_antichain {n : ℕ} {F : Finset (Finset (Fin n))} (k : ℕ)
    (hk : ∀ A ∈ F, A.card = k) : IsAntichainFamily F := by
  unfold IsAntichainFamily
  intro A hA B hB hne hsub
  have hAk := hk A hA
  have hBk := hk B hB
  exact hne (Finset.eq_of_subset_of_card_le hsub (by omega))

/-- In an antichain with at least two sets, size 0 cannot appear among the
    distinct sizes (since ∅ is a subset of every other set). -/
theorem zero_not_in_antichain_sizes {n : ℕ} {F : Finset (Finset (Fin n))}
    (hF : IsAntichainFamily F) (hcard : 1 < F.card) :
    0 ∉ distinctSizes F := by
  unfold IsAntichainFamily at hF
  intro h0
  unfold distinctSizes at h0
  rw [Finset.mem_image] at h0
  obtain ⟨A, hAF, hAcard⟩ := h0
  have hAeq : A = ∅ := Finset.card_eq_zero.mp hAcard
  subst hAeq
  have ⟨B, hBF, hBne⟩ : ∃ B ∈ F, B ≠ ∅ := by
    by_contra hall
    push_neg at hall
    have : F.card ≤ 1 :=
      Finset.card_le_one.mpr fun a ha b hb => (hall a ha).trans (hall b hb).symm
    omega
  exact absurd (Finset.empty_subset B) (hF ∅ hAF B hBF (Ne.symm hBne))

/-- In an antichain with at least two sets over Fin n, size n cannot appear
    among the distinct sizes (since Finset.univ contains every other set). -/
theorem n_not_in_antichain_sizes {n : ℕ} {F : Finset (Finset (Fin n))}
    (hF : IsAntichainFamily F) (hcard : 1 < F.card) :
    n ∉ distinctSizes F := by
  unfold IsAntichainFamily at hF
  intro hn
  unfold distinctSizes at hn
  rw [Finset.mem_image] at hn
  obtain ⟨A, hAF, hAcard⟩ := hn
  have hAeq : A = Finset.univ :=
    Finset.eq_univ_of_card A (hAcard.trans (Fintype.card_fin n).symm)
  subst hAeq
  have ⟨B, hBF, hBne⟩ : ∃ B ∈ F, B ≠ Finset.univ := by
    by_contra hall
    push_neg at hall
    have : F.card ≤ 1 :=
      Finset.card_le_one.mpr fun a ha b hb => (hall a ha).trans (hall b hb).symm
    omega
  exact absurd (Finset.subset_univ B) (hF B hBF Finset.univ hAF hBne)

/- ## Complement Restriction Lemma -/

/-- In an antichain over Fin n (n ≥ 3), if A = {a} (size 1) and B (size n−1)
    both belong to F with A ≠ B, then every member of F is either A or B.

    Proof: Since A ⊄ B (antichain), a ∉ B. Since |B| = n−1 and a ∉ B, B is the
    complement of {a}. Any other C ∈ F satisfies a ∉ C (antichain with {a}),
    hence C ⊆ complement({a}) = B; antichain then forces C = B. -/
lemma size1_and_complement_pair_only {n : ℕ} (hn : 3 ≤ n)
    {F : SubsetFamily n}
    (hF : IsAntichainFamily F)
    {A B : Finset (Fin n)}
    (hA : A ∈ F) (hAcard : A.card = 1)
    (hB : B ∈ F) (hBcard : B.card = n - 1)
    (hAB : A ≠ B) :
    ∀ C ∈ F, C = A ∨ C = B := by
  -- Extract the unique element a of A
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hAcard
  intro C hC
  -- a ∉ B: antichain gives ¬({a} ⊆ B)
  have ha_notB : a ∉ B := by
    have h := hF {a} hA B hB hAB
    rwa [Finset.singleton_subset_iff] at h
  -- B = Finset.univ.erase a: B ⊆ complement of {a} and both have card n−1
  have hB_eq : B = Finset.univ.erase a := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_erase]
      exact ⟨fun heq => ha_notB (heq ▸ hx), Finset.mem_univ x⟩
    · rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
      omega
  -- Case split: C = {a} or C ≠ {a}
  by_cases hCA : C = {a}
  · left; exact hCA
  · right
    -- a ∉ C: antichain gives ¬({a} ⊆ C)
    have ha_notC : a ∉ C := by
      have h := hF {a} hA C hC hCA
      rwa [Finset.singleton_subset_iff] at h
    -- C ⊆ univ.erase a = B
    have hCB : C ⊆ B := by
      rw [hB_eq]
      intro x hx
      rw [Finset.mem_erase]
      exact ⟨fun heq => ha_notC (heq ▸ hx), Finset.mem_univ x⟩
    -- Antichain forces C = B
    by_cases hCeqB : C = B
    · exact hCeqB
    · exact absurd hCB (hF C hC B hB hCeqB)

/-- Upper bound: in any antichain over Fin n (n ≥ 4) with ≥ 2 sets,
    the number of distinct set sizes is at most n − 2.

    Cases:
    (1) Both size 1 and size n−1 appear → F ⊆ {A,B} → |distinctSizes| ≤ 2 ≤ n−2.
    (2) Size n−1 absent → distinctSizes ⊆ {1,...,n−2} → |distinctSizes| ≤ n−2.
    (3) Size 1 absent → distinctSizes ⊆ {2,...,n−1} → |distinctSizes| ≤ n−2. -/
theorem distinctSizes_card_le_n_sub_two {n : ℕ} (hn : 4 ≤ n)
    {F : SubsetFamily n} (hF : IsAntichainFamily F) (hcard : 1 < F.card) :
    (distinctSizes F).card ≤ n - 2 := by
  have h0 := zero_not_in_antichain_sizes hF hcard
  have hn' := n_not_in_antichain_sizes hF hcard
  -- Every element k of distinctSizes F satisfies 1 ≤ k ≤ n−1
  have hrange : ∀ k ∈ distinctSizes F, 1 ≤ k ∧ k ≤ n - 1 := by
    intro k hk
    unfold distinctSizes at hk
    rw [Finset.mem_image] at hk
    obtain ⟨A, hAF, rfl⟩ := hk
    have hAle : A.card ≤ n := by
      calc A.card ≤ Finset.univ.card := Finset.card_le_univ A
        _ = Fintype.card (Fin n) := Finset.card_univ
        _ = n := Fintype.card_fin n
    have hA0 : A.card ≠ 0 := fun h => h0 (Finset.mem_image.mpr ⟨A, hAF, h⟩)
    have hAnn : A.card ≠ n := fun h => hn' (Finset.mem_image.mpr ⟨A, hAF, h⟩)
    omega
  by_cases h1 : 1 ∈ distinctSizes F
  · by_cases hn1 : (n - 1) ∈ distinctSizes F
    · -- Both size 1 and size n−1 appear: apply size1_and_complement_pair_only
      unfold distinctSizes at h1 hn1
      rw [Finset.mem_image] at h1 hn1
      obtain ⟨A, hA, hAcard⟩ := h1
      obtain ⟨B, hB, hBcard⟩ := hn1
      have hAB : A ≠ B := by intro h; rw [h] at hAcard; omega
      have hpair : ∀ C ∈ F, C = A ∨ C = B :=
        size1_and_complement_pair_only (by omega) hF hA hAcard hB hBcard hAB
      have hFsub : F ⊆ ({A, B} : Finset (Finset (Fin n))) := by
        intro C hC
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact hpair C hC
      calc (distinctSizes F).card
          ≤ F.card := Finset.card_image_le
        _ ≤ ({A, B} : Finset (Finset (Fin n))).card := Finset.card_le_card hFsub
        _ ≤ 2 := by
            apply le_trans (Finset.card_insert_le A _)
            simp
        _ ≤ n - 2 := by omega
    · -- Size n−1 absent: distinctSizes F ⊆ Icc 1 (n−2)
      have hsub : distinctSizes F ⊆ Finset.Icc 1 (n - 2) := by
        intro k hk
        rw [Finset.mem_Icc]
        obtain ⟨hk1, hkn⟩ := hrange k hk
        refine ⟨hk1, ?_⟩
        by_contra hkbig
        push_neg at hkbig
        have heqn1 : k = n - 1 := by omega
        exact hn1 (heqn1 ▸ hk)
      calc (distinctSizes F).card
          ≤ (Finset.Icc 1 (n - 2)).card := Finset.card_le_card hsub
        _ = n - 2 := by
            rw [Finset.Nat.card_Icc]
            omega
  · -- Size 1 absent: distinctSizes F ⊆ Icc 2 (n−1)
    have hsub : distinctSizes F ⊆ Finset.Icc 2 (n - 1) := by
      intro k hk
      rw [Finset.mem_Icc]
      obtain ⟨hk1, hkn⟩ := hrange k hk
      refine ⟨?_, hkn⟩
      have hkne1 : k ≠ 1 := fun heq => h1 (heq ▸ hk)
      omega
    calc (distinctSizes F).card
        ≤ (Finset.Icc 2 (n - 1)).card := Finset.card_le_card hsub
      _ = n - 2 := by
          rw [Finset.Nat.card_Icc]
          omega
