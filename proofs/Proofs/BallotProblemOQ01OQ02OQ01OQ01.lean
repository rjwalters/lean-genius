/-
  Uniform Fiber Counting: A Mathlib Contribution Candidate

  Open Question (ballot-problem-oq-01-oq-02-oq-01-oq-01):
  Could the abstract `ncard_biUnion_eq_of_uniform` lemma (proved in
  BallotProblemOQ01OQ02OQ01.lean as a helper for the multi-candidate ballot theorem)
  be contributed to Mathlib?

  ## Answer: Yes — in at least three forms

  **Form 1 (Finset, cardinal)**: `Finset.card_biUnion_of_uniform`
    If `f : ι → Finset α` is a family of pairwise-disjoint Finsets indexed by `s : Finset ι`,
    and every member has cardinality `k`, then the biUnion has cardinality `k * s.card`.
    Proof: Finset.card_biUnion + Finset.sum_const. Two rewrites.

  **Form 2 (Finset, PairwiseDisjoint variant)**: `Finset.card_biUnion_of_pairwiseDisjoint_uniform`
    Same as Form 1 with disjointness expressed via `Set.PairwiseDisjoint` (Mathlib's
    canonical API for indexed families).

  **Form 3 (Set, ncard)**: `Set.ncard_biUnion_of_uniform`
    The Set analogue using `Set.ncard` and `Set.PairwiseDisjoint`. Uses `Set.ncard_biUnion`
    to reduce to a Finset sum, then collapses via `Finset.sum_const`.

  **Form 4 (surjection corollary)**: `ncard_surjOn_mapsTo_uniform_fiber`
    If `f : α → β` maps `s` onto `t` (both ways: MapsTo + SurjOn), and every fiber
    `f⁻¹{y} ∩ s` has ncard `k`, then `s.ncard = k * t.ncard`.
    Note: Both MapsTo and SurjOn are needed — MapsTo ensures elements of s map INTO t
    (so s is partitioned by fibers over t); SurjOn ensures every y ∈ t is hit.

  ## Why MapsTo is Needed

  `SurjOn f s t` only says `t ⊆ f '' s`; elements of `s` can map OUTSIDE `t`.
  Without `MapsTo f s t`, the equality `s = ⋃ y ∈ t, f⁻¹{y} ∩ s` fails, and
  `s.ncard` can exceed `k * t.ncard` by the count of "escaped" elements.
  In the ballot application, `f = project (leader m)` maps sequences injectively into
  the target, so both MapsTo and SurjOn hold.

  ## Mathlib Placement

  Forms 1-2 would fit in `Mathlib.Data.Finset.Card` after `Finset.card_biUnion`.
  Form 3 would fit in `Mathlib.Data.Set.Card` after `Set.ncard_biUnion`.
  Form 4 would fit in `Mathlib.Data.Set.Function` or as a corollary in Set.Card.

  ## Parent

  Proofs.BallotProblemOQ01OQ02OQ01 proved `ncard_biUnion_eq_of_uniform` as a helper.
  This file is self-contained: it does NOT import the parent.
-/

import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Function
import Mathlib.Tactic

namespace UniformFiberCounting

open Set Finset BigOperators

-- ============================================================
-- PART I: Finset Versions (Mathlib.Data.Finset.Card)
-- ============================================================

/-- **Uniform Fiber Counting (Finset)**: If a family of pairwise-disjoint finite
    sets all have the same cardinality `k`, their biUnion has cardinality `k * s.card`.

    This is the Finset analogue of `Set.ncard_biUnion_of_uniform` and would slot
    naturally into Mathlib alongside `Finset.card_biUnion`. -/
theorem Finset.card_biUnion_of_uniform {α ι : Type*} (s : Finset ι) (f : ι → Finset α)
    (hdisj : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → Disjoint (f x) (f y))
    (k : ℕ) (hk : ∀ i ∈ s, (f i).card = k) :
    (s.biUnion f).card = k * s.card := by
  rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hk,
      Finset.sum_const, smul_eq_mul, mul_comm]

/-- **Uniform Fiber Counting via PairwiseDisjoint**: Same result with disjointness
    expressed via `Set.PairwiseDisjoint` — Mathlib's canonical API for indexed families. -/
theorem Finset.card_biUnion_of_pairwiseDisjoint_uniform {α ι : Type*}
    (s : Finset ι) (f : ι → Finset α)
    (hdisj : (s : Set ι).PairwiseDisjoint f)
    (k : ℕ) (hk : ∀ i ∈ s, (f i).card = k) :
    (s.biUnion f).card = k * s.card :=
  Finset.card_biUnion_of_uniform s f
    (fun x hx y hy hne => hdisj (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hne)
    k hk

-- ============================================================
-- PART II: Set Version (Mathlib.Data.Set.Card)
-- ============================================================

/-- **Uniform Fiber Counting (Set/ncard)**: If a family of pairwise-disjoint finite
    sets indexed by a finite `S` all have ncard `k`, their indexed union has ncard
    `k * S.ncard`.

    Uses `Set.PairwiseDisjoint` throughout. Fits in `Mathlib.Data.Set.Card`
    alongside `Set.ncard_biUnion`. -/
theorem Set.ncard_biUnion_of_uniform {α ι : Type*} {S : Set ι} {f : ι → Set α}
    (hS : S.Finite) (hfin : ∀ i ∈ S, (f i).Finite)
    (hdisj : S.PairwiseDisjoint f)
    (k : ℕ) (hk : ∀ i ∈ S, (f i).ncard = k) :
    (⋃ i ∈ S, f i).ncard = k * S.ncard := by
  rw [Set.ncard_biUnion hS hdisj hfin]
  have hmem : ∀ i ∈ hS.toFinset, (f i).ncard = k :=
    fun i hi => hk i (hS.mem_toFinset.mp hi)
  rw [Finset.sum_congr rfl hmem, Finset.sum_const, smul_eq_mul,
      mul_comm, hS.toFinset_card]

-- ============================================================
-- PART III: Surjection Corollary (needs MapsTo + SurjOn)
-- ============================================================

/-- **Uniform Fiber Partition**: If `f : α → β` maps `s` INTO `t` (`MapsTo`) and
    ONTO `t` (`SurjOn`), with every fiber `f⁻¹{y} ∩ s` having ncard `k`,
    then `s.ncard = k * t.ncard`.

    The `MapsTo` hypothesis is essential: it ensures `s` is exactly the disjoint
    union of fibers `f⁻¹{y} ∩ s` for `y ∈ t`. Without it, elements of `s` may map
    outside `t`, making `s.ncard > k * t.ncard`. -/
theorem ncard_surjOn_mapsTo_uniform_fiber {α β : Type*} {s : Set α} {t : Set β}
    {f : α → β} (hmaps : Set.MapsTo f s t) (hsurj : Set.SurjOn f s t)
    (ht : t.Finite) (hs : s.Finite)
    (k : ℕ) (hk : ∀ y ∈ t, (f ⁻¹' {y} ∩ s).ncard = k) :
    s.ncard = k * t.ncard := by
  -- Decompose s as disjoint union of fibers over t
  have hdecomp : s = ⋃ y ∈ t, f ⁻¹' {y} ∩ s := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      exact ⟨f x, hmaps hx, rfl, hx⟩
    · rintro ⟨_, _, _, hx⟩
      exact hx
  have hdisj : t.PairwiseDisjoint (fun y => f ⁻¹' {y} ∩ s) := by
    intro y₁ _ y₂ _ hne
    simp only [Set.disjoint_left, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    intro a h1 h2
    exact hne (h1.1.symm.trans h2.1)
  have hfin : ∀ y ∈ t, (f ⁻¹' {y} ∩ s).Finite :=
    fun y _ => hs.subset Set.inter_subset_right
  rw [hdecomp]
  exact Set.ncard_biUnion_of_uniform ht hfin hdisj k hk

-- ============================================================
-- PART IV: Probability Ratio Corollary
-- ============================================================

/-- **Ratio Preservation for Uniform Fiber Maps**: For any `P ⊆ β`,
    `ncard(f⁻¹P ∩ s) * t.ncard = ncard(P ∩ t) * s.ncard`.

    This is the combinatorial core of the ballot problem's probability transfer:
    equal fiber sizes imply that the probability of an event is the same whether
    measured in the source or the target space.

    Proof: apply `ncard_surjOn_mapsTo_uniform_fiber` twice — once to `f : s → t`
    and once to `f : f⁻¹P ∩ s → P ∩ t`. -/
theorem ncard_ratio_preserved_of_uniform_fiber {α β : Type*} {s : Set α} {t : Set β}
    {f : α → β} (hmaps : Set.MapsTo f s t) (hsurj : Set.SurjOn f s t)
    (ht : t.Finite) (hs : s.Finite)
    {k : ℕ} (hk : ∀ y ∈ t, (f ⁻¹' {y} ∩ s).ncard = k)
    (P : Set β) :
    (f ⁻¹' P ∩ s).ncard * t.ncard = (P ∩ t).ncard * s.ncard := by
  have hs_eq : s.ncard = k * t.ncard :=
    ncard_surjOn_mapsTo_uniform_fiber hmaps hsurj ht hs k hk
  -- The restriction f : f⁻¹P ∩ s → P ∩ t also has uniform fibers
  have hmaps_P : Set.MapsTo f (f ⁻¹' P ∩ s) (P ∩ t) := by
    intro x ⟨hxP, hxs⟩
    exact ⟨hxP, hmaps hxs⟩
  have hsurj_P : Set.SurjOn f (f ⁻¹' P ∩ s) (P ∩ t) := by
    intro y ⟨hyP, hyt⟩
    obtain ⟨x, hxs, hfx⟩ := hsurj hyt
    exact ⟨x, ⟨show f x ∈ P by rw [hfx]; exact hyP, hxs⟩, hfx⟩
  have hs_P : (f ⁻¹' P ∩ s).Finite := hs.subset Set.inter_subset_right
  have ht_P : (P ∩ t).Finite := ht.subset Set.inter_subset_right
  -- Fiber of (f : f⁻¹P ∩ s → P ∩ t) over y is the same as fiber of (f : s → t) over y
  have hk_P : ∀ y ∈ P ∩ t, (f ⁻¹' {y} ∩ (f ⁻¹' P ∩ s)).ncard = k := by
    intro y ⟨hyP, hyt⟩
    have heq : f ⁻¹' {y} ∩ (f ⁻¹' P ∩ s) = f ⁻¹' {y} ∩ s := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hfy, _, hxs⟩; exact ⟨hfy, hxs⟩
      · rintro ⟨hfy, hxs⟩; exact ⟨hfy, show f x ∈ P by rw [hfy]; exact hyP, hxs⟩
    rw [heq]; exact hk y hyt
  have hfibP_eq : (f ⁻¹' P ∩ s).ncard = k * (P ∩ t).ncard :=
    ncard_surjOn_mapsTo_uniform_fiber hmaps_P hsurj_P ht_P hs_P k hk_P
  rw [hfibP_eq, hs_eq]; ring

-- ============================================================
-- PART V: Computational Examples
-- ============================================================

-- 3 disjoint pairs: biUnion has size 6 = 2 × 3
example : (({0, 1, 2} : Finset ℕ).biUnion (fun i => ({2*i, 2*i+1} : Finset ℕ))).card =
    2 * ({0, 1, 2} : Finset ℕ).card := by
  apply Finset.card_biUnion_of_uniform
  · decide
  · intro i hi; fin_cases hi <;> decide

-- 4 disjoint triples: biUnion has size 12 = 3 × 4
example : (({0, 1, 2, 3} : Finset ℕ).biUnion (fun i => ({3*i, 3*i+1, 3*i+2} : Finset ℕ))).card =
    3 * ({0, 1, 2, 3} : Finset ℕ).card := by
  apply Finset.card_biUnion_of_uniform
  · decide
  · intro i hi; fin_cases hi <;> decide

end UniformFiberCounting
