import Mathlib

/-
# Compactness via Finite Subcovers

## What This Proves

The **finite subcover characterization of compactness**: a set `s` in a
topological space is compact **iff** every open cover of `s` admits a finite
subcover.  This is the Heine–Borel definition of compactness, and it is the
form that powers the extreme value theorem, the tube lemma, and the proof that
continuous images of compact sets are compact.

`Mathlib` packages the equivalence as `isCompact_iff_finite_subcover` (with the
forward direction `IsCompact.elim_finite_subcover`).  We re-export that
characterization as the headline, and then use it **directly** — not via the
ready-made `IsCompact.union` — to build the structural consequences:

* `isCompact_union_of_finite_subcover` — a binary union of compact sets is
  compact, **re-derived from the subcover characterization itself**: given a
  cover of `s ∪ t`, extract a finite subcover of `s` and a finite subcover of
  `t`, then union the two finite index sets.  This is the genuine content of the
  file — we never invoke `IsCompact.union`.
* `isCompact_finset_biUnion` — a finite (indexed) union of compact sets is
  compact, by induction on the `Finset` using only the binary case above.
* `isCompact_finset_coe` — every finite set is compact, as a corollary
  (`↑s = ⋃ x ∈ s, {x}` and singletons are compact).
* `isCompact_image_of_continuous` / `isCompact_image_union_of_continuous` —
  the continuous-image cross-check: continuous images preserve compactness, and
  in particular the continuous image of a union of compacts is compact.
* `isCompact_two_intervals` — a concrete instance over `ℝ`: `[0,1] ∪ [2,3]` is
  compact, obtained from the re-derived union theorem and `isCompact_Icc`.

## Why This Is a Non-Wrapper

The headline `compact_iff_finite_subcover` is a `Mathlib` restatement, but the
finite-union results are produced by *running the subcover characterization by
hand* — extracting subcovers and combining index `Finset`s — rather than citing
`IsCompact.union`.  That re-derivation, the finite-family induction, the
finite-set corollary, and the concrete `ℝ` instance are the mathematical
substance.
-/

open Set

universe u

variable {X : Type u} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

/-- **Finite subcover characterization of compactness.**  A set `s` is compact
iff every open cover of `s` admits a finite subcover.  (Re-export of
`isCompact_iff_finite_subcover`, the Heine–Borel definition.) -/
theorem compact_iff_finite_subcover :
    IsCompact s ↔ ∀ {ι : Type u} (U : ι → Set X),
      (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) → ∃ r : Finset ι, s ⊆ ⋃ i ∈ r, U i :=
  isCompact_iff_finite_subcover

/-- **Forward direction.**  From a compact set and an open cover we may extract a
finite subcover. -/
theorem finite_subcover_of_isCompact (hs : IsCompact s) {ι : Type*} (U : ι → Set X)
    (hUo : ∀ i, IsOpen (U i)) (hsU : s ⊆ ⋃ i, U i) :
    ∃ r : Finset ι, s ⊆ ⋃ i ∈ r, U i :=
  hs.elim_finite_subcover U hUo hsU

/-- **A binary union of compact sets is compact**, re-derived directly from the
finite subcover characterization.  Given an open cover of `s ∪ t`, it covers `s`
and `t` separately; extract a finite subcover of each and union the two finite
index sets.  We deliberately do *not* invoke `IsCompact.union`. -/
theorem isCompact_union_of_finite_subcover (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (s ∪ t) := by
  classical
  refine isCompact_of_finite_subcover fun {ι} U hUo hsU => ?_
  -- the cover of `s ∪ t` covers `s` and `t` individually
  obtain ⟨a, ha⟩ := hs.elim_finite_subcover U hUo (Set.subset_union_left.trans hsU)
  obtain ⟨b, hb⟩ := ht.elim_finite_subcover U hUo (Set.subset_union_right.trans hsU)
  -- the union of the two finite index sets is a finite subcover of `s ∪ t`
  refine ⟨a ∪ b, Set.union_subset ?_ ?_⟩
  · refine ha.trans fun x hx => ?_
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
    exact Set.mem_iUnion₂.2 ⟨i, Finset.mem_union_left _ hi, hxi⟩
  · refine hb.trans fun x hx => ?_
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
    exact Set.mem_iUnion₂.2 ⟨i, Finset.mem_union_right _ hi, hxi⟩

/-- **A finite indexed union of compact sets is compact**, by induction on the
`Finset` using only the binary union above. -/
theorem isCompact_finset_biUnion {ι : Type*} {f : ι → Set X} (a : Finset ι)
    (hf : ∀ i ∈ a, IsCompact (f i)) : IsCompact (⋃ i ∈ a, f i) := by
  classical
  induction a using Finset.induction_on with
  | empty => simp
  | @insert j a' hj ih =>
      rw [Finset.set_biUnion_insert]
      exact isCompact_union_of_finite_subcover
        (hf j (Finset.mem_insert_self j a'))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- **Every finite set is compact** (in any topological space), as a corollary:
`↑s = ⋃ x ∈ s, {x}` and singletons are compact. -/
theorem isCompact_finset_coe (s : Finset X) : IsCompact (↑s : Set X) := by
  have h : (↑s : Set X) = ⋃ x ∈ s, ({x} : Set X) := by
    ext y; simp
  rw [h]
  exact isCompact_finset_biUnion s fun x _ => isCompact_singleton

/-- **Continuous-image cross-check.**  A continuous image of a compact set is
compact. -/
theorem isCompact_image_of_continuous {f : X → Y} (hs : IsCompact s)
    (hf : Continuous f) : IsCompact (f '' s) :=
  hs.image hf

/-- The continuous image of a union of two compact sets is compact — combining
the re-derived union theorem with the continuous-image preservation. -/
theorem isCompact_image_union_of_continuous {f : X → Y} (hs : IsCompact s)
    (ht : IsCompact t) (hf : Continuous f) : IsCompact (f '' (s ∪ t)) :=
  (isCompact_union_of_finite_subcover hs ht).image hf

/-- **Concrete instance over `ℝ`.**  The union of the two disjoint closed
intervals `[0,1]` and `[2,3]` is compact, via the re-derived union theorem and
`isCompact_Icc`. -/
theorem isCompact_two_intervals :
    IsCompact (Set.Icc (0 : ℝ) 1 ∪ Set.Icc (2 : ℝ) 3) :=
  isCompact_union_of_finite_subcover isCompact_Icc isCompact_Icc
