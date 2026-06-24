import Mathlib
import Proofs.CompactnessFiniteSubcoverOq01Oq02

/-
# The cluster-point form of compactness, from the finite-intersection dual

## Open Question (compactness-finite-subcover-oq-01-oq-02-oq-02)

> Derive the cluster-point form of compactness from the FIP dual: every net (or
> filter) on a compact set has a cluster point, by applying the finite
> intersection property to the closures of the net's tails, again without citing
> `Mathlib`'s filter-based compactness lemmas.

## What this proves

The parent entry **compactness-finite-subcover-oq-01-oq-02** recorded the
finite-intersection dual of compactness and rebuilt Cantor's intersection
theorem from it.  Its declared open question asks for the *other* classical
consequence of the FIP characterisation: the **cluster-point (Bolzano–Weierstrass
for filters)** form of compactness.

We prove

  `exists_clusterPt_of_isCompact` :
    if `s` is compact and `F` is a filter with `F.NeBot` and `F ≤ 𝓟 s`,
    then `F` has a cluster point inside `s`.

The proof is exactly the textbook FIP argument.  A filter is a directed family of
"tails"; we feed the **closures of all of `F`'s sets** to the parent's FIP dual
`compact_inter_iInter_nonempty`.  A finite subfamily `{closure A : A ∈ v}` is
pinned below by the single set `s ∩ ⋂_{A ∈ v} A`, which lies in `F` (a filter is
closed under finite intersections, and `s ∈ F` because `F ≤ 𝓟 s`) and is therefore
nonempty (`F.NeBot`); every point of it lies in every `closure A`.  So the finite
intersection property holds, the FIP dual returns a point `x ∈ s` lying in every
`closure A` (`A ∈ F`), and "`x ∈ closure A` for every `A ∈ F`" is precisely the
statement `ClusterPt x F`.

## Why this is not a wrapper

`Mathlib`'s `IsCompact s` is *defined* as the cluster-point property
(`∀ F, F.NeBot → F ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x F`), so the result is one line
from the definition — `exact hs hF`.  That definitional shortcut, and every
filter-based compactness lemma resting on it, is **deliberately avoided**.
Instead the cluster-point form is re-derived through the closed-set / finite
intersection characterisation `compact_inter_iInter_nonempty` (the parent's FIP
dual, itself the complement of the finite-subcover headline), reproducing the
genuine equivalence between the two faces of compactness.  As corollaries we
record the `CompactSpace` form and the **sequential** statement: every sequence
eventually inside a compact set clusters (`MapClusterPt … atTop`), with a concrete
`ℝ` instance for a sequence in `[0,1]`.
-/

namespace CompactnessFiniteSubcoverOq01Oq02Oq02

open Set Filter Topology

variable {X : Type*} [TopologicalSpace X]

/-! ## The cluster-point form, via the finite-intersection dual -/

/-- **Cluster-point form of compactness.**  If `s` is compact and `F` is a
nontrivial filter refining the principal filter of `s` (i.e. `s ∈ F`), then `F`
has a cluster point in `s`.

Proved from the parent's finite-intersection dual `compact_inter_iInter_nonempty`
applied to the family of **closures of the members of `F`** (the generalized
tails), *not* from `Mathlib`'s definitional `IsCompact ⇒ cluster point`. -/
theorem exists_clusterPt_of_isCompact {s : Set X} (hs : IsCompact s)
    (F : Filter X) [F.NeBot] (hF : F ≤ 𝓟 s) :
    ∃ x ∈ s, ClusterPt x F := by
  -- `s` itself belongs to `F`.
  have hsF : s ∈ F := le_principal_iff.mp hF
  -- The closed family fed to the FIP dual: closures of all members of `F`.
  set t : {A : Set X // A ∈ F} → Set X := fun A => closure (A : Set X) with ht
  have htc : ∀ A, IsClosed (t A) := fun _ => isClosed_closure
  -- Finite intersection property: every finite subfamily already meets `s`.
  have hfip : ∀ v : Finset {A : Set X // A ∈ F}, (s ∩ ⋂ A ∈ v, t A).Nonempty := by
    intro v
    -- `W = s ∩ ⋂_{A ∈ v} A` lies in `F`, hence is nonempty since `F.NeBot`.
    have hWmem : (s ∩ ⋂ A ∈ v, (A : Set X)) ∈ F :=
      inter_mem hsF ((biInter_finset_mem v).2 fun A _ => A.2)
    obtain ⟨p, hp⟩ := Filter.nonempty_of_mem hWmem
    -- Each member sits inside its own closure, so `p` lands in `s ∩ ⋂ closures`.
    exact ⟨p, hp.1, Set.mem_iInter₂.2 fun A hAv =>
      subset_closure (Set.mem_iInter₂.1 hp.2 A hAv)⟩
  -- The FIP dual returns a point of `s` lying in every `closure A`, `A ∈ F`.
  obtain ⟨x, hxs, hx⟩ := compact_inter_iInter_nonempty hs t htc hfip
  refine ⟨x, hxs, ?_⟩
  -- `x ∈ closure A` for every `A ∈ F` is exactly `ClusterPt x F`.
  refine clusterPt_iff_frequently'.mpr fun A hA => ?_
  have hxc : x ∈ closure A := by simpa [ht] using mem_iInter.mp hx ⟨A, hA⟩
  exact mem_closure_iff_frequently.mp hxc

/-- **Cluster-point form in a compact space.**  Every nontrivial filter on a
compact space has a cluster point. -/
theorem exists_clusterPt_of_compactSpace [CompactSpace X] (F : Filter X) [F.NeBot] :
    ∃ x, ClusterPt x F := by
  obtain ⟨x, _, hx⟩ :=
    exists_clusterPt_of_isCompact isCompact_univ F (le_principal_iff.mpr univ_mem)
  exact ⟨x, hx⟩

/-! ## The sequential (net) form -/

/-- **Sequential cluster-point form.**  A sequence eventually inside a compact set
`s` clusters at some point of `s`: there is `x ∈ s` with `MapClusterPt x atTop a`,
i.e. every neighbourhood of `x` contains `a n` for infinitely many `n`.

This is the "net" reading of the open question: `atTop` is the directed index
filter, its image `map a atTop` is the filter generated by the **tails** of the
sequence, and the cluster point of that filter is obtained from
`exists_clusterPt_of_isCompact`. -/
theorem exists_mapClusterPt_of_isCompact {s : Set X} (hs : IsCompact s)
    (a : ℕ → X) (ha : ∀ᶠ n in atTop, a n ∈ s) :
    ∃ x ∈ s, MapClusterPt x atTop a := by
  have hmem : s ∈ map a atTop := mem_map.mpr ha
  obtain ⟨x, hxs, hx⟩ :=
    exists_clusterPt_of_isCompact hs (map a atTop) (le_principal_iff.mpr hmem)
  exact ⟨x, hxs, hx⟩

/-- **Sequential cluster-point form in a compact space.**  Every sequence in a
compact space clusters. -/
theorem exists_mapClusterPt_of_compactSpace [CompactSpace X] (a : ℕ → X) :
    ∃ x, MapClusterPt x atTop a := by
  obtain ⟨x, _, hx⟩ :=
    exists_mapClusterPt_of_isCompact isCompact_univ a (Eventually.of_forall fun _ => mem_univ _)
  exact ⟨x, hx⟩

/-! ## A concrete instance over `ℝ` -/

/-- **Concrete instance.**  Any sequence valued in the compact interval `[0,1]`
clusters at a point of `[0,1]`. -/
example (a : ℕ → ℝ) (ha : ∀ n, a n ∈ Set.Icc (0 : ℝ) 1) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, MapClusterPt x atTop a :=
  exists_mapClusterPt_of_isCompact isCompact_Icc a (Eventually.of_forall ha)

end CompactnessFiniteSubcoverOq01Oq02Oq02
