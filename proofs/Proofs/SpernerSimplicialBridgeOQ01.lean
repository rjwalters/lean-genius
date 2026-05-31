/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Proofs.SpernerSimplicialBridge

/-!
# Sperner's Lemma for Mixed-Dimension Simplicial Complexes (OQ-01)

The parent `Proofs.SpernerSimplicialBridge` proves Sperner's lemma for
*pure* pseudomanifold simplicial complexes — every top simplex has the
same dimension `d + 1`. This companion file lifts the API to *mixed*
(stratified) simplicial complexes, where top simplices may have
different dimensions.

The key structural observation is that *door dimensions are graded*:
a codimension-1 face of a `(d+1)`-simplex has cardinality `d`, and
faces in different dimensions cannot be doors of each other. So the
pseudomanifold condition decomposes stratum by stratum, and Sperner's
lemma applies independently per stratum.

## Main definitions

* `Sperner.SimplicialComplex.topCellsOfDim K d`: the dimension-`d`
  stratum of a complex `K` (the cells with exactly `d + 1` vertices).
* `Sperner.SimplicialComplex.MixedPseudomanifold K`: stratum-wise
  pseudomanifold predicate — for every dimension `d` and every
  `d`-element face `f`, at most 2 cells of dimension `d` contain `f`.

## Main results

* `Sperner.SimplicialComplex.topCellsOfDim_eq_of_pure`: when all cells
  in `K` have the same dimension `d`, the stratum at `d` is `K`.
* `Sperner.SimplicialComplex.topCellsOfDim_eq_empty_of_pure`: when all
  cells in `K` have dimension `d`, strata at other dimensions are
  empty.
* `Sperner.SimplicialComplex.MixedPseudomanifold.of_pure`: a pure
  pseudomanifold lifts to a mixed pseudomanifold.

## References

* [M. De Longueville, *A Course in Topological Combinatorics*]

## Tags

Sperner, simplicial complex, mixed pseudomanifold, stratified
-/

namespace Sperner.SimplicialComplex

open Finset

/-! ## Stratification of a finite simplicial complex by dimension -/

variable {E : Type} [DecidableEq E]

/-- The dimension-`d` stratum of a finite set of simplices `K`:
the cells with exactly `d + 1` vertices. -/
def topCellsOfDim (K : Finset (Finset E)) (d : Nat) : Finset (Finset E) :=
  K.filter (fun s => s.card = d + 1)

/-- A complex is a *mixed pseudomanifold* if each dimension's stratum
is a pseudomanifold: every `d`-element face `f` is contained in at
most 2 cells of dimension `d`. -/
def MixedPseudomanifold (K : Finset (Finset E)) : Prop :=
  ∀ d : Nat, ∀ f : Finset E, f.card = d →
    ((topCellsOfDim K d).filter (fun s => f ⊆ s)).card ≤ 2

/-! ## Pure → Mixed coercion lemmas -/

/-- When every cell in `K` has cardinality `d + 1`, the dimension-`d`
stratum is `K` itself. -/
omit [DecidableEq E] in
theorem topCellsOfDim_eq_of_pure {d : Nat}
    (K : Finset (Finset E))
    (hcard : ∀ s ∈ K, s.card = d + 1) :
    topCellsOfDim K d = K := by
  unfold topCellsOfDim
  exact Finset.filter_eq_self.mpr hcard

/-- When every cell in `K` has cardinality `d + 1`, strata at other
dimensions `d' ≠ d` are empty. -/
omit [DecidableEq E] in
theorem topCellsOfDim_eq_empty_of_pure {d d' : Nat}
    (K : Finset (Finset E))
    (hcard : ∀ s ∈ K, s.card = d + 1) (hne : d' ≠ d) :
    topCellsOfDim K d' = ∅ := by
  unfold topCellsOfDim
  rw [Finset.filter_eq_empty_iff]
  intro s hs hbad
  have hs_card : s.card = d + 1 := hcard s hs
  omega

/-- A pure pseudomanifold lifts to a mixed pseudomanifold: if all
top cells have the same dimension `d` and the pseudomanifold property
holds at dimension `d`, then the mixed predicate holds at every
dimension (vacuously at dimensions other than `d`). -/
theorem MixedPseudomanifold.of_pure {d : Nat}
    (K : Finset (Finset E))
    (hcard : ∀ s ∈ K, s.card = d + 1)
    (hpseudo : ∀ f : Finset E, f.card = d →
      (K.filter (fun s => f ⊆ s)).card ≤ 2) :
    MixedPseudomanifold K := by
  intro d' f hfcard
  by_cases hd : d' = d
  · subst hd
    rw [topCellsOfDim_eq_of_pure K hcard]
    exact hpseudo f hfcard
  · rw [topCellsOfDim_eq_empty_of_pure K hcard hd, Finset.filter_empty]
    exact Nat.zero_le _

/-! ## API ergonomics: stratum membership, empty complex, and monotonicity -/

/-- `topCellsOfDim K d` is a sub-`Finset` of `K`. -/
omit [DecidableEq E] in
theorem topCellsOfDim_subset (K : Finset (Finset E)) (d : Nat) :
    topCellsOfDim K d ⊆ K := by
  unfold topCellsOfDim
  exact Finset.filter_subset _ _

/-- Clean iff form of stratum membership: `s` lies in the dimension-`d`
stratum iff `s ∈ K` and `s` has exactly `d + 1` vertices. -/
omit [DecidableEq E] in
theorem mem_topCellsOfDim_iff {d : Nat} {K : Finset (Finset E)} {s : Finset E} :
    s ∈ topCellsOfDim K d ↔ s ∈ K ∧ s.card = d + 1 := by
  unfold topCellsOfDim
  exact Finset.mem_filter

/-- Every dimension stratum of the empty complex is empty. -/
omit [DecidableEq E] in
theorem topCellsOfDim_empty (d : Nat) :
    topCellsOfDim (∅ : Finset (Finset E)) d = ∅ := by
  unfold topCellsOfDim
  exact Finset.filter_empty _

/-- The empty complex is (vacuously) a mixed pseudomanifold. -/
omit [DecidableEq E] in
theorem MixedPseudomanifold.empty :
    MixedPseudomanifold (∅ : Finset (Finset E)) := by
  intro d f _
  rw [topCellsOfDim_empty, Finset.filter_empty]
  exact Nat.zero_le _

/-- **Mixed pseudomanifold is preserved under sub-complexes.** Dropping
cells from a mixed pseudomanifold can only decrease the count of
dimension-`d` cells containing any given face, so the `≤ 2` upper bound
carries through. Useful when restricting attention to a sub-complex. -/
omit [DecidableEq E] in
theorem MixedPseudomanifold.mono {K K' : Finset (Finset E)}
    (hsub : K' ⊆ K) (h : MixedPseudomanifold K) :
    MixedPseudomanifold K' := by
  intro d f hf
  have h_stratum_sub : topCellsOfDim K' d ⊆ topCellsOfDim K d := by
    intro s hs
    rw [mem_topCellsOfDim_iff] at hs ⊢
    exact ⟨hsub hs.1, hs.2⟩
  have h_filter_sub :
      (topCellsOfDim K' d).filter (fun s => f ⊆ s)
        ⊆ (topCellsOfDim K d).filter (fun s => f ⊆ s) :=
    Finset.filter_subset_filter _ h_stratum_sub
  exact le_trans (Finset.card_le_card h_filter_sub) (h d f hf)

/-! ## Per-stratum Sperner via the parent's `exists_panchromatic`

The Sperner-mixed theorem decomposes stratum by stratum: fixing a
dimension `d`, the dimension-`d` stratum `topCellsOfDim K d` is a
pure pseudomanifold (by `MixedPseudomanifold`), so the parent's
`exists_panchromatic` applies directly. We package the per-stratum
hypotheses as three helpers and one boundary-door count abstraction.

The parent's `exists_panchromatic` requires `[LinearOrder E]`
(its `vertexEnum` uses `Finset.sort (· ≤ ·)`), so the section adds
that instance to the variable context. -/

section MixedSperner

variable [LinearOrder E]

/-- Every cell in the dimension-`d` stratum has cardinality `d + 1`. -/
omit [DecidableEq E] [LinearOrder E] in
theorem card_of_mem_topCellsOfDim {d : Nat}
    {K : Finset (Finset E)} {s : Finset E}
    (hs : s ∈ topCellsOfDim K d) : s.card = d + 1 :=
  (Finset.mem_filter.mp hs).2

/-- Per-dimension specialisation of the mixed-pseudomanifold predicate. -/
omit [LinearOrder E] in
theorem hpseudo_of_mixed {d : Nat}
    {K : Finset (Finset E)} (hmixed : MixedPseudomanifold K) :
    ∀ f : Finset E, f.card = d →
      ((topCellsOfDim K d).filter (fun s => f ⊆ s)).card ≤ 2 :=
  fun f hf => hmixed d f hf

/-- The boundary-door count at dimension `d` for a coloring `c`.

A pair `(s, k)` with `s ∈ topCellsOfDim K d` and `k : Fin (d+1)` is a
boundary door iff `Sperner.IsDoor` holds (the lower colours
`{0, …, d-1}` are all present on `s \ {vertex k}`) AND
`adjFn (topCellsOfDim K d) hcard s k = none` (the face `s \ {vertex k}`
lies in no other cell of dimension `d`). The count of such pairs is
the input to `exists_panchromatic`'s `Odd …` hypothesis. -/
noncomputable def boundaryDoorCount {d : Nat}
    (K : Finset (Finset E)) (c : E → Fin (d + 1)) : ℕ :=
  (Finset.univ.filter
    (fun p : { s : Finset E // s ∈ topCellsOfDim K d } × Fin (d + 1) =>
      Sperner.IsDoor (fun (σ : { s // s ∈ topCellsOfDim K d }) =>
        vertexEnum σ.1 (card_of_mem_topCellsOfDim σ.2))
        c p.1 p.2 ∧
      adjFn (topCellsOfDim K d)
        (fun _ hs => card_of_mem_topCellsOfDim hs) p.1 p.2 = none)).card

/-- **Sperner's lemma for mixed-dimension simplicial complexes
(OQ-01, per-stratum version).**

For each dimension `d` such that the boundary-door count at dimension
`d` is odd, the dimension-`d` stratum of a mixed pseudomanifold `K`
contains a panchromatic top cell.

The proof is a direct application of the parent file's
`exists_panchromatic` to `topCells := topCellsOfDim K d`: the
`hcard` hypothesis is `card_of_mem_topCellsOfDim` and the per-stratum
`hpseudo` hypothesis is `hpseudo_of_mixed`. `boundaryDoorCount`
unfolds to the parent's `hbdry` argument by construction. -/
theorem sperner_mixed_panchromatic_at_dim {d : Nat}
    (K : Finset (Finset E)) (hmixed : MixedPseudomanifold K)
    (c : E → Fin (d + 1))
    (hbdry : Odd (boundaryDoorCount (d := d) K c)) :
    ∃ s : { s : Finset E // s ∈ topCellsOfDim K d },
      Sperner.IsPanchromatic
        (fun (σ : { s // s ∈ topCellsOfDim K d }) =>
          vertexEnum σ.1 (card_of_mem_topCellsOfDim σ.2)) c s :=
  exists_panchromatic (topCellsOfDim K d)
    (fun _ hs => card_of_mem_topCellsOfDim hs)
    (hpseudo_of_mixed hmixed) c hbdry

/-- **Mixed-dimension Sperner aggregator (alias).** Same content as
`sperner_mixed_panchromatic_at_dim` with `d` re-exported as an
implicit argument. Ergonomic alias for callers that don't need
`_at_dim` in the name. -/
theorem sperner_mixed_panchromatic
    (K : Finset (Finset E)) (hmixed : MixedPseudomanifold K)
    {d : Nat} (c : E → Fin (d + 1))
    (hbdry : Odd (boundaryDoorCount (d := d) K c)) :
    ∃ s : { s : Finset E // s ∈ topCellsOfDim K d },
      Sperner.IsPanchromatic
        (fun (σ : { s // s ∈ topCellsOfDim K d }) =>
          vertexEnum σ.1 (card_of_mem_topCellsOfDim σ.2)) c s :=
  sperner_mixed_panchromatic_at_dim K hmixed c hbdry

/-- **Mixed-dimension Sperner aggregator (global existential).**
If the mixed pseudomanifold `K` admits any dimension `d` and coloring
`c` with `Odd (boundaryDoorCount d K c)`, then there exists a
panchromatic top cell at that dimension. -/
theorem sperner_mixed_panchromatic_global
    (K : Finset (Finset E)) (hmixed : MixedPseudomanifold K)
    (hd : ∃ d (c : E → Fin (d + 1)), Odd (boundaryDoorCount (d := d) K c)) :
    ∃ d (c : E → Fin (d + 1)) (s : { s : Finset E // s ∈ topCellsOfDim K d }),
      Sperner.IsPanchromatic
        (fun (σ : { s // s ∈ topCellsOfDim K d }) =>
          vertexEnum σ.1 (card_of_mem_topCellsOfDim σ.2)) c s := by
  obtain ⟨d, c, hbdry⟩ := hd
  exact ⟨d, c, sperner_mixed_panchromatic_at_dim K hmixed c hbdry⟩

end MixedSperner

end Sperner.SimplicialComplex
