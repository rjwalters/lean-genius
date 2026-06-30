/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Proofs.SpernerSimplicialBridge
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-
# Extending the Sperner bridge to `Geometry.SimplicialComplex`

The parent file `SpernerSimplicialBridge.lean` proves Sperner's lemma for a
finite set `topCells : Finset (Finset E)` of top simplices satisfying a purity
and a pseudomanifold condition (`Sperner.SimplicialComplex.exists_panchromatic`).
Its closing remark poses the open question:

> Does this bridge extend to Mathlib's `Geometry.SimplicialComplex` type by
> extracting `facets` and verifying the pseudomanifold condition? The key
> obstacle is reconciling Mathlib's affine-set encoding with this bridge's
> finset-of-vertices encoding.

This file answers it. The reconciliation turns out to be clean: Mathlib already
stores the faces of a `Geometry.SimplicialComplex 𝕜 E` as `Finset E` (vertex
sets), the very same encoding the bridge consumes. The affine structure
(`AffineIndependent`, convex-hull gluing) is *extra* data layered on top of the
combinatorial vertex sets, not a competing encoding. So the bridge applies
verbatim once we package three structural facts:

1. **Finiteness / facet extraction.** `K.facets : Set (Finset E)` must be
   enumerated by a `Finset (Finset E)`. We supply `exists_facet_superset`: in a
   *finite* complex every face lies below a facet, so the facets genuinely form
   the "top cells" the bridge needs.
2. **Purity.** Every facet has `d + 1` vertices.
3. **Pseudomanifold.** Every codimension-1 face lies in at most two facets.

## Main results

* `Sperner.SimplicialComplex.exists_facet_superset` — every face of a finite
  Mathlib complex is contained in a facet (a genuinely new lemma; Mathlib has
  only `not_facet_iff_subface`).
* `Sperner.SimplicialComplex.facet_affineIndependent` — facets carry the affine
  structure: the vertices of a facet are affinely independent.
* `Sperner.SimplicialComplex.facet_card_le_finrank_succ` /
  `facet_dim_le_ambient` — the affine encoding bounds the combinatorial
  dimension: a facet has at most `finrank 𝕜 E + 1` vertices, so a pure complex of
  combinatorial dimension `d` requires ambient dimension `d ≤ finrank 𝕜 E`.
* `Sperner.SimplicialComplex.exists_panchromatic_facet` — the bridge applied to a
  Mathlib complex: a panchromatic facet exists, and the witness is a genuine
  element of `K.facets`.
* `Sperner.SimplicialComplex.exists_panchromatic_facet_of_finrank` — the same,
  in a finite-dimensional field setting, additionally certifying `d ≤ finrank`.

## References

* [M. De Longueville, *A Course in Topological Combinatorics*]

## Tags

Sperner, simplicial complex, pseudomanifold, bridge, facets, Geometry
-/

namespace Sperner.SimplicialComplex

open Finset

/-! ## Facet extraction for finite Mathlib complexes

These lemmas establish the structural facts the bridge consumes when its input is
a Mathlib `Geometry.SimplicialComplex` rather than a raw `Finset (Finset E)`.
They make precise the sense in which the "affine-set encoding" and the
"finset-of-vertices encoding" agree: a face *is* a `Finset E`, and facets are
distinguished combinatorially as the maximal faces. -/

section MathlibFacets

variable {𝕜 : Type*} {E : Type*}
  [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **Every face of a finite complex lies below a facet.**

Mathlib provides `not_facet_iff_subface` (a non-facet has a strict superface) but
not the existence of a maximal superface. For a finite complex it follows by
picking a face of maximal cardinality among those containing `s`. This certifies
that the `facets` we hand to the bridge actually exhaust the top-dimensional
combinatorial data. -/
theorem exists_facet_superset (K : Geometry.SimplicialComplex 𝕜 E)
    (hfin : K.faces.Finite) {s : Finset E} (hs : s ∈ K.faces) :
    ∃ t ∈ K.facets, s ⊆ t := by
  have hFfin : {t | t ∈ K.faces ∧ s ⊆ t}.Finite := hfin.subset fun t ht => ht.1
  obtain ⟨t, ⟨htf, hst⟩, htmax⟩ := hFfin.exists_maximal ⟨s, hs, subset_rfl⟩
  refine ⟨t, Geometry.SimplicialComplex.mem_facets.mpr ⟨htf, fun u hu htu => ?_⟩, hst⟩
  exact le_antisymm htu (htmax ⟨hu, hst.trans htu⟩ htu)

/-- A facet is in particular a face, so its vertices are affinely independent.
This is the precise statement that the bridge's combinatorial facets carry
Mathlib's affine structure for free. -/
theorem facet_affineIndependent (K : Geometry.SimplicialComplex 𝕜 E)
    {s : Finset E} (hs : s ∈ K.facets) :
    AffineIndependent 𝕜 ((↑) : s → E) :=
  K.indep (K.facets_subset hs)

end MathlibFacets

/-! ## The affine encoding bounds the combinatorial dimension

Over a finite-dimensional space the affine independence of a facet's vertices
caps its cardinality at `finrank 𝕜 E + 1`. This is exactly the obstruction the
open question worries about — reconciling the affine encoding with the
combinatorial one — resolved quantitatively. -/

section Dimension

variable {𝕜 : Type*} {E : Type*}
  [DivisionRing 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]

/-- A facet has at most `finrank 𝕜 E + 1` vertices: its affinely independent
vertex set cannot exceed the ambient affine dimension plus one. -/
theorem facet_card_le_finrank_succ (K : Geometry.SimplicialComplex 𝕜 E)
    {s : Finset E} (hs : s ∈ K.facets) :
    s.card ≤ Module.finrank 𝕜 E + 1 := by
  have hbound := (facet_affineIndependent K hs).card_le_finrank_succ
  rw [Fintype.card_coe] at hbound
  have hle : Module.finrank 𝕜 (vectorSpan 𝕜 (Set.range ((↑) : s → E)))
      ≤ Module.finrank 𝕜 E := Submodule.finrank_le _
  omega

/-- In a pure complex of combinatorial dimension `d` (every facet has `d + 1`
vertices) the ambient space must have dimension at least `d`. -/
theorem facet_dim_le_ambient (K : Geometry.SimplicialComplex 𝕜 E)
    {s : Finset E} (hs : s ∈ K.facets) {d : ℕ} (hcard : s.card = d + 1) :
    d ≤ Module.finrank 𝕜 E := by
  have := facet_card_le_finrank_succ K hs
  omega

end Dimension

/-! ## The bridge applied to a Mathlib complex

Given a `Finset (Finset E)` enumerating the facets of `K`, together with purity,
the pseudomanifold condition, a coloring, and an odd boundary parity, the bridge
delivers a panchromatic top cell — and that cell is a genuine `K.facets` member.
This is the concrete affirmative answer to the open question. -/

section Bridge

variable {𝕜 : Type*} {E : Type}
  [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E] [LinearOrder E] {d : ℕ}

/-- **Sperner's lemma for a Mathlib `Geometry.SimplicialComplex`.**

Let `K : Geometry.SimplicialComplex 𝕜 E` and let `topCells` enumerate the facets
of `K` (`htop`). If `K` is pure of combinatorial dimension `d` (`hpure`),
satisfies the pseudomanifold condition (`hpseudo`), and `c` is a coloring whose
boundary door count is odd (`hbdry`), then some facet of `K` is panchromatic:
the `d + 1` vertices of that facet receive all `d + 1` colours. -/
theorem exists_panchromatic_facet (K : Geometry.SimplicialComplex 𝕜 E)
    (topCells : Finset (Finset E))
    (htop : ∀ s, s ∈ topCells ↔ s ∈ K.facets)
    (hpure : ∀ s ∈ topCells, s.card = d + 1)
    (hpseudo : ∀ f : Finset E, f.card = d →
      (topCells.filter (fun s => f ⊆ s)).card ≤ 2)
    (c : E → Fin (d + 1))
    (hbdry : Odd (Finset.univ.filter
      (fun p : { s : Finset E // s ∈ topCells } × Fin (d + 1) =>
        Sperner.IsDoor (fun (σ : { s // s ∈ topCells }) => vertexEnum σ.1 (hpure σ.1 σ.2))
          c p.1 p.2 ∧
        adjFn topCells hpure p.1 p.2 = none)).card) :
    ∃ σ : { s : Finset E // s ∈ topCells },
      Sperner.IsPanchromatic
        (fun (σ : { s // s ∈ topCells }) => vertexEnum σ.1 (hpure σ.1 σ.2)) c σ ∧
      σ.1 ∈ K.facets := by
  obtain ⟨σ, hσ⟩ := exists_panchromatic topCells hpure hpseudo c hbdry
  exact ⟨σ, hσ, (htop σ.1).mp σ.2⟩

end Bridge

/-! ## Capstone: a panchromatic facet of certified dimension

Specialising to a finite-dimensional field, the panchromatic facet supplied by
the bridge additionally respects the ambient dimension: its combinatorial
dimension `d` satisfies `d ≤ finrank 𝕜 E`. This packages the whole answer to the
open question — facet extraction, the pseudomanifold input, the combinatorial
Sperner conclusion, and the affine-dimension constraint — in one statement. -/

section Capstone

variable {𝕜 : Type*} {E : Type}
  [DivisionRing 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
  [DecidableEq E] [LinearOrder E] {d : ℕ}

/-- The bridge for a finite-dimensional Mathlib complex, certifying both that the
panchromatic witness is a genuine facet and that the combinatorial dimension is
bounded by the ambient affine dimension. -/
theorem exists_panchromatic_facet_of_finrank (K : Geometry.SimplicialComplex 𝕜 E)
    (topCells : Finset (Finset E))
    (htop : ∀ s, s ∈ topCells ↔ s ∈ K.facets)
    (hpure : ∀ s ∈ topCells, s.card = d + 1)
    (hpseudo : ∀ f : Finset E, f.card = d →
      (topCells.filter (fun s => f ⊆ s)).card ≤ 2)
    (c : E → Fin (d + 1))
    (hbdry : Odd (Finset.univ.filter
      (fun p : { s : Finset E // s ∈ topCells } × Fin (d + 1) =>
        Sperner.IsDoor (fun (σ : { s // s ∈ topCells }) => vertexEnum σ.1 (hpure σ.1 σ.2))
          c p.1 p.2 ∧
        adjFn topCells hpure p.1 p.2 = none)).card) :
    ∃ σ : { s : Finset E // s ∈ topCells },
      Sperner.IsPanchromatic
        (fun (σ : { s // s ∈ topCells }) => vertexEnum σ.1 (hpure σ.1 σ.2)) c σ ∧
      σ.1 ∈ K.facets ∧ d ≤ Module.finrank 𝕜 E := by
  obtain ⟨σ, hpan, hfacet⟩ :=
    exists_panchromatic_facet K topCells htop hpure hpseudo c hbdry
  exact ⟨σ, hpan, hfacet, facet_dim_le_ambient K hfacet (hpure σ.1 σ.2)⟩

end Capstone

end Sperner.SimplicialComplex
