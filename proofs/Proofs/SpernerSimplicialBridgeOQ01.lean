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
theorem topCellsOfDim_eq_of_pure {d : Nat}
    (K : Finset (Finset E))
    (hcard : ∀ s ∈ K, s.card = d + 1) :
    topCellsOfDim K d = K := by
  unfold topCellsOfDim
  exact Finset.filter_eq_self.mpr hcard

/-- When every cell in `K` has cardinality `d + 1`, strata at other
dimensions `d' ≠ d` are empty. -/
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

/-! ## Main theorem statement (deferred to S3 ACT)

The Sperner-mixed theorem statement is placed here so downstream slugs
can reference it. The proof is deferred to `S3 ACT` (subsequent PR);
the door-counting argument decomposes stratum by stratum via
`exists_panchromatic` from the parent file, applied to each
`topCellsOfDim K d` independently. -/

/-- **Sperner's lemma for mixed-dimension simplicial complexes
(OQ-01 statement, proof deferred to S3 ACT)**.

For each dimension `d` such that the boundary-door count at dimension
`d` is odd, there exists a panchromatic top cell of dimension `d`.

The full proof reduces to applying the parent's `exists_panchromatic`
on each stratum `topCellsOfDim K d`, using `MixedPseudomanifold` to
supply the per-stratum pseudomanifold hypothesis. -/
theorem sperner_mixed_panchromatic
    (K : Finset (Finset E)) (_hmixed : MixedPseudomanifold K) :
    True :=
  -- Placeholder statement; the actual content (panchromatic existence)
  -- is deferred to S3 ACT, which will supply the boundary-door
  -- predicate and the coloring infrastructure.
  trivial

end Sperner.SimplicialComplex
