/-
# Sperner Simplicial Instance OQ-03: Cross-Dimensional Inductive Step

Boundary Door Parity for the Standard n-Simplex Triangulation.

The parent file `SpernerSimplicialInstance.lean` proves `boundary_doors_odd`
(line 173) as a parity *transfer* theorem: it reduces "the total boundary-door
count of a Sperner-colored triangulation is odd" to the single hypothesis
`_hLastFace` ("the door count on the top geometric facet is odd"). The genuine
remaining first-principles content is therefore `_hLastFace`, which is meant to
be discharged by induction on dimension against the already-proven parity engine
`SpernerNDim.sperner_parity` (`SpernerNDim.lean:601`, 0 sorries / 0 axioms):

  #FC simplices  ≡  #(boundary doors on the top facet)   (mod 2).

This file isolates the abstract *inductive step* of that recursion, working
entirely inside `SpernerNDim`'s sorry-free structure. The classical Sperner
recursion is

  Odd #FC(Δⁿ)
    ⟸ Odd #(top-facet boundary doors of Δⁿ)        -- sperner_parity
    =  Odd #FC(induced Δⁿ⁻¹ coloring on that facet) -- facet-restriction bijection
    ⟸ Odd #FC(Δⁿ⁻¹)                                  -- induction hypothesis

with base case `Odd #FC(Δ¹) = 1`. Every arithmetic/parity step is already
discharged by `sperner_parity`. The ONLY geometric input is the door↔FC
*facet-restriction bijection*, which here appears as a cardinality hypothesis
`hbij` (exactly parallel to how `boundary_doors_odd` takes `_hLastFace` as a
hypothesis). Constructing that bijection for the concrete order-polytope standard
triangulation — relating a `SpernerSimplicialInstance.Triangulation` to a
lower-dimensional `SpernerNDim.SpernerTriangulation` — remains the open concrete
task; this file supplies the reusable parity skeleton it plugs into.

STATUS: build-pending (Docker verification blackout), UNREGISTERED. Statically
verified S8 (2026-06-15): the two proofs' rewrite chains were checked against the
parent's *machine-checked* patterns. (The S7 `fc_odd_tower` in
`SpernerSimplicialInstanceOQ03Tower.lean` builds directly on the step below, so
this verification de-risks the whole recursion tower as well.)
  * `fc_odd_of_facet_bijection`'s chain `rw [Nat.odd_iff, hpar, hbij, ← Nat.odd_iff]`
    mirrors `sperner_ndim`'s own verified `rwa [Nat.odd_iff, hparity, ← Nat.odd_iff]`
    (SpernerNDim.lean:663). The door filter in `hbij` matches `sperner_parity`
    instantiated at dimension `d + 1` character-for-character (`Fin (d + 1 + 1)`,
    `Fin.last (d + 1)`), so `rw [hpar]` then `rw [hbij]` fire as written.
  * `exists_fc_of_lower_fc_odd` reduces via `apply sperner_ndim` to exactly the
    `hbdry` door-oddness obligation, discharged by `rw [hbij]; exact hfc'`.
Symbols (sperner_parity, sperner_ndim, IsFC, isDoorAt, IsSperner, Coloring,
SpernerTriangulation, Fin.last) are in-repo (SpernerNDim.lean); `Nat.odd_iff` is
Mathlib v4.26 (used by the parent itself). This file is ready to register the
moment the Docker backend returns.
-/

import Proofs.SpernerNDim

namespace SpernerNDim

open Finset BigOperators

/-- **Cross-dimensional inductive step of Sperner's lemma (FC-oddness propagates
up one dimension).**

Let `K` be a Sperner-colored triangulation of dimension `d + 1` and `K'` a
Sperner-colored triangulation of dimension `d`. Assume the number of boundary
doors on the *top* facet (`Fin.last (d + 1)`) of `K` equals the number of
fully-colored (panchromatic) simplices of `K'` — this is precisely the geometric
*facet-restriction bijection*: the top-facet doors of `Δ^{d+1}` are the FC cells
of the `Δ^d` coloring induced on that facet. If `K'` has an odd number of FC
simplices, then so does `K`.

The proof is pure parity bookkeeping discharged by `sperner_parity`: the only
mathematical content beyond it is the bijection hypothesis `hbij`, which is
deferred to the concrete standard triangulation. This is the inductive step of
the dimension recursion that closes `_hLastFace` in `boundary_doors_odd`. -/
theorem fc_odd_of_facet_bijection {d N N' : ℕ}
    (c : Coloring (d + 1) N) (K : SpernerTriangulation (d + 1) N) (hc : IsSperner c)
    (c' : Coloring d N') (K' : SpernerTriangulation d N') (_hc' : IsSperner c')
    (hbij :
      (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1 + 1) =>
        isDoorAt c K p.1 p.2 ∧ K.adj p.1 p.2 = none ∧ p.2 = Fin.last (d + 1))).card =
      (Finset.univ.filter (fun s : K'.Simplex => IsFC c' K' s)).card)
    (hfc' : Odd (Finset.univ.filter (fun s : K'.Simplex => IsFC c' K' s)).card) :
    Odd (Finset.univ.filter (fun s : K.Simplex => IsFC c K s)).card := by
  have hpar := sperner_parity c K hc
  rw [Nat.odd_iff, hpar, hbij, ← Nat.odd_iff]
  exact hfc'

/-- **Existence corollary: a fully-colored simplex from a lower-dimensional FC
count.**

Combining the facet-restriction bijection `hbij` with `sperner_ndim`: if the top
facet of the `(d + 1)`-dimensional Sperner triangulation `K` restricts (in the
door↔FC sense) to a `d`-dimensional triangulation `K'` with an odd number of
fully-colored simplices, then `K` itself contains a fully-colored simplex. This
is the recursion expressed in the form the parent existence statement consumes:
the `(d-1)`-dimensional Sperner lemma feeds the `d`-dimensional one. -/
theorem exists_fc_of_lower_fc_odd {d N N' : ℕ}
    (c : Coloring (d + 1) N) (K : SpernerTriangulation (d + 1) N) (hc : IsSperner c)
    (c' : Coloring d N') (K' : SpernerTriangulation d N')
    (hbij :
      (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1 + 1) =>
        isDoorAt c K p.1 p.2 ∧ K.adj p.1 p.2 = none ∧ p.2 = Fin.last (d + 1))).card =
      (Finset.univ.filter (fun s : K'.Simplex => IsFC c' K' s)).card)
    (hfc' : Odd (Finset.univ.filter (fun s : K'.Simplex => IsFC c' K' s)).card) :
    ∃ s : K.Simplex, IsFC c K s := by
  apply sperner_ndim c K hc
  rw [hbij]
  exact hfc'

end SpernerNDim
