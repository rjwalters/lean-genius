import Proofs.Erdos85PureEndpointShoreCoordinateBijection
import Proofs.Erdos85SecondOrderDefectOwnerDisjointness
import Proofs.Erdos85PureEndpointDefectCutProfile

/-!
# The endpoint shore defect graph in subset coordinates

The canonical shore chart embeds every second-order defect edge into the
disjointness relation on the one- and two-subsets of the full-center family.
It also transports the exact two-level internal degree profile.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The shore defect graph is a spanning subgraph of the disjointness graph
on singleton and two-subset coordinates, with internal degrees `q-1` and
`m-1` on the two coordinate classes. -/
theorem c4Free_binarySquare_pureEndpoint_shore_disjointness_embedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    let F := fullLineCenters G S q
    let C := {i : V // i ∈ F}
    let I := {e : Finset V // e ∈ F.powersetCard 2}
    let coord : Sum C I → Finset V :=
      Sum.elim (fun i => {i.1}) (fun e => e.1)
    ∃ ψ : Sum C I → {z : V // z ∈ S},
      Function.Bijective ψ ∧
      (∀ a, G.neighborFinset (ψ a).1 ∩ F = coord a) ∧
      (∀ {a b}, (secondOrderDefectGraph G).Adj (ψ a).1 (ψ b).1 →
        Disjoint (coord a) (coord b)) ∧
      (∀ i : C,
        ((secondOrderDefectGraph G).neighborFinset (ψ (Sum.inl i)).1 ∩ S).card =
          q - 1) ∧
      ∀ e : I,
        ((secondOrderDefectGraph G).neighborFinset (ψ (Sum.inr e)).1 ∩ S).card =
          m - 1 := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let C := {i : V // i ∈ F}
  let I := {e : Finset V // e ∈ F.powersetCard 2}
  let coord : Sum C I → Finset V :=
    Sum.elim (fun i => {i.1}) (fun e => e.1)
  obtain ⟨ψ, hψBij, hcoord⟩ :=
    c4Free_binarySquare_pureEndpoint_shore_coordinate_bijection
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hdisj : ∀ {x y : V}, (secondOrderDefectGraph G).Adj x y →
      Disjoint (exceptionalOwnerSet G (fullLineCenters G S q) x)
        (exceptionalOwnerSet G (fullLineCenters G S q) y) :=
    (c4Free_binarySquare_pureEndpoint_ownerLabel_disjointness_profile
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri).2.2
  have hdeg := c4Free_binarySquare_pureEndpoint_defect_biregular_decomposition
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  refine ⟨ψ, hψBij, ?_, ?_, ?_, ?_⟩
  · intro a
    simpa [F, C, I, coord] using hcoord a
  · intro a b hab
    have hd := hdisj hab
    simpa [exceptionalOwnerSet, F, C, I, coord, hcoord a, hcoord b] using hd
  · intro i
    apply (hdeg (ψ (Sum.inl i)).1).1
    rw [hcoord (Sum.inl i)]
    simp [F, C]
  · intro e
    apply (hdeg (ψ (Sum.inr e)).1).2.1
    rw [hcoord (Sum.inr e)]
    exact (mem_powersetCard.1 e.2).2

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_shore_disjointness_embedding
