import Proofs.Erdos85PureEndpointCanonicalPrivatePoints
import Proofs.Erdos85PureEndpointCanonicalPairPoints

/-!
# One- and two-subset coordinates for the pure endpoint shore

The replication-one and replication-two bijections combine into a single
coordinate chart for the whole shore.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- At the pure endpoint, the shore is bijective with the disjoint union of
the full centers and their two-subsets.  The coordinate of a shore point is
exactly its set of adjacent full centers. -/
theorem c4Free_binarySquare_pureEndpoint_shore_coordinate_bijection
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
    ∃ ψ : Sum C I → {z : V // z ∈ S},
      Function.Bijective ψ ∧
      ∀ a, G.neighborFinset (ψ a).1 ∩ F =
        Sum.elim (fun i : C => {i.1}) (fun e : I => e.1) a := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let C := {i : V // i ∈ F}
  let I := {e : Finset V // e ∈ F.powersetCard 2}
  obtain ⟨p, hpInj, hp, hpSurj⟩ :=
    c4Free_binarySquare_pureEndpoint_privatePoint_bijection
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  obtain ⟨φ, hφInj, hφ, hφSurj⟩ :=
    c4Free_binarySquare_pureEndpoint_pairPoint_bijection
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hprofile :=
    (c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri).1
  let ψ : Sum C I → {z : V // z ∈ S} := fun a => match a with
    | Sum.inl i => ⟨p i, (hp i).1⟩
    | Sum.inr e => ⟨φ e, (hφ e).1⟩
  have hcoord : ∀ a, G.neighborFinset (ψ a).1 ∩ F =
      Sum.elim (fun i : C => {i.1}) (fun e : I => e.1) a := by
    intro a
    cases a with
    | inl i => simpa [ψ, F, C] using (hp i).2.2
    | inr e => simpa [ψ, F, I] using (hφ e).2
  have hψInj : Function.Injective ψ := by
    intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j =>
        apply congrArg Sum.inl
        apply hpInj
        exact congrArg Subtype.val hab
      | inr e =>
        exfalso
        have heCard : e.1.card = 2 := (mem_powersetCard.1 e.2).2
        have hsets : ({i.1} : Finset V) = e.1 := by
          calc
            {i.1} = G.neighborFinset (ψ (Sum.inl i)).1 ∩ F := by
              simpa using (hcoord (Sum.inl i)).symm
            _ = G.neighborFinset (ψ (Sum.inr e)).1 ∩ F := by
              rw [hab]
            _ = e.1 := by simpa using hcoord (Sum.inr e)
        have := congrArg Finset.card hsets
        simp [heCard] at this
    | inr e =>
      cases b with
      | inl i =>
        exfalso
        have heCard : e.1.card = 2 := (mem_powersetCard.1 e.2).2
        have hsets : e.1 = ({i.1} : Finset V) := by
          calc
            e.1 = G.neighborFinset (ψ (Sum.inr e)).1 ∩ F := by
              simpa using (hcoord (Sum.inr e)).symm
            _ = G.neighborFinset (ψ (Sum.inl i)).1 ∩ F := by
              rw [hab]
            _ = {i.1} := by simpa using hcoord (Sum.inl i)
        have := congrArg Finset.card hsets
        simp [heCard] at this
      | inr f =>
        apply congrArg Sum.inr
        apply hφInj
        exact congrArg Subtype.val hab
  have hψSurj : Function.Surjective ψ := by
    intro z
    rcases (hprofile z.1).mp z.2 with hzOne | hzTwo
    · obtain ⟨i, hi⟩ := hpSurj z.1 z.2 hzOne
      refine ⟨Sum.inl i, ?_⟩
      apply Subtype.ext
      simpa [ψ] using hi
    · obtain ⟨e, he⟩ := hφSurj z.1 z.2 hzTwo
      refine ⟨Sum.inr e, ?_⟩
      apply Subtype.ext
      simpa [ψ] using he
  exact ⟨ψ, ⟨hψInj, hψSurj⟩, hcoord⟩

end

end Erdos85

#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_shore_coordinate_bijection
