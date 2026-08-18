import Proofs.Erdos85CollisionRainbowOwnerPattern
import Proofs.Erdos85NearTwinOwnerFork
import Proofs.Erdos85RoutingOwnerRainbowExactColors

/-! # Graph-facing owner pattern of a collision rainbow -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Three distinct restricted-owner row collisions on the edges of a
selector-complement triangle force the canonical edge-owner pattern to be
monochromatic in the fourth color or one of the three `2+1` patterns.

This discharges the abstract theorem's palette exhaustion and exact edge-color
hypotheses directly from the four-component order-64 graph interface. -/
theorem orderSixtyFour_collisionRainbow_canonicalEdgeOwnerPattern
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (source α β γ δ : (secondOrderDefectGraph G).ConnectedComponent)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hαδ : α ≠ δ) (hβδ : β ≠ δ) (hγδ : γ ≠ δ)
    (a b c : source.supp)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hnotAB : ¬ ((secondOrderDefectGraph G).induce source.supp).Adj a b)
    (hnotAC : ¬ ((secondOrderDefectGraph G).induce source.supp).Adj a c)
    (hnotBC : ¬ ((secondOrderDefectGraph G).induce source.supp).Adj b c)
    (habRows :
      (restrictedComponentOwnerGraph G source α).neighborFinset a =
        (restrictedComponentOwnerGraph G source α).neighborFinset b)
    (hacRows :
      (restrictedComponentOwnerGraph G source β).neighborFinset a =
        (restrictedComponentOwnerGraph G source β).neighborFinset c)
    (hbcRows :
      (restrictedComponentOwnerGraph G source γ).neighborFinset b =
        (restrictedComponentOwnerGraph G source γ).neighborFinset c) :
    let p := nondefectPairOwner G hfree
      (fun h => hab (Subtype.ext h)) (by simpa using hnotAB)
    let q := nondefectPairOwner G hfree
      (fun h => hac (Subtype.ext h)) (by simpa using hnotAC)
    let r := nondefectPairOwner G hfree
      (fun h => hbc (Subtype.ext h)) (by simpa using hnotBC)
    (p = δ ∧ q = δ ∧ r = δ) ∨
      (p = δ ∧ q = α ∧ r = α) ∨
      (p = β ∧ q = δ ∧ r = β) ∨
      (p = γ ∧ q = γ ∧ r = δ) := by
  classical
  let p := nondefectPairOwner G hfree
    (fun h => hab (Subtype.ext h)) (by simpa using hnotAB)
  let q := nondefectPairOwner G hfree
    (fun h => hac (Subtype.ext h)) (by simpa using hnotAC)
  let r := nondefectPairOwner G hfree
    (fun h => hbc (Subtype.ext h)) (by simpa using hnotBC)
  have hall : ∀ owner : (secondOrderDefectGraph G).ConnectedComponent,
      owner = α ∨ owner = β ∨ owner = γ ∨ owner = δ := by
    have hcard : ({α, β, γ, δ} : Finset
        (secondOrderDefectGraph G).ConnectedComponent).card = 4 := by
      simp [hαβ, hαγ, hβγ, hαδ, hβδ, hγδ]
    have hexhaust : ({α, β, γ, δ} : Finset
        (secondOrderDefectGraph G).ConnectedComponent) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [hcard, Finset.card_univ, hcount]
    intro owner
    have : owner ∈ ({α, β, γ, δ} : Finset
        (secondOrderDefectGraph G).ConnectedComponent) := by
      rw [hexhaust]
      exact Finset.mem_univ owner
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  have hpAdj :
      (componentOwnerGraph G (secondOrderDefectGraph G) p).Adj a.1 b.1 := by
    exact nondefectPairOwner_adj G hfree
      (fun h => hab (Subtype.ext h)) (by simpa using hnotAB)
  have hqAdj :
      (componentOwnerGraph G (secondOrderDefectGraph G) q).Adj a.1 c.1 := by
    exact nondefectPairOwner_adj G hfree
      (fun h => hac (Subtype.ext h)) (by simpa using hnotAC)
  have hrAdj :
      (componentOwnerGraph G (secondOrderDefectGraph G) r).Adj b.1 c.1 := by
    exact nondefectPairOwner_adj G hfree
      (fun h => hbc (Subtype.ext h)) (by simpa using hnotBC)
  have hAB : ∀ owner,
      (restrictedComponentOwnerGraph G source owner).Adj a b ↔ owner = p := by
    intro owner
    exact componentOwnerGraph_adj_iff_owner_eq_of_adj
      G hfree p hpAdj owner
  have hAC : ∀ owner,
      (restrictedComponentOwnerGraph G source owner).Adj a c ↔ owner = q := by
    intro owner
    exact componentOwnerGraph_adj_iff_owner_eq_of_adj
      G hfree q hqAdj owner
  have hBC : ∀ owner,
      (restrictedComponentOwnerGraph G source owner).Adj b c ↔ owner = r := by
    intro owner
    exact componentOwnerGraph_adj_iff_owner_eq_of_adj
      G hfree r hrAdj owner
  have matrixRows {H : SimpleGraph source.supp} [DecidableRel H.Adj]
      {x y : source.supp} (hN : H.neighborFinset x = H.neighborFinset y) :
      ∀ z, H.adjMatrix ℤ x z = H.adjMatrix ℤ y z := by
    intro z
    rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
    have hiff : H.Adj x z ↔ H.Adj y z := by
      rw [← H.mem_neighborFinset, ← H.mem_neighborFinset, hN]
    by_cases hxz : H.Adj x z <;> by_cases hyz : H.Adj y z <;>
      simp_all
  exact fourColor_equalRows_triangle_ownerPattern
    (fun owner => restrictedComponentOwnerGraph G source owner)
      hαβ hαγ hβγ hαδ hβδ hγδ hall hAB hAC hBC
      (matrixRows habRows) (matrixRows hacRows) (matrixRows hbcRows)

end

end Erdos85
