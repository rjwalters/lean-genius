import Mathlib

/-!
# Closed-neighborhood escape in connected defect graphs

This is the graph-specific half of the `NONBIP-CONNECTED [q]` incidence
bottleneck.  A connected graph has an edge leaving every nonempty proper
vertex set.  At square order, the closed neighborhood of a vertex in a
`(q-1)`-regular graph has only `q` vertices, hence is proper and has such an
escaping edge.
-/

open SimpleGraph

namespace Erdos85

/-- Every nonempty proper vertex set in a connected graph has an edge to its
complement. -/
theorem connected_exists_adj_outside_of_nonempty_proper
    {V : Type*} (G : SimpleGraph V) (hconn : G.Connected)
    (S : Set V) (hne : S.Nonempty) (hproper : S ≠ Set.univ) :
    ∃ u ∈ S, ∃ v ∉ S, G.Adj u v := by
  by_contra! hcross
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy⟩ : ∃ y, y ∉ S := by
    simpa [Set.eq_univ_iff_forall] using hproper
  let H : G.Subgraph := (⊤ : G.Subgraph).induce S
  have hyH : y ∈ H.verts :=
    (hconn.preconnected x y).mem_subgraphVerts
      (H := H) (fun v hv w hvw ↦ by
        have hvS : v ∈ S := by simpa [H] using hv
        have hwS : w ∈ S := by
          by_contra hw
          exact hcross v hvS w hw hvw
        simp [H, hvw, hvS, hwS]) (by simp [H, hx])
  exact hy (by simpa [H] using hyH)

/-- In a connected `(q-1)`-regular graph on `q²` vertices (`q ≥ 2`), every
closed neighborhood has an escaping edge.  Thus no closed neighborhood can
be an isolated `K_q` component. -/
theorem connected_regular_squareOrder_exists_closedNeighborhood_escape
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) {q : ℕ} (hq : 2 ≤ q)
    (hreg : ∀ x, G.degree x = q - 1)
    (hcard : Fintype.card V = q * q) (x : V) :
    ∃ u, (u = x ∨ G.Adj x u) ∧
      ∃ v, v ≠ x ∧ ¬ G.Adj x v ∧ G.Adj u v := by
  let Sfin : Finset V := insert x (G.neighborFinset x)
  let S : Set V := (Sfin : Set V)
  have hSne : S.Nonempty := ⟨x, by simp [S, Sfin]⟩
  have hScard : Sfin.card = q := by
    simp [Sfin, hreg x]
    omega
  have hSproper : S ≠ Set.univ := by
    intro hSu
    have hfin : Sfin = Finset.univ := by
      ext y
      simpa [S] using Set.ext_iff.mp hSu y
    have hqq : q = q * q := by
      calc
        q = Sfin.card := hScard.symm
        _ = (Finset.univ : Finset V).card := congrArg Finset.card hfin
        _ = Fintype.card V := Finset.card_univ
        _ = q * q := hcard
    nlinarith
  obtain ⟨u, huS, v, hvS, huv⟩ :=
    connected_exists_adj_outside_of_nonempty_proper G hconn S hSne hSproper
  refine ⟨u, ?_, v, ?_, ?_, huv⟩
  · simpa [S, Sfin] using huS
  · intro hvx
    subst v
    exact hvS (by simp [S, Sfin])
  · intro hxv
    exact hvS (by simp [S, Sfin, hxv])

#print axioms connected_exists_adj_outside_of_nonempty_proper
#print axioms connected_regular_squareOrder_exists_closedNeighborhood_escape

end Erdos85
