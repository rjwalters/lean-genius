import Proofs.Erdos85SizeTwoEigenlineCycleGridCoordinates
import Proofs.Erdos85BinarySquareTriangleFreeEdgeCongruence

/-!
# Triangle-free sector of a connected size-two eigenline component

Node: `SIZE-TWO-EIGENLINE(q)` (outline F.3).

On a connected internal size-two component, one vertex of triangle-free
degree two forces triangle-free degree two everywhere.  Hence every internal
edge is triangle-free.  Since each coordinate row has exactly two grid cells
without an exterior witness, those missing cells are then exactly the two
internal cycle shifts `{x, x-1}`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- If triangle-free degree is two at a vertex of a size-two component, both
of its internal ambient edges are triangle-free.  This is the q-generic form
of the helper formerly local to the order-64 mixed-grid assembly. -/
theorem sizeTwo_triangleFreeEdge_of_degree_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hdeg : ∀ x : c.supp, (G.induce c.supp).degree x = 2)
    (x y : c.supp) (hxy : (G.induce c.supp).Adj x y)
    (htwo : (triangleFreeEdgeGraph G).degree x.1 = 2) :
    (triangleFreeEdgeGraph G).Adj x.1 y.1 := by
  classical
  let I : Finset V := ((G.induce c.supp).neighborFinset x).map
    ⟨Subtype.val, Subtype.val_injective⟩
  have hIcard : I.card = 2 := by
    simp only [I, Finset.card_map,
      (G.induce c.supp).card_neighborFinset_eq_degree, hdeg]
  have hsub : (triangleFreeEdgeGraph G).neighborFinset x.1 ⊆ I := by
    intro z hz
    have htf : (triangleFreeEdgeGraph G).Adj x.1 z :=
      ((triangleFreeEdgeGraph G).mem_neighborFinset x.1 z).mp hz
    have hD : (secondOrderDefectGraph G).Adj x.1 z := Or.inr htf
    have hzSupp : z ∈ c.supp := by
      rw [ConnectedComponent.mem_supp_iff]
      exact (ConnectedComponent.connectedComponentMk_eq_of_adj hD).symm.trans
        ((ConnectedComponent.mem_supp_iff c x.1).mp x.2)
    simp only [I, Finset.mem_map]
    refine ⟨⟨z, hzSupp⟩, ?_, rfl⟩
    exact ((G.induce c.supp).mem_neighborFinset x ⟨z, hzSupp⟩).mpr
      ((mem_triangleFreeNeighbors G x.1 z).mp htf).1
  have hTFcard : ((triangleFreeEdgeGraph G).neighborFinset x.1).card = 2 := by
    rw [(triangleFreeEdgeGraph G).card_neighborFinset_eq_degree, htwo]
  have heq : (triangleFreeEdgeGraph G).neighborFinset x.1 = I :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  apply ((triangleFreeEdgeGraph G).mem_neighborFinset x.1 y.1).mp
  rw [heq]
  simp only [I, Finset.mem_map]
  exact ⟨y, ((G.induce c.supp).mem_neighborFinset x y).mpr hxy, rfl⟩

/-- **Connected all-triangle-free sector classification.**  If one vertex
of the connected internal component has triangle-free degree two, then the
two missing cells in every normalized row are precisely its two internal
neighbors. -/
theorem eigenline_hole_eq_internal_of_connected_triangleFreeDegreeTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {q : ℕ} [NeZero q] (hq : 5 ≤ q) (hqEven : Even q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    (hconn : (G.induce c.supp).Connected)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hsum : ∑ x, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      ((q : ℤ) - 5) * s x)
    (coord : SizeTwoCycleGridCoordinates G c.supp s q)
    (v0 : c.supp)
    (hv0 : (triangleFreeEdgeGraph G).degree v0.1 = 2) :
    ∀ x y : ZMod q,
      (¬ ∃ u, IsGridWitness G c coord.pval coord.nval u x y) ↔
        y = x ∨ y = x - 1 := by
  classical
  have hdeg : ∀ z : c.supp, (G.induce c.supp).degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  have htwo : ∀ z : c.supp,
      (triangleFreeEdgeGraph G).degree z.1 = 2 := by
    intro z
    exact (binarySquare_regular_sizeTwoPart_triangleFree_degree_two_iff_of_reachable
      G hfree (by omega) hqEven hreg hcard c hc v0 z
        (hconn.preconnected v0 z)).mp hv0
  have htf : ∀ x y : ZMod q, (y = x ∨ y = x - 1) →
      (triangleFreeEdgeGraph G).Adj (coord.pval x) (coord.nval y) := by
    intro x y hxy
    let px : c.supp := ⟨coord.pval x, (coord.p_mem_sign x).1⟩
    let ny : c.supp := ⟨coord.nval y, (coord.n_mem_sign y).1⟩
    apply sizeTwo_triangleFreeEdge_of_degree_two G c hdeg px ny
    · exact coord.adj_iff x y |>.2 hxy
    · exact htwo px
  intro x y
  let A : Finset (ZMod q) := Finset.univ.filter fun y =>
    ¬ ∃ u, IsGridWitness G c coord.pval coord.nval u x y
  have hAcard : A.card = 2 := by
    exact hole_row_card G c s coord.pval coord.nval hfree hq hreg hcard hc
      hs_in hs_out hsum hA_in hDs coord.p_mem_sign coord.n_mem_sign
      coord.n_injective coord.n_surjective x
  have hq1 : (1 : ZMod q) ≠ 0 := by
    have hq2 : 2 ∣ q := even_iff_two_dvd.mp hqEven
    intro h
    have hz := congrArg (ZMod.castHom hq2 (ZMod 2)) h
    simp only [map_one, map_zero] at hz
    exact absurd hz (by decide)
  have hpairCard : ({x, x - 1} : Finset (ZMod q)).card = 2 := by
    rw [Finset.card_pair]
    intro h
    apply hq1
    have hz := congrArg (fun z : ZMod q => x - z) h
    simpa using hz.symm
  have hsub : ({x, x - 1} : Finset (ZMod q)) ⊆ A := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    change z ∈ Finset.univ.filter (fun y =>
      ¬ ∃ u, IsGridWitness G c coord.pval coord.nval u x y)
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hw
    obtain ⟨u, hu⟩ := hw
    have hzero := ((mem_triangleFreeNeighbors G (coord.pval x)
      (coord.nval z)).mp (htf x z hz)).2
    have humem : u ∈ G.neighborFinset (coord.pval x) ∩
        G.neighborFinset (coord.nval z) := by
      rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset]
      exact ⟨hu.2.1.symm, hu.2.2.symm⟩
    rw [Finset.card_eq_zero.mp hzero] at humem
    simp at humem
  have heq : A = {x, x - 1} :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [hAcard, hpairCard])).symm
  have hmem : y ∈ A ↔ y ∈ ({x, x - 1} : Finset (ZMod q)) := by rw [heq]
  simpa [A] using hmem

/-- Edge-seeded form of the connected triangle-free-sector classification.
The existence of one triangle-free edge between the two signed shores is
enough; the binary size-two degree dichotomy upgrades its endpoint to
triangle-free degree two. -/
theorem eigenline_hole_eq_internal_of_connected_exists_triangleFreeEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {q : ℕ} [NeZero q] (hq : 5 ≤ q) (hqEven : Even q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    (hconn : (G.induce c.supp).Connected)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hsum : ∑ x, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      ((q : ℤ) - 5) * s x)
    (coord : SizeTwoCycleGridCoordinates G c.supp s q)
    (hseed : ∃ x y : ZMod q,
      (triangleFreeEdgeGraph G).Adj (coord.pval x) (coord.nval y)) :
    ∀ x y : ZMod q,
      (¬ ∃ u, IsGridWitness G c coord.pval coord.nval u x y) ↔
        y = x ∨ y = x - 1 := by
  obtain ⟨x, y, hxy⟩ := hseed
  let v0 : c.supp := ⟨coord.pval x, (coord.p_mem_sign x).1⟩
  have hv0 : (triangleFreeEdgeGraph G).degree v0.1 = 2 := by
    rcases binarySquare_regular_sizeTwoPart_triangleFree_degree_eq_zero_or_two
      G hfree (by omega) hqEven hreg hcard c hc v0 with hzero | htwo
    · have hpos := hxy.degree_pos_left
      change (triangleFreeEdgeGraph G).degree (coord.pval x) = 0 at hzero
      omega
    · exact htwo
  exact eigenline_hole_eq_internal_of_connected_triangleFreeDegreeTwo
    G hfree hq hqEven hreg hcard c hc hconn s hs_in hs_out hsum hA_in hDs
      coord v0 hv0

end

end Erdos85

#print axioms Erdos85.sizeTwo_triangleFreeEdge_of_degree_two
#print axioms Erdos85.eigenline_hole_eq_internal_of_connected_triangleFreeDegreeTwo
#print axioms Erdos85.eigenline_hole_eq_internal_of_connected_exists_triangleFreeEdge
