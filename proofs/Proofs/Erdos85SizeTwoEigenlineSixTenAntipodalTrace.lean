import Proofs.Erdos85SizeTwoEigenlineSixTenTriangleCensus
import Proofs.Erdos85BinarySquareMixedOwnerTriangleCensus

/-!
# Antipodal cube-trace lower bound in the q=8 six-plus-ten stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The sixty rooted triples from the six-plus-ten triangle census inject into
the standard cyclic triple finset for the antipodal graph.  The generic
cyclic-census/trace identity then yields the concrete lower bound
`60 ≤ tr(C³)`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

theorem binarySquare_regular_sizeTwoPart_eight_sixTen_antipodalCubeTrace_ge_sixty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      3 * s x)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (u : ZMod 6 → c.supp) (v : ZMod 10 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    (60 : ℤ) ≤ Matrix.trace
      ((antipodalGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ) := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let B := (Finset.univ : Finset c.supp).filter fun y => y ∈ b.supp
  let E := B.sigma fun y =>
    (componentNeighborFinset K H b y).filter fun z => s z.1 = s y.1
  let T := E.sigma fun p =>
    (componentNeighborFinset K H a p.1).filter fun x =>
      (antipodalGraph G).Adj x.1 p.1.1 ∧
        (antipodalGraph G).Adj x.1 p.2.1
  have hTcard : T.card = 60 := by
    exact binarySquare_regular_sizeTwoPart_eight_sixTen_rootedAntipodalTriangles_card
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
        u v huinj hvinj hurange hvrange hu hv
  let f : (Σ _ : (Σ _ : c.supp, c.supp), c.supp) → V × V × V := fun q =>
    (q.2.1, q.1.2.1, q.1.1.1)
  have hmaps : ∀ q ∈ T,
      f q ∈ cyclicColoredTriples
        (antipodalGraph G) (antipodalGraph G) (antipodalGraph G) := by
    rintro ⟨⟨y, z⟩, x⟩ hq
    have hq' := Finset.mem_sigma.mp hq
    have hyz := Finset.mem_sigma.mp hq'.1
    have hyb : y ∈ b.supp := (Finset.mem_filter.mp hyz.1).2
    have hzdata := Finset.mem_filter.mp hyz.2
    have hzb : z ∈ b.supp :=
      (ConnectedComponent.mem_supp_iff b z).mpr
        (Finset.mem_filter.mp hzdata.1).2
    have hyzK : K.Adj y z :=
      (K.mem_neighborFinset y z).mp (Finset.mem_filter.mp hzdata.1).1
    have hyrange : y ∈ Set.range v := by
      rw [hvrange]
      exact hyb
    have hzrange : z ∈ Set.range v := by
      rw [hvrange]
      exact hzb
    obtain ⟨i, rfl⟩ := hyrange
    obtain ⟨j, rfl⟩ := hzrange
    have hyzAnti :=
      (binarySquare_regular_sizeTwoPart_eight_sixTen_sameSignDiagonal_three_antipodalTriangles
        G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
          u v huinj hvinj hurange hvrange hu hv i j hyzK hzdata.2).1
    have hxdata := Finset.mem_filter.mp hq'.2
    simp only [cyclicColoredTriples, Finset.mem_filter, Finset.mem_univ,
      true_and, f]
    exact ⟨hxdata.2.1, hyzAnti, hxdata.2.2.symm⟩
  have hinj : Set.InjOn f
      (↑T : Set (Σ _ : (Σ _ : c.supp, c.supp), c.supp)) := by
    rintro ⟨⟨y, z⟩, x⟩ _ ⟨⟨y', z'⟩, x'⟩ _ heq
    simp only [f] at heq
    have hx : x = x' := Subtype.ext (congrArg Prod.fst heq)
    have hz : z = z' := Subtype.ext (congrArg (fun t => t.2.1) heq)
    have hy : y = y' := Subtype.ext (congrArg (fun t => t.2.2) heq)
    subst x'
    subst z'
    subst y'
    rfl
  have hcardle : T.card ≤
      (cyclicColoredTriples
        (antipodalGraph G) (antipodalGraph G) (antipodalGraph G)).card :=
    Finset.card_le_card_of_injOn f hmaps hinj
  have htrace := trace_three_adjMatrices_eq_card_cyclicColoredTriples
    (antipodalGraph G) (antipodalGraph G) (antipodalGraph G)
  rw [htrace]
  exact_mod_cast hTcard ▸ hcardle

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_antipodalCubeTrace_ge_sixty
