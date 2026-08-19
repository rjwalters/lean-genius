import Proofs.Erdos85SizeTwoEigenlineSixTenAntipodalTrace

/-!
# Sharp antipodal cube-trace lower bound in the q=8 six-plus-ten stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The sixty directed rooted triangles have three disjoint cyclic rotations,
distinguished by the position occupied by their six-cycle vertex.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

theorem binarySquare_regular_sizeTwoPart_eight_sixTen_antipodalCubeTrace_ge_oneEighty
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
    (180 : ℤ) ≤ Matrix.trace
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
  have hTcard : T.card = 60 :=
    binarySquare_regular_sizeTwoPart_eight_sixTen_rootedAntipodalTriangles_card
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
        u v huinj hvinj hurange hvrange hu hv
  let f : (Σ _ : (Σ _ : c.supp, c.supp), c.supp) → Fin 3 → V × V × V :=
    fun q k => ![(q.2.1, q.1.2.1, q.1.1.1),
      (q.1.2.1, q.1.1.1, q.2.1),
      (q.1.1.1, q.2.1, q.1.2.1)] k
  have hbase : ∀ q ∈ T,
      (q.2.1, q.1.2.1, q.1.1.1) ∈ cyclicColoredTriples
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
    obtain ⟨i, rfl⟩ : y ∈ Set.range v := by rw [hvrange]; exact hyb
    obtain ⟨j, rfl⟩ : z ∈ Set.range v := by rw [hvrange]; exact hzb
    have hyzAnti :=
      (binarySquare_regular_sizeTwoPart_eight_sixTen_sameSignDiagonal_three_antipodalTriangles
        G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
          u v huinj hvinj hurange hvrange hu hv i j hyzK hzdata.2).1
    have hxdata := Finset.mem_filter.mp hq'.2
    simp only [cyclicColoredTriples, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨hxdata.2.1, hyzAnti, hxdata.2.2.symm⟩
  have hmaps : ∀ p ∈ T.product (Finset.univ : Finset (Fin 3)),
      f p.1 p.2 ∈ cyclicColoredTriples
        (antipodalGraph G) (antipodalGraph G) (antipodalGraph G) := by
    rintro ⟨q, k⟩ hp
    have hq := (Finset.mem_product.mp hp).1
    have hb0 := hbase q hq
    simp only [cyclicColoredTriples, Finset.mem_filter, Finset.mem_univ,
      true_and] at hb0 ⊢
    rcases hb0 with ⟨h₁, h₂, h₃⟩
    fin_cases k
    · exact ⟨h₁, h₂, h₃⟩
    · dsimp [f]
      exact ⟨h₃, h₁, h₂⟩
    · dsimp [f]
      exact ⟨h₂, h₃, h₁⟩
  have hshores : ∀ q ∈ T,
      q.2 ∈ a.supp ∧ q.1.1 ∈ b.supp ∧ q.1.2 ∈ b.supp := by
    rintro ⟨⟨y, z⟩, x⟩ hq
    have hq' := Finset.mem_sigma.mp hq
    have hyz := Finset.mem_sigma.mp hq'.1
    exact ⟨(ConnectedComponent.mem_supp_iff a x).mpr
        (Finset.mem_filter.mp (Finset.mem_filter.mp hq'.2).1).2,
      (Finset.mem_filter.mp hyz.1).2,
      (ConnectedComponent.mem_supp_iff b z).mpr
        (Finset.mem_filter.mp (Finset.mem_filter.mp hyz.2).1).2⟩
  have hab : a ≠ b := by
    intro hab
    rw [hab] at ha
    omega
  have hdisj : ∀ z : c.supp, z ∈ a.supp → z ∈ b.supp → False := by
    intro z hza hzb
    apply hab
    rw [← (ConnectedComponent.mem_supp_iff a z).mp hza,
      ← (ConnectedComponent.mem_supp_iff b z).mp hzb]
  have hfinj : ∀ k : Fin 3, Function.Injective (fun q => f q k) := by
    intro k
    fin_cases k
    · rintro ⟨⟨y, z⟩, x⟩ ⟨⟨y', z'⟩, x'⟩ heq
      have hx : x = x' := Subtype.ext (congrArg Prod.fst heq)
      have hz : z = z' := Subtype.ext (congrArg (fun t => t.2.1) heq)
      have hy : y = y' := Subtype.ext (congrArg (fun t => t.2.2) heq)
      subst x'; subst z'; subst y'; rfl
    · rintro ⟨⟨y, z⟩, x⟩ ⟨⟨y', z'⟩, x'⟩ heq
      have hz : z = z' := Subtype.ext (congrArg Prod.fst heq)
      have hy : y = y' := Subtype.ext (congrArg (fun t => t.2.1) heq)
      have hx : x = x' := Subtype.ext (congrArg (fun t => t.2.2) heq)
      subst x'; subst z'; subst y'; rfl
    · rintro ⟨⟨y, z⟩, x⟩ ⟨⟨y', z'⟩, x'⟩ heq
      have hy : y = y' := Subtype.ext (congrArg Prod.fst heq)
      have hx : x = x' := Subtype.ext (congrArg (fun t => t.2.1) heq)
      have hz : z = z' := Subtype.ext (congrArg (fun t => t.2.2) heq)
      subst x'; subst z'; subst y'; rfl
  have hinj : Set.InjOn (fun p => f p.1 p.2)
      (↑(T.product (Finset.univ : Finset (Fin 3))) :
        Set ((Σ _ : (Σ _ : c.supp, c.supp), c.supp) × Fin 3)) := by
    rintro ⟨q, k⟩ hp ⟨q', k'⟩ hp' heq
    have hq := (Finset.mem_product.mp hp).1
    have hq' := (Finset.mem_product.mp hp').1
    have hs := hshores q hq
    have hs' := hshores q' hq'
    fin_cases k <;> fin_cases k'
    · exact congrArg (fun q => (q, (0 : Fin 3))) (hfinj 0 heq)
    · exact False.elim (hdisj q.2 hs.1
        ((Subtype.ext (congrArg Prod.fst heq)) ▸ hs'.2.2))
    · exact False.elim (hdisj q.2 hs.1
        ((Subtype.ext (congrArg Prod.fst heq)) ▸ hs'.2.1))
    · exact False.elim (hdisj q'.2 hs'.1
        ((Subtype.ext (congrArg Prod.fst heq)).symm ▸ hs.2.2))
    · exact congrArg (fun q => (q, (1 : Fin 3))) (hfinj 1 heq)
    · exact False.elim (hdisj q'.2 hs'.1
        ((Subtype.ext (congrArg (fun t => t.2.1) heq)).symm ▸ hs.2.1))
    · exact False.elim (hdisj q'.2 hs'.1
        ((Subtype.ext (congrArg Prod.fst heq)).symm ▸ hs.2.1))
    · exact False.elim (hdisj q.2 hs.1
        ((Subtype.ext (congrArg (fun t => t.2.1) heq)) ▸ hs'.2.1))
    · exact congrArg (fun q => (q, (2 : Fin 3))) (hfinj 2 heq)
  have hcardle := Finset.card_le_card_of_injOn
    (fun p : (Σ _ : (Σ _ : c.supp, c.supp), c.supp) × Fin 3 =>
      f p.1 p.2) hmaps hinj
  have htrace := trace_three_adjMatrices_eq_card_cyclicColoredTriples
    (antipodalGraph G) (antipodalGraph G) (antipodalGraph G)
  rw [htrace]
  have hprod : (T.product (Finset.univ : Finset (Fin 3))).card = 180 := by
    simp [hTcard]
  exact_mod_cast hprod ▸ hcardle

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_antipodalCubeTrace_ge_oneEighty
