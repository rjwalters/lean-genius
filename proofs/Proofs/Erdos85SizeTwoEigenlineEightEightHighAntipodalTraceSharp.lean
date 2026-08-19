import Proofs.Erdos85SizeTwoEigenlineEightEightHighTriangleCensus
import Proofs.Erdos85BinarySquareMixedOwnerTriangleCensus

/-!
# Sharp one-shore antipodal trace bound in the high eight-plus-eight sector

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The at least thirty-two directed half-turn triples on one C8 have three
disjoint cyclic rotations, distinguished by the position of the unique
opposite-shore vertex.  Hence they contribute at least ninety-six entries to
the antipodal cube trace.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

theorem binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_antipodalCubeTrace_ge_ninetySix
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
    (ha : a.supp.ncard = 8) (hb : b.supp.ncard = 8) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (hab6 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 6) :
    (96 : ℤ) ≤ Matrix.trace
      ((antipodalGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ) := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let F : ZMod 8 → Finset c.supp := fun i =>
    (componentNeighborFinset K H b (u i)) ∩
      componentNeighborFinset K H b (u (i + 4))
  let T := (Finset.univ : Finset (ZMod 8)).sigma F
  have hTcard : 32 ≤ T.card := by
    have hsum :=
      binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_firstCycle_rootedAntipodalTriangles_sum_ge
        G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb hab
          u v huinj hvinj hurange hvrange hu hv hab6
    simpa [T, F, K, H] using hsum
  let f : (Σ _ : ZMod 8, c.supp) → Fin 3 → V × V × V := fun q k =>
    ![((u q.1).1, (u (q.1 + 4)).1, q.2.1),
      ((u (q.1 + 4)).1, q.2.1, (u q.1).1),
      (q.2.1, (u q.1).1, (u (q.1 + 4)).1)] k
  have hbase : ∀ q ∈ T,
      ((u q.1).1, (u (q.1 + 4)).1, q.2.1) ∈ cyclicColoredTriples
        (antipodalGraph G) (antipodalGraph G) (antipodalGraph G) := by
    rintro ⟨i, z⟩ hq
    have hzF := (Finset.mem_sigma.mp hq).2
    have htri :=
      binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_firstCycle_four_antipodalTriangles
        G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb hab
          u v huinj hvinj hurange hvrange hu hv hab6 i
    have hz := htri.2.2 z (by simpa [F, K, H] using hzF)
    simp only [cyclicColoredTriples, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨hz.1, hz.2.symm, htri.1.symm⟩
  have hmaps : ∀ p ∈ T.product (Finset.univ : Finset (Fin 3)),
      f p.1 p.2 ∈ cyclicColoredTriples
        (antipodalGraph G) (antipodalGraph G) (antipodalGraph G) := by
    rintro ⟨q, k⟩ hp
    have hb0 := hbase q (Finset.mem_product.mp hp).1
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
      u q.1 ∈ a.supp ∧ u (q.1 + 4) ∈ a.supp ∧ q.2 ∈ b.supp := by
    rintro ⟨i, z⟩ hq
    have hzF := (Finset.mem_sigma.mp hq).2
    have hzFirst := (Finset.mem_inter.mp hzF).1
    refine ⟨?_, ?_, ?_⟩
    · rw [← hurange]; exact ⟨i, rfl⟩
    · rw [← hurange]; exact ⟨i + 4, rfl⟩
    · exact (ConnectedComponent.mem_supp_iff b z).mpr
        (Finset.mem_filter.mp hzFirst).2
  have hdisj : ∀ z : c.supp, z ∈ a.supp → z ∈ b.supp → False := by
    intro z hza hzb
    apply hab
    rw [← (ConnectedComponent.mem_supp_iff a z).mp hza,
      ← (ConnectedComponent.mem_supp_iff b z).mp hzb]
  have hfinj : ∀ k : Fin 3, Function.Injective (fun q => f q k) := by
    intro k
    fin_cases k
    · rintro ⟨i, z⟩ ⟨i', z'⟩ heq
      have hi : i = i' := huinj (Subtype.ext (congrArg Prod.fst heq))
      have hz : z = z' := Subtype.ext (congrArg (fun t => t.2.2) heq)
      subst i'; subst z'; rfl
    · rintro ⟨i, z⟩ ⟨i', z'⟩ heq
      have hi4 : i + 4 = i' + 4 := huinj
        (Subtype.ext (congrArg Prod.fst heq))
      have hi : i = i' := by linear_combination hi4
      have hz : z = z' := Subtype.ext (congrArg (fun t => t.2.1) heq)
      subst i'; subst z'; rfl
    · rintro ⟨i, z⟩ ⟨i', z'⟩ heq
      have hz : z = z' := Subtype.ext (congrArg Prod.fst heq)
      have hi : i = i' := huinj
        (Subtype.ext (congrArg (fun t => t.2.1) heq))
      subst i'; subst z'; rfl
  have hinj : Set.InjOn (fun p => f p.1 p.2)
      (↑(T.product (Finset.univ : Finset (Fin 3))) :
        Set ((Σ _ : ZMod 8, c.supp) × Fin 3)) := by
    rintro ⟨q, k⟩ hp ⟨q', k'⟩ hp' heq
    have hq := (Finset.mem_product.mp hp).1
    have hq' := (Finset.mem_product.mp hp').1
    have hs := hshores q hq
    have hs' := hshores q' hq'
    fin_cases k <;> fin_cases k'
    · exact congrArg (fun q => (q, (0 : Fin 3))) (hfinj 0 heq)
    · exact False.elim (hdisj (u (q.1 + 4)) hs.2.1
        ((Subtype.ext (congrArg (fun t => t.2.1) heq)) ▸ hs'.2.2))
    · exact False.elim (hdisj (u q.1) hs.1
        ((Subtype.ext (congrArg Prod.fst heq)) ▸ hs'.2.2))
    · exact False.elim (hdisj (u (q'.1 + 4)) hs'.2.1
        ((Subtype.ext (congrArg (fun t => t.2.1) heq)).symm ▸ hs.2.2))
    · exact congrArg (fun q => (q, (1 : Fin 3))) (hfinj 1 heq)
    · exact False.elim (hdisj (u (q.1 + 4)) hs.2.1
        ((Subtype.ext (congrArg Prod.fst heq)) ▸ hs'.2.2))
    · exact False.elim (hdisj (u q'.1) hs'.1
        ((Subtype.ext (congrArg Prod.fst heq)).symm ▸ hs.2.2))
    · exact False.elim (hdisj (u q.1) hs.1
        ((Subtype.ext (congrArg (fun t => t.2.1) heq)) ▸ hs'.2.2))
    · exact congrArg (fun q => (q, (2 : Fin 3))) (hfinj 2 heq)
  have hcardle := Finset.card_le_card_of_injOn
    (fun p : (Σ _ : ZMod 8, c.supp) × Fin 3 => f p.1 p.2) hmaps hinj
  have htrace := trace_three_adjMatrices_eq_card_cyclicColoredTriples
    (antipodalGraph G) (antipodalGraph G) (antipodalGraph G)
  rw [htrace]
  have hprod : 96 ≤ (T.product (Finset.univ : Finset (Fin 3))).card := by
    have hmul := Nat.mul_le_mul_right 3 hTcard
    simpa using hmul
  exact_mod_cast hprod.trans hcardle

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_antipodalCubeTrace_ge_ninetySix
