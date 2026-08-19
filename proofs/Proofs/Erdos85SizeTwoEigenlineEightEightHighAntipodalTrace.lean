import Proofs.Erdos85SizeTwoEigenlineEightEightHighTriangleCensus
import Proofs.Erdos85BinarySquareMixedOwnerTriangleCensus

/-!
# Antipodal cube-trace lower bound in the high eight-plus-eight sector

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The two high-sector C8 shores contribute at least sixty-four distinct
rooted antipodal triples, hence `64 ≤ tr(C³)` for the antipodal adjacency
matrix. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_antipodalCubeTrace_ge_sixtyFour
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
    (64 : ℤ) ≤ Matrix.trace
      ((antipodalGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ) := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  obtain ⟨r, _hr2, _hr7, _haa, habq, hbaq, _hbb⟩ :=
    binarySquare_regular_sizeTwoPart_eight_eightEight_cycleQuotient
      G hfree hreg hcard c hc s hs_in hs_out hA_in a b ha hb hab
  have hba6 : componentQuotientMatrix K H b a = 6 := by
    have hr : r = 6 := by omega
    simpa [K, H, hr] using hbaq
  let F : Bool × ZMod 8 → Finset c.supp := fun p =>
    if p.1 then
      (componentNeighborFinset K H a (v p.2)) ∩
        componentNeighborFinset K H a (v (p.2 + 4))
    else
      (componentNeighborFinset K H b (u p.2)) ∩
        componentNeighborFinset K H b (u (p.2 + 4))
  let T := (Finset.univ : Finset (Bool × ZMod 8)).sigma F
  have hlocal : ∀ p : Bool × ZMod 8, 4 ≤ (F p).card := by
    rintro ⟨flag, i⟩
    cases flag
    · simpa [F, K, H] using
        (binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_firstCycle_four_antipodalTriangles
          G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb hab
            u v huinj hvinj hurange hvrange hu hv hab6 i).2.1
    · simpa [F, K, H] using
        (binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_firstCycle_four_antipodalTriangles
          G hfree hreg hcard c hc s hs_in hs_out hA_in hDs b a hb ha hab.symm
            v u hvinj huinj hvrange hurange hv hu hba6 i).2.1
  have hTcard : 64 ≤ T.card := by
    have hsum : 64 ≤ ∑ p : Bool × ZMod 8, (F p).card := by
      calc
        64 = ∑ _p : Bool × ZMod 8, 4 := by
          norm_num [Finset.sum_const, Nat.card_zmod]
        _ ≤ ∑ p : Bool × ZMod 8, (F p).card :=
          Finset.sum_le_sum fun p _ => hlocal p
    simpa [T] using hsum
  let f : (Σ _ : Bool × ZMod 8, c.supp) → V × V × V := fun q =>
    if q.1.1 then
      ((v q.1.2).1, (v (q.1.2 + 4)).1, q.2.1)
    else
      ((u q.1.2).1, (u (q.1.2 + 4)).1, q.2.1)
  have hmaps : ∀ q ∈ T,
      f q ∈ cyclicColoredTriples
        (antipodalGraph G) (antipodalGraph G) (antipodalGraph G) := by
    rintro ⟨⟨flag, i⟩, z⟩ hq
    have hzF := (Finset.mem_sigma.mp hq).2
    cases flag
    · have htri :=
        binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_firstCycle_four_antipodalTriangles
          G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb hab
            u v huinj hvinj hurange hvrange hu hv hab6 i
      have hz := htri.2.2 z (by simpa [F, K, H] using hzF)
      simp only [cyclicColoredTriples, Finset.mem_filter, Finset.mem_univ,
        true_and, f, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hz.1, hz.2.symm, htri.1.symm⟩
    · have htri :=
        binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_firstCycle_four_antipodalTriangles
          G hfree hreg hcard c hc s hs_in hs_out hA_in hDs b a hb ha hab.symm
            v u hvinj huinj hvrange hurange hv hu hba6 i
      have hz := htri.2.2 z (by simpa [F, K, H] using hzF)
      simp only [cyclicColoredTriples, Finset.mem_filter, Finset.mem_univ,
        true_and, f, ↓reduceIte]
      exact ⟨hz.1, hz.2.symm, htri.1.symm⟩
  have huv_ne : ∀ i j, u i ≠ v j := by
    intro i j heq
    have hua : u i ∈ a.supp := by rw [← hurange]; exact ⟨i, rfl⟩
    have hvb : v j ∈ b.supp := by rw [← hvrange]; exact ⟨j, rfl⟩
    have heqComp : a = b := by
      rw [← (ConnectedComponent.mem_supp_iff a (u i)).mp hua,
        ← (ConnectedComponent.mem_supp_iff b (v j)).mp hvb, heq]
    exact hab heqComp
  have hinj : Set.InjOn f (↑T : Set (Σ _ : Bool × ZMod 8, c.supp)) := by
    rintro ⟨⟨flag, i⟩, z⟩ _ ⟨⟨flag', i'⟩, z'⟩ _ heq
    cases flag <;> cases flag'
    · simp only [f, Bool.false_eq_true, ↓reduceIte] at heq
      have hi : i = i' := huinj (Subtype.ext (congrArg Prod.fst heq))
      have hz : z = z' := Subtype.ext (congrArg (fun t => t.2.2) heq)
      subst i'; subst z'; rfl
    · simp only [f, Bool.false_eq_true, ↓reduceIte] at heq
      exact False.elim (huv_ne i i' (Subtype.ext (congrArg Prod.fst heq)))
    · simp only [f, Bool.false_eq_true, ↓reduceIte] at heq
      exact False.elim (huv_ne i' i (Subtype.ext (congrArg Prod.fst heq)).symm)
    · simp only [f, ↓reduceIte] at heq
      have hi : i = i' := hvinj (Subtype.ext (congrArg Prod.fst heq))
      have hz : z = z' := Subtype.ext (congrArg (fun t => t.2.2) heq)
      subst i'; subst z'; rfl
  have hcardle : T.card ≤
      (cyclicColoredTriples
        (antipodalGraph G) (antipodalGraph G) (antipodalGraph G)).card :=
    Finset.card_le_card_of_injOn f hmaps hinj
  have htrace := trace_three_adjMatrices_eq_card_cyclicColoredTriples
    (antipodalGraph G) (antipodalGraph G) (antipodalGraph G)
  rw [htrace]
  exact_mod_cast hTcard.trans hcardle

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_antipodalCubeTrace_ge_sixtyFour
