import Proofs.Erdos85SizeTwoEigenlineEightEightHighAntipodalTraceSharp

/-!
# Tagged two-shore rotation patterns for the high eight-plus-eight trace

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The two shores and three cyclic rotations give six distinct membership
patterns with respect to the first internal component.  This finite kernel
lemma is the injectivity discriminator for combining both 96-contributions
into a single 192-term antipodal trace census.
-/

namespace Erdos85

/-- Membership in the first shore at each of the three tuple positions.
`false` tags a base with two first-shore vertices; `true` tags a base with
one first-shore vertex. -/
def eightEightTwoShoreRotationPattern
    (shore : Bool) (rotation position : Fin 3) : Bool :=
  if shore then
    ![![false, false, true], ![false, true, false], ![true, false, false]]
      rotation position
  else
    ![![true, true, false], ![true, false, true], ![false, true, true]]
      rotation position

/-- The shore tag and cyclic rotation are recovered uniquely from their
three-position shore-membership pattern. -/
theorem eightEightTwoShoreRotationPattern_injective :
    Function.Injective (fun p : Bool × Fin 3 =>
      fun position => eightEightTwoShoreRotationPattern p.1 p.2 position) := by
  intro p q hpq
  have hp0 := congrFun hpq 0
  have hp1 := congrFun hpq 1
  have hp2 := congrFun hpq 2
  revert p q
  decide

open Finset SimpleGraph

noncomputable section

/-- Combining both high-sector shores and all three cyclic rotations gives
the sharp structural lower bound `192 ≤ tr(C³)`. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_antipodalCubeTrace_ge_oneNinetyTwo
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
    (192 : ℤ) ≤ Matrix.trace
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
  let g : (Σ _ : Bool × ZMod 8, c.supp) → Fin 3 →
      c.supp × c.supp × c.supp := fun q k =>
    if q.1.1 then
      ![(v q.1.2, v (q.1.2 + 4), q.2),
        (v (q.1.2 + 4), q.2, v q.1.2),
        (q.2, v q.1.2, v (q.1.2 + 4))] k
    else
      ![(u q.1.2, u (q.1.2 + 4), q.2),
        (u (q.1.2 + 4), q.2, u q.1.2),
        (q.2, u q.1.2, u (q.1.2 + 4))] k
  let f : (Σ _ : Bool × ZMod 8, c.supp) → Fin 3 → V × V × V := fun q k =>
    ((g q k).1.1, (g q k).2.1, (g q k).2.2.1)
  let coord : (c.supp × c.supp × c.supp) → Fin 3 → c.supp := fun t position =>
    ![t.1, t.2.1, t.2.2] position
  have hbase : ∀ q ∈ T,
      f q 0 ∈ cyclicColoredTriples
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
        true_and, f, g, Bool.false_eq_true, ↓reduceIte, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two]
      exact ⟨hz.1, hz.2.symm, htri.1.symm⟩
    · have htri :=
        binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_firstCycle_four_antipodalTriangles
          G hfree hreg hcard c hc s hs_in hs_out hA_in hDs b a hb ha hab.symm
            v u hvinj huinj hvrange hurange hv hu hba6 i
      have hz := htri.2.2 z (by simpa [F, K, H] using hzF)
      simp only [cyclicColoredTriples, Finset.mem_filter, Finset.mem_univ,
        true_and, f, g, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two]
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
    · rcases q with ⟨⟨flag, i⟩, z⟩
      cases flag <;> exact ⟨h₃, h₁, h₂⟩
    · rcases q with ⟨⟨flag, i⟩, z⟩
      cases flag <;> exact ⟨h₂, h₃, h₁⟩
  have hua (i : ZMod 8) : u i ∈ a.supp := by
    rw [← hurange]; exact ⟨i, rfl⟩
  have hvb (i : ZMod 8) : v i ∈ b.supp := by
    rw [← hvrange]; exact ⟨i, rfl⟩
  have hdisj : ∀ z : c.supp, z ∈ a.supp → z ∈ b.supp → False := by
    intro z hza hzb
    apply hab
    rw [← (ConnectedComponent.mem_supp_iff a z).mp hza,
      ← (ConnectedComponent.mem_supp_iff b z).mp hzb]
  let isA : c.supp → Bool := fun z => decide (z ∈ a.supp)
  have huaMk (i : ZMod 8) : H.connectedComponentMk (u i) = a :=
    (ConnectedComponent.mem_supp_iff a (u i)).mp (hua i)
  have hvbMk (i : ZMod 8) : H.connectedComponentMk (v i) = b :=
    (ConnectedComponent.mem_supp_iff b (v i)).mp (hvb i)
  have huNotB (i : ZMod 8) : ¬ u i ∈ b.supp := fun h => hdisj (u i) (hua i) h
  have hvNotA (i : ZMod 8) : ¬ v i ∈ a.supp := fun h => hdisj (v i) h (hvb i)
  have hvNotAMk (i : ZMod 8) : H.connectedComponentMk (v i) ≠ a := fun h =>
    hvNotA i ((ConnectedComponent.mem_supp_iff a (v i)).mpr h)
  have hpattern : ∀ q ∈ T, ∀ k position,
      isA (coord (g q k) position) =
        eightEightTwoShoreRotationPattern q.1.1 k position := by
    rintro ⟨⟨flag, i⟩, z⟩ hq k position
    have hzF := (Finset.mem_sigma.mp hq).2
    have hzFalse : flag = false → z ∈ b.supp := by
      intro hf
      subst flag
      change z ∈ componentNeighborFinset K H b (u i) ∩
        componentNeighborFinset K H b (u (i + 4)) at hzF
      exact (ConnectedComponent.mem_supp_iff b z).mpr
        (Finset.mem_filter.mp (Finset.mem_inter.mp hzF).1).2
    have hzTrue : flag = true → z ∈ a.supp := by
      intro hf
      subst flag
      change z ∈ componentNeighborFinset K H a (v i) ∩
        componentNeighborFinset K H a (v (i + 4)) at hzF
      exact (ConnectedComponent.mem_supp_iff a z).mpr
        (Finset.mem_filter.mp (Finset.mem_inter.mp hzF).1).2
    have hzFalseNotAMk : flag = false → H.connectedComponentMk z ≠ a := by
      intro hf hza
      exact hdisj z ((ConnectedComponent.mem_supp_iff a z).mpr hza) (hzFalse hf)
    have hzTrueMk : flag = true → H.connectedComponentMk z = a := fun hf =>
      (ConnectedComponent.mem_supp_iff a z).mp (hzTrue hf)
    fin_cases k <;> fin_cases position <;> cases flag <;>
      simp [H, isA, coord, g, eightEightTwoShoreRotationPattern, huaMk,
        hvNotAMk, hzFalseNotAMk, hzTrueMk]
  have hinj : Set.InjOn (fun p => f p.1 p.2)
      (↑(T.product (Finset.univ : Finset (Fin 3))) :
        Set ((Σ _ : Bool × ZMod 8, c.supp) × Fin 3)) := by
    rintro ⟨q, k⟩ hp ⟨q', k'⟩ hp' heq
    have hq := (Finset.mem_product.mp hp).1
    have hq' := (Finset.mem_product.mp hp').1
    have hgEq : g q k = g q' k' := by
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst heq)
      · apply Prod.ext
        · exact Subtype.ext (congrArg (fun t => t.2.1) heq)
        · exact Subtype.ext (congrArg (fun t => t.2.2) heq)
    have hpatt : (q.1.1, k) = (q'.1.1, k') := by
      apply eightEightTwoShoreRotationPattern_injective
      funext position
      change eightEightTwoShoreRotationPattern q.1.1 k position =
        eightEightTwoShoreRotationPattern q'.1.1 k' position
      rw [← hpattern q hq k position, ← hpattern q' hq' k' position]
      exact congrArg (fun t => isA (coord t position)) hgEq
    rcases q with ⟨⟨flag, i⟩, z⟩
    rcases q' with ⟨⟨flag', i'⟩, z'⟩
    have hflag : flag = flag' := congrArg Prod.fst hpatt
    have hk : k = k' := congrArg Prod.snd hpatt
    subst flag'
    subst k'
    cases flag <;> fin_cases k
    · have hi : i = i' := huinj (congrArg Prod.fst hgEq)
      have hz : z = z' := congrArg (fun t => t.2.2) hgEq
      subst i'; subst z'; rfl
    · have hi : i = i' := huinj (congrArg (fun t => t.2.2) hgEq)
      have hz : z = z' := congrArg (fun t => t.2.1) hgEq
      subst i'; subst z'; rfl
    · have hi : i = i' := huinj (congrArg (fun t => t.2.1) hgEq)
      have hz : z = z' := congrArg Prod.fst hgEq
      subst i'; subst z'; rfl
    · have hi : i = i' := hvinj (congrArg Prod.fst hgEq)
      have hz : z = z' := congrArg (fun t => t.2.2) hgEq
      subst i'; subst z'; rfl
    · have hi : i = i' := hvinj (congrArg (fun t => t.2.2) hgEq)
      have hz : z = z' := congrArg (fun t => t.2.1) hgEq
      subst i'; subst z'; rfl
    · have hi : i = i' := hvinj (congrArg (fun t => t.2.1) hgEq)
      have hz : z = z' := congrArg Prod.fst hgEq
      subst i'; subst z'; rfl
  have hcardle := Finset.card_le_card_of_injOn
    (fun p : (Σ _ : Bool × ZMod 8, c.supp) × Fin 3 => f p.1 p.2) hmaps hinj
  have htrace := trace_three_adjMatrices_eq_card_cyclicColoredTriples
    (antipodalGraph G) (antipodalGraph G) (antipodalGraph G)
  rw [htrace]
  have hprod : 192 ≤ (T.product (Finset.univ : Finset (Fin 3))).card := by
    have hmul := Nat.mul_le_mul_right 3 hTcard
    simpa using hmul
  exact_mod_cast hprod.trans hcardle

end

end Erdos85

#print axioms Erdos85.eightEightTwoShoreRotationPattern_injective
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_antipodalCubeTrace_ge_oneNinetyTwo
