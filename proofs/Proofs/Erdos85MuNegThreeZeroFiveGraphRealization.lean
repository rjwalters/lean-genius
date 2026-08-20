import Proofs.Erdos85MuNegThreeZeroFiveCrossCountFields
import Proofs.Erdos85MuNegOneOneFourGraphC4Intertwine

/-! # Graph realization of the h305 owner semantics -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option linter.unusedSectionVars false

private theorem rowZero_exactOpp_count
    {uTri vTri sigma : Bool} {D X : Nat → Nat → Bool}
    (hopp : ∀ i, i < 8 →
      (((List.range 8).filter fun j =>
        !(muNegOneSign sigma i == muNegOneSign sigma (8 + j))).countP
          fun j => D i j) = 3) :
    (if sigma then
      [muNegOneValOfRelations uTri vTri D X 1,
       muNegOneValOfRelations uTri vTri D X 3,
       muNegOneValOfRelations uTri vTri D X 5,
       muNegOneValOfRelations uTri vTri D X 7]
    else
      [muNegOneValOfRelations uTri vTri D X 2,
       muNegOneValOfRelations uTri vTri D X 4,
       muNegOneValOfRelations uTri vTri D X 6,
       muNegOneValOfRelations uTri vTri D X 8]).count true = 3 := by
  have h := hopp 0 (by omega)
  cases sigma with
  | false =>
      have hv2 : muNegOneValOfRelations uTri vTri D X 2 = D 0 1 :=
        muNegOneValOfRelations_dvar uTri vTri D X
          (i := 0) (j := 1) (by omega) (by omega)
      have hv4 : muNegOneValOfRelations uTri vTri D X 4 = D 0 3 :=
        muNegOneValOfRelations_dvar uTri vTri D X
          (i := 0) (j := 3) (by omega) (by omega)
      have hv6 : muNegOneValOfRelations uTri vTri D X 6 = D 0 5 :=
        muNegOneValOfRelations_dvar uTri vTri D X
          (i := 0) (j := 5) (by omega) (by omega)
      have hv8 : muNegOneValOfRelations uTri vTri D X 8 = D 0 7 :=
        muNegOneValOfRelations_dvar uTri vTri D X
          (i := 0) (j := 7) (by omega) (by omega)
      simp only [Bool.false_eq_true, if_false, hv2, hv4, hv6, hv8]
      have hfilter : ((List.range 8).filter fun j =>
          !(muNegOneSign false 0 == muNegOneSign false (8 + j))) =
          [1, 3, 5, 7] := by decide
      rw [hfilter] at h
      change List.countP (fun j => D 0 j) [1, 3, 5, 7] = 3 at h
      simp only [List.countP_cons, List.countP_nil] at h
      simp only [List.count_cons, List.count_nil]
      simpa using h
  | true =>
      have hv1 : muNegOneValOfRelations uTri vTri D X 1 = D 0 0 :=
        muNegOneValOfRelations_dvar uTri vTri D X
          (i := 0) (j := 0) (by omega) (by omega)
      have hv3 : muNegOneValOfRelations uTri vTri D X 3 = D 0 2 :=
        muNegOneValOfRelations_dvar uTri vTri D X
          (i := 0) (j := 2) (by omega) (by omega)
      have hv5 : muNegOneValOfRelations uTri vTri D X 5 = D 0 4 :=
        muNegOneValOfRelations_dvar uTri vTri D X
          (i := 0) (j := 4) (by omega) (by omega)
      have hv7 : muNegOneValOfRelations uTri vTri D X 7 = D 0 6 :=
        muNegOneValOfRelations_dvar uTri vTri D X
          (i := 0) (j := 6) (by omega) (by omega)
      simp only [if_true, hv1, hv3, hv5, hv7]
      have hfilter : ((List.range 8).filter fun j =>
          !(muNegOneSign true 0 == muNegOneSign true (8 + j))) =
          [0, 2, 4, 6] := by decide
      rw [hfilter] at h
      change List.countP (fun j => D 0 j) [0, 2, 4, 6] = 3 at h
      simp only [List.countP_cons, List.countP_nil] at h
      simp only [List.count_cons, List.count_nil]
      simpa using h

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)
  [DecidableEq (G.induce c.supp).ConnectedComponent]

theorem muNegThreeZeroFive_graph_false_of_exterior
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8) (hcard : Fintype.card V = 8 * 8)
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (su sv : ZMod 8 → ℤ)
    (hsu : ∀ i, su i = -1 ∨ su i = 1)
    (hsv : ∀ j, sv j = -1 ∨ sv j = 1)
    (hflipu : ∀ i, su (i + 1) = -su i)
    (hflipv : ∀ j, sv (j + 1) = -sv j)
    (hcross : MuNegThreeZeroFiveCrossExteriorSplit
      (exteriorPairGraph G c.supp) u v su sv)
    (uTri vTri : Bool)
    (hcanon : (uTri = false ∧ vTri = false) ∨
      (uTri = false ∧ vTri = true) ∨ (uTri = true ∧ vTri = true))
    (hmodeu : if uTri then
        MuNegOneOneFourTriangleShoreMode (exteriorPairGraph G c.supp) u
      else MuNegOneOneFourTfShoreMode (exteriorPairGraph G c.supp) u)
    (hmodev : if vTri then
        MuNegOneOneFourTriangleShoreMode (exteriorPairGraph G c.supp) v
      else MuNegOneOneFourTfShoreMode (exteriorPairGraph G c.supp) v) :
    False := by
  let sigma := muNegOneSigmaOf su sv
  let D := muNegOneDGraph G c u v
  let X := muNegOneXGraph G c u v uTri vTri
  have hphase := zmodEight_two_alternating_sign_phase_routing su sv
    hsu hsv hflipu hflipv
  obtain ⟨hrowSame, hrowOpp, hcolSame, hcolOpp⟩ :=
    muNegThreeZeroFive_crossDefect_count_fields
      (exteriorPairGraph G c.supp) u v su sv hsu hsv hphase hcross
  have hnonCross : MuNegThreeZeroFiveNonCrossSemantics
      uTri vTri sigma D X := {
    intertwine := muNegOne_intertwine_graph G c u v hfree hreg
      a b hab huinj hvinj hurange hvrange hu hv
    hit_active := muNegOne_hit_active_graph G c u v uTri vTri
      a b hab hurange hvrange
    service_exists := muNegOne_service_exists_graph G c u v uTri vTri
      hfree hreg hcard hc a b hab huinj hvinj hurange hvrange hu hv
      hmodeu hmodev
    service_unique := muNegOne_service_unique_graph G c u v uTri vTri
      hfree hreg hcard hc a b hab huinj hvinj hurange hvrange
      hmodeu hmodev
    c4_intersecting := muNegOne_c4_intersecting_graph G c u v uTri vTri
      hfree hreg hcard hc a b hab huinj hvinj hurange hvrange
    c4_no_two := muNegOne_c4_no_two_graph G c u v uTri vTri
      hfree hreg hcard hc a b hab huinj hvinj hurange hvrange }
  apply muNegThreeZeroFiveOwnerConstraintSemantics_false' hcanon
    (muNegThreeZeroFiveOwnerConstraintSemantics_of_finite
      hrowSame hrowOpp hcolSame hcolOpp hnonCross)
  exact rowZero_exactOpp_count hrowOpp

end

end Erdos85

#print axioms Erdos85.muNegThreeZeroFive_graph_false_of_exterior
