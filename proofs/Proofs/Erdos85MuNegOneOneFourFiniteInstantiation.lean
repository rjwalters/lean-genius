import Proofs.Erdos85MuNegOneOneFourGraphC4Intertwine
import Proofs.Erdos85MuNegOneOneFourCrossCountFields
import Proofs.Erdos85MuNegOneOneFourEnrichedCapstone

/-!
# Finite-semantics instantiation for the μ=-1 `(1,4)` cell

Node: outline F.3 (bridge increment 3c-iii — the h114 closure; squad
msg 14123).

Assembles the eleven banked field proofs into the finite-semantics
record for the concrete graph relations and routes the two shore-model
disjunctions through the canonical mode triple, swapping shores for the
reverse mixed orientation.  Composed with the checked certificates this
eliminates the complete exterior geometry of the `(−1,1,4)` self cell.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)
  [DecidableEq (G.induce c.supp).ConnectedComponent]

/-- **Record assembly.**  The concrete relations satisfy all eleven
finite-semantics fields under canonical shore modes. -/
theorem muNegOneOneFour_finiteSemantics_graph
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
    (hcross : MuNegOneOneFourCrossExteriorSplit
      (exteriorPairGraph G c.supp) u v su sv)
    (uTri vTri : Bool)
    (hmodeu : if uTri then
        MuNegOneOneFourTriangleShoreMode (exteriorPairGraph G c.supp) u
      else MuNegOneOneFourTfShoreMode (exteriorPairGraph G c.supp) u)
    (hmodev : if vTri then
        MuNegOneOneFourTriangleShoreMode (exteriorPairGraph G c.supp) v
      else MuNegOneOneFourTfShoreMode (exteriorPairGraph G c.supp) v) :
    MuNegOneOneFourFiniteSemantics uTri vTri (muNegOneSigmaOf su sv)
      (muNegOneDGraph G c u v) (muNegOneXGraph G c u v uTri vTri) := by
  have hphase := zmodEight_two_alternating_sign_phase_routing su sv
    hsu hsv hflipu hflipv
  have hcounts := muNegOneOneFour_crossDefect_count_fields
    (exteriorPairGraph G c.supp) u v su sv hsu hsv hphase hcross
  obtain ⟨h1, h2, h3, h4⟩ := hcounts
  exact {
    row_same_two := h1
    row_opp_two := h2
    col_same_two := h3
    col_opp_two := h4
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

/-- **Canonical-mode elimination.** -/
theorem muNegOneOneFour_graph_false_of_canonical
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
    (hcross : MuNegOneOneFourCrossExteriorSplit
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
    False :=
  muNegOneOneFourFiniteSemantics_false hcanon
    (muNegOneOneFour_finiteSemantics_graph G c hfree hreg hcard hc
      a b hab u v huinj hvinj hurange hvrange hu hv su sv
      hsu hsv hflipu hflipv hcross uTri vTri hmodeu hmodev)

/-- **The h114 graph elimination.**  The complete exterior geometry of
the `(−1,1,4)` self cell is impossible: both shore models, the signed
cross split, and alternating `±1` sign lines contradict the checked
owner certificates in every mode orientation. -/
theorem muNegOneOneFour_graph_false
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
    (hgeom : MuNegOneOneFourShoreExteriorModel
        (exteriorPairGraph G c.supp) u ∧
      MuNegOneOneFourShoreExteriorModel (exteriorPairGraph G c.supp) v ∧
      MuNegOneOneFourCrossExteriorSplit
        (exteriorPairGraph G c.supp) u v su sv) :
    False := by
  obtain ⟨hmu, hmv, hcross⟩ := hgeom
  rcases hmu with hmu | hmu <;> rcases hmv with hmv | hmv
  · -- TF / TF.
    exact muNegOneOneFour_graph_false_of_canonical G c hfree hreg hcard
      hc a b hab u v huinj hvinj hurange hvrange hu hv su sv
      hsu hsv hflipu hflipv hcross false false
      (Or.inl ⟨rfl, rfl⟩) hmu hmv
  · -- TF / triangle.
    exact muNegOneOneFour_graph_false_of_canonical G c hfree hreg hcard
      hc a b hab u v huinj hvinj hurange hvrange hu hv su sv
      hsu hsv hflipu hflipv hcross false true
      (Or.inr (Or.inl ⟨rfl, rfl⟩)) hmu hmv
  · -- triangle / TF: swap the shores.
    exact muNegOneOneFour_graph_false_of_canonical G c hfree hreg hcard
      hc b a hab.symm v u hvinj huinj hvrange hurange hv hu sv su
      hsv hsu hflipv hflipu
      ((muNegOneOneFour_crossExteriorSplit_swap
        (exteriorPairGraph G c.supp) u v su sv).mp hcross)
      false true (Or.inr (Or.inl ⟨rfl, rfl⟩)) hmv hmu
  · -- triangle / triangle.
    exact muNegOneOneFour_graph_false_of_canonical G c hfree hreg hcard
      hc a b hab u v huinj hvinj hurange hvrange hu hv su sv
      hsu hsv hflipu hflipv hcross true true
      (Or.inr (Or.inr ⟨rfl, rfl⟩)) hmu hmv

end

end Erdos85

#print axioms Erdos85.muNegOneOneFour_finiteSemantics_graph
#print axioms Erdos85.muNegOneOneFour_graph_false
