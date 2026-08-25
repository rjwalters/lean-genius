import Proofs.Erdos85MuNegThreeZeroFiveCorrectServerClassification
import Proofs.Erdos85MuNegThreeZeroFiveCorrectGraphC4

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option linter.unusedSectionVars false

private theorem twelve_mem_lt (p : Nat × Nat) {w : Nat}
    (hw : w ∈ muNegOneTwelve p) : w < 16 := by
  unfold muNegOneTwelve at hw
  exact List.mem_range.mp (List.mem_of_mem_filter hw)

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)
  [DecidableEq (G.induce c.supp).ConnectedComponent]

section Service

variable (u v : ZMod 8 → c.supp) (uTri vTri : Bool)

theorem muNegThreeZeroFiveCorrect_service_exists_graph
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8) (hcard : Fintype.card V = 8 * 8)
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (hmodeu : if uTri then
        MuNegThreeZeroFiveTriangleShoreMode (exteriorPairGraph G c.supp) u
      else MuNegThreeZeroFiveTfShoreMode (exteriorPairGraph G c.supp) u)
    (hmodev : if vTri then
        MuNegThreeZeroFiveTriangleShoreMode (exteriorPairGraph G c.supp) v
      else MuNegThreeZeroFiveTfShoreMode (exteriorPairGraph G c.supp) v) :
    ∀ aa, aa < 88 →
      muNegThreeZeroFiveCorrectOwnerActive uTri vTri
        (muNegThreeZeroFiveCorrectDGraph G c u v) aa = true →
      ∀ w ∈ muNegOneTwelve ((muNegThreeZeroFiveCorrectOwners uTri vTri)[aa]!),
        ∃ bb, bb < 88 ∧ bb ≠ aa ∧
          muNegOnePairMem ((muNegThreeZeroFiveCorrectOwners uTri vTri)[bb]!) w = true ∧
          (min aa bb, max aa bb) ∈ muNegThreeZeroFiveCorrectHitPairs uTri vTri ∧
          muNegThreeZeroFiveCorrectXGraph G c u v uTri vTri (min aa bb) (max aa bb) = true := by
  intro aa haa hact w hw
  have hw16 : w < 16 := twelve_mem_lt _ hw
  rw [muNegThreeZeroFiveCorrectOwners_getElem! uTri vTri ⟨aa, haa⟩] at hw
  have hcont : (muNegOneTwelve
      (muNegThreeZeroFiveCorrectOwnerAt uTri vTri ⟨aa, haa⟩)).contains w = true := by
    rw [List.contains_eq_mem]
    exact decide_eq_true hw
  obtain ⟨te, hte, _⟩ := muNegThreeZeroFiveCorrect_ownerVertex_of_active G c u v uTri vTri
    hfree hmodeu hmodev (e := ⟨aa, haa⟩) hact
  obtain ⟨f, hfne, tf, htf, hadj, hpm⟩ := muNegThreeZeroFiveCorrect_server_classification
    G c hfree hreg hcard hc a b hab u v huinj hvinj hurange hvrange
    hu hv uTri vTri hmodeu hmodev hte hw16 hcont
  have hpm' : muNegOnePairMem
      ((muNegThreeZeroFiveCorrectOwners uTri vTri)[f.val]!) w = true := by
    rw [muNegThreeZeroFiveCorrectOwners_getElem! uTri vTri f]
    exact hpm
  refine ⟨f.val, f.2, ?_, hpm', ?_, ?_⟩
  · intro h
    exact hfne (Fin.ext h)
  · rcases Nat.lt_or_ge aa f.val with hlt | hge
    · rw [Nat.min_eq_left (Nat.le_of_lt hlt),
        Nat.max_eq_right (Nat.le_of_lt hlt)]
      exact mem_muNegThreeZeroFiveCorrectHitPairs_of_ownerVertices_adj G c u v uTri vTri
        hfree a b hab huinj hvinj hurange hvrange hu hv
        (e := ⟨aa, haa⟩) (f := f) hlt hte htf hadj
    · have hlt : f.val < aa := by
        have hne : f.val ≠ aa := fun h => hfne (Fin.ext h)
        omega
      rw [Nat.min_eq_right (Nat.le_of_lt hlt),
        Nat.max_eq_left (Nat.le_of_lt hlt)]
      exact mem_muNegThreeZeroFiveCorrectHitPairs_of_ownerVertices_adj G c u v uTri vTri
        hfree a b hab huinj hvinj hurange hvrange hu hv
        (e := f) (f := ⟨aa, haa⟩) hlt htf hte hadj.symm
  · rcases Nat.lt_or_ge aa f.val with hlt | hge
    · rw [Nat.min_eq_left (Nat.le_of_lt hlt),
        Nat.max_eq_right (Nat.le_of_lt hlt)]
      rw [muNegThreeZeroFiveCorrectXGraph_true_iff]
      exact ⟨haa, f.2, te, tf, hte, htf, hadj⟩
    · have hlt : f.val < aa := by
        have hne : f.val ≠ aa := fun h => hfne (Fin.ext h)
        omega
      rw [Nat.min_eq_right (Nat.le_of_lt hlt),
        Nat.max_eq_left (Nat.le_of_lt hlt)]
      rw [muNegThreeZeroFiveCorrectXGraph_true_iff]
      exact ⟨f.2, haa, tf, te, htf, hte, hadj.symm⟩

/-- Extract an adjacency between the owner vertices of the two indices
of a true hit variable, oriented to the given order. -/
theorem muNegThreeZeroFiveCorrect_service_unique_graph
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8) (hcard : Fintype.card V = 8 * 8)
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hmodeu : if uTri then
        MuNegThreeZeroFiveTriangleShoreMode (exteriorPairGraph G c.supp) u
      else MuNegThreeZeroFiveTfShoreMode (exteriorPairGraph G c.supp) u)
    (hmodev : if vTri then
        MuNegThreeZeroFiveTriangleShoreMode (exteriorPairGraph G c.supp) v
      else MuNegThreeZeroFiveTfShoreMode (exteriorPairGraph G c.supp) v) :
    ∀ aa, aa < 88 →
      muNegThreeZeroFiveCorrectOwnerActive uTri vTri
        (muNegThreeZeroFiveCorrectDGraph G c u v) aa = true →
      ∀ w ∈ muNegOneTwelve ((muNegThreeZeroFiveCorrectOwners uTri vTri)[aa]!),
      ∀ bb cc, bb < 88 → bb ≠ aa →
        muNegOnePairMem ((muNegThreeZeroFiveCorrectOwners uTri vTri)[bb]!) w = true →
        (min aa bb, max aa bb) ∈ muNegThreeZeroFiveCorrectHitPairs uTri vTri →
        muNegThreeZeroFiveCorrectXGraph G c u v uTri vTri (min aa bb) (max aa bb) = true →
        cc < 88 → cc ≠ aa →
        muNegOnePairMem ((muNegThreeZeroFiveCorrectOwners uTri vTri)[cc]!) w = true →
        (min aa cc, max aa cc) ∈ muNegThreeZeroFiveCorrectHitPairs uTri vTri →
        muNegThreeZeroFiveCorrectXGraph G c u v uTri vTri (min aa cc) (max aa cc) = true →
        bb = cc := by
  intro aa haa hact w hw bb cc hbb hbne hpmb _ hXb hcc hcne hpmc _ hXc
  have hw16 : w < 16 := twelve_mem_lt _ hw
  rw [muNegThreeZeroFiveCorrectOwners_getElem! uTri vTri ⟨bb, hbb⟩] at hpmb
  rw [muNegThreeZeroFiveCorrectOwners_getElem! uTri vTri ⟨cc, hcc⟩] at hpmc
  obtain ⟨te, hte, _⟩ := muNegThreeZeroFiveCorrect_ownerVertex_of_active G c u v uTri vTri
    hfree hmodeu hmodev (e := ⟨aa, haa⟩) hact
  obtain ⟨tb, htb, hteb⟩ := muNegThreeZeroFiveCorrectXGraph_extract G c u v uTri vTri
    hfree a b hab huinj hvinj hurange hvrange haa hbb hXb hte
  obtain ⟨tc, htc, htec⟩ := muNegThreeZeroFiveCorrectXGraph_extract G c u v uTri vTri
    hfree a b hab huinj hvinj hurange hvrange haa hcc hXc hte
  -- both servers are common neighbors of the source vertex and target.
  have hbw : G.Adj tb (muNegOneCodeVertex G c u v w) :=
    muNegThreeZeroFiveCorrect_ownerVertex_adj_target G c u v uTri vTri htb hpmb
  have hcw : G.Adj tc (muNegOneCodeVertex G c u v w) :=
    muNegThreeZeroFiveCorrect_ownerVertex_adj_target G c u v uTri vTri htc hpmc
  have hne : te ≠ muNegOneCodeVertex G c u v w := by
    intro h
    apply hte.1
    rw [h]
    exact muNegOneCodeVertex_mem_supp G c u v w
  have hbc : tb = tc := commonServer_unique G hfree hne
    hteb hbw.symm htec hcw.symm
  subst hbc
  have := muNegThreeZeroFiveCorrectOwnerVertex_inj G c u v uTri vTri hfree
    (q := 8) (by omega) hreg hcard hc a b hab huinj hvinj
    hurange hvrange htb htc
  exact congrArg Fin.val this

end Service

end

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveCorrect_service_exists_graph
#print axioms Erdos85.muNegThreeZeroFiveCorrect_service_unique_graph
