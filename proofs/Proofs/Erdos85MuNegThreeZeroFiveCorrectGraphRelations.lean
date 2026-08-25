import Proofs.Erdos85MuNegThreeZeroFiveCorrectGraphRealization

/-! # Concrete hit relation for the honest h305 owner table -/

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

open Classical in
/-- Two corrected owners hit when their unique ambient owner vertices are
adjacent. -/
noncomputable def muNegThreeZeroFiveCorrectXGraph
    (u v : ZMod 8 → c.supp) (uTri vTri : Bool) : Nat → Nat → Bool :=
  fun aa bb ↦ decide (∃ (ha : aa < 88) (hb : bb < 88) (te tf : V),
    MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri ⟨aa, ha⟩ te ∧
    MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri ⟨bb, hb⟩ tf ∧
    G.Adj te tf)

section Laws

variable (u v : ZMod 8 → c.supp) (uTri vTri : Bool)

theorem muNegThreeZeroFiveCorrectXGraph_true_iff (aa bb : Nat) :
    muNegThreeZeroFiveCorrectXGraph G c u v uTri vTri aa bb = true ↔
      ∃ (ha : aa < 88) (hb : bb < 88) (te tf : V),
        MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri
          ⟨aa, ha⟩ te ∧
        MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri
          ⟨bb, hb⟩ tf ∧ G.Adj te tf := by
  classical
  unfold muNegThreeZeroFiveCorrectXGraph
  exact decide_eq_true_iff

/-- Extract owner vertices in a requested symmetric index order. -/
theorem muNegThreeZeroFiveCorrectXGraph_extract₂
    {aa bb : Nat} (haa : aa < 88) (hbb : bb < 88)
    (hX : muNegThreeZeroFiveCorrectXGraph G c u v uTri vTri
      (min aa bb) (max aa bb) = true) :
    ∃ ta tb : V,
      MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri
        ⟨aa, haa⟩ ta ∧
      MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri
        ⟨bb, hbb⟩ tb ∧ G.Adj ta tb := by
  rw [muNegThreeZeroFiveCorrectXGraph_true_iff] at hX
  obtain ⟨h1, h2, t1, t2, ht1, ht2, hadj⟩ := hX
  rcases Nat.le_total aa bb with hle | hle
  · have e1 : (⟨min aa bb, h1⟩ : Fin 88) = ⟨aa, haa⟩ :=
      Fin.ext (Nat.min_eq_left hle)
    have e2 : (⟨max aa bb, h2⟩ : Fin 88) = ⟨bb, hbb⟩ :=
      Fin.ext (Nat.max_eq_right hle)
    rw [e1] at ht1
    rw [e2] at ht2
    exact ⟨t1, t2, ht1, ht2, hadj⟩
  · have e1 : (⟨min aa bb, h1⟩ : Fin 88) = ⟨bb, hbb⟩ :=
      Fin.ext (Nat.min_eq_right hle)
    have e2 : (⟨max aa bb, h2⟩ : Fin 88) = ⟨aa, haa⟩ :=
      Fin.ext (Nat.max_eq_left hle)
    rw [e1] at ht1
    rw [e2] at ht2
    exact ⟨t2, t1, ht2, ht1, hadj.symm⟩

/-- Extract the partner vertex while aligning a chosen realization of the
first owner. -/
theorem muNegThreeZeroFiveCorrectXGraph_extract
    (hfree : ¬ containsC4 V G)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    {aa bb : Nat} (haa : aa < 88) (hbb : bb < 88)
    (hX : muNegThreeZeroFiveCorrectXGraph G c u v uTri vTri
      (min aa bb) (max aa bb) = true)
    {ta : V}
    (hta : MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri
      ⟨aa, haa⟩ ta) :
    ∃ tb : V,
      MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri
        ⟨bb, hbb⟩ tb ∧ G.Adj ta tb := by
  obtain ⟨ta', tb, hta', htb, hadj⟩ :=
    muNegThreeZeroFiveCorrectXGraph_extract₂ G c u v uTri vTri haa hbb hX
  have heq : ta' = ta :=
    muNegThreeZeroFiveCorrectOwnerVertex_unique G c u v uTri vTri hfree
      a b hab huinj hvinj hurange hvrange _ hta' hta
  subst heq
  exact ⟨tb, htb, hadj⟩

end Laws

end

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveCorrectXGraph_true_iff
#print axioms Erdos85.muNegThreeZeroFiveCorrectXGraph_extract
