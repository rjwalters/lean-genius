import Proofs.Erdos85MuNegThreeZeroFiveCorrectAdmissibility

/-! # C4 fields for the honest h305 graph relations -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option linter.unusedSectionVars false

private theorem pairMem_iff (p : Nat × Nat) (w : Nat) :
    muNegOnePairMem p w = true ↔ p.1 = w ∨ p.2 = w := by
  unfold muNegOnePairMem
  rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq]

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)
  [DecidableEq (G.induce c.supp).ConnectedComponent]

section Fields

variable (u v : ZMod 8 → c.supp) (uTri vTri : Bool)

theorem muNegThreeZeroFiveCorrect_ownerVertex_adj_target
    {f : Fin 88} {tf : V}
    (htf : MuNegThreeZeroFiveCorrectOwnerVertex G c u v uTri vTri f tf)
    {w : Nat}
    (hpm : muNegOnePairMem
      (muNegThreeZeroFiveCorrectOwnerAt uTri vTri f) w = true) :
    G.Adj tf (muNegOneCodeVertex G c u v w) := by
  rcases (pairMem_iff _ w).mp hpm with h | h
  · rw [← h]
    exact htf.2.1.symm
  · rw [← h]
    exact htf.2.2.symm

theorem muNegThreeZeroFiveCorrect_c4_intersecting_graph
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8) (hcard : Fintype.card V = 8 * 8)
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp) :
    ∀ aa bb gg, aa < bb → bb < 88 → gg < 88 → gg ≠ aa → gg ≠ bb →
      muNegOneShare ((muNegThreeZeroFiveCorrectOwners uTri vTri)[aa]!)
        ((muNegThreeZeroFiveCorrectOwners uTri vTri)[bb]!) = true →
      (min aa gg, max aa gg) ∈
        muNegThreeZeroFiveCorrectHitPairs uTri vTri →
      (min bb gg, max bb gg) ∈
        muNegThreeZeroFiveCorrectHitPairs uTri vTri →
      muNegThreeZeroFiveCorrectXGraph G c u v uTri vTri
        (min aa gg) (max aa gg) = true →
      muNegThreeZeroFiveCorrectXGraph G c u v uTri vTri
        (min bb gg) (max bb gg) = true → False := by
  intro aa bb gg hab' hbb hgg _ _ hshare _ _ hX1 hX2
  have haa : aa < 88 := by omega
  obtain ⟨ta, tg, hta, htg, hatg⟩ :=
    muNegThreeZeroFiveCorrectXGraph_extract₂ G c u v uTri vTri haa hgg hX1
  obtain ⟨tb, tg2, htb, htg2, hbtg⟩ :=
    muNegThreeZeroFiveCorrectXGraph_extract₂ G c u v uTri vTri hbb hgg hX2
  have htgeq : tg2 = tg :=
    muNegThreeZeroFiveCorrectOwnerVertex_unique G c u v uTri vTri hfree
      a b hab huinj hvinj hurange hvrange _ htg2 htg
  rw [htgeq] at hbtg
  have heqa : (muNegThreeZeroFiveCorrectOwners uTri vTri)[aa]! =
      muNegThreeZeroFiveCorrectOwnerAt uTri vTri ⟨aa, haa⟩ := by
    have h : aa < (muNegThreeZeroFiveCorrectOwners uTri vTri).length := by
      rw [muNegThreeZeroFiveCorrectOwners_length]
      exact haa
    rw [getElem!_pos (c := muNegThreeZeroFiveCorrectOwners uTri vTri)
      (i := aa) h]
    rfl
  have heqb : (muNegThreeZeroFiveCorrectOwners uTri vTri)[bb]! =
      muNegThreeZeroFiveCorrectOwnerAt uTri vTri ⟨bb, hbb⟩ := by
    have h : bb < (muNegThreeZeroFiveCorrectOwners uTri vTri).length := by
      rw [muNegThreeZeroFiveCorrectOwners_length]
      exact hbb
    rw [getElem!_pos (c := muNegThreeZeroFiveCorrectOwners uTri vTri)
      (i := bb) h]
    rfl
  rw [heqa, heqb] at hshare
  have hsh : ∃ s : Nat,
      muNegOnePairMem
          (muNegThreeZeroFiveCorrectOwnerAt uTri vTri ⟨aa, haa⟩) s = true ∧
      muNegOnePairMem
          (muNegThreeZeroFiveCorrectOwnerAt uTri vTri ⟨bb, hbb⟩) s = true := by
    unfold muNegOneShare at hshare
    rw [Bool.or_eq_true] at hshare
    rcases hshare with h | h
    · refine ⟨(muNegThreeZeroFiveCorrectOwnerAt
          uTri vTri ⟨aa, haa⟩).1, ?_, h⟩
      rw [pairMem_iff]
      exact Or.inl rfl
    · refine ⟨(muNegThreeZeroFiveCorrectOwnerAt
          uTri vTri ⟨aa, haa⟩).2, ?_, h⟩
      rw [pairMem_iff]
      exact Or.inr rfl
  obtain ⟨s, hsa, hsb⟩ := hsh
  have hsta : G.Adj ta (muNegOneCodeVertex G c u v s) :=
    muNegThreeZeroFiveCorrect_ownerVertex_adj_target G c u v uTri vTri
      hta hsa
  have hstb : G.Adj tb (muNegOneCodeVertex G c u v s) :=
    muNegThreeZeroFiveCorrect_ownerVertex_adj_target G c u v uTri vTri
      htb hsb
  have htanb : ta ≠ tb := by
    intro h
    subst h
    have hi := muNegThreeZeroFiveCorrectOwnerVertex_inj G c u v uTri vTri
      hfree (q := 8) (by omega) hreg hcard hc a b hab huinj hvinj
      hurange hvrange hta htb
    have hv := congrArg Fin.val hi
    simp at hv
    omega
  have heq : muNegOneCodeVertex G c u v s = tg :=
    commonServer_unique G hfree htanb hsta hstb hatg hbtg
  exact htg.1 (heq ▸ muNegOneCodeVertex_mem_supp G c u v s)

end Fields

end

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveCorrect_c4_intersecting_graph
