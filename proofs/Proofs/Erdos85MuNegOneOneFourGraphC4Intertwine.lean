import Proofs.Erdos85MuNegOneOneFourGraphService

/-!
# C4 and intertwining fields for the μ=-1 `(1,4)` finite semantics

Node: outline F.3 (bridge increment 3c-ii-h; squad msg 14105).

The two exterior-C4 laws collapse to common-server uniqueness through
owner-vertex alignment and injectivity, and the cross-defect
intertwining balance is the entrywise commutation of the induced defect
and cycle blocks transported through the complement decode.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option linter.unusedSectionVars false

/-- Cyclic decrement census. -/
theorem natMod_pred_cast :
    ∀ i : Fin 8, (((i.val + 7) % 8 : Nat) : ZMod 8) = (i.val : ZMod 8) - 1 := by
  decide

/-- Cyclic increment census. -/
theorem natMod_succ_cast :
    ∀ i : Fin 8, (((i.val + 1) % 8 : Nat) : ZMod 8) = (i.val : ZMod 8) + 1 := by
  decide

/-- Cycle antipode distinctness. -/
theorem zmodEight_pred_ne_succ : ∀ x : ZMod 8, x - 1 ≠ x + 1 := by
  decide

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

/-- Symmetric-order extraction from a true hit variable. -/
theorem muNegOneXGraph_extract₂
    {aa bb : Nat} (haa : aa < 80) (hbb : bb < 80)
    (hX : muNegOneXGraph G c u v uTri vTri (min aa bb) (max aa bb) = true) :
    ∃ ta tb : V, MuNegOneOwnerVertex G c u v uTri vTri ⟨aa, haa⟩ ta ∧
      MuNegOneOwnerVertex G c u v uTri vTri ⟨bb, hbb⟩ tb ∧ G.Adj ta tb := by
  rw [muNegOneXGraph_true_iff] at hX
  obtain ⟨h1, h2, t1, t2, ht1, ht2, hadj⟩ := hX
  rcases Nat.le_total aa bb with hle | hle
  · have e1 : (⟨min aa bb, h1⟩ : Fin 80) = ⟨aa, haa⟩ :=
      Fin.ext (Nat.min_eq_left hle)
    have e2 : (⟨max aa bb, h2⟩ : Fin 80) = ⟨bb, hbb⟩ :=
      Fin.ext (Nat.max_eq_right hle)
    rw [e1] at ht1
    rw [e2] at ht2
    exact ⟨t1, t2, ht1, ht2, hadj⟩
  · have e1 : (⟨min aa bb, h1⟩ : Fin 80) = ⟨bb, hbb⟩ :=
      Fin.ext (Nat.min_eq_right hle)
    have e2 : (⟨max aa bb, h2⟩ : Fin 80) = ⟨aa, haa⟩ :=
      Fin.ext (Nat.max_eq_left hle)
    rw [e1] at ht1
    rw [e2] at ht2
    exact ⟨t2, t1, ht2, ht1, hadj.symm⟩

/-- **Intersecting C4 law** for the concrete relations. -/
theorem muNegOne_c4_intersecting_graph
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8) (hcard : Fintype.card V = 8 * 8)
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp) :
    ∀ aa bb gg, aa < bb → bb < 80 → gg < 80 → gg ≠ aa → gg ≠ bb →
      muNegOneShare ((muNegOneOwners uTri vTri)[aa]!)
        ((muNegOneOwners uTri vTri)[bb]!) = true →
      (min aa gg, max aa gg) ∈ muNegOneHitPairs uTri vTri →
      (min bb gg, max bb gg) ∈ muNegOneHitPairs uTri vTri →
      muNegOneXGraph G c u v uTri vTri (min aa gg) (max aa gg) = true →
      muNegOneXGraph G c u v uTri vTri (min bb gg) (max bb gg) = true →
      False := by
  intro aa bb gg hab' hbb hgg _ _ hshare _ _ hX1 hX2
  have haa : aa < 80 := by omega
  obtain ⟨ta, tg, hta, htg, hatg⟩ := muNegOneXGraph_extract₂ G c u v
    uTri vTri haa hgg hX1
  obtain ⟨tb, tg2, htb, htg2, hbtg⟩ := muNegOneXGraph_extract₂ G c u v
    uTri vTri hbb hgg hX2
  have htgeq : tg2 = tg := muNegOneOwnerVertex_unique G c u v uTri vTri
    hfree a b hab huinj hvinj hurange hvrange _ htg2 htg
  rw [htgeq] at hbtg
  -- a shared internal endpoint of the two owners.
  have hsh : ∃ s : Nat,
      muNegOnePairMem (muNegOneOwnerAt uTri vTri ⟨aa, haa⟩) s = true ∧
      muNegOnePairMem (muNegOneOwnerAt uTri vTri ⟨bb, hbb⟩) s = true := by
    unfold muNegOneShare at hshare
    rw [Bool.or_eq_true] at hshare
    rcases hshare with h | h
    · refine ⟨(muNegOneOwnerAt uTri vTri ⟨aa, haa⟩).1, ?_, h⟩
      rw [muNegOnePairMem_iff]
      exact Or.inl rfl
    · refine ⟨(muNegOneOwnerAt uTri vTri ⟨aa, haa⟩).2, ?_, h⟩
      rw [muNegOnePairMem_iff]
      exact Or.inr rfl
  obtain ⟨s, hsa, hsb⟩ := hsh
  have hsta : G.Adj ta (muNegOneCodeVertex G c u v s) :=
    muNegOne_ownerVertex_adj_target G c u v uTri vTri hta hsa
  have hstb : G.Adj tb (muNegOneCodeVertex G c u v s) :=
    muNegOne_ownerVertex_adj_target G c u v uTri vTri htb hsb
  have htanb : ta ≠ tb := by
    intro h
    subst h
    have := muNegOneOwnerVertex_inj G c u v uTri vTri hfree
      (q := 8) (by omega) hreg hcard hc a b hab huinj hvinj
      hurange hvrange hta htb
    have := congrArg Fin.val this
    simp at this
    omega
  have heq : muNegOneCodeVertex G c u v s = tg :=
    commonServer_unique G hfree htanb hsta hstb hatg hbtg
  exact htg.1 (heq ▸ muNegOneCodeVertex_mem_supp G c u v s)

/-- **Disjoint C4 law** for the concrete relations. -/
theorem muNegOne_c4_no_two_graph
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8) (hcard : Fintype.card V = 8 * 8)
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp) :
    ∀ aa bb gg hh, aa < bb → bb < 80 → gg < 80 → hh < 80 → gg ≠ hh →
      gg ≠ aa → gg ≠ bb → hh ≠ aa → hh ≠ bb →
      muNegOneShare ((muNegOneOwners uTri vTri)[aa]!)
        ((muNegOneOwners uTri vTri)[bb]!) = false →
      (min aa gg, max aa gg) ∈ muNegOneHitPairs uTri vTri →
      (min bb gg, max bb gg) ∈ muNegOneHitPairs uTri vTri →
      (min aa hh, max aa hh) ∈ muNegOneHitPairs uTri vTri →
      (min bb hh, max bb hh) ∈ muNegOneHitPairs uTri vTri →
      muNegOneXGraph G c u v uTri vTri (min aa gg) (max aa gg) = true →
      muNegOneXGraph G c u v uTri vTri (min bb gg) (max bb gg) = true →
      muNegOneXGraph G c u v uTri vTri (min aa hh) (max aa hh) = true →
      muNegOneXGraph G c u v uTri vTri (min bb hh) (max bb hh) = true →
      False := by
  intro aa bb gg hh hab' hbb hgg hhh hgh _ _ _ _ _ _ _ _ _
    hXag hXbg hXah hXbh
  have haa : aa < 80 := by omega
  obtain ⟨ta, tg, hta, htg, hatg⟩ := muNegOneXGraph_extract₂ G c u v
    uTri vTri haa hgg hXag
  obtain ⟨tb, tg2, htb, htg2, hbtg⟩ := muNegOneXGraph_extract₂ G c u v
    uTri vTri hbb hgg hXbg
  obtain ⟨ta2, th, hta2, hth, hath⟩ := muNegOneXGraph_extract₂ G c u v
    uTri vTri haa hhh hXah
  obtain ⟨tb2, th2, htb2, hth2, hbth⟩ := muNegOneXGraph_extract₂ G c u v
    uTri vTri hbb hhh hXbh
  have e1 : tg2 = tg := muNegOneOwnerVertex_unique G c u v uTri vTri
    hfree a b hab huinj hvinj hurange hvrange _ htg2 htg
  have e2 : ta2 = ta := muNegOneOwnerVertex_unique G c u v uTri vTri
    hfree a b hab huinj hvinj hurange hvrange _ hta2 hta
  have e3 : tb2 = tb := muNegOneOwnerVertex_unique G c u v uTri vTri
    hfree a b hab huinj hvinj hurange hvrange _ htb2 htb
  have e4 : th2 = th := muNegOneOwnerVertex_unique G c u v uTri vTri
    hfree a b hab huinj hvinj hurange hvrange _ hth2 hth
  rw [e1] at hbtg
  rw [e2] at hath
  rw [e3] at hbth
  rw [e4] at hbth
  have htanb : ta ≠ tb := by
    intro h
    subst h
    have := muNegOneOwnerVertex_inj G c u v uTri vTri hfree
      (q := 8) (by omega) hreg hcard hc a b hab huinj hvinj
      hurange hvrange hta htb
    have := congrArg Fin.val this
    simp at this
    omega
  have heq : tg = th :=
    commonServer_unique G hfree htanb hatg hbtg hath hbth
  rw [heq] at htg
  have := muNegOneOwnerVertex_inj G c u v uTri vTri hfree
    (q := 8) (by omega) hreg hcard hc a b hab huinj hvinj
    hurange hvrange htg hth
  have := congrArg Fin.val this
  simp at this
  omega

/-- Complement decode: the cross-defect relation reads the induced
defect block. -/
theorem muNegOneDGraph_eq_defect
    (hfree : ¬ containsC4 V G)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (i j : Nat) :
    muNegOneDGraph G c u v i j =
      decide (((secondOrderDefectGraph G).induce c.supp).Adj
        (u (i : ZMod 8)) (v (j : ZMod 8))) := by
  unfold muNegOneDGraph
  have hiff := sizeTwo_distinctCycle_cross_exteriorPair_iff_not_defect
    G hfree c a b hab u v hurange hvrange (i : ZMod 8) (j : ZMod 8)
  rw [decide_eq_decide.mpr hiff, decide_not, Bool.not_not]

/-- **Intertwining field** for the concrete relations. -/
theorem muNegOne_intertwine_graph
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    ∀ i j, i < 8 → j < 8 →
      (cond (muNegOneDGraph G c u v ((i + 7) % 8) j) 1 0) +
        (cond (muNegOneDGraph G c u v ((i + 1) % 8) j) 1 0) =
      (cond (muNegOneDGraph G c u v i ((j + 1) % 8)) 1 0) +
        (cond (muNegOneDGraph G c u v i ((j + 7) % 8)) 1 0) := by
  intro i j hi hj
  have hcomm : ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ *
      (G.induce c.supp).adjMatrix ℤ =
      (G.induce c.supp).adjMatrix ℤ *
        ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ :=
    (adjMatrix_comm_secondOrderDefect_induce_component_of_regular
      G hfree hreg c).symm
  have hua : ∀ x : ZMod 8, u (x - 1) ≠ u (x + 1) := by
    intro x h
    exact zmodEight_pred_ne_succ x (huinj h)
  have hvb : ∀ y : ZMod 8, v (y - 1) ≠ v (y + 1) := by
    intro y h
    exact zmodEight_pred_ne_succ y (hvinj h)
  have hbal := entry_cycleIntertwine_of_adjMatrix_comm
    ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) u v 1 1
    hcomm hu hv hua hvb (i : ZMod 8) (j : ZMod 8)
  -- decode the four defect entries through the complement relation.
  have hDdec : ∀ x y : Nat,
      ((cond (muNegOneDGraph G c u v x y) 1 0 : ℕ) : ℤ) =
        ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
          (u (x : ZMod 8)) (v (y : ZMod 8)) := by
    intro x y
    rw [muNegOneDGraph_eq_defect G c u v hfree a b hab hurange hvrange]
    by_cases h : ((secondOrderDefectGraph G).induce c.supp).Adj
      (u (x : ZMod 8)) (v (y : ZMod 8))
    · have h' : (secondOrderDefectGraph G).Adj (u (x : ZMod 8)).1
          (v (y : ZMod 8)).1 := h
      rw [decide_eq_true h]
      simp [h']
    · have h' : ¬ (secondOrderDefectGraph G).Adj (u (x : ZMod 8)).1
          (v (y : ZMod 8)).1 := fun hh => h hh
      rw [decide_eq_false h]
      simp [h']
  have hcast : (((cond (muNegOneDGraph G c u v ((i + 7) % 8) j) 1 0) +
      (cond (muNegOneDGraph G c u v ((i + 1) % 8) j) 1 0) : ℕ) : ℤ) =
      (((cond (muNegOneDGraph G c u v i ((j + 1) % 8)) 1 0) +
        (cond (muNegOneDGraph G c u v i ((j + 7) % 8)) 1 0) : ℕ) : ℤ) := by
    push_cast
    rw [hDdec, hDdec, hDdec, hDdec,
      natMod_pred_cast ⟨i, hi⟩, natMod_succ_cast ⟨i, hi⟩,
      natMod_succ_cast ⟨j, hj⟩, natMod_pred_cast ⟨j, hj⟩]
    exact hbal
  exact_mod_cast hcast

end Fields

end

end Erdos85

#print axioms Erdos85.muNegOne_c4_intersecting_graph
#print axioms Erdos85.muNegOne_c4_no_two_graph
#print axioms Erdos85.muNegOne_intertwine_graph
