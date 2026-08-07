import Proofs.Erdos85MinimumLayerDefectCover
import Proofs.Erdos85EqualCycleResidual

/-!
# Classification of the saturated minimum-layer branch

The defect graph of the exact-boundary child is the parent defect graph
restricted to the minimum layer.  Its components are therefore all the
same size.  The complete equal-cycle theorem classifies the child degree,
and the saturation equation then leaves only two parent degrees.
-/

namespace Erdos85

noncomputable section

/-- The frequency-pair residual analysis actually determines the common
defect-cycle length, independently of which exceptional degree survives:
every equal-cycle exact even boundary has common length three. -/
theorem equalCycle_common_length_eq_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d r : ℕ}
    (hd : 4 ≤ d) (hdeven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hlen : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = r) :
    r = 3 := by
  obtain ⟨hr3, -, -, -⟩ :=
    equalCycle_length_facts G hfree hd hdeven hmin hcard hlen
  obtain ⟨k, hk⟩ :=
    equalCycle_three_pow G hfree hd hdeven hmin hcard hlen
  by_cases hk2 : 2 ≤ k
  · exfalso
    apply false_of_equalCycle_nine_dvd
      G hfree hd hdeven hmin hcard hlen
    rw [hk]
    exact pow_dvd_pow 3 hk2
  · have hk1 : k ≤ 1 := by omega
    interval_cases k
    · omega
    · simpa using hk

/-- A saturated exact-boundary descent whose child degree is itself in the
even boundary range has child degree `4` or `12`; consequently the parent
degree is `12` or `124`. -/
theorem minimumLayer_saturated_degree_eq_twelve_or_oneTwentyFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hs4 : 4 ≤ s) (hsEven : Even s)
    (hsat : d = (s - 1) * (s - 1) + 3) :
    (d = 12 ∨ d = 124) ∧ c₀.supp.ncard = 3 := by
  classical
  let D := secondOrderDefectGraph G
  let H := minimumLayerGraph G D c₀
  let P := minimumLayerParentDefect D c₀
  let DH := secondOrderDefectGraph H
  have hfreeChild : ¬ containsC4 _ H :=
    minimumLayerGraph_c4Free G D c₀ hfree
  obtain ⟨v₀, hv₀⟩ := c₀.nonempty_supp
  let a₀ : minimumLayerVertex D c₀ :=
    ⟨⟨c₀, rfl⟩, ⟨v₀, hv₀⟩⟩
  letI : Nonempty (minimumLayerVertex D c₀) := ⟨a₀⟩
  have hminChild : s ≤ H.minDegree := by
    exact H.le_minDegree_of_forall_le_degree s fun x => by
      rw [hregChild x]
  have hEq : P = DH :=
    minimumLayerParentDefect_eq_childDefect
      G hfree hd heven hmin hcard c₀ hregChild hcardChild
  let e : P ≃g DH :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by
        intro a b
        simpa only [Equiv.refl_apply, hEq] }
  have hlen : ∀ c : DH.ConnectedComponent,
      c.supp.ncard = c₀.supp.ncard := by
    intro c
    let cp : P.ConnectedComponent := e.connectedComponentEquiv.symm c
    obtain ⟨a, ha⟩ := cp.nonempty_supp
    have hcp : P.connectedComponentMk a = cp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff cp a).mp ha
    have hpcard : cp.supp.ncard = c₀.supp.ncard := by
      rw [← hcp]
      exact minimumLayerParentDefect_component_card D c₀ a
    have hmap : e.connectedComponentEquiv cp = c :=
      e.connectedComponentEquiv.apply_symm_apply c
    have hcardIso : cp.supp.ncard =
        (e.connectedComponentEquiv cp).supp.ncard := by
      rw [← Set.fintypeCard_eq_ncard, ← Set.fintypeCard_eq_ncard]
      exact Fintype.card_congr
        (SimpleGraph.ConnectedComponent.isoEquivSupp e cp)
    rw [hmap] at hcardIso
    exact hcardIso.symm.trans hpcard
  have hsClass : s = 4 ∨ s = 12 :=
    equalCycle_degree_eq_four_or_twelve
      H hfreeChild hs4 hsEven hminChild hcardChild hlen
  have hc₀three : c₀.supp.ncard = 3 :=
    equalCycle_common_length_eq_three
      H hfreeChild hs4 hsEven hminChild hcardChild hlen
  refine ⟨?_, hc₀three⟩
  rcases hsClass with rfl | rfl <;> omega

/-- **Sharp-descent capstone.**  Away from the genuine degree-`4` and
degree-`12` equal-cycle exceptions, the minimum-layer descent either has
the strict order gap, or the ambient degree is the single residual value
`124`.  Thus the formerly infinite saturated branch is reduced to one
degree. -/
theorem secondOrder_minimumLayer_gap_or_degree_oneTwentyFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hd4 : d ≠ 4) (hd12 : d ≠ 12)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard) :
    ∃ s : ℕ,
      (∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
        (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s) ∧
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3 ∧
      Even s ∧ s < d ∧
      ((d = 124 ∧ c₀.supp.ncard = 3) ∨
        s * (s - 1) + 4 ≤ d) := by
  obtain ⟨s, hreg, _hfreeChild, hcardChild, hsEven, hdesc⟩ :=
    secondOrder_minimumLayer_sharp_descent
      G hfree hd heven hmin hcard c₀ hc₀min
  obtain ⟨hsd, hbranch⟩ := hdesc hd4 hd12
  refine ⟨s, hreg, hcardChild, hsEven, hsd, ?_⟩
  rcases hbranch with hsat | hgap
  · have hs4 : 4 ≤ s := by
      by_contra hnot
      have hslt : s < 4 := Nat.lt_of_not_ge hnot
      obtain ⟨k, hk⟩ := hsEven
      have hsSmall : s = 0 ∨ s = 2 := by omega
      rcases hsSmall with rfl | rfl
      · norm_num at hsat
        omega
      · norm_num at hsat
        exact hd4 hsat
    have hdClass := minimumLayer_saturated_degree_eq_twelve_or_oneTwentyFour
      G hfree hd heven hmin hcard c₀ hreg hcardChild hs4 hsEven hsat
    exact Or.inl ⟨hdClass.1.resolve_left hd12, hdClass.2⟩
  · exact Or.inr hgap

end

end Erdos85
