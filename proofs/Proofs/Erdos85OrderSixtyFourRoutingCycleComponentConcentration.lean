import Proofs.Erdos85OrderSixtyFourNoRainbowRoutingCyclePressure

/-! # Component concentration of rooted routing cycles -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Rooted all-distinct routing cycles whose middle and closing vertices lie
in two prescribed defect components. -/
def rootedAllDistinctRoutingCyclePairsInComponents
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (a b c e f : (secondOrderDefectGraph G).ConnectedComponent)
    (x : Fin 64) : Finset (Fin 64 × Fin 64) :=
  (rootedAllDistinctRoutingCyclePairs G hfree a b c x).filter fun p =>
    (secondOrderDefectGraph G).connectedComponentMk p.2 = e ∧
      (secondOrderDefectGraph G).connectedComponentMk p.1 = f

set_option maxRecDepth 10000 in
/-- Six-bucket pigeonhole: in the no-rainbow branch, for every root and
distinct routing-color triple, some fixed ordered pair of distinct external
components carries at least three rooted routing cycles. -/
theorem orderSixtyFour_regular_fourComponents_noRainbow_exists_componentPair_three_routingCycles
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hno : ¬ ∃ d : (secondOrderDefectGraph G).ConnectedComponent,
      routingOwnerRainbow G d a b c)
    (x : Fin 64) :
    ∃ e f : (secondOrderDefectGraph G).ConnectedComponent,
      e ≠ (secondOrderDefectGraph G).connectedComponentMk x ∧
      f ≠ (secondOrderDefectGraph G).connectedComponentMk x ∧ e ≠ f ∧
      3 ≤ (rootedAllDistinctRoutingCyclePairsInComponents
        G hfree a b c e f x).card := by
  classical
  let D := secondOrderDefectGraph G
  let d := D.connectedComponentMk x
  let S := rootedAllDistinctRoutingCyclePairs G hfree a b c x
  let E := (Finset.univ : Finset D.ConnectedComponent).erase d
  let T := E.sigma fun e => E.erase e
  let routeComponents : Fin 64 × Fin 64 → Σ _e : D.ConnectedComponent,
      D.ConnectedComponent := fun p => ⟨D.connectedComponentMk p.2,
        D.connectedComponentMk p.1⟩
  have hEcard : E.card = 3 := by
    dsimp [E]
    rw [Finset.card_erase_of_mem (Finset.mem_univ d), Finset.card_univ,
      hcount]
  have hTcard : T.card = 6 := by
    change (E.sigma fun e => E.erase e).card = 6
    rw [Finset.card_sigma]
    calc
      (∑ e ∈ E, (E.erase e).card) = ∑ _e ∈ E, 2 := by
        apply Finset.sum_congr rfl
        intro e he
        rw [Finset.card_erase_of_mem he, hEcard]
      _ = 6 := by simp [hEcard]
  have hmaps : ∀ p ∈ S, routeComponents p ∈ T := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    obtain ⟨hxy, hyz, hzx, _ha, _hb, _hc⟩ := hp'.2
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_univ _⟩, ?_⟩
    exact Finset.mem_erase.mpr
      ⟨hyz.symm, Finset.mem_erase.mpr ⟨hzx, Finset.mem_univ _⟩⟩
  have hScard : 16 ≤ S.card :=
    orderSixtyFour_regular_fourComponents_noRainbow_rootedRoutingCycles_card_ge_sixteen
      G hfree hreg hcount a b c hab hac hbc hno x
  have hlt : T.card * 2 < S.card := by omega
  obtain ⟨key, hkey, hkeyCard⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (f := routeComponents) hmaps hlt
  rcases key with ⟨e, f⟩
  have hkey' := Finset.mem_sigma.mp hkey
  have he := Finset.mem_erase.mp hkey'.1
  have hf := Finset.mem_erase.mp hkey'.2
  have hfiber : S.filter (fun p => routeComponents p = ⟨e, f⟩) =
      rootedAllDistinctRoutingCyclePairsInComponents G hfree a b c e f x := by
    ext p
    simp only [rootedAllDistinctRoutingCyclePairsInComponents,
      Finset.mem_filter]
    constructor
    · rintro ⟨hp, hcomponents⟩
      refine ⟨hp, ?_⟩
      have heq := congrArg Sigma.fst hcomponents
      have hfeq := congrArg
        (fun r : Σ _e : D.ConnectedComponent, D.ConnectedComponent => r.2)
        hcomponents
      exact ⟨heq, hfeq⟩
    · rintro ⟨hp, heq, hfeq⟩
      refine ⟨hp, ?_⟩
      apply Sigma.ext heq
      simpa [heq] using hfeq
  refine ⟨e, f, he.1, (Finset.mem_erase.mp hf.2).1, hf.1.symm, ?_⟩
  rw [← hfiber]
  omega

end

end Erdos85
