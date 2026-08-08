import Proofs.Erdos85MixedAnchorDiagonal
import Proofs.Erdos85MixedAnchorPartition

/-!
# The unique off-cycle component covering an admissible difference

The off-cycle mass dichotomy and mixed-block quantization together imply a
sharp component-level partition: whenever a target difference is absent from
the diagonal ordered-difference set, exactly one other defect component
supplies its entire pair mass.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- For a difference outside the diagonal support, exactly one off-target
defect component contributes the full target-cycle pair mass. -/
theorem existsUnique_component_full_anchorPairMultiplicity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (e : (secondOrderDefectGraph G).ConnectedComponent)
    (heOdd : Odd e.supp.ncard)
    (δ : ZMod e.supp.ncard) (hδ0 : δ ≠ 0)
    (hδ1 : δ ≠ 1) (hδ2 : δ ≠ -1)
    (hδdiag : δ ∉ orderedDifferenceSet
      (mixedAnchorSupport G (u e 0) (u e))) :
    ∃! c : (secondOrderDefectGraph G).ConnectedComponent,
      c ∈ Finset.univ.erase e ∧
      (∑ z : ZMod c.supp.ncard,
        anchorPairMultiplicity G (u c z) (u e) δ) = e.supp.ncard := by
  classical
  let D := secondOrderDefectGraph G
  let C := D.ConnectedComponent
  let ℓ : C → ℕ := fun c ↦ c.supp.ncard
  have hsep : ∀ {c f : C}, c ≠ f → ∀ x y, u c x ≠ u f y := by
    intro c f hcf x y hxy
    apply hcf
    have hcx : D.connectedComponentMk (u c x) = c :=
      (ConnectedComponent.mem_supp_iff c (u c x)).mp (by
        rw [← huRange c]
        exact ⟨x, rfl⟩)
    have hfy : D.connectedComponentMk (u f y) = f :=
      (ConnectedComponent.mem_supp_iff f (u f y)).mp (by
        rw [← huRange f]
        exact ⟨y, rfl⟩)
    rw [← hcx, ← hfy, hxy]
  have hcover : ∀ v : V, ∃ c : C, ∃ x, u c x = v := by
    intro v
    let c : C := D.connectedComponentMk v
    have hv : v ∈ c.supp := (ConnectedComponent.mem_supp_iff c v).mpr rfl
    rw [← huRange c] at hv
    exact ⟨c, hv⟩
  let M : C → ℕ := fun c ↦
    ∑ z : ZMod c.supp.ncard, anchorPairMultiplicity G (u c z) (u e) δ
  have hoff := sum_offCycle_anchorPairMultiplicity G hfree hd heven hmin
    hcard (hu e) (hℓ3 e) heOdd (huD e) δ hδ0 hδ1 hδ2
  have hreindex := sum_filter_not_range_eq_sum_components_erase
    (ℓ := ℓ) u hu hsep hcover e
      (fun x ↦ anchorPairMultiplicity G x (u e) δ)
  have hsum : ∑ c ∈ Finset.univ.erase e, M c = e.supp.ncard := by
    rw [hreindex] at hoff
    rw [if_neg hδdiag] at hoff
    simpa [M, ℓ] using hoff
  have hquant : ∀ c ∈ Finset.univ.erase e,
      M c ∈ ({0, e.supp.ncard} : Set ℕ) := by
    intro c hc
    exact sum_anchorPairMultiplicity_mixedBlock_mem G hfree hd heven hmin
      hcard (hℓ3 c) (hℓ3 e) heOdd c e (u c) (u e) (hu c) (hu e)
        (huRange c) (huRange e) (huD c) (huD e) rfl rfl δ hδ0
  exact existsUnique_mem_fullMass_of_quantized_sum
    (Finset.univ.erase e) M (by have := hℓ3 e; omega) hquant hsum

end

end Erdos85
