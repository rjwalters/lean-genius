import Proofs.Erdos85DoubleCoverTargetUniqueness
import Proofs.Erdos85SquareMinimumLeakageArithmetic

/-!
# Universal minimum-layer bounds

The large-prime sector argument has a prime-free core.  This file records
the first graph-facing half: cyclic-cover target uniqueness and detailed
balance bound the total leakage from the minimum-order defect components by
the number of vertices outside that layer, scaled by the minimum order.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- **Prime-free minimum-layer leakage bound.**  Let `M` be all defect
components having the same (globally minimum) order as `c₀`.  Then the
minimum order times the total quotient mass from `M` to larger components
is at most the number of vertices outside `M`. -/
theorem secondOrder_minimumLayer_scaledLeakage_le_outsideOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard) :
    let C := (secondOrderDefectGraph G).ConnectedComponent
    let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
    let M : Finset C := Finset.univ.filter
      (fun c ↦ c.supp.ncard = c₀.supp.ncard)
    c₀.supp.ncard *
        (∑ c ∈ M, ∑ e ∈ Finset.univ \ M, Q c e) ≤
      d * (d - 1) + 3 - M.card * c₀.supp.ncard := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let C := D.ConnectedComponent
  let Q := componentQuotientMatrix G D
  let M : Finset C := Finset.univ.filter
    (fun c ↦ c.supp.ncard = c₀.supp.ncard)
  have hminimum : ∀ c ∈ M, ∀ e : C,
      c.supp.ncard ≤ e.supp.ncard := by
    intro c hc e
    rw [(Finset.mem_filter.mp hc).2]
    exact hc₀min e
  have hlarger : ∀ c ∈ M, ∀ e ∈ Finset.univ \ M,
      c.supp.ncard < e.supp.ncard := by
    intro c hc e he
    have hle := hminimum c hc e
    have heNot : e ∉ M := (Finset.mem_sdiff.mp he).2
    have hcEq := (Finset.mem_filter.mp hc).2
    rw [hcEq] at hle ⊢
    have hne : e.supp.ncard ≠ c₀.supp.ncard := by
      intro heq
      exact heNot (Finset.mem_filter.mpr ⟨Finset.mem_univ e, heq⟩)
    omega
  have hunique : ∀ c₁ ∈ M, ∀ c₂ ∈ M,
      ∀ e ∈ Finset.univ \ M, 0 < Q c₁ e → 0 < Q c₂ e → c₁ = c₂ := by
    intro c₁ hc₁ c₂ hc₂ e he hpos₁ hpos₂
    apply secondOrder_minimum_largerTarget_source_unique
      G hfree hd heven hmin hcard c₁ c₂ e
        (hminimum c₁ hc₁)
    · rw [(Finset.mem_filter.mp hc₁).2,
        (Finset.mem_filter.mp hc₂).2]
    · exact hlarger c₁ hc₁ e he
    · simpa [Q, D] using hpos₁
    · simpa [Q, D] using hpos₂
  have hexact : ∀ c ∈ M, ∀ e ∈ Finset.univ \ M,
      0 < Q c e → c₀.supp.ncard * Q c e = e.supp.ncard := by
    intro c hc e he hpos
    have hs := secondOrder_componentQuotientMatrix_entries_of_size_lt
      G hfree hd heven hmin hcard c e (hlarger c hc e he)
        (by simpa [Q, D] using hpos)
    have hcEq := (Finset.mem_filter.mp hc).2
    simpa only [Q, D, hcEq] using hs.2.2
  have hscaled := disjoint_target_finset_scaled_incidence_le_weight
    M (Finset.univ \ M) Q (fun e : C ↦ e.supp.ncard)
      c₀.supp.ncard hunique hexact
  have hsumSizes : (∑ e : C, e.supp.ncard) = d * (d - 1) + 3 := by
    rw [sum_connectedComponent_supp_ncard D, hcard]
  have hinside : ∑ e ∈ M, e.supp.ncard = M.card * c₀.supp.ncard := by
    calc
      _ = ∑ _e ∈ M, c₀.supp.ncard := by
        apply Finset.sum_congr rfl
        intro e he
        exact (Finset.mem_filter.mp he).2
      _ = M.card * c₀.supp.ncard := by simp
  have hsplit := Finset.sum_sdiff
    (f := fun e : C ↦ e.supp.ncard) (Finset.subset_univ M)
  have houtside : ∑ e ∈ Finset.univ \ M, e.supp.ncard =
      d * (d - 1) + 3 - M.card * c₀.supp.ncard := by
    rw [hsumSizes, hinside] at hsplit
    omega
  rw [houtside] at hscaled
  exact hscaled

end

end Erdos85
