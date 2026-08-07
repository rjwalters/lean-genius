import Proofs.Erdos85MinimumLayerUniversal
import Proofs.Erdos85MinimumLayerCrossPairIdentity
import Proofs.Erdos85MinimumLayerGramArithmetic

/-!
# Universal minimum-layer terminal

At every exact even boundary, the minimum defect-cycle layer obeys a sharp
prime-free dichotomy: either it contains every defect component, or its
total number of vertices is at most `2*d - 1`.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- **Universal minimum-layer dichotomy.**  If `c₀` has globally minimum
defect-component order and `M` is the set of all components of that order,
then either every component has that common order or `M` contains at most
`2*d-1` vertices in total. -/
theorem secondOrder_minimumLayer_allEqual_or_totalOrder_le
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
    (∀ e : (secondOrderDefectGraph G).ConnectedComponent,
        e.supp.ncard = c₀.supp.ncard) ∨
      (Finset.univ.filter
        (fun c : (secondOrderDefectGraph G).ConnectedComponent ↦
          c.supp.ncard = c₀.supp.ncard)).card * c₀.supp.ncard ≤
        2 * d - 1 := by
  classical
  let D := secondOrderDefectGraph G
  let C := D.ConnectedComponent
  let Q := componentQuotientMatrix G D
  let M : Finset C := Finset.univ.filter
    (fun c ↦ c.supp.ncard = c₀.supp.ncard)
  let L : C → ℕ := fun c ↦ ∑ e ∈ Finset.univ \ M, Q c e
  let n := d * (d - 1) + 3
  let S := ∑ c ∈ M, L c
  let R := ∑ c ∈ M, L c * L c
  have hMsize : ∀ c ∈ M, c.supp.ncard = c₀.supp.ncard := by
    intro c hc
    exact (Finset.mem_filter.mp hc).2
  have hsumSizes : (∑ c : C, c.supp.ncard) = n := by
    rw [sum_connectedComponent_supp_ncard D, hcard]
  have hinside : ∑ c ∈ M, c.supp.ncard = M.card * c₀.supp.ncard := by
    calc
      _ = ∑ _c ∈ M, c₀.supp.ncard := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hMsize c hc
      _ = M.card * c₀.supp.ncard := by simp
  have huw : M.card * c₀.supp.ncard ≤ n := by
    rw [← hinside, ← hsumSizes]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ M)
  have hidentityRaw := secondOrder_minimumLayer_crossPair_identity
    G hfree hd heven hmin hcard c₀ hc₀min
  have hidentity :
      (∑ c ∈ M,
        (((d : ℤ) - (L c : ℤ)) * ((d : ℤ) - (L c : ℤ)) -
          ((d : ℤ) - (L c : ℤ)) - ((c₀.supp.ncard : ℤ) - 3))) =
        (M.card : ℤ) * ((M.card : ℤ) - 1) *
          (c₀.supp.ncard : ℤ) := by
    simpa only [M, L, Q, D, Nat.cast_sum] using hidentityRaw
  have hNat : M.card * (n - M.card * c₀.supp.ncard) + R =
      (2 * d - 1) * S := by
    exact minimumLayer_crossPair_identity_nat M L d n c₀.supp.ncard
      (by omega) huw rfl hidentity
  have hmass := secondOrder_minimumLayer_scaledLeakage_le_outsideOrder
    G hfree hd heven hmin hcard c₀ hc₀min
  have hmass' : c₀.supp.ncard * S ≤ n - M.card * c₀.supp.ncard := by
    simpa only [M, S, L, Q, D, n] using hmass
  have hcollapse := minimumLayer_orderMass_le_or_all
    d n c₀.supp.ncard M.card S R huw hmass' hNat
  rcases hcollapse with hallMass | hsmall
  · left
    have hsplit := Finset.sum_sdiff
      (f := fun c : C ↦ c.supp.ncard) (Finset.subset_univ M)
    have houtsideZero : ∑ c ∈ Finset.univ \ M, c.supp.ncard = 0 := by
      rw [hsumSizes, hinside, hallMass] at hsplit
      omega
    intro e
    by_contra heq
    have heNot : e ∉ M := by
      intro heM
      exact heq (hMsize e heM)
    have heLe : e.supp.ncard ≤
        ∑ c ∈ Finset.univ \ M, c.supp.ncard :=
      Finset.single_le_sum
        (f := fun c : C ↦ c.supp.ncard) (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, heNot⟩)
    have hePos := e.nonempty_supp.ncard_pos
    omega
  · right
    simpa only [M] using hsmall

end

end Erdos85
