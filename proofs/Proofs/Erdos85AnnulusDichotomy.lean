import Proofs.Erdos85ComponentBoundaryBridge
import Proofs.Erdos85QuadraticConductor

/-!
# The quadratic-annulus component dichotomy

This packages the exact interface between the quadratic conductor and the
componentwise spectral boundary.  Either a plateau representative has a
component below `d²`, where the regular-excess bridge applies, or all of its
components lie in the unresolved quadratic annulus.  In the latter case
there are at most 35 components.
-/

namespace Erdos85

open SimpleGraph

/-- A plateau core has a representative with either a small regular,
one-step-nonextendable component, or fewer than 36 components, all of order
at least `d²`. -/
theorem C4PlateauCore.exists_small_boundary_component_or_large_component_family
    {m d : ℕ} (hm : 4 ≤ m) (hd : 3 ≤ d)
    (hcore : C4PlateauCore m d) :
    ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
      G.minDegree = d ∧ ¬ containsC4 (Fin m) G ∧
      ((∃ (c : G.ConnectedComponent) (e : ℕ),
          c.supp.ncard < d * d ∧
          e ≤ d - 3 ∧
          c.supp.ncard = d * (d - 1) + 2 + e ∧
          (∀ x : c.supp, (G.induce c.supp).degree x = d) ∧
          (c.supp.ncard < m →
            ¬ C4FreeMinDegreeWitness (c.supp.ncard + 1) d)) ∨
        (Fintype.card G.ConnectedComponent < 36 ∧
          ∀ c : G.ConnectedComponent, d * d ≤ c.supp.ncard)) := by
  obtain ⟨G, hdec, hmin, hfree, hsmall⟩ :=
    hcore.exists_small_component_boundary_data hm hd
  letI : DecidableRel G.Adj := hdec
  refine ⟨G, hdec, hmin, hfree, ?_⟩
  by_cases hex : ∃ c : G.ConnectedComponent, c.supp.ncard < d * d
  · left
    obtain ⟨c, hc⟩ := hex
    obtain ⟨e, he, hcard, hreg, hno⟩ := hsmall c hc
    exact ⟨c, e, hc, he, hcard, hreg, hno⟩
  · right
    have hlarge : ∀ c : G.ConnectedComponent, d * d ≤ c.supp.ncard := by
      intro c
      exact Nat.le_of_not_gt fun hc ↦ hex ⟨c, hc⟩
    refine ⟨?_, hlarge⟩
    have hsum : (∑ c : G.ConnectedComponent, c.supp.ncard) = m := by
      classical
      calc
        (∑ c : G.ConnectedComponent, c.supp.ncard) =
            ∑ c : G.ConnectedComponent, Fintype.card c.supp := by
          apply Finset.sum_congr rfl
          intro c _hc
          simpa [Nat.card_eq_fintype_card] using
            (Nat.card_coe_set_eq c.supp).symm
        _ = Fintype.card (Σ c : G.ConnectedComponent, c.supp) :=
          Fintype.card_sigma.symm
        _ = m := by
          simpa using
            (Fintype.card_congr (vertexConnectedComponentEquiv G)).symm
    have hmass : Fintype.card G.ConnectedComponent * (d * d) ≤ m := by
      calc
        Fintype.card G.ConnectedComponent * (d * d) =
            ∑ _c : G.ConnectedComponent, d * d := by simp
        _ ≤ ∑ c : G.ConnectedComponent, c.supp.ncard :=
          Finset.sum_le_sum fun c _hc ↦ hlarge c
        _ = m := hsum
    have hmUpper : m < 36 * d * d := by
      have h := hcore.order_succ_lt_quadratic hm
      omega
    by_contra hnot
    have h36 : 36 ≤ Fintype.card G.ConnectedComponent := by omega
    have hscale : 36 * (d * d) ≤
        Fintype.card G.ConnectedComponent * (d * d) :=
      Nat.mul_le_mul_right (d * d) h36
    have hdd : 0 < d * d := by positivity
    nlinarith

end Erdos85
