import Proofs.Erdos85LocalThresholdRigidity
import Proofs.Erdos85RamseyPlateau

/-!
# Local degree rigidity inside a plateau core

The sharp adjacent-clone surgery applies directly to the edge-minimal graph
stored in a `C4PlateauCore`.  This packages its consequences in the global
plateau vocabulary used by the eventual-monotonicity reduction.
-/

open SimpleGraph

namespace Erdos85

/-- Every plateau core has a representative whose degrees lie in the sharp
window `[d,2d-2]`.  For odd `d` the upper endpoint improves to `2d-3`.
At an even-degree endpoint, the whole neighbourhood is a perfect matching
and every matching edge has a tight endpoint. -/
theorem C4PlateauCore.exists_sharp_local_rigidity
    {m d : ℕ} (hm : 4 ≤ m) (hcore : C4PlateauCore m d) :
    ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
      G.minDegree = d ∧
      ¬ containsC4 (Fin m) G ∧
      (∀ v, G.degree v ≤ 2 * d - 2) ∧
      (Odd d → ∀ v, G.degree v ≤ 2 * d - 3) ∧
      (∀ x, 2 * d - 2 ≤ G.degree x →
        G.degree x = 2 * d - 2 ∧
          Even d ∧
          (∀ c : (deletedNeighborhoodInducedGraph G x).ConnectedComponent,
            c.supp.ncard = 2) ∧
          (∀ a b : Fin m, G.Adj a x → G.Adj b x → G.Adj a b →
            G.degree a = d ∨ G.degree b = d)) := by
  rcases hcore with ⟨G, hdec, hmin, hfree, _hcover, hnext⟩
  letI : DecidableRel G.Adj := hdec
  have hd : 1 ≤ d := by
    have hd2 : 2 ≤ d := by
      have htwo : 2 ≤ minDegreeForC4 (m + 1) :=
        two_le_minDegreeForC4 (n := m) (by omega)
      have hdnext : minDegreeForC4 (m + 1) ≤ d := by
        by_contra hnot
        have hlt : d < minDegreeForC4 (m + 1) := by omega
        obtain ⟨H, hHdec, hHmin, hHfree⟩ :=
          (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 (by omega)).2 hlt
        exact hHfree (hnext H hHdec hHmin)
      exact htwo.trans hdnext
    omega
  have hno : ¬ C4FreeMinDegreeWitness (m + 1) d := by
    rintro ⟨H, hHdec, hHmin, hHfree⟩
    exact hHfree (hnext H hHdec hHmin)
  have hupper := degree_le_two_mul_sub_two_of_not_witness_succ
    G (N := m) (by simp) hmin.ge hfree hd hno
  refine ⟨G, hdec, hmin, hfree, hupper, ?_, ?_⟩
  · intro hodd
    exact degree_le_two_mul_sub_three_of_odd_not_witness_succ
      G (N := m) (by simp) hmin.ge hfree hd (Nat.odd_iff.mp hodd) hno
  · intro x hx
    exact local_threshold_rigidity_of_not_witness_succ
      G x (N := m) (by simp) hmin.ge hfree hd hno hx

/-- In particular, an odd-degree plateau core has a representative whose
maximum degree is at most `2d-3`; the parity-obstructed endpoint cannot
occur. -/
theorem C4PlateauCore.exists_degree_le_two_mul_sub_three_of_odd
    {m d : ℕ} (hm : 4 ≤ m) (hodd : Odd d)
    (hcore : C4PlateauCore m d) :
    ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
      G.minDegree = d ∧ ¬ containsC4 (Fin m) G ∧
        ∀ v, G.degree v ≤ 2 * d - 3 := by
  obtain ⟨G, hdec, hmin, hfree, _hupper, hoddUpper, _hrigid⟩ :=
    hcore.exists_sharp_local_rigidity hm
  exact ⟨G, hdec, hmin, hfree, hoddUpper hodd⟩

end Erdos85
