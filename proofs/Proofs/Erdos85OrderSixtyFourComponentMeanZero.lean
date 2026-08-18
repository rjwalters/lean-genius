import Proofs.Erdos85OrderSixtyFourK8ResidualDeterminant

/-! # The residual sector as componentwise mean-zero vectors -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 10000

/-- Applying normalized component averaging at a vertex is the normalized
coordinate sum over that vertex's connected component. -/
theorem defectComponentNormalizedProjection_mulVec_apply
    (D : SimpleGraph (Fin 64)) [DecidableEq D.ConnectedComponent]
    [∀ c : D.ConnectedComponent, Fintype c.supp]
    (v : Fin 64 → ℚ) (x : Fin 64) :
    (defectComponentNormalizedProjection D).mulVec v x =
      ((D.connectedComponentMk x).supp.ncard : ℚ)⁻¹ *
        ∑ y : (D.connectedComponentMk x).supp, v y.1 := by
  let hdec := ‹DecidableEq D.ConnectedComponent›
  classical
  letI : DecidableEq D.ConnectedComponent := hdec
  let c := D.connectedComponentMk x
  rw [Matrix.mulVec, dotProduct]
  simp only [defectComponentNormalizedProjection]
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.univ : Finset (Fin 64)).filter
          (fun y => D.connectedComponentMk x = D.connectedComponentMk y) =
        Finset.univ.filter (fun y => y ∈ c.supp) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change c = D.connectedComponentMk y ↔ y ∈ c.supp
    simpa only [eq_comm] using
      (SimpleGraph.ConnectedComponent.mem_supp_iff c y).symm
  rw [hfilter]
  calc
    (∑ y ∈ Finset.univ.filter (fun y => y ∈ c.supp),
        ((c.supp.ncard : ℚ)⁻¹) * v y) =
      (c.supp.ncard : ℚ)⁻¹ *
        ∑ y ∈ Finset.univ.filter (fun y => y ∈ c.supp), v y := by
      rw [Finset.mul_sum]
    _ = (c.supp.ncard : ℚ)⁻¹ * ∑ y : c.supp, v y.1 := by
      congr 1
      simpa using (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset (Fin 64)))
        (p := fun y => y ∈ c.supp)
        v).symm

/-- A vector is killed by normalized component averaging exactly when its
coordinates sum to zero separately on every connected component. -/
theorem mem_ker_defectComponentNormalizedProjection_iff_component_sum_zero
    (D : SimpleGraph (Fin 64)) [DecidableEq D.ConnectedComponent]
    [∀ c : D.ConnectedComponent, Fintype c.supp]
    (v : Fin 64 → ℚ) :
    v ∈ LinearMap.ker (defectComponentNormalizedProjection D).toLin' ↔
      ∀ c : D.ConnectedComponent,
        ∑ y : c.supp, v y.1 = 0 := by
  constructor
  · intro hv c
    obtain ⟨x, hx⟩ := c.nonempty_supp
    have hcx : D.connectedComponentMk x = c :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c x).mp hx
    have happ := congrFun hv x
    rw [Matrix.toLin'_apply,
      defectComponentNormalizedProjection_mulVec_apply] at happ
    rw [hcx] at happ
    have hncard : c.supp.ncard ≠ 0 :=
      Nat.ne_of_gt c.nonempty_supp.ncard_pos
    have hinv : ((c.supp.ncard : ℚ)⁻¹) ≠ 0 := by
      exact inv_ne_zero (by exact_mod_cast hncard)
    exact (mul_eq_zero.mp happ).resolve_left hinv
  · intro hsum
    apply LinearMap.mem_ker.mpr
    funext x
    rw [Matrix.toLin'_apply,
      defectComponentNormalizedProjection_mulVec_apply]
    rw [hsum (D.connectedComponentMk x), mul_zero]
    rfl

end

end Erdos85
