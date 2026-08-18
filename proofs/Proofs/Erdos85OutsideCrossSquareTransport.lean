import Proofs.Erdos85OrderSixtyFourOutsideFeasibility
import Proofs.Erdos85BinarySquareRegularParity

/-!
# Squaring the outside cross-block equation

The label-free unordered-pair hit law is the entrywise content of the usual
cross-block equation `A B + B C = J`.  Iterating it once transports `C²`
back to `A²`.  This is the scalable algebraic replacement for enumerating
the 48 outside vertices.
-/

namespace Erdos85

noncomputable section

/-- Abstract rectangular square transport.  If the internal and outside
blocks have row sums `a` and `c`, respectively, then one further outside step
is determined by two internal steps. -/
theorem rectangular_cross_square_transport
    {H O : Type*} [Fintype H] [Fintype O]
    [DecidableEq H] [DecidableEq O]
    {K : Type*} [CommRing K]
    (A : Matrix H H K) (B : Matrix H O K) (C : Matrix O O K)
    (J : Matrix H O K) (a c : K)
    (hcross : A * B + B * C = J)
    (hAJ : A * J = a • J)
    (hJC : J * C = c • J) :
    B * C * C = c • J - a • J + (A * A) * B := by
  have hBC : B * C = J - A * B := eq_sub_of_add_eq' hcross
  calc
    B * C * C = (J - A * B) * C := by rw [hBC]
    _ = J * C - (A * B) * C := by rw [Matrix.sub_mul]
    _ = c • J - A * (B * C) := by rw [hJC, Matrix.mul_assoc]
    _ = c • J - A * (J - A * B) := by rw [hBC]
    _ = c • J - (A * J - A * (A * B)) := by rw [Matrix.mul_sub]
    _ = c • J - A * J + A * (A * B) := by abel
    _ = c • J - a • J + A * (A * B) := by rw [hAJ]
    _ = c • J - a • J + (A * A) * B := by rw [Matrix.mul_assoc]

/-- Degree-`2`/degree-`6` specialization for the order-64 size-two block. -/
theorem rectangular_cross_square_transport_two_six
    {H O : Type*} [Fintype H] [Fintype O]
    [DecidableEq H] [DecidableEq O]
    {K : Type*} [CommRing K]
    (A : Matrix H H K) (B : Matrix H O K) (C : Matrix O O K)
    (J : Matrix H O K)
    (hcross : A * B + B * C = J)
    (hAJ : A * J = (2 : K) • J)
    (hJC : J * C = (6 : K) • J) :
    B * C * C = (4 : K) • J + (A * A) * B := by
  rw [rectangular_cross_square_transport A B C J 2 6 hcross hAJ hJC]
  module

/-- Graph-facing square transport for the unique order-16 component in the
seven-component order-64 branch. -/
theorem orderSixtyFour_seven_components_outside_cross_square_transport
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16 ∧
      let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
      let q : Set (Fin 64) := {x | ¬p x}
      let H := (G.induce c.supp).adjMatrix ℂ
      let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ x ∈ q)
      let C := (G.induce q).adjMatrix ℂ
      let J : Matrix c.supp q ℂ := fun _ _ ↦ 1
      B * C * C = (4 : ℂ) • J + (H * H) * B := by
  classical
  obtain ⟨c, hc, _label, _hqcard, _htwo, _hinj, _himage,
      _hRreg, _hRedges, hCreg, _hC4, hcross⟩ :=
    orderSixtyFour_seven_components_outside_feasibility
      G hfree hmin hcover hcount
  refine ⟨c, hc, ?_⟩
  let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
  let q : Set (Fin 64) := {x | ¬p x}
  let Hg := G.induce c.supp
  let Cg := G.induce q
  let H := Hg.adjMatrix ℂ
  let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ x ∈ q)
  let C := Cg.adjMatrix ℂ
  let J : Matrix c.supp q ℂ := fun _ _ ↦ 1
  have hreg := orderSixtyFour_regular_of_tightCover G hfree hmin hcover
  have hHreg : ∀ x, Hg.degree x = 2 := by
    intro x
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg (by norm_num) c hc x
  have hAJ : H * J = (2 : ℂ) • J := by
    ext x y
    have hrow : H.mulVec (fun _ ↦ 1) x = (2 : ℂ) := by
      change (Hg.adjMatrix ℂ).mulVec (Function.const c.supp 1) x = 2
      rw [SimpleGraph.adjMatrix_mulVec_const_apply, hHreg x]
      norm_num
    rw [Matrix.mulVec, dotProduct] at hrow
    simpa [Matrix.mul_apply, J] using hrow
  have hJC : J * C = (6 : ℂ) • J := by
    ext x y
    have hrow : C.mulVec (fun _ ↦ 1) y = (6 : ℂ) := by
      change (Cg.adjMatrix ℂ).mulVec (Function.const q 1) y = 6
      rw [SimpleGraph.adjMatrix_mulVec_const_apply, hCreg y]
      norm_num
    rw [Matrix.mulVec, dotProduct] at hrow
    calc
      (J * C) x y = ∑ z, C z y := by simp [Matrix.mul_apply, J]
      _ = ∑ z, C y z := by
        apply Finset.sum_congr rfl
        intro z _
        exact congr_fun₂ Cg.isSymm_adjMatrix.eq y z
      _ = 6 := by simpa using hrow
      _ = ((6 : ℂ) • J) x y := by simp [J]
  exact rectangular_cross_square_transport_two_six
    H B C J hcross hAJ hJC

end


end Erdos85

#print axioms Erdos85.rectangular_cross_square_transport
#print axioms Erdos85.rectangular_cross_square_transport_two_six
#print axioms Erdos85.orderSixtyFour_seven_components_outside_cross_square_transport
