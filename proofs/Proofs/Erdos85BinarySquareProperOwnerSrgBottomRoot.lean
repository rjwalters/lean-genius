import Proofs.Erdos85BinarySquareOwnerBottomMultiplicity
import Proofs.Erdos85StronglyRegularBottomRootEquation

/-!
# The forced bottom root of a proper owner SRG

This file extracts the scalar strongly-regular root equation from the exact
bottom eigenspace of a proper component-owner graph.  The nonlinear parameter
solve and the final centered-matrix contradiction live in separate modules.
-/

open Finset SimpleGraph

namespace Erdos85

/-- For a proper owner color, exact bottom multiplicity supplies a genuine
`-m` eigenvector; the SRG quadratic then gives the scalar equation consumed
by `properOwner_srg_parameters_of_bottom_root`. -/
theorem binarySquare_regular_properOwner_srg_bottom_root_equation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m lambda mu : ℕ}
    (hmpos : 1 ≤ m) (hm : m < q) (hc : c.supp.ncard = q * m)
    (hSRG : (componentOwnerGraph G (secondOrderDefectGraph G) c).IsSRGWith
      (q * q) (m * (q - 1)) lambda mu) :
    (m : ℤ) * lambda - ((m : ℤ) - 1) * mu =
      (m : ℤ) * ((q : ℤ) - m - 1) := by
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  let M := O.adjMatrix ℝ + (m : ℝ) • (1 : Matrix V V ℝ)
  have hfinrank : Module.finrank ℝ (LinearMap.ker M.mulVecLin) =
      q * q - q * m := by
    simpa [O, M] using
      (binarySquare_regular_finrank_componentOwnerGraph_bottom_kernel_real
        G hfree hq hreg hcard c hc)
  have hqm : q * m < q * q := by nlinarith
  have hkerpos : 0 < Module.finrank ℝ (LinearMap.ker M.mulVecLin) := by
    rw [hfinrank]
    omega
  obtain ⟨w, hw0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hkerpos
  let v : V → ℝ := w
  have hv0 : v ≠ 0 := by
    intro hv
    apply hw0
    ext x
    exact congrFun hv x
  have hwker : M.mulVec v = 0 := by
    exact w.property
  have heig : (O.adjMatrix ℝ).mulVec v = fun x => -(m : ℝ) * v x := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hwker
    funext x
    have hx := congrFun hwker x
    simp only [Pi.add_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at hx
    nlinarith
  have hrootR := srg_bottom_root_equation O hSRG hmpos v hv0 heig
  have hrootR' :
      (m : ℝ) * lambda - ((m : ℝ) - 1) * mu =
        (m : ℝ) * ((q : ℝ) - m - 1) := by
    push_cast at hrootR
    rw [Nat.cast_sub (by omega : 1 ≤ q)] at hrootR
    norm_num at hrootR ⊢
    nlinarith
  exact_mod_cast hrootR'

#print axioms binarySquare_regular_properOwner_srg_bottom_root_equation

end Erdos85
