import Proofs.Erdos85BinarySquareOwnerBottomMultiplicity

/-! # Dimension balance for two owner-bottom sectors

When two normalized defect-component sizes add to `q`, the exact bottom
multiplicity formula forces the two shifted-owner kernels to have total
dimension `q²`.  The Grassmann identity then turns this into an exact tradeoff:
their span loses precisely as many dimensions as their intersection gains.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The real bottom eigenspace of one component owner graph. -/
def realComponentOwnerBottomSubmodule
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent) (m_c : ℕ) :
    Submodule ℝ (V → ℝ) :=
  LinearMap.ker
    ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℝ +
      (m_c : ℝ) • (1 : Matrix V V ℝ)).mulVecLin

/-- The q-generic exact bottom-nullity theorem in reusable submodule form. -/
theorem binarySquare_regular_finrank_realComponentOwnerBottomSubmodule
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m_c : ℕ}
    (hc : c.supp.ncard = q * m_c) :
    Module.finrank ℝ (realComponentOwnerBottomSubmodule G c m_c) =
      q * q - q * m_c := by
  exact binarySquare_regular_finrank_componentOwnerGraph_bottom_kernel_real
    G hfree hq hreg hcard c hc

/-- **Two-owner bottom balance.**  If the two normalized component sizes add
to `q`, their bottom eigenspace dimensions add to the full ambient dimension.
This uses no order-64 enumeration. -/
theorem binarySquare_regular_twoOwner_bottom_finrank_add
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (a b : (secondOrderDefectGraph G).ConnectedComponent)
    {m_a m_b : ℕ}
    (ha : a.supp.ncard = q * m_a)
    (hb : b.supp.ncard = q * m_b)
    (hsum : m_a + m_b = q) :
    Module.finrank ℝ (realComponentOwnerBottomSubmodule G a m_a) +
        Module.finrank ℝ (realComponentOwnerBottomSubmodule G b m_b) =
      q * q := by
  rw [binarySquare_regular_finrank_realComponentOwnerBottomSubmodule
      G hfree hq hreg hcard a ha,
    binarySquare_regular_finrank_realComponentOwnerBottomSubmodule
      G hfree hq hreg hcard b hb]
  have hprod : q * m_a + q * m_b = q * q := by
    rw [← Nat.mul_add, hsum]
  have hlea : q * m_a ≤ q * q := by omega
  have hleb : q * m_b ≤ q * q := by omega
  omega

/-- Grassmann form of the two-owner balance: the span codimension is exactly
the intersection dimension.  Any new common-bottom direction therefore costs
one dimension of joint coverage, and conversely. -/
theorem binarySquare_regular_twoOwner_bottom_sup_inf_finrank_add
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (a b : (secondOrderDefectGraph G).ConnectedComponent)
    {m_a m_b : ℕ}
    (ha : a.supp.ncard = q * m_a)
    (hb : b.supp.ncard = q * m_b)
    (hsum : m_a + m_b = q) :
    Module.finrank ℝ
          ↥(realComponentOwnerBottomSubmodule G a m_a ⊔
            realComponentOwnerBottomSubmodule G b m_b) +
        Module.finrank ℝ
          ↥(realComponentOwnerBottomSubmodule G a m_a ⊓
            realComponentOwnerBottomSubmodule G b m_b) =
      q * q := by
  rw [Submodule.finrank_sup_add_finrank_inf_eq]
  exact binarySquare_regular_twoOwner_bottom_finrank_add
    G hfree hq hreg hcard a b ha hb hsum

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_twoOwner_bottom_finrank_add
#print axioms Erdos85.binarySquare_regular_twoOwner_bottom_sup_inf_finrank_add
