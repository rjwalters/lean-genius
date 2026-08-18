import Proofs.Erdos85BinarySquareTwoOwnerBottomZeroSum

/-! # Explicit two-owner decomposition of centered vectors

The equality between the two-owner bottom span and the zero-sum hyperplane is
unpacked into an existential interface suited to routing-vector consumers.
Any two such decompositions differ by the common one-dimensional bottom line.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Explicit centered-vector decomposition.**  Every zero-sum real vector
is a sum of bottom vectors for the two owner colors. -/
theorem binarySquare_regular_twoOwner_exists_bottom_decomposition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = q * m c)
    (hsum : ∑ c, m c = q)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2)
    (a b : (secondOrderDefectGraph G).ConnectedComponent) (hab : a ≠ b)
    (v : V → ℝ) (hv : ∑ x, v x = 0) :
    ∃ v_a ∈ realComponentOwnerBottomSubmodule G a (m a),
      ∃ v_b ∈ realComponentOwnerBottomSubmodule G b (m b),
        v_a + v_b = v := by
  have hvZero : v ∈ realZeroSumSubmodule := hv
  rw [← binarySquare_regular_twoOwner_bottom_sup_eq_zeroSum
    G hfree hq hreg hcard m hm hsum hcount a b hab] at hvZero
  exact Submodule.mem_sup.mp hvZero

/-- Two decompositions of the same vector differ by a vector in the common
bottom intersection. -/
theorem twoOwner_bottom_decomposition_difference_mem_inf
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (a b : (secondOrderDefectGraph G).ConnectedComponent)
    {m_a m_b : ℕ} {v_a v_b v_a' v_b' : V → ℝ}
    (hva : v_a ∈ realComponentOwnerBottomSubmodule G a m_a)
    (hvb : v_b ∈ realComponentOwnerBottomSubmodule G b m_b)
    (hva' : v_a' ∈ realComponentOwnerBottomSubmodule G a m_a)
    (hvb' : v_b' ∈ realComponentOwnerBottomSubmodule G b m_b)
    (hsum : v_a + v_b = v_a' + v_b') :
    v_a - v_a' ∈
      realComponentOwnerBottomSubmodule G a m_a ⊓
        realComponentOwnerBottomSubmodule G b m_b := by
  rw [Submodule.mem_inf]
  constructor
  · exact Submodule.sub_mem _ hva hva'
  · have heq : v_a - v_a' = v_b' - v_b := by
      funext x
      have hx := congrFun hsum x
      change v_a x + v_b x = v_a' x + v_b' x at hx
      dsimp only [Pi.sub_apply]
      linarith
    rw [heq]
    exact Submodule.sub_mem _ hvb' hvb

/-- In the genuine two-component regime, the ambiguity vector in any two
bottom decompositions is killed by ambient adjacency. -/
theorem binarySquare_regular_twoOwner_bottom_decomposition_difference_adjKernel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = q * m c)
    (hsumM : ∑ c, m c = q)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2)
    (a b : (secondOrderDefectGraph G).ConnectedComponent) (hab : a ≠ b)
    {v_a v_b v_a' v_b' : V → ℝ}
    (hva : v_a ∈ realComponentOwnerBottomSubmodule G a (m a))
    (hvb : v_b ∈ realComponentOwnerBottomSubmodule G b (m b))
    (hva' : v_a' ∈ realComponentOwnerBottomSubmodule G a (m a))
    (hvb' : v_b' ∈ realComponentOwnerBottomSubmodule G b (m b))
    (hsum : v_a + v_b = v_a' + v_b') :
    v_a - v_a' ∈ LinearMap.ker (G.adjMatrix ℝ).mulVecLin := by
  let E : (secondOrderDefectGraph G).ConnectedComponent ≃ Fin 2 :=
    Fintype.equivFinOfCardEq hcount
  have hcover (c : (secondOrderDefectGraph G).ConnectedComponent) :
      c = a ∨ c = b := by
    have habE : E a ≠ E b := fun h => hab (E.injective h)
    have hcE : E c = E a ∨ E c = E b := by omega
    rcases hcE with h | h
    · exact Or.inl (E.injective h)
    · exact Or.inr (E.injective h)
  have hd := twoOwner_bottom_decomposition_difference_mem_inf
    G a b hva hvb hva' hvb' hsum
  have hcommon : v_a - v_a' ∈
      realBinarySquareOwnerCommonBottomSubmodule G m := by
    rw [realBinarySquareOwnerCommonBottomSubmodule, Submodule.mem_iInf]
    intro c
    rcases hcover c with rfl | rfl
    · exact hd.1
    · exact hd.2
  rw [binarySquare_regular_realOwnerCommonBottomSubmodule_eq_adjKernel
    G hfree hq hreg hcard m hm hsumM] at hcommon
  exact hcommon

/-- The adjacency kernel acts on two-owner decompositions by opposite shifts.
This is the converse to
`binarySquare_regular_twoOwner_bottom_decomposition_difference_adjKernel`:
the kernel is not merely an upper bound on the ambiguity, but exactly the
space of allowed changes of decomposition. -/
theorem binarySquare_regular_twoOwner_shift_bottom_decomposition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = q * m c)
    (hsumM : ∑ c, m c = q)
    (a b : (secondOrderDefectGraph G).ConnectedComponent)
    {v_a v_b w : V → ℝ}
    (hva : v_a ∈ realComponentOwnerBottomSubmodule G a (m a))
    (hvb : v_b ∈ realComponentOwnerBottomSubmodule G b (m b))
    (hw : w ∈ LinearMap.ker (G.adjMatrix ℝ).mulVecLin) :
    v_a + w ∈ realComponentOwnerBottomSubmodule G a (m a) ∧
      v_b - w ∈ realComponentOwnerBottomSubmodule G b (m b) ∧
      (v_a + w) + (v_b - w) = v_a + v_b := by
  have hwCommon : w ∈ realBinarySquareOwnerCommonBottomSubmodule G m := by
    rw [binarySquare_regular_realOwnerCommonBottomSubmodule_eq_adjKernel
      G hfree hq hreg hcard m hm hsumM]
    exact hw
  have hwBottom (c : (secondOrderDefectGraph G).ConnectedComponent) :
      w ∈ realComponentOwnerBottomSubmodule G c (m c) := by
    rw [realBinarySquareOwnerCommonBottomSubmodule,
      Submodule.mem_iInf] at hwCommon
    exact hwCommon c
  refine ⟨Submodule.add_mem _ hva (hwBottom a), ?_, ?_⟩
  · exact Submodule.sub_mem _ hvb (hwBottom b)
  · ext x
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_twoOwner_exists_bottom_decomposition
#print axioms Erdos85.binarySquare_regular_twoOwner_bottom_decomposition_difference_adjKernel
#print axioms Erdos85.binarySquare_regular_twoOwner_shift_bottom_decomposition
