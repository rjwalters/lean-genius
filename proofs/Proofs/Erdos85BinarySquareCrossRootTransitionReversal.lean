import Proofs.Erdos85BinarySquareCrossRootCenterPairs

/-! # Reversal of cross-root transition factors -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Transpose a finite bipartite relation by exchanging its coordinates. -/
def transposePairFinset
    {A : Type*} [DecidableEq A] (S : Finset (A × A)) : Finset (A × A) :=
  S.image Prod.swap

/-- Transposition is an involution on finite pair relations. -/
theorem transposePairFinset_transposePairFinset
    {A : Type*} [DecidableEq A] (S : Finset (A × A)) :
    transposePairFinset (transposePairFinset S) = S := by
  classical
  ext ⟨a, b⟩
  simp [transposePairFinset, Prod.swap]

/-- Reversing the ordered root pair transposes each canonical center pair. -/
theorem crossRootCenterPair_swap_roots
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d e : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (x y : d.supp) (w : e.supp) :
    crossRootCenterPair G hfree hde y x w =
      (crossRootCenterPair G hfree hde x y w).swap := by
  rfl

/-- Reversing a defect edge transposes the entire transition factor supplied
by a fixed remote target component. -/
theorem crossRootCenterPairFinset_swap_roots
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d e : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (x y : d.supp) :
    crossRootCenterPairFinset G hfree hde y x =
      transposePairFinset (crossRootCenterPairFinset G hfree hde x y) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨w, _hw, hpw⟩ := Finset.mem_image.mp hp
    rw [crossRootCenterPair_swap_roots G hfree hde x y w] at hpw
    apply Finset.mem_image.mpr
    refine ⟨(crossRootCenterPair G hfree hde x y w), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩
    · simpa [transposePairFinset] using hpw
  · intro hp
    rw [transposePairFinset] at hp
    obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hp
    obtain ⟨w, _hw, hqw⟩ := Finset.mem_image.mp hq
    apply Finset.mem_image.mpr
    refine ⟨w, Finset.mem_univ _, ?_⟩
    rw [crossRootCenterPair_swap_roots G hfree hde x y w]
    simpa [hqw] using hqp

/-- Pointwise membership form of transition-factor reversal. -/
theorem mem_crossRootCenterPairFinset_swap_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d e : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (x y : d.supp) (p : V × V) :
    p ∈ crossRootCenterPairFinset G hfree hde x y ↔
      p.swap ∈ crossRootCenterPairFinset G hfree hde y x := by
  rw [crossRootCenterPairFinset_swap_roots G hfree hde x y]
  simp [transposePairFinset]

end

end Erdos85
