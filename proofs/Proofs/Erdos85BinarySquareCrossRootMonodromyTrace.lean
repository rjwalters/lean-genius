import Proofs.Erdos85BinarySquareCrossRootTransitionComposition

/-! # Diagonal trace of cross-root transition monodromy -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Fixed points of a finite relation, i.e. its diagonal support. -/
def pairRelationFixedPoints
    {A : Type*} [Fintype A] [DecidableEq A]
    (S : Finset (A × A)) : Finset A :=
  (Finset.univ : Finset A).filter fun a => (a, a) ∈ S

/-- Transposition does not change the diagonal support of a relation. -/
theorem pairRelationFixedPoints_transpose
    {A : Type*} [Fintype A] [DecidableEq A]
    (S : Finset (A × A)) :
    pairRelationFixedPoints (transposePairFinset S) =
      pairRelationFixedPoints S := by
  classical
  ext a
  simp [pairRelationFixedPoints, mem_transposePairFinset_iff]

/-- Cardinal-valued diagonal trace of a finite relation. -/
def pairRelationTrace
    {A : Type*} [Fintype A] [DecidableEq A]
    (S : Finset (A × A)) : ℕ :=
  (pairRelationFixedPoints S).card

theorem pairRelationTrace_transpose
    {A : Type*} [Fintype A] [DecidableEq A]
    (S : Finset (A × A)) :
    pairRelationTrace (transposePairFinset S) = pairRelationTrace S := by
  rw [pairRelationTrace, pairRelationTrace,
    pairRelationFixedPoints_transpose]

/-- Reversing an oriented transition path preserves its monodromy fixed
points exactly, not merely their cardinality. -/
theorem pairRelationFixedPoints_reversePath
    {A : Type*} [Fintype A] [DecidableEq A]
    (factors : List (Finset (A × A))) :
    pairRelationFixedPoints
        (composePairFinsetList
          (factors.reverse.map transposePairFinset)) =
      pairRelationFixedPoints (composePairFinsetList factors) := by
  rw [← transposePairFinset_composePairFinsetList,
    pairRelationFixedPoints_transpose]

/-- Scalar trace form of path-reversal invariance. -/
theorem pairRelationTrace_reversePath
    {A : Type*} [Fintype A] [DecidableEq A]
    (factors : List (Finset (A × A))) :
    pairRelationTrace
        (composePairFinsetList
          (factors.reverse.map transposePairFinset)) =
      pairRelationTrace (composePairFinsetList factors) := by
  simp only [pairRelationTrace]
  rw [pairRelationFixedPoints_reversePath]

/-- Existence of a closed transition is cyclic for a two-block composite.
The number of supported diagonal vertices need not be cyclic, so this is the
correct basepoint-free Boolean monodromy invariant. -/
theorem pairRelationFixedPoints_compose_nonempty_comm
    {A : Type*} [Fintype A] [DecidableEq A]
    (S T : Finset (A × A)) :
    (pairRelationFixedPoints (composePairFinset S T)).Nonempty ↔
      (pairRelationFixedPoints (composePairFinset T S)).Nonempty := by
  classical
  constructor
  · rintro ⟨a, ha⟩
    have haa : (a, a) ∈ composePairFinset S T := by
      simpa [pairRelationFixedPoints] using ha
    obtain ⟨b, hab, hba⟩ :=
      (mem_composePairFinset_iff S T a a).mp haa
    refine ⟨b, ?_⟩
    simp only [pairRelationFixedPoints, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact (mem_composePairFinset_iff T S b b).mpr ⟨a, hba, hab⟩
  · rintro ⟨b, hb⟩
    have hbb : (b, b) ∈ composePairFinset T S := by
      simpa [pairRelationFixedPoints] using hb
    obtain ⟨a, hba, hab⟩ :=
      (mem_composePairFinset_iff T S b b).mp hbb
    refine ⟨a, ?_⟩
    simp only [pairRelationFixedPoints, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact (mem_composePairFinset_iff S T a a).mpr ⟨b, hab, hba⟩

/-- Closed-transition existence is invariant under changing the basepoint of
a cyclic factor list, represented by exchanging two consecutive chunks. -/
theorem pairRelationFixedPoints_composeList_rotate_nonempty
    {A : Type*} [Fintype A] [DecidableEq A]
    (xs ys : List (Finset (A × A))) :
    (pairRelationFixedPoints (composePairFinsetList (xs ++ ys))).Nonempty ↔
      (pairRelationFixedPoints (composePairFinsetList (ys ++ xs))).Nonempty := by
  rw [composePairFinsetList_append, composePairFinsetList_append]
  exact pairRelationFixedPoints_compose_nonempty_comm _ _

/-- For two consecutive cross-root factors, traversing the roots in the
opposite direction preserves the exact monodromy fixed-point set. -/
theorem crossRoot_twoStepTransition_fixedPoints_reverse
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d e : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (x y z : d.supp) :
    pairRelationFixedPoints
        (composePairFinset
          (crossRootCenterPairFinset G hfree hde z y)
          (crossRootCenterPairFinset G hfree hde y x)) =
      pairRelationFixedPoints
        (composePairFinset
          (crossRootCenterPairFinset G hfree hde x y)
          (crossRootCenterPairFinset G hfree hde y z)) := by
  rw [← crossRoot_twoStepTransition_reverse G hfree hde x y z,
    pairRelationFixedPoints_transpose]

end

end Erdos85
