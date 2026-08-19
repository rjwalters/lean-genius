import Mathlib

/-!
# Residual of a regular graph and a free matching

On eight points, the complement of a four-regular graph together with a
disjoint perfect matching is two-regular.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

def freeInvolutionMatchingGraph {X : Type*}
    (mate : X → X) (hinv : Function.Involutive mate)
    (hfree : ∀ x, mate x ≠ x) : SimpleGraph X where
  Adj x y := mate x = y
  symm := ⟨by
    intro x y hxy
    rw [← hxy, hinv x]⟩
  loopless := ⟨fun x h => hfree x h⟩

instance freeInvolutionMatchingGraph_decidableAdj
    {X : Type*} [DecidableEq X]
    (mate : X → X) (hinv : Function.Involutive mate)
    (hfree : ∀ x, mate x ≠ x) :
    DecidableRel (freeInvolutionMatchingGraph mate hinv hfree).Adj := by
  unfold freeInvolutionMatchingGraph
  infer_instance

theorem freeInvolutionMatchingGraph_degree
    {X : Type*} [Fintype X] [DecidableEq X]
    (mate : X → X) (hinv : Function.Involutive mate)
    (hfree : ∀ x, mate x ≠ x) (x : X) :
    (freeInvolutionMatchingGraph mate hinv hfree).degree x = 1 := by
  rw [degree_eq_one_iff_existsUnique_adj]
  exact ⟨mate x, rfl, fun y hy => Eq.symm hy⟩

/-- The unused pairs after a disjoint four-regular graph and perfect matching
on eight points form a two-factor. -/
theorem fourRegular_disjoint_freeMatching_residual_twoRegular
    {X : Type*} [Fintype X] [DecidableEq X]
    (hcard : Fintype.card X = 8)
    (S : SimpleGraph X) [DecidableRel S.Adj]
    (hS : ∀ x, S.degree x = 4)
    (mate : X → X) (hinv : Function.Involutive mate)
    (hfree : ∀ x, mate x ≠ x)
    (hdisj : ∀ ⦃x y⦄, S.Adj x y → mate x ≠ y) :
    ∀ x, ((S ⊔ freeInvolutionMatchingGraph mate hinv hfree)ᶜ).degree x = 2 := by
  classical
  let M := freeInvolutionMatchingGraph mate hinv hfree
  have hM : ∀ x, M.degree x = 1 :=
    freeInvolutionMatchingGraph_degree mate hinv hfree
  have hUnion : ∀ x, (S ⊔ M).degree x = 5 := by
    intro x
    have hneighbors : (S ⊔ M).neighborFinset x =
        S.neighborFinset x ∪ M.neighborFinset x := by
      ext y
      simp [M]
    have hd : Disjoint (S.neighborFinset x) (M.neighborFinset x) := by
      rw [Finset.disjoint_left]
      intro y hyS hyM
      exact hdisj ((S.mem_neighborFinset x y).mp hyS)
        ((M.mem_neighborFinset x y).mp hyM)
    rw [← (S ⊔ M).card_neighborFinset_eq_degree, hneighbors,
      Finset.card_union_of_disjoint hd, S.card_neighborFinset_eq_degree,
      M.card_neighborFinset_eq_degree, hS x, hM x]
  intro x
  rw [SimpleGraph.degree_compl, hUnion x, hcard]

end

end Erdos85

#print axioms Erdos85.fourRegular_disjoint_freeMatching_residual_twoRegular
