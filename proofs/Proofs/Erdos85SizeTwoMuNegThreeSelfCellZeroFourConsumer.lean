import Proofs.Erdos85SizeTwoMuNegThreeSelfCellZeroFour
import Proofs.Erdos85SizeTwoMuNegThreeEightEightDiagonalSameShape

/-!
# Graph socket for the μ=-3 self-cell (k,r) = (0,4) kill

Node: outline F.3 (μ=-3 lane; consumer of kernel `e42f2a64a8`).

On a normalized C8 shore whose diagonal defect block has row degree `3`
(that is, cross quotient `r = 4`), empty same-sign rows (`k = 0`), and
both ambient cycle entries present (the all-TF sector), the coordinate
defect matrix satisfies the impossible profile of
`zmodEight_selfIntertwiner_oppositeOnly_rowThree_with_cycle_impossible`.
The cell-router discharges the three ledger hypotheses from the banked
quotient, normal-form, and sector theorems.
-/

open Finset SimpleGraph

namespace Erdos85

/-- **The `(0,4)` self-cell socket.**  A normalized alternating C8 shore
whose diagonal defect rows have cardinal `3`, no same-sign entries, and
both cycle entries present is impossible. -/
theorem graph_zmodEight_selfCell_zeroFour_false
    {X : Type*} [Fintype X] [DecidableEq X]
    (H K : SimpleGraph X) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (u : ZMod 8 → X) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (s : X → ℤ)
    (hsign : ∀ i, s (u i) = -1 ∨ s (u i) = 1)
    (hflip : ∀ i, s (u (i + 1)) = -s (u i))
    (hcomm : K.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * K.adjMatrix ℤ)
    (hrow3 : ∀ i, ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      K.Adj (u i) (u j)).card = 3)
    (hsame0 : ∀ i, ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      s (u j) = s (u i) ∧ K.Adj (u i) (u j)).card = 0)
    (hcyc : ∀ i, K.Adj (u i) (u (i + 1))) : False := by
  classical
  let M : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  have hupair : ∀ z, u (z - 1) ≠ u (z + 1) := fun z ↦
    huinj.ne (zmod_sub_one_ne_add_one_of_three_le (by omega) z)
  have hinter : ∀ i j,
      M (i - 1) j + M (i + 1) j = M i (j + 1) + M i (j - 1) := by
    simpa only [M] using entry_cycleIntertwine_of_adjMatrix_comm
      K H u u (1 : ZMod 8) (1 : ZMod 8) hcomm hu hu hupair hupair
  have hsymmM : ∀ i j, M i j = M j i := by
    intro i j
    by_cases hij : K.Adj (u i) (u j)
    · have hji : K.Adj (u j) (u i) := (K.adj_comm _ _).mp hij
      simp [M, SimpleGraph.adjMatrix_apply, hij, hji]
    · have hji : ¬ K.Adj (u j) (u i) := by
        intro h
        exact hij ((K.adj_comm _ _).mp h)
      simp [M, SimpleGraph.adjMatrix_apply, hij, hji]
  have hbinaryM : ∀ i j, M i j = 0 ∨ M i j = 1 := by
    intro i j
    by_cases h : K.Adj (u i) (u j)
    · right
      simp [M, SimpleGraph.adjMatrix_apply, h]
    · left
      simp [M, SimpleGraph.adjMatrix_apply, h]
  have hrowM : ∀ i, ∑ j, M i j = 3 := by
    intro i
    have hcast : ∑ j, M i j =
        (((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          K.Adj (u i) (u j)).card : ℤ) := by
      simp [M, SimpleGraph.adjMatrix_apply, Finset.sum_boole]
    rw [hcast, hrow3]
    norm_num
  have heven := zmodEight_alternating_sign_eq_iff_evenOffset
    (fun i ↦ s (u i)) hsign hflip
  have heven0M : ∀ i j, ZModEightEvenOffset (j - i) → M i j = 0 := by
    intro i j he
    by_contra hM
    have hadj : K.Adj (u i) (u j) := by
      by_contra h
      exact hM (by simp [M, SimpleGraph.adjMatrix_apply, h])
    have hfeq : s (u j) = s (u i) := (heven i j).mpr he
    have hmem : j ∈ (Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (u j) = s (u i) ∧ K.Adj (u i) (u j) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfeq, hadj⟩
    have := hsame0 i
    rw [Finset.card_eq_zero] at this
    rw [this] at hmem
    exact Finset.notMem_empty _ hmem
  have hcycM : ∀ i, M i (i - 1) = 1 ∧ M i (i + 1) = 1 := by
    intro i
    constructor
    · have hadj : K.Adj (u i) (u (i - 1)) := by
        have h := hcyc (i - 1)
        rw [show i - 1 + 1 = i by ring] at h
        exact (K.adj_comm _ _).mp h
      simp [M, SimpleGraph.adjMatrix_apply, hadj]
    · simp [M, SimpleGraph.adjMatrix_apply, hcyc i]
  exact zmodEight_selfIntertwiner_oppositeOnly_rowThree_with_cycle_impossible
    M hsymmM hinter hbinaryM hrowM heven0M hcycM

end Erdos85

#print axioms Erdos85.graph_zmodEight_selfCell_zeroFour_false
