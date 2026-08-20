import Proofs.Erdos85MuNegThreeZeroFiveCorrectShoreGeometry

/-! # Exceptional coordinates for cross-shore cubic equality -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

def h305CrossCubicExceptionalCoordinates
    {V : Type*} [DecidableEq V]
    (u v : ZMod 8 → V) (i j : ZMod 8) : Finset V :=
  {u (i - 1), u (i + 1), v (j - 1), v (j + 1)}

set_option maxRecDepth 100000 in
private theorem zmodEight_plusMinus_ne :
    ∀ i : ZMod 8, i - 1 ≠ i + 1 := by
  native_decide

/-- The two coordinates adjacent to each endpoint on each C8 shore are four
distinct vertices. -/
theorem h305CrossCubicExceptionalCoordinates_card_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hdisj : ∀ k l, u k ≠ v l) (i j : ZMod 8) :
    (h305CrossCubicExceptionalCoordinates u v i j).card = 4 := by
  classical
  have huu : u (i - 1) ≠ u (i + 1) :=
    huinj.ne (zmodEight_plusMinus_ne i)
  have hvv : v (j - 1) ≠ v (j + 1) :=
    hvinj.ne (zmodEight_plusMinus_ne j)
  simp [h305CrossCubicExceptionalCoordinates, huu, hvv,
    hdisj (i - 1) (j - 1), hdisj (i - 1) (j + 1),
    hdisj (i + 1) (j - 1), hdisj (i + 1) (j + 1)]

set_option maxRecDepth 100000 in
private theorem zmodEight_plusMinus_difference :
    ∀ i : ZMod 8, (i + 1) - (i - 1) = 2 := by
  native_decide

/-- In either correct h305 shore mode, the two exceptional coordinates on
one shore are not joined by an exterior edge (their cyclic offset is two). -/
theorem h305_crossExceptional_sameShore_not_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V)
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (i : ZMod 8) :
    ¬ R.Adj (u (i - 1)) (u (i + 1)) := by
  rcases hmode with hmode | hmode
  · rw [hmode]
    rw [zmodEight_plusMinus_difference]
    native_decide
  · rw [hmode]
    rw [zmodEight_plusMinus_difference]
    native_decide

/-- An exterior edge supported on the four exceptional coordinates has one
endpoint on each shore.  The only other possible two-point supports are the
two forbidden offset-two same-shore pairs. -/
theorem h305_crossExceptional_edge_one_endpoint_each_shore
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hdisj : ∀ k l, u k ≠ v l)
    (hmodeu : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hmodev : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v)
    (i j : ZMod 8) (b : R.edgeFinset)
    (hsub : b.1.toFinset ⊆ h305CrossCubicExceptionalCoordinates u v i j) :
    (b.1.toFinset ∩ {u (i - 1), u (i + 1)}).card = 1 ∧
      (b.1.toFinset ∩ {v (j - 1), v (j + 1)}).card = 1 := by
  classical
  let E := b.1.toFinset
  let U : Finset V := {u (i - 1), u (i + 1)}
  let W : Finset V := {v (j - 1), v (j + 1)}
  have hEcard : E.card = 2 := R.card_toFinset_mem_edgeFinset b
  have hUcard : U.card = 2 := by
    simp [U, huinj.ne (zmodEight_plusMinus_ne i)]
  have hWcard : W.card = 2 := by
    simp [W, hvinj.ne (zmodEight_plusMinus_ne j)]
  have hX : h305CrossCubicExceptionalCoordinates u v i j = U ∪ W := by
    ext x
    simp only [h305CrossCubicExceptionalCoordinates, U, W,
      Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
    aesop
  have hEUW : E ⊆ U ∪ W := by simpa [E, hX] using hsub
  have hUW : Disjoint U W := by
    refine Finset.disjoint_left.mpr ?_
    intro x hxU hxW
    simp only [U, Finset.mem_insert, Finset.mem_singleton] at hxU
    simp only [W, Finset.mem_insert, Finset.mem_singleton] at hxW
    rcases hxU with hxU | hxU <;> rcases hxW with hxW | hxW
    all_goals exact hdisj _ _ (hxU.symm.trans hxW)
  have hnotU : E ≠ U := by
    intro hEq
    have hEq' : b.1.toFinset = {u (i - 1), u (i + 1)} := by
      simpa [E, U] using hEq
    have hedge : b.1 = s(u (i - 1), u (i + 1)) := by
      apply Sym2.ext
      intro x
      rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, hEq']
      simp [Sym2.toFinset_mk_eq]
    have hadj : R.Adj (u (i - 1)) (u (i + 1)) := by
      apply (R.mem_edgeSet).mp
      simpa [hedge] using b.2
    exact h305_crossExceptional_sameShore_not_adj R u hmodeu i hadj
  have hnotW : E ≠ W := by
    intro hEq
    have hEq' : b.1.toFinset = {v (j - 1), v (j + 1)} := by
      simpa [E, W] using hEq
    have hedge : b.1 = s(v (j - 1), v (j + 1)) := by
      apply Sym2.ext
      intro x
      rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, hEq']
      simp [Sym2.toFinset_mk_eq]
    have hadj : R.Adj (v (j - 1)) (v (j + 1)) := by
      apply (R.mem_edgeSet).mp
      simpa [hedge] using b.2
    exact h305_crossExceptional_sameShore_not_adj R v hmodev j hadj
  have hsplit : (E ∩ U).card + (E ∩ W).card = E.card := by
    have hdiff : E \ U = E ∩ W := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_inter]
      constructor
      · rintro ⟨hxE, hxU⟩
        have hxUW := hEUW hxE
        rw [Finset.mem_union] at hxUW
        exact ⟨hxE, hxUW.resolve_left hxU⟩
      · rintro ⟨hxE, hxW⟩
        exact ⟨hxE, fun hxU ↦ Finset.disjoint_left.mp hUW hxU hxW⟩
    simpa [hdiff] using Finset.card_inter_add_card_sdiff E U
  have hUne : (E ∩ U).card ≠ 2 := by
    intro hcard
    have heq : E ∩ U = E :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    apply hnotU
    apply Finset.eq_of_subset_of_card_le
    · simpa [heq] using Finset.inter_subset_right (s₁ := E) (s₂ := U)
    · omega
  have hWne : (E ∩ W).card ≠ 2 := by
    intro hcard
    have heq : E ∩ W = E :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    apply hnotW
    apply Finset.eq_of_subset_of_card_le
    · simpa [heq] using Finset.inter_subset_right (s₁ := E) (s₂ := W)
    · omega
  change (E ∩ U).card = 1 ∧ (E ∩ W).card = 1
  omega

end

end Erdos85

#print axioms Erdos85.h305CrossCubicExceptionalCoordinates_card_four
#print axioms Erdos85.h305_crossExceptional_sameShore_not_adj
#print axioms Erdos85.h305_crossExceptional_edge_one_endpoint_each_shore
