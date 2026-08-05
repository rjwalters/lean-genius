import Proofs.Erdos85BinaryCycleIntertwiner

/-!
# Diagonal cycle blocks of the adjacency matrix are circulant

The orientation dichotomy `graph_equalOddCycleBlock_orientation` for the
adjacency block between two labeled equal odd defect cycles leaves two
cases: translation invariant (circulant) or reverse-translation
invariant.  For the **diagonal** block of a cycle against itself the
reverse case degenerates: a reverse-invariant block is a function of the
coordinate sum, its diagonal entries are the loops `A (u x) (u x) = 0`,
and for odd `r` doubling is onto, so the block vanishes identically — in
particular it is then also translation invariant.  Hence every diagonal
cycle block is circulant.

This is exactly the translation-invariance input consumed by the
frequency-pair trace identity in `Erdos85FrequencyPairProjector`, and it
requires no global orientation propagation across different cycles.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Diagonal blocks of an adjacency matrix commuting with the equal-odd-
cycle two-factor are translation invariant. -/
theorem graph_equalOddCycle_diagBlock_translationInvariant
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r) (hrOdd : Odd r)
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : ZMod r → V) (huinj : Function.Injective u)
    (hcomm : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    (hu : ∀ x, D.neighborFinset (u x) = {u (x - 1), u (x + 1)}) :
    ∀ x y : ZMod r, G.adjMatrix ℤ (u (x + 1)) (u (y + 1)) =
      G.adjMatrix ℤ (u x) (u y) := by
  rcases graph_equalOddCycleBlock_orientation hr3 hrOdd G D u u huinj huinj
    hcomm hu hu with hcirc | hrev
  · exact hcirc
  · have hunit : IsUnit (2 : ZMod r) := by
      simpa using (ZMod.isUnit_iff_coprime 2 r).mpr
        (Nat.coprime_two_left.mpr hrOdd)
    set B : Matrix (ZMod r) (ZMod r) ℤ :=
      Matrix.of fun x y ↦ G.adjMatrix ℤ (u x) (u y) with hB
    have hrevB : ∀ x y, B (x + 1) (y - 1) = B x y := fun x y ↦ hrev x y
    have hzero : ∀ x y : ZMod r, B x y = 0 := by
      intro x y
      obtain ⟨w, hw⟩ := hunit.exists_left_inv
      have hm : (w * (y + x)) + (w * (y + x)) = y + x := by
        have h2 : (w * (y + x)) + (w * (y + x)) = (w * 2) * (y + x) := by
          ring
        rw [h2, hw, one_mul]
      have heq : B (w * (y + x)) (w * (y + x)) = B x y :=
        reverseTranslationInvariant_eq_of_add_eq B hrevB hm
      rw [← heq, hB]
      simp [SimpleGraph.adjMatrix_apply]
    intro x y
    have h1 : G.adjMatrix ℤ (u (x + 1)) (u (y + 1)) = B (x + 1) (y + 1) :=
      rfl
    have h2 : G.adjMatrix ℤ (u x) (u y) = B x y := rfl
    rw [h1, h2, hzero, hzero]

/-- Adjacency form of the diagonal-block translation invariance. -/
theorem graph_equalOddCycle_diagBlock_adj_shift_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r) (hrOdd : Odd r)
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : ZMod r → V) (huinj : Function.Injective u)
    (hcomm : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    (hu : ∀ x, D.neighborFinset (u x) = {u (x - 1), u (x + 1)})
    (x y : ZMod r) :
    G.Adj (u (x + 1)) (u (y + 1)) ↔ G.Adj (u x) (u y) := by
  have h := graph_equalOddCycle_diagBlock_translationInvariant hr3 hrOdd
    G D u huinj hcomm hu x y
  simp only [SimpleGraph.adjMatrix_apply] at h
  by_cases h1 : G.Adj (u (x + 1)) (u (y + 1)) <;>
    by_cases h2 : G.Adj (u x) (u y) <;>
      simp [h1, h2] at h ⊢

end

end Erdos85
