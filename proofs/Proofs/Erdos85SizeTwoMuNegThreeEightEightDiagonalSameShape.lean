import Proofs.Erdos85SizeTwoMuNegThreeEightEightSignedParameterConsumer
import Proofs.Erdos85SizeTwoEigenlineEightEightHighAntipodalMatching
import Proofs.Erdos85ZModEightMixedSelfIntertwinerExclusion

/-! # The three signed diagonal shapes in the `mu=-3` eight-plus-eight stratum -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- The three possible same-sign supports of a loopless signed C8 block. -/
def ZModEightSameSignShape
    (M : Matrix (ZMod 8) (ZMod 8) ℤ) (f : ZMod 8 → ℤ) (k : ℕ) : Prop :=
  (k = 0 ∧ ∀ i j, f j = f i → M i j ≠ 1) ∨
  (k = 1 ∧ ∀ i j, f j = f i → (M i j = 1 ↔ j - i = 4)) ∨
  (k = 2 ∧ ∀ i j, f j = f i →
    (M i j = 1 ↔ j - i = 2 ∨ j - i = 6))

/-- A symmetric loopless C8 self-intertwiner whose alternating-line
same-sign degree is at most two has exactly one of three shapes: empty,
the antipodal matching, or the offset `±2` cycle. -/
theorem zmodEight_selfIntertwiner_sameSign_shape_of_degree_le_two
    (M : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f : ZMod 8 → ℤ)
    (k : ℕ) (hk : k ≤ 2)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i)
    (hdiag : ∀ i, M i i = 0)
    (hsymm : ∀ i j, M i j = M j i)
    (hinter : ∀ i j,
      M (i - 1) j + M (i + 1) j = M i (j + 1) + M i (j - 1))
    (hdegree : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        f j = f i ∧ M i j = 1).card = k) :
    ZModEightSameSignShape M f k := by
  classical
  dsimp [ZModEightSameSignShape]
  have heven := zmodEight_alternating_sign_eq_iff_evenOffset f hsign hflip
  interval_cases k
  · left
    refine ⟨rfl, ?_⟩
    intro i j hsame hm
    have hjmem : j ∈ (Finset.univ : Finset (ZMod 8)).filter
        (fun z ↦ f z = f i ∧ M i z = 1) := by simp [hsame, hm]
    have hpos := Finset.card_pos.mpr ⟨j, hjmem⟩
    rw [hdegree i] at hpos
    omega
  · right; left
    refine ⟨rfl, ?_⟩
    have hdegree' : ∀ i,
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          ZModEightEvenOffset (j - i) ∧ M i j = 1).card = 1 := by
      intro i
      calc
        _ = ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
            f j = f i ∧ M i j = 1).card := by
          congr 1
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← heven i j]
        _ = 1 := hdegree i
    have hshape := zmodEight_selfIntertwiner_sameParity_degreeOne_offset_four
      M hdiag hsymm hinter hdegree'
    intro i j hsame
    exact hshape i j ((heven i j).mp hsame)
  · right; right
    refine ⟨rfl, ?_⟩
    have hdegree' : ∀ i,
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          ZModEightEvenOffset (j - i) ∧ M i j = 1).card = 2 := by
      intro i
      calc
        _ = ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
            f j = f i ∧ M i j = 1).card := by
          congr 1
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← heven i j]
        _ = 2 := hdegree i
    have hshape := zmodEight_selfIntertwiner_sameParity_degreeTwo_offset_two_six
      M hdiag hsymm hinter hdegree'
    intro i j hsame
    exact hshape i j ((heven i j).mp hsame)

/-- Pulling a filtered graph row back through an injective coordinate map
preserves its cardinality. -/
theorem coordinate_sameSign_adj_card_eq_support
    {X : Type*} [Fintype X] [DecidableEq X]
    (K : SimpleGraph X) [DecidableRel K.Adj]
    (A : Finset X) (u : ZMod 8 → X) (huinj : Function.Injective u)
    (hurange : Set.range u = ↑A) (s : X → ℤ) (i : ZMod 8) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      s (u j) = s (u i) ∧ K.Adj (u i) (u j)).card =
    (A.filter fun y ↦ K.Adj (u i) y ∧ s y = s (u i)).card := by
  classical
  apply Finset.card_bij (fun j _ ↦ u j)
  · intro j hj
    have hj' := Finset.mem_filter.mp hj
    rw [Finset.mem_filter]
    refine ⟨?_, hj'.2.2, hj'.2.1⟩
    change u j ∈ (↑A : Set X)
    rw [← hurange]
    exact ⟨j, rfl⟩
  · intro j₁ hj₁ j₂ hj₂ h
    exact huinj h
  · intro x hx
    have hx' := Finset.mem_filter.mp hx
    have hxS : x ∈ (↑A : Set X) := hx'.1
    rw [← hurange] at hxS
    obtain ⟨j, rfl⟩ := hxS
    refine ⟨j, ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hx'.2.2, hx'.2.1⟩

end

end Erdos85

#print axioms Erdos85.zmodEight_selfIntertwiner_sameSign_shape_of_degree_le_two
