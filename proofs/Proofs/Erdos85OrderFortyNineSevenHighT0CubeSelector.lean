import Mathlib

/-!
# The seven-way selector forced by the normalized `t = 0` prefix

Once the first two high neighborhoods and their internal matchings have been
normalized, the low-neighborhood partition law forces vertex `9` to meet one
of `15, ..., 21`.  The `C₄` common-neighbor bound makes that choice unique.
This is exactly the final seven-way cube selector used by the certificate
generator.
-/

namespace Erdos85

open Std.Tactic.BVDecide

/-- The structural fields shared by all seven cubes already force a unique
cube selector.  This packages the only non-canonical datum left after the
`N₀`/`N₁` prefix normalization. -/
theorem sevenHighT0_exists_unique_cube_selector
    (adj : Fin 49 → Fin 49 → Bool)
    (hsymm : ∀ i j, adj i j = adj j i)
    (h97 : adj 7 9 = false)
    (hn1 : ∀ x : Fin 49, 7 ≤ x.val →
      adj 1 x = decide (x.val = 7 ∨ (15 ≤ x.val ∧ x.val < 22)))
    (hc4 : ∀ i j : Fin 49, i ≠ j →
      (Finset.univ.filter fun w => adj i w && adj j w).card ≤ 1)
    (hpartition : ∃ x : Fin 49,
      (x.val = 7 ∨ (15 ≤ x.val ∧ x.val < 22)) ∧
      x ≠ (9 : Fin 49) ∧ adj 9 x = true) :
    ∃ cube : Fin 7, ∀ index : Fin 7,
      adj 9 ⟨index.val + 15, by omega⟩ = decide (index = cube) := by
  obtain ⟨x, hxrange, hxne, h9x⟩ := hpartition
  have hxnot7 : x.val ≠ 7 := by
    intro hx7
    have h9seven : adj (9 : Fin 49) (7 : Fin 49) = false :=
      (hsymm 9 7).trans h97
    have hxeq : x = (⟨7, by omega⟩ : Fin 49) := Fin.ext hx7
    have hseven : (⟨7, by omega⟩ : Fin 49) = 7 := Fin.ext rfl
    rw [hxeq, hseven, h9seven] at h9x
    contradiction
  have hx15 : 15 ≤ x.val := (hxrange.resolve_left hxnot7).1
  have hx22 : x.val < 22 := (hxrange.resolve_left hxnot7).2
  let cube : Fin 7 := ⟨x.val - 15, by omega⟩
  refine ⟨cube, ?_⟩
  intro index
  let z : Fin 49 := ⟨index.val + 15, by omega⟩
  have h1x : adj 1 x = true := by
    rw [hn1 x (by omega)]
    simp [hx15, hx22]
  have h1z : adj 1 z = true := by
    have hz7 : 7 ≤ z.val := by simp [z]
    have hz15 : 15 ≤ z.val := by simp [z]
    have hz22 : z.val < 22 := by simp [z]; omega
    rw [hn1 z hz7]
    simp [hz15, hz22]
  by_cases hiz : index = cube
  · subst index
    have hzx : z = x := by
      apply Fin.ext
      simp [z, cube]
      omega
    simp only [decide_true]
    simpa [z] using (show adj 9 z = true from hzx ▸ h9x)
  · have hzx : z ≠ x := by
      intro h
      apply hiz
      apply Fin.ext
      have hval : index.val + 15 = x.val := congrArg Fin.val h
      change index.val = cube.val
      change index.val = x.val - 15
      omega
    have h9z : adj 9 z = false := by
      by_contra h9zfalse
      have h9ztrue : adj 9 z = true := by simpa using h9zfalse
      let common := Finset.univ.filter fun w => adj 1 w && adj 9 w
      have hxcommon : x ∈ common := by simp [common, h1x, h9x]
      have hzcommon : z ∈ common := by simp [common, h1z, h9ztrue]
      have heq := (Finset.card_le_one.mp
        (hc4 (1 : Fin 49) (9 : Fin 49) (by decide))) x hxcommon z hzcommon
      exact hzx heq.symm
    simp [hiz, z, h9z]

end Erdos85
