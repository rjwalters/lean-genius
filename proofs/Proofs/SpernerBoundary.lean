/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Proofs.SpernerDoorCount

/-!
# Sperner boundary reduction

With a Sperner coloring, every boundary door lies on the last face.
This eliminates the need to sum over all faces and ties the abstract
door-counting machinery to the Sperner coloring condition.

## Main results

* `Sperner.IsSpernerColoring`: a coloring satisfying the Sperner
  boundary condition (vertices on face `k` do not receive color `k`).
* `Sperner.boundary_doors_on_last_face`: every boundary door lies on
  the last face under a Sperner coloring.
* `Sperner.boundary_doors_odd_of_last_face`: the boundary door set
  equals the last-face door set, so its parity is determined by the
  last face alone.
-/

namespace Sperner

open Finset

/-! ### Boundary reduction

With a Sperner coloring, every boundary door lies on the last face.
This eliminates the need to sum over all faces. -/

section BoundaryReduction

variable {V : Type*} [DecidableEq V] {n : ℕ}
variable {Cell : Type*} [DecidableEq Cell] [Fintype Cell]

/-- A Sperner coloring: if vertex `v` is on face `k`, then `c v` is
not `k`. -/
def IsSpernerColoring
    (c : V → Fin (n + 1))
    (onFace : V → Fin (n + 1) → Prop) : Prop :=
  ∀ v k, onFace v k → c v ≠ k

omit [DecidableEq V] [DecidableEq Cell] [Fintype Cell] in
/-- **Boundary doors on the last face**: given a Sperner coloring, every
boundary door must lie on face `n` (the last face). Any door on a lower
face `faceIdx < n` leads to a contradiction between the door condition
(which requires color `faceIdx` on some non-omitted vertex) and the
Sperner condition (which forbids color `faceIdx` on vertices of face
`faceIdx`). -/
theorem boundary_doors_on_last_face
    (vertex : Cell → Fin (n + 1) → V)
    (adj : Cell → Fin (n + 1) → Option (Cell × Fin (n + 1)))
    (c : V → Fin (n + 1))
    (onFace : V → Fin (n + 1) → Prop)
    [∀ v k, Decidable (onFace v k)]
    (hSperner : IsSpernerColoring c onFace)
    (hBoundaryOnFace : ∀ s k, adj s k = none →
      ∃ faceIdx : Fin (n + 1), ∀ j : Fin (n + 1),
        j ≠ k → onFace (vertex s j) faceIdx)
    {s : Cell} {k : Fin (n + 1)}
    (hDoor : IsDoor vertex c s k)
    (hAdj : adj s k = none) :
    ∀ j : Fin (n + 1), j ≠ k →
      onFace (vertex s j) ⟨n, by omega⟩ := by
  obtain ⟨faceIdx, hOnFace⟩ := hBoundaryOnFace s k hAdj
  by_cases hlt : faceIdx.val < n
  · exfalso
    have hDoor' := hDoor ⟨faceIdx.val, hlt⟩
    obtain ⟨i, hi_ne, hi_color⟩ := hDoor'
    have hOnFace_i := hOnFace i hi_ne
    have hSperner_i := hSperner (vertex s i) faceIdx hOnFace_i
    have hcast : (⟨faceIdx.val, hlt⟩ : Fin n).castSucc = faceIdx :=
      Fin.ext (by simp [Fin.castSucc])
    rw [hcast] at hi_color
    exact hSperner_i hi_color
  · have hval : faceIdx.val = n := by have := faceIdx.isLt; omega
    have heq : faceIdx = ⟨n, by omega⟩ := Fin.ext hval
    rw [heq] at hOnFace
    exact hOnFace

omit [DecidableEq V] in
/-- **Boundary door parity for Sperner colorings**: given that all
boundary doors lie on the last face, the boundary door set equals
the last-face door set, so its parity is determined by the last
face alone. -/
theorem boundary_doors_odd_of_last_face
    (vertex : Cell → Fin (n + 1) → V)
    (adj : Cell → Fin (n + 1) → Option (Cell × Fin (n + 1)))
    (c : V → Fin (n + 1))
    (onFace : V → Fin (n + 1) → Prop)
    [∀ v k, Decidable (onFace v k)]
    (hSperner : IsSpernerColoring c onFace)
    (hBoundaryOnFace : ∀ s k, adj s k = none →
      ∃ faceIdx : Fin (n + 1), ∀ j : Fin (n + 1),
        j ≠ k → onFace (vertex s j) faceIdx)
    (hLastFace : Odd (univ.filter
      (fun p : Cell × Fin (n + 1) =>
        IsDoor vertex c p.1 p.2 ∧
        adj p.1 p.2 = none ∧
        (∀ j : Fin (n + 1), j ≠ p.2 →
          onFace (vertex p.1 j) ⟨n, by omega⟩))).card) :
    Odd (univ.filter
      (fun p : Cell × Fin (n + 1) =>
        IsDoor vertex c p.1 p.2 ∧ adj p.1 p.2 = none)).card := by
  suffices h : univ.filter
      (fun p : Cell × Fin (n + 1) =>
        IsDoor vertex c p.1 p.2 ∧ adj p.1 p.2 = none) =
    univ.filter
      (fun p : Cell × Fin (n + 1) =>
        IsDoor vertex c p.1 p.2 ∧ adj p.1 p.2 = none ∧
        (∀ j : Fin (n + 1), j ≠ p.2 →
          onFace (vertex p.1 j) ⟨n, by omega⟩)) by
    rw [h]; exact hLastFace
  ext ⟨s, k⟩
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro ⟨hDoor, hAdj⟩
    exact ⟨hDoor, hAdj,
      boundary_doors_on_last_face vertex adj c onFace hSperner
        hBoundaryOnFace hDoor hAdj⟩
  · intro ⟨hDoor, hAdj, _⟩
    exact ⟨hDoor, hAdj⟩

end BoundaryReduction

end Sperner
