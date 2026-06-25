import Mathlib

/-
# Descartes' Theorem on the total angular defect (discrete Gauss–Bonnet)

Around 1630 Descartes observed that for a convex polyhedron the *total angular
defect* — the sum over all vertices of `2π` minus the angles of the faces
meeting there — is always `4π` (i.e. `720°`), regardless of the shape.  This is
the polyhedral (discrete) form of the Gauss–Bonnet theorem, and it is
equivalent to Euler's polyhedral formula `V - E + F = 2`.

This file gives a self-contained, 0-axiom formalization.  We model the
combinatorial data of a polyhedral surface (the vertex/edge/face counts and the
multiset of face sizes), define the total angular defect using the elementary
fact that a planar `n`-gon has interior angles summing to `(n-2)π`, and prove:

  * `totalDefect_eq_two_pi_euler` : the total defect equals `2π · (V - E + F)`,
    the discrete Gauss–Bonnet identity (defect = `2π ·` Euler characteristic);
  * `descartes` : for a surface satisfying Euler's formula the total defect is
    exactly `4π`.

Worked examples (tetrahedron, cube, octahedron, icosahedron, dodecahedron)
confirm the constant `4π`.  Everything is checked by `ring` / `linear_combination`
over `ℝ`: no axioms beyond Lean's foundations, no sorries.
-/

namespace EulerPolyhedralDescartes

open scoped Real

/-- The total interior angle contributed by all faces, where a face that is an
`n`-gon contributes `(n - 2)·π` (the planar polygon angle sum).  `faceSizes` is
the multiset of face sizes. -/
noncomputable def totalFaceAngle (faceSizes : Multiset ℕ) : ℝ :=
  (faceSizes.map (fun n => (n : ℝ) * Real.pi - 2 * Real.pi)).sum

/-- Closed form: the total face angle is `(Σ sizes)·π - 2π·(#faces)`. -/
theorem totalFaceAngle_eq (s : Multiset ℕ) :
    totalFaceAngle s = (s.sum : ℝ) * Real.pi - 2 * Real.pi * (s.card : ℝ) := by
  induction s using Multiset.induction_on with
  | empty => simp [totalFaceAngle]
  | cons a s ih =>
      have hcons : totalFaceAngle (a ::ₘ s)
          = ((a : ℝ) * Real.pi - 2 * Real.pi) + totalFaceAngle s := by
        simp [totalFaceAngle, Multiset.map_cons, Multiset.sum_cons]
      rw [hcons, ih, Multiset.sum_cons, Multiset.card_cons]
      push_cast
      ring

/-- The combinatorial data of a polyhedral surface: vertex, edge and face counts,
the multiset of face sizes, the face–edge handshake `Σ sizes = 2E`, and Euler's
formula `V - E + F = 2`. -/
structure PolyhedralSurface where
  /-- number of vertices -/
  V : ℕ
  /-- number of edges -/
  E : ℕ
  /-- number of faces -/
  F : ℕ
  /-- the size (number of sides) of each face -/
  faceSizes : Multiset ℕ
  /-- there are exactly `F` faces -/
  card_eq : faceSizes.card = F
  /-- each face is at least a triangle -/
  faceSizes_ge : ∀ n ∈ faceSizes, 3 ≤ n
  /-- each edge borders two faces: `Σ (sides of face) = 2E` -/
  handshake : faceSizes.sum = 2 * E
  /-- Euler's polyhedral formula -/
  euler : (V : ℤ) - (E : ℤ) + (F : ℤ) = 2

/-- The total angular defect: `2π` per vertex minus the angles contributed by the
faces.  (At a single vertex the defect is `2π` minus the face angles there;
summing over vertices regroups the face angles by face, which is `totalFaceAngle`.) -/
noncomputable def totalDefect (P : PolyhedralSurface) : ℝ :=
  2 * Real.pi * (P.V : ℝ) - totalFaceAngle P.faceSizes

/-- **Discrete Gauss–Bonnet.**  The total angular defect equals
`2π · (V - E + F)` — that is, `2π` times the Euler characteristic.  This identity
uses only the handshake `Σ sizes = 2E`, not Euler's formula. -/
theorem totalDefect_eq_two_pi_euler (P : PolyhedralSurface) :
    totalDefect P
      = 2 * Real.pi * ((P.V : ℝ) - (P.E : ℝ) + (P.F : ℝ)) := by
  unfold totalDefect
  rw [totalFaceAngle_eq, P.card_eq]
  have hsum : (P.faceSizes.sum : ℝ) = 2 * (P.E : ℝ) := by
    rw [P.handshake]; push_cast; ring
  rw [hsum]
  ring

/-- **Descartes' Theorem.**  For any polyhedral surface (a sphere, `V - E + F = 2`)
the total angular defect is exactly `4π`. -/
theorem descartes (P : PolyhedralSurface) :
    totalDefect P = 4 * Real.pi := by
  have hcast : (P.V : ℝ) - (P.E : ℝ) + (P.F : ℝ) = 2 := by exact_mod_cast P.euler
  rw [totalDefect_eq_two_pi_euler, hcast]
  ring

/-! ## Worked examples: the five Platonic solids all give `4π` -/

/-- Tetrahedron: 4 triangular faces, `V=4, E=6, F=4`. -/
def tetrahedron : PolyhedralSurface where
  V := 4; E := 6; F := 4
  faceSizes := Multiset.replicate 4 3
  card_eq := by simp
  faceSizes_ge := by intro n hn; simp [Multiset.eq_of_mem_replicate hn]
  handshake := by decide
  euler := by decide

/-- Cube: 6 square faces, `V=8, E=12, F=6`. -/
def cube : PolyhedralSurface where
  V := 8; E := 12; F := 6
  faceSizes := Multiset.replicate 6 4
  card_eq := by simp
  faceSizes_ge := by intro n hn; simp [Multiset.eq_of_mem_replicate hn]
  handshake := by decide
  euler := by decide

/-- Octahedron: 8 triangular faces, `V=6, E=12, F=8`. -/
def octahedron : PolyhedralSurface where
  V := 6; E := 12; F := 8
  faceSizes := Multiset.replicate 8 3
  card_eq := by simp
  faceSizes_ge := by intro n hn; simp [Multiset.eq_of_mem_replicate hn]
  handshake := by decide
  euler := by decide

/-- Dodecahedron: 12 pentagonal faces, `V=20, E=30, F=12`. -/
def dodecahedron : PolyhedralSurface where
  V := 20; E := 30; F := 12
  faceSizes := Multiset.replicate 12 5
  card_eq := by simp
  faceSizes_ge := by intro n hn; simp [Multiset.eq_of_mem_replicate hn]
  handshake := by decide
  euler := by decide

/-- Icosahedron: 20 triangular faces, `V=12, E=30, F=20`. -/
def icosahedron : PolyhedralSurface where
  V := 12; E := 30; F := 20
  faceSizes := Multiset.replicate 20 3
  card_eq := by simp
  faceSizes_ge := by intro n hn; simp [Multiset.eq_of_mem_replicate hn]
  handshake := by decide
  euler := by decide

/-- Each Platonic solid has total angular defect `4π` (Descartes). -/
theorem platonic_defects :
    totalDefect tetrahedron = 4 * Real.pi ∧
    totalDefect cube = 4 * Real.pi ∧
    totalDefect octahedron = 4 * Real.pi ∧
    totalDefect dodecahedron = 4 * Real.pi ∧
    totalDefect icosahedron = 4 * Real.pi :=
  ⟨descartes _, descartes _, descartes _, descartes _, descartes _⟩

/-- A direct, formula-free check for the cube: `8` vertices each with defect
`2π - 3·(π/2) = π/2`, total `4π`. -/
theorem cube_defect_direct : totalDefect cube = 4 * Real.pi := by
  unfold totalDefect totalFaceAngle cube
  simp [Multiset.replicate]
  ring

end EulerPolyhedralDescartes
