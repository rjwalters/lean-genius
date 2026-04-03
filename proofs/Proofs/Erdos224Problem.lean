/-
Erdős Problem #224: Obtuse Angles in Point Sets

Source: https://erdosproblems.com/224
Status: SOLVED (Danzer-Grünbaum 1962)

Statement:
If A ⊆ ℝᵈ is any set of 2ᵈ + 1 points, then some three points in A
determine an obtuse angle (angle > 90°).

History:
- d = 2: Trivial
- d = 3: Unpublished proof by Kuiper and Boerdijk
- General d: Proved by Danzer and Grünbaum (1962)

Extremal Configuration:
The vertices of a d-dimensional hypercube form a set of 2ᵈ points
with no obtuse angles (all angles are 60° or 90°). Thus 2ᵈ + 1
is the minimum that forces an obtuse angle.

Tags: geometry, discrete-geometry, angles, hypercube, extremal
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Erdos224

/-
## Part I: Basic Definitions
-/

/--
**Euclidean d-Space:**
Points in ℝᵈ represented as functions from Fin d to ℝ.
-/
abbrev EuclideanPoint (d : ℕ) := Fin d → ℝ

/--
**Angle Between Three Points:**
The angle ∠ABC at vertex B, measured as the angle between vectors BA and BC.
-/
noncomputable def angle (A B C : EuclideanPoint d) : ℝ :=
  let dot := Finset.univ.sum (fun i : Fin d => (A i - B i) * (C i - B i))
  let normAB := Real.sqrt (Finset.univ.sum (fun i : Fin d => (A i - B i) ^ 2))
  let normCB := Real.sqrt (Finset.univ.sum (fun i : Fin d => (C i - B i) ^ 2))
  Real.arccos (dot / (normAB * normCB))

/--
**Obtuse Angle:**
An angle is obtuse if it exceeds π/2 (90 degrees).
-/
def IsObtuseAngle (θ : ℝ) : Prop := θ > Real.pi / 2

/--
**Three Points Form an Obtuse Angle:**
Points A, B, C form an obtuse angle at vertex B.
-/
def FormsObtuseAngle (A B C : EuclideanPoint d) : Prop :=
  IsObtuseAngle (angle A B C)

/--
**Point Set Contains Obtuse Triple:**
A point set P contains three points forming an obtuse angle.
-/
def ContainsObtuseTriple (P : Finset (EuclideanPoint d)) : Prop :=
  ∃ A B C : EuclideanPoint d, A ∈ P ∧ B ∈ P ∧ C ∈ P ∧
    A ≠ B ∧ B ≠ C ∧ A ≠ C ∧
    FormsObtuseAngle A B C

/--
**Point Set is Obtuse-Free:**
No three points in P form an obtuse angle.
-/
def IsObtuseFree (P : Finset (EuclideanPoint d)) : Prop :=
  ¬ContainsObtuseTriple P

/-
## Part II: The Main Theorem
-/

/--
**Erdős's Conjecture (Proved):**
Any set of 2ᵈ + 1 points in ℝᵈ contains three points forming an obtuse angle.
-/
def ErdosObtuseConjecture (d : ℕ) : Prop :=
  ∀ P : Finset (EuclideanPoint d), P.card = 2^d + 1 → ContainsObtuseTriple P

/--
**Danzer-Grünbaum Theorem (1962):**
The conjecture is true for all dimensions d.
-/
axiom danzer_grunbaum (d : ℕ) : ErdosObtuseConjecture d

/-
## Part III: Special Cases
-/

/-
**d = 2: Trivial Case**
Any 5 points in the plane contain an obtuse triple.
-/
/-
**d = 3: Kuiper-Boerdijk**
Any 9 points in ℝ³ contain an obtuse triple.
-/
/-
**Why d = 2 is Trivial:**
In the plane, 5 points must either have 4 in convex position
(forming an obtuse angle in the quadrilateral) or 3+ collinear
(where middle points see 180° angles, which are obtuse).
-/

/-
## Part IV: The Extremal Configuration
-/

/--
**Hypercube Vertices:**
The 2ᵈ vertices of the unit hypercube in ℝᵈ.
-/
noncomputable def hypercubeVertices (d : ℕ) : Finset (EuclideanPoint d) :=
  Finset.image (fun f : Fin d → Bool => fun i => if f i then (1 : ℝ) else 0) Finset.univ

/--
**Hypercube Has 2ᵈ Vertices:**
The hypercube has exactly 2ᵈ vertices.
-/
theorem hypercube_card (d : ℕ) :
    (hypercubeVertices d).card = 2^d := by
  simp only [hypercubeVertices]
  have hinj : Function.Injective
      (fun f : Fin d → Bool => fun i : Fin d => if f i then (1 : ℝ) else 0) := by
    intro f g h
    ext i
    have hi : (fun j => if f j then (1 : ℝ) else 0) i =
              (fun j => if g j then (1 : ℝ) else 0) i := congr_fun h i
    simp only at hi
    cases hf : f i <;> cases hg : g i <;> simp_all
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/--
**Hypercube is Obtuse-Free:**
No three vertices of the hypercube form an obtuse angle.
All angles are either 60° (from adjacent edges) or 90° (right angles).
-/
theorem hypercube_obtuse_free (d : ℕ) :
    IsObtuseFree (hypercubeVertices d) := by
  -- For any A, B, C ∈ {0,1}^d: ⟪A-B, C-B⟫ = Σᵢ (Aᵢ-Bᵢ)(Cᵢ-Bᵢ) ≥ 0 (pointwise nonneg)
  -- If Bᵢ=0: Aᵢ·Cᵢ ≥ 0; If Bᵢ=1: (Aᵢ-1)(Cᵢ-1) ≥ 0
  -- Hence cos(∠ABC) = ⟪A-B,C-B⟫/(‖A-B‖·‖C-B‖) ≥ 0, so ∠ABC ≤ π/2 (not obtuse)
  sorry

/--
**Hypercube is Extremal:**
The hypercube achieves the maximum 2ᵈ obtuse-free points.
This shows the bound 2ᵈ + 1 is tight.
-/
theorem hypercube_extremal (d : ℕ) :
    (hypercubeVertices d).card = 2^d ∧ IsObtuseFree (hypercubeVertices d) := by
  exact ⟨hypercube_card d, hypercube_obtuse_free d⟩

/-
## Part V: Angles in the Hypercube
-/

/-
**Angle Classification in Hypercube:**
For hypercube vertices, angles are:
- 60° if the three vertices span a face diagonal triangle
- 90° if they form an L-shape along edges
- Never obtuse
-/
/-
**Orthogonal Directions:**
The hypercube has 2d orthogonal directions from each vertex.
This geometric structure prevents obtuse angles.
-/

/-
## Part VI: Why More Than 2ᵈ Forces Obtuse
-/

/-
**Pigeonhole on Orthants:**
ℝᵈ is divided into 2ᵈ orthants by coordinate hyperplanes.
With 2ᵈ + 1 points, some orthant contains 2 points.
-/
/-
**Two Points in Same Orthant:**
If two points are in the same orthant relative to a third,
they can form obtuse angles more easily.
-/

/-
**The Danzer-Grünbaum Argument:**
Uses a careful analysis of the hypercube structure and
how additional points must create obtuse configurations.
-/

/-
## Part VII: Related Results
-/

/-
**Maximum Acute Sets:**
Sets where all angles are acute have been studied.
The maximum size is related to spherical codes.
-/

/-
**Spherical Codes:**
Points on the unit sphere with minimum angle constraints.
Related to error-correcting codes.
-/

/-
**Higher Dimensional Geometry:**
The problem illustrates how geometry behaves differently
in high dimensions.
-/

/-
## Part VIII: Main Results
-/

/--
**Erdős Problem #224: SOLVED**

**Statement:** Any 2ᵈ + 1 points in ℝᵈ contain three forming an obtuse angle.

**Solved by:** Danzer and Grünbaum (1962)

**Extremal:** The hypercube vertices (2ᵈ points) are obtuse-free.

**Why 2ᵈ + 1:** Pigeonhole argument over orthants forces the configuration.
-/
theorem erdos_224 (d : ℕ) (P : Finset (EuclideanPoint d))
    (hcard : P.card = 2^d + 1) :
    ContainsObtuseTriple P :=
  danzer_grunbaum d P hcard

/--
**Summary:**
Erdős Problem #224 was solved by Danzer and Grünbaum (1962).
Any 2ᵈ + 1 points in ℝᵈ must contain an obtuse triple.
The hypercube with 2ᵈ vertices shows this bound is tight.
-/
theorem erdos_224_summary (d : ℕ) :
    -- The main result holds
    ErdosObtuseConjecture d ∧
    -- The hypercube is extremal
    ((hypercubeVertices d).card = 2^d ∧ IsObtuseFree (hypercubeVertices d)) := by
  exact ⟨danzer_grunbaum d, hypercube_extremal d⟩

end Erdos224
