import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Hilbert's Third Problem, OQ-02: Tensor-product foundation of the Dehn invariant

## The open question

The parent gallery entry *Hilbert's 3rd Problem: Scissors Congruence*
(`Hilbert3ScissorsCongruence.lean`) models the Dehn invariant with a deliberately
crude *list-of-pairs* surrogate, and its open question OQ-02 asks to

> "Formalize Sydler's completeness theorem in Lean via Mathlib tensor-product
>  machinery."

Sydler's 1965 theorem — that volume together with the Dehn invariant is a
*complete* invariant for scissors congruence in `ℝ³` — is genuinely deep (it
rests on transcendence theory and a hard surjectivity/"if" direction) and is far
out of reach of a single formalization session. **This file does not claim it.**

What it *does* deliver is the algebraic substrate that Sydler's theorem, and even
Dehn's original obstruction, are actually phrased in: the honest Dehn target group

  `D = ℝ ⊗_ℤ (ℝ / πℚ)`

built with Mathlib's real `TensorProduct`, replacing the parent's list surrogate.
On top of it we prove the two facts that carry the whole geometric argument and
that the parent file could only state as `:= trivial` (i.e. as `True`):

* **Rational angles vanish** — a length tensored with a rational multiple of `π`
  is `0` in `D`. This is exactly why the cube (all dihedral angles `π/2`) — and,
  more generally, every polyhedron all of whose dihedral angles are rational
  multiples of `π` — has Dehn invariant `0`.

* **Supplementary-angle cancellation** — `l ⊗ θ + l ⊗ (π − θ) = 0`. This is the
  algebraic heart of "cutting preserves the Dehn invariant": a planar cut through
  an edge replaces a dihedral angle `θ` by the two angles `θ` and `π − θ` on the
  two new pieces, whose contributions cancel because `θ + (π − θ) = π ≡ 0` in
  `ℝ / πℚ`. The parent file left this as `cutting_preserves_dehn := trivial`.

Everything here is proved from Mathlib with **no axioms and no sorries**.

## References
- https://en.wikipedia.org/wiki/Dehn_invariant
- J.-P. Sydler, *Conditions nécessaires et suffisantes pour l'équivalence des
  polyèdres de l'espace euclidien à trois dimensions*, Comment. Math. Helv. 1965.
-/

namespace Hilbert3OQ02

open scoped TensorProduct

/-- The additive homomorphism `ℚ →+ ℝ`, `q ↦ q · π`. Its range is the subgroup
`πℚ = {qπ : q ∈ ℚ}` of `ℝ`. -/
noncomputable def piRatHom : ℚ →+ ℝ where
  toFun q := (q : ℝ) * Real.pi
  map_zero' := by simp
  map_add' a b := by push_cast; ring

/-- The subgroup `πℚ = {q · π : q ∈ ℚ}` of `ℝ`, the "rational multiples of `π`". -/
noncomputable def piRat : AddSubgroup ℝ := piRatHom.range

/-- The angle group `A = ℝ / πℚ`, where dihedral angles are measured modulo
rational multiples of `π`. -/
abbrev AngleGroup := ℝ ⧸ piRat

/-- The Dehn target group `D = ℝ ⊗_ℤ (ℝ / πℚ)`: edge lengths tensored with
angle classes. This is the genuine group in which the Dehn invariant lives,
formed with Mathlib's `TensorProduct`. -/
abbrev DehnGroup := ℝ ⊗[ℤ] AngleGroup

/-- The class of an angle `θ` in `A = ℝ / πℚ`, packaged as the value of the
canonical additive quotient homomorphism (so we inherit its `map_add`, etc.). -/
noncomputable def angleClass (θ : ℝ) : AngleGroup := QuotientAddGroup.mk' piRat θ

/-- A single Dehn contribution: an edge of length `l` at dihedral angle `θ`
contributes `l ⊗ [θ]` to the Dehn invariant. -/
noncomputable def dehnTerm (l θ : ℝ) : DehnGroup := l ⊗ₜ[ℤ] angleClass θ

/-- The Dehn invariant of a polyhedron whose edges are indexed by a finite set
`s`, with length function `len` and dihedral-angle function `ang`:
`D = Σ_{e ∈ s} len e ⊗ [ang e]`. -/
noncomputable def dehnSum {ι : Type*} (s : Finset ι) (len ang : ι → ℝ) : DehnGroup :=
  ∑ i ∈ s, dehnTerm (len i) (ang i)

-- ============================================================
-- The angle group: rational multiples of π are zero
-- ============================================================

/-- An angle that is a rational multiple of `π` is `0` in `A = ℝ / πℚ`. -/
theorem angleClass_eq_zero_of_ratPi (θ : ℝ) (q : ℚ) (h : θ = (q : ℝ) * Real.pi) :
    angleClass θ = 0 := by
  rw [angleClass, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  exact ⟨q, by simp [piRatHom, h]⟩

/-- `[π] = 0` in `A`, since `π = 1 · π`. -/
theorem angleClass_pi : angleClass Real.pi = 0 :=
  angleClass_eq_zero_of_ratPi Real.pi 1 (by push_cast; ring)

/-- `angleClass` is additive. -/
theorem angleClass_add (θ₁ θ₂ : ℝ) :
    angleClass (θ₁ + θ₂) = angleClass θ₁ + angleClass θ₂ := by
  simp only [angleClass, map_add]

-- ============================================================
-- The Dehn term: linearity and the key vanishing facts
-- ============================================================

/-- **Rational-angle vanishing.** A length at a dihedral angle that is a rational
multiple of `π` contributes nothing to the Dehn invariant. This is the algebraic
reason `D(cube) = 0`. -/
theorem dehnTerm_eq_zero_of_ratPi (l θ : ℝ) (q : ℚ) (h : θ = (q : ℝ) * Real.pi) :
    dehnTerm l θ = 0 := by
  rw [dehnTerm, angleClass_eq_zero_of_ratPi θ q h, TensorProduct.tmul_zero]

/-- The Dehn term is additive in the edge length: `(l₁ + l₂) ⊗ θ = l₁ ⊗ θ + l₂ ⊗ θ`.
(Splitting an edge into two collinear edges of the same dihedral angle.) -/
theorem dehnTerm_add_length (l₁ l₂ θ : ℝ) :
    dehnTerm (l₁ + l₂) θ = dehnTerm l₁ θ + dehnTerm l₂ θ := by
  rw [dehnTerm, dehnTerm, dehnTerm, TensorProduct.add_tmul]

/-- The Dehn term is additive in the angle: `l ⊗ (θ₁ + θ₂) = l ⊗ θ₁ + l ⊗ θ₂`. -/
theorem dehnTerm_add_angle (l θ₁ θ₂ : ℝ) :
    dehnTerm l (θ₁ + θ₂) = dehnTerm l θ₁ + dehnTerm l θ₂ := by
  rw [dehnTerm, dehnTerm, dehnTerm, angleClass_add, TensorProduct.tmul_add]

/-- **Supplementary-angle cancellation** — the algebraic heart of "cutting
preserves the Dehn invariant". A planar cut through an edge of length `l` splits
its dihedral angle `θ` into the two angles `θ` and `π − θ` on the two new pieces;
their Dehn contributions cancel because `θ + (π − θ) = π ≡ 0` in `ℝ / πℚ`.

The parent file left the corresponding statement as `cutting_preserves_dehn := trivial`. -/
theorem dehnTerm_supplementary (l θ : ℝ) :
    dehnTerm l θ + dehnTerm l (Real.pi - θ) = 0 := by
  rw [← dehnTerm_add_angle]
  have : θ + (Real.pi - θ) = Real.pi := by ring
  rw [this, dehnTerm, angleClass_pi, TensorProduct.tmul_zero]

-- ============================================================
-- Whole-polyhedron consequences
-- ============================================================

/-- **Dehn invariant of a rational-angle polyhedron is zero.** If every dihedral
angle is a rational multiple of `π`, the whole Dehn invariant vanishes. This
covers the cube (all angles `π/2`) and indeed every polyhedron built from such
angles. -/
theorem dehnSum_eq_zero_of_ratPi {ι : Type*} (s : Finset ι) (len ang : ι → ℝ)
    (h : ∀ i ∈ s, ∃ q : ℚ, ang i = (q : ℝ) * Real.pi) :
    dehnSum s len ang = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  obtain ⟨q, hq⟩ := h i hi
  exact dehnTerm_eq_zero_of_ratPi (len i) (ang i) q hq

/-- **The cube has Dehn invariant zero.** Every one of the cube's edges carries
dihedral angle `π/2 = (1/2)·π`, a rational multiple of `π`, so the Dehn invariant
is `0` in the genuine group `ℝ ⊗_ℤ (ℝ / πℚ)`. -/
theorem cube_dehnSum_zero {ι : Type*} (s : Finset ι) (len : ι → ℝ) :
    dehnSum s len (fun _ => Real.pi / 2) = 0 := by
  apply dehnSum_eq_zero_of_ratPi
  intro i _
  exact ⟨1 / 2, by push_cast; ring⟩

end Hilbert3OQ02

-- Sanity checks
#check @Hilbert3OQ02.dehnTerm_eq_zero_of_ratPi
#check @Hilbert3OQ02.dehnTerm_supplementary
#check @Hilbert3OQ02.cube_dehnSum_zero
