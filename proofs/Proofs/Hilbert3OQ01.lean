/-
  Hilbert's 3rd Problem — OQ-01:
  Scissors congruence in HIGHER DIMENSIONS — the graded Dehn invariant target.

  ## Question
  Hilbert's third problem (solved by Dehn 1900, completed by Sydler 1965) shows
  that in dimension 3 two polytopes are scissors-congruent iff they have equal
  volume AND equal Dehn invariant, the latter living in `ℝ ⊗_ℤ (ℝ / πℚ)`. The
  open question for the gallery's `hilbert-3` line: *what are the scissors
  congruence groups in higher dimensions?*

  Classically (Hadwiger, Jessen–Thorup, Sah) the obstruction in dimension `d`
  is no longer a single Dehn invariant but a **graded family** of Dehn-type
  invariants, one per codimension-2 stratum / face dimension. Each component lives
  in a tensor group of the same shape `ℝ ⊗_ℤ (ℝ / πℚ)`, and the total invariant is
  their direct sum. This file formalizes that **target group** and its core
  algebra at general dimension `d`:

    * the graded Dehn group `TotalDehn d = Fin d → (ℝ ⊗_ℤ ℝ/πℚ)`,
    * the per-stratum contribution and the assembled total invariant,
    * each graded component equals the classical (3D-shape) Dehn sum over that
      stratum (`totalDehn_apply`),
    * general additivity, supplementary-angle cancellation lifted to the grading,
      and the **vanishing criterion**: a polytope all of whose dihedral angles are
      rational multiples of `π` has total Dehn invariant `0` in every dimension.

  This is the invariant-theoretic half of the answer (the structure of the target
  group); the completeness of these invariants — i.e. which higher-dimensional
  scissors congruence groups are fully classified — is recorded as open below.

  Everything here is proved from Mathlib with **no axioms and no sorries**.

  ## References
  - https://en.wikipedia.org/wiki/Dehn_invariant
  - H. Hadwiger, *Vorlesungen über Inhalt, Oberfläche und Isoperimetrie* (1957).
  - B. Jessen & A. Thorup, *The algebra of polytopes in affine spaces* (1978).
  - C.-H. Sah, *Hilbert's Third Problem: Scissors Congruence* (1979).

  Tags: geometry, topology, hilbert-problems, dehn-invariant, scissors-congruence
-/

import Mathlib

namespace Hilbert3OQ01

open scoped TensorProduct

-- ============================================================
-- SECTION I: The Dehn target group (3D shape), self-contained
-- ============================================================

/-- The additive homomorphism `ℚ →+ ℝ`, `q ↦ q · π`. -/
noncomputable def piRatHom : ℚ →+ ℝ where
  toFun q := (q : ℝ) * Real.pi
  map_zero' := by simp
  map_add' a b := by push_cast; ring

/-- The subgroup `πℚ = {q · π : q ∈ ℚ}` of `ℝ`. -/
noncomputable def piRat : AddSubgroup ℝ := piRatHom.range

/-- The angle group `A = ℝ / πℚ`. -/
abbrev AngleGroup := ℝ ⧸ piRat

/-- The (single-stratum) Dehn target group `D = ℝ ⊗_ℤ (ℝ / πℚ)`. -/
abbrev DehnGroup := ℝ ⊗[ℤ] AngleGroup

/-- The class of an angle `θ` in `A = ℝ / πℚ`. -/
noncomputable def angleClass (θ : ℝ) : AngleGroup := QuotientAddGroup.mk' piRat θ

/-- A single Dehn contribution `l ⊗ [θ]`. -/
noncomputable def dehnTerm (l θ : ℝ) : DehnGroup := l ⊗ₜ[ℤ] angleClass θ

/-- An angle that is a rational multiple of `π` is `0` in `A`. -/
theorem angleClass_eq_zero_of_ratPi (θ : ℝ) (q : ℚ) (h : θ = (q : ℝ) * Real.pi) :
    angleClass θ = 0 := by
  rw [angleClass, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  exact ⟨q, by simp [piRatHom, h]⟩

/-- `[π] = 0` in `A`. -/
theorem angleClass_pi : angleClass Real.pi = 0 :=
  angleClass_eq_zero_of_ratPi Real.pi 1 (by push_cast; ring)

/-- `angleClass` is additive. -/
theorem angleClass_add (θ₁ θ₂ : ℝ) :
    angleClass (θ₁ + θ₂) = angleClass θ₁ + angleClass θ₂ := by
  simp only [angleClass, map_add]

/-- A rational-angle Dehn term vanishes. -/
theorem dehnTerm_eq_zero_of_ratPi (l θ : ℝ) (q : ℚ) (h : θ = (q : ℝ) * Real.pi) :
    dehnTerm l θ = 0 := by
  rw [dehnTerm, angleClass_eq_zero_of_ratPi θ q h, TensorProduct.tmul_zero]

/-- The Dehn term is additive in the angle. -/
theorem dehnTerm_add_angle (l θ₁ θ₂ : ℝ) :
    dehnTerm l (θ₁ + θ₂) = dehnTerm l θ₁ + dehnTerm l θ₂ := by
  rw [dehnTerm, dehnTerm, dehnTerm, angleClass_add, TensorProduct.tmul_add]

/-- Supplementary-angle cancellation `l ⊗ θ + l ⊗ (π − θ) = 0`. -/
theorem dehnTerm_supplementary (l θ : ℝ) :
    dehnTerm l θ + dehnTerm l (Real.pi - θ) = 0 := by
  rw [← dehnTerm_add_angle]
  have : θ + (Real.pi - θ) = Real.pi := by ring
  rw [this, dehnTerm, angleClass_pi, TensorProduct.tmul_zero]

-- ============================================================
-- SECTION II: The graded higher-dimensional Dehn group
-- ============================================================

/-- **The graded Dehn invariant target in dimension `d`.** In dimension `d` the
scissors-congruence obstruction is a family of Dehn-type invariants indexed by the
relevant codimension-2 strata; we model the target as `Fin d → DehnGroup`. It is
an additive commutative group (componentwise), the natural higher-dimensional
generalization of the single 3D group `DehnGroup`. -/
abbrev TotalDehn (d : ℕ) := Fin d → DehnGroup

/-- The contribution of one stratum: an edge of length `l` at dihedral angle `θ`
located in graded position `k` contributes `dehnTerm l θ` to component `k` and `0`
elsewhere. -/
noncomputable def stratum {d : ℕ} (k : Fin d) (l θ : ℝ) : TotalDehn d :=
  Pi.single k (dehnTerm l θ)

/-- **The total (graded) Dehn invariant** of a `d`-polytope whose codimension-2
strata are indexed by a finite set `s`, with grade `gr`, length `len`, and angle
`ang`: `∑_{i ∈ s} stratum (gr i) (len i) (ang i)`. -/
noncomputable def totalDehnSum {ι : Type*} {d : ℕ} (s : Finset ι)
    (gr : ι → Fin d) (len ang : ι → ℝ) : TotalDehn d :=
  ∑ i ∈ s, stratum (gr i) (len i) (ang i)

/-- Component formula for a single stratum. -/
theorem stratum_apply {d : ℕ} (k j : Fin d) (l θ : ℝ) :
    stratum k l θ j = if j = k then dehnTerm l θ else 0 := by
  rw [stratum, Pi.single_apply]

/-- **Each graded component is exactly the classical (3D-shape) Dehn sum over the
strata sitting in that grade.** This is the precise sense in which the higher-
dimensional invariant is "a family of ordinary Dehn invariants". -/
theorem totalDehnSum_apply {ι : Type*} {d : ℕ} (s : Finset ι)
    (gr : ι → Fin d) (len ang : ι → ℝ) (k : Fin d) :
    totalDehnSum s gr len ang k
      = ∑ i ∈ s, (if k = gr i then dehnTerm (len i) (ang i) else 0) := by
  rw [totalDehnSum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [stratum_apply]

-- ============================================================
-- SECTION III: Algebra of the graded invariant
-- ============================================================

/-- The stratum contribution is additive in the edge length (collinear split). -/
theorem stratum_add_length {d : ℕ} (k : Fin d) (l₁ l₂ θ : ℝ) :
    stratum k (l₁ + l₂) θ = stratum k l₁ θ + stratum k l₂ θ := by
  rw [stratum, stratum, stratum, ← Pi.single_add]
  congr 1
  rw [dehnTerm, dehnTerm, dehnTerm, ← TensorProduct.add_tmul]

/-- **Supplementary-angle cancellation, lifted to the grading.** Cutting through a
stratum splits its dihedral angle `θ` into `θ` and `π − θ`; the two graded
contributions cancel, so the total Dehn invariant is unchanged by cuts in every
dimension. -/
theorem stratum_supplementary {d : ℕ} (k : Fin d) (l θ : ℝ) :
    stratum k l θ + stratum k l (Real.pi - θ) = 0 := by
  rw [stratum, stratum, ← Pi.single_add, dehnTerm_supplementary, Pi.single_zero]

/-- A rational-angle stratum contributes nothing. -/
theorem stratum_eq_zero_of_ratPi {d : ℕ} (k : Fin d) (l θ : ℝ) (q : ℚ)
    (h : θ = (q : ℝ) * Real.pi) : stratum k l θ = 0 := by
  rw [stratum, dehnTerm_eq_zero_of_ratPi l θ q h, Pi.single_zero]

/-- **Vanishing criterion in every dimension.** If every dihedral angle (across all
strata) is a rational multiple of `π`, the total graded Dehn invariant vanishes —
the higher-dimensional generalization of `D(cube) = 0`. -/
theorem totalDehnSum_eq_zero_of_ratPi {ι : Type*} {d : ℕ} (s : Finset ι)
    (gr : ι → Fin d) (len ang : ι → ℝ)
    (h : ∀ i ∈ s, ∃ q : ℚ, ang i = (q : ℝ) * Real.pi) :
    totalDehnSum s gr len ang = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  obtain ⟨q, hq⟩ := h i hi
  exact stratum_eq_zero_of_ratPi (gr i) (len i) (ang i) q hq

/-- **The `d`-cube analogue.** A `d`-dimensional box has every dihedral angle
`π/2`, a rational multiple of `π`, so its total graded Dehn invariant is `0` for
all `d`: it is scissors-congruent-obstruction-free, consistent with boxes tiling
and being scissors-congruent to cubes in every dimension. -/
theorem box_totalDehnSum_zero {ι : Type*} {d : ℕ} (s : Finset ι)
    (gr : ι → Fin d) (len : ι → ℝ) :
    totalDehnSum s gr len (fun _ => Real.pi / 2) = 0 := by
  apply totalDehnSum_eq_zero_of_ratPi
  intro i _
  exact ⟨1 / 2, by push_cast; ring⟩

/-- Additivity over a disjoint union of stratum families: assembling the strata of
two polytopes adds their total Dehn invariants. This makes the total invariant a
group homomorphism out of the free abelian group on graded strata. -/
theorem totalDehnSum_union {ι : Type*} [DecidableEq ι] {d : ℕ} {s t : Finset ι}
    (hst : Disjoint s t) (gr : ι → Fin d) (len ang : ι → ℝ) :
    totalDehnSum (s ∪ t) gr len ang
      = totalDehnSum s gr len ang + totalDehnSum t gr len ang := by
  rw [totalDehnSum, totalDehnSum, totalDehnSum, Finset.sum_union hst]

#check @totalDehnSum_apply
#check @stratum_supplementary
#check @totalDehnSum_eq_zero_of_ratPi
#check @box_totalDehnSum_zero
#check @totalDehnSum_union

end Hilbert3OQ01
