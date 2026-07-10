/-
# Feuerbach's Theorem in Non-Euclidean Geometry (OQ-04): spherical side-midpoints

This companion file to `Proofs.FeuerbachsTheoremOQ04` supplies the **spherical midpoint**
of two model points and, feeding it into the merged circumcircle primitive, the existence of
the **spherical nine-point circle** of a spherical triangle.

## Why this matters for Feuerbach

The spherical **nine-point circle** of a spherical triangle is the circumcircle of its
*medial triangle* — the triangle whose vertices are the three side-midpoints.  The merged
`sphericalCircumcircle_exists` (companion file `FeuerbachsTheoremOQ04Circumcircle.lean`)
already produces a common circle through any three model points; the one missing ingredient
was a genuine **midpoint** of a spherical side.  This file supplies exactly that primitive
and closes the long-standing frontier item "side-midpoints (`sMidpoint`), in-flight".

## The construction

For two model points `A, B` on the sphere the natural midpoint of the (minor) great-circle
arc `AB` is the normalised sum `sMidpoint A B = ‖A + B‖⁻¹ • (A + B)`.  Being a positive
combination of `A` and `B`, it lies on the great circle through them and — crucially — is
spherically equidistant from both: `⟪A, A+B⟫ = 1 + ⟪A,B⟫ = ⟪B, A+B⟫`, so `scos A M = scos B M`
and hence `sdist A M = sdist B M`.  Equivalently `M` is orthogonal to the pole `A − B`, i.e.
lies on the spherical perpendicular bisector of `AB` characterised in
`inner_sub_eq_zero_iff_scos_eq`.  The construction is well-defined precisely when `A` and `B`
are not antipodal (`A + B ≠ 0`) — a genuine spherical nondegeneracy condition, since two
antipodal points bound infinitely many geodesics and have no unique midpoint.

Everything is built on the *merged* metric/circle API of `Proofs.FeuerbachsTheoremOQ04`
(`OnSphere`, `scos`, `sdist`, `sCircle`) and the merged `sphericalCircumcircle_exists`; this
file adds no axioms and no sorries.

## What this file proves (0 axioms, 0 sorries)

* `sMidpoint` — the spherical midpoint `‖A + B‖⁻¹ • (A + B)`.
* `sMidpoint_comm` — symmetry `sMidpoint A B = sMidpoint B A`.
* `onSphere_sMidpoint` — for non-antipodal `A, B` (`A + B ≠ 0`) the midpoint is a model point.
* `inner_sMidpoint_sub` — the midpoint lies on the perpendicular bisector: `⟪M, A − B⟫ = 0`.
* `scos_sMidpoint_eq` / `sdist_sMidpoint_eq` — the midpoint is spherically equidistant from the
  two endpoints.
* `norm_add_sq_unit` — `‖A+B‖² = 2 + 2⟪A,B⟫` for model points.
* `scos_sMidpoint_left` — the explicit vertex-to-midpoint spherical cosine `‖A+B‖⁻¹(1+⟪A,B⟫)`.
* `sdist_sMidpoint_half` — **the midpoint bisects the arc**: `sdist A (sMidpoint A B) = ½·sdist A B`,
  the sharper fact (beyond equidistance) that justifies the name.
* `sdist_sMidpoint_half_right` — the other half-arc `sdist (sMidpoint A B) B = ½·sdist A B`.
* `sdist_sMidpoint_add` — **spherical betweenness**: `sdist A M + sdist M B = sdist A B`, the
  equality case of the triangle inequality placing `M` on the geodesic segment `AB`.
* `sphericalNinePointCircle_exists` — **existence of the spherical nine-point circle**: the
  three side-midpoints of a spherical triangle lie on a common spherical circle.
-/
import Mathlib
import Proofs.FeuerbachsTheoremOQ04
import Proofs.FeuerbachsTheoremOQ04Circumcircle

namespace FeuerbachsTheoremOQ04

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The spherical midpoint** of two model points `A, B`: the normalised sum
`‖A + B‖⁻¹ • (A + B)`.  When `A` and `B` are not antipodal this is the midpoint of the minor
great-circle arc joining them — the unique point of that arc equidistant from both endpoints. -/
noncomputable def sMidpoint (A B : E) : E := (‖A + B‖)⁻¹ • (A + B)

/-- The spherical midpoint is symmetric in its two arguments. -/
theorem sMidpoint_comm (A B : E) : sMidpoint A B = sMidpoint B A := by
  unfold sMidpoint; rw [add_comm A B]

/-- **The spherical midpoint of a model point with itself is that point.**  `sMidpoint A A = A`
for `A` on the sphere: the degenerate side `AA` has the vertex as its own midpoint.  (Here
`A + A ≠ 0` automatically, since `‖A‖ = 1`.) -/
theorem sMidpoint_self {A : E} (hA : OnSphere A) : sMidpoint A A = A := by
  have hnorm : ‖A‖ = 1 := hA
  have h2 : ‖A + A‖ = 2 := by
    rw [← two_smul ℝ A, norm_smul, hnorm, mul_one]; simp
  unfold sMidpoint
  rw [h2, ← two_smul ℝ A, smul_smul,
      inv_mul_cancel₀ (by norm_num : (2:ℝ) ≠ 0), one_smul]

/-- **The midpoint of a non-degenerate spherical side is a model point.**  For non-antipodal
`A, B` (`A + B ≠ 0`) the normalised sum has unit norm.  The hypothesis is genuinely needed:
antipodal points sum to `0` and have no well-defined midpoint. -/
theorem onSphere_sMidpoint {A B : E} (h : A + B ≠ 0) : OnSphere (sMidpoint A B) := by
  unfold OnSphere sMidpoint
  rw [norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (by rwa [ne_eq, norm_eq_zero])

/-- **The midpoint lies on the spherical perpendicular bisector of `AB`.**  It is orthogonal
to the pole `A − B`, since `⟪A + B, A − B⟫ = ‖A‖² − ‖B‖² = 0` for two model points.  By
`inner_sub_eq_zero_iff_scos_eq` this is the equidistance property in disguise. -/
theorem inner_sMidpoint_sub (A B : E) (hA : OnSphere A) (hB : OnSphere B) :
    (⟪sMidpoint A B, A - B⟫ : ℝ) = 0 := by
  unfold OnSphere at hA hB
  unfold sMidpoint
  rw [real_inner_smul_left, inner_sub_right, inner_add_left, inner_add_left,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hA, hB, real_inner_comm B A]
  ring

/-- **The spherical midpoint lies on the geodesic through `A` and `B`.**  Being the normalised
sum `‖A + B‖⁻¹ • (A + B)`, the midpoint is a linear combination of `A` and `B`, hence lies in the
plane they span — i.e. on the great circle through `A` and `B`.  Together with
`inner_sMidpoint_sub` (the midpoint is on the perpendicular bisector of `AB`) this locates
`sMidpoint A B` as the intersection of the side's geodesic with its perpendicular bisector. -/
theorem sMidpoint_mem_span (A B : E) :
    sMidpoint A B ∈ Submodule.span ℝ ({A, B} : Set E) := by
  unfold sMidpoint
  refine Submodule.smul_mem _ _ (Submodule.add_mem _ ?_ ?_)
  · exact Submodule.subset_span (by simp)
  · exact Submodule.subset_span (by simp)

/-- **The spherical midpoint is equidistant (equal spherical cosine) from the two endpoints.**
`scos A M = ‖A+B‖⁻¹ (1 + ⟪A,B⟫) = scos B M`, so `A` and `B` are on a common spherical circle
about `M`. -/
theorem scos_sMidpoint_eq (A B : E) (hA : OnSphere A) (hB : OnSphere B) :
    scos A (sMidpoint A B) = scos B (sMidpoint A B) := by
  unfold OnSphere at hA hB
  unfold scos sMidpoint
  rw [real_inner_smul_right, real_inner_smul_right, inner_add_right, inner_add_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hA, hB, real_inner_comm B A]
  ring

/-- **The spherical midpoint is spherically equidistant from the two endpoints.**
`sdist A M = sdist B M`, the defining "midpoint" property, obtained from `scos_sMidpoint_eq`
via `sdist = arccos ∘ scos`. -/
theorem sdist_sMidpoint_eq (A B : E) (hA : OnSphere A) (hB : OnSphere B) :
    sdist A (sMidpoint A B) = sdist B (sMidpoint A B) := by
  have h := scos_sMidpoint_eq A B hA hB
  unfold scos at h
  unfold sdist
  rw [h]

/-! ### The spherical midpoint bisects the arc

`sdist_sMidpoint_eq` shows `M = sMidpoint A B` is *equidistant* from `A` and `B`, but a
point equidistant from two others need not be their midpoint (the antipode of the true
midpoint is equidistant too).  Here we prove the sharper fact that pins down the geometry
and justifies the name: `M` bisects the arc, `sdist A M = ½ · sdist A B`.  The computation
runs through the spherical cosine: `scos A M = ‖A+B‖⁻¹(1 + ⟪A,B⟫)` is nonnegative, so
`sdist A M ≤ π/2`, and the double-angle identity `cos(2·sdist A M) = 2·(scos A M)² − 1`
collapses to `⟪A,B⟫ = cos(sdist A B)`; injectivity of `cos` on `[0, π]` closes it. -/

/-- **Squared norm of a spherical side.**  For two model points, `‖A + B‖² = 2 + 2⟪A,B⟫`
(the parallelogram/polarisation expansion with `‖A‖ = ‖B‖ = 1`). -/
theorem norm_add_sq_unit (A B : E) (hA : OnSphere A) (hB : OnSphere B) :
    ‖A + B‖ ^ 2 = 2 + 2 * ⟪A, B⟫ := by
  unfold OnSphere at hA hB
  rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hA, hB, real_inner_comm B A]
  ring

/-- **Explicit spherical cosine from a vertex to the midpoint of its side.**
`scos A (sMidpoint A B) = ‖A+B‖⁻¹ (1 + ⟪A,B⟫)`.  This closed form is the computational core
of both the equidistance (`scos_sMidpoint_eq`) and the arc-bisection facts. -/
theorem scos_sMidpoint_left (A B : E) (hA : OnSphere A) (_hB : OnSphere B) :
    scos A (sMidpoint A B) = (‖A + B‖)⁻¹ * (1 + ⟪A, B⟫) := by
  unfold scos sMidpoint
  rw [real_inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq]
  unfold OnSphere at hA
  rw [hA]; norm_num

/-- **The spherical midpoint bisects the arc: `sdist A (sMidpoint A B) = ½ · sdist A B`.**
For non-antipodal model points `A, B` the spherical midpoint `M = ‖A+B‖⁻¹•(A+B)` lies at
spherical distance exactly half of `sdist A B` from `A` (equivalently, from `B`).  This is
strictly stronger than equidistance (`sdist_sMidpoint_eq`) and is what genuinely justifies
the name "midpoint": the equidistant locus of `A, B` also contains the antipode of the true
midpoint, which this rules out (`sdist A M ≤ π/2`).  Proof: `scos A M = ‖A+B‖⁻¹(1+⟪A,B⟫) ≥ 0`
gives `sdist A M ≤ π/2`; the double-angle identity turns `cos(2·sdist A M)` into `⟪A,B⟫ =
cos(sdist A B)`, and `cos` is injective on `[0, π]`. -/
theorem sdist_sMidpoint_half (A B : E) (hA : OnSphere A) (hB : OnSphere B)
    (hAB : A + B ≠ 0) :
    sdist A (sMidpoint A B) = sdist A B / 2 := by
  set M := sMidpoint A B with hM
  have hnormpos : 0 < ‖A + B‖ := by rw [norm_pos_iff]; exact hAB
  have htle1 : ⟪A, B⟫ ≤ 1 := by
    have := real_inner_le_norm A B
    unfold OnSphere at hA hB; rw [hA, hB] at this; linarith
  have hnsq : ‖A + B‖ ^ 2 = 2 + 2 * ⟪A, B⟫ := norm_add_sq_unit A B hA hB
  have hden_pos : (0:ℝ) < 2 + 2 * ⟪A, B⟫ := by rw [← hnsq]; positivity
  have h1t : (0:ℝ) ≤ 1 + ⟪A, B⟫ := by linarith
  have hscos_val : scos A M = (‖A + B‖)⁻¹ * (1 + ⟪A, B⟫) := scos_sMidpoint_left A B hA hB
  have hscos_nn : 0 ≤ scos A M := by rw [hscos_val]; positivity
  have hscos_le1 : scos A M ≤ 1 := by
    rw [hscos_val, inv_mul_le_iff₀ hnormpos, mul_one]
    nlinarith [hnsq, hnormpos.le, mul_nonneg (sub_nonneg.mpr htle1) h1t]
  have hcosM : Real.cos (sdist A M) = scos A M := by
    unfold sdist scos
    exact Real.cos_arccos (by rw [← scos]; linarith) (by rw [← scos]; exact hscos_le1)
  have hsq2 : scos A M ^ 2 = (1 + ⟪A, B⟫) / 2 := by
    rw [hscos_val, mul_pow, inv_pow, hnsq, inv_mul_eq_div, div_eq_iff hden_pos.ne']
    ring
  have hcos2 : Real.cos (2 * sdist A M) = ⟪A, B⟫ := by
    rw [Real.cos_two_mul, hcosM, hsq2]; ring
  have hcosAB : Real.cos (sdist A B) = ⟪A, B⟫ := by
    unfold sdist; exact Real.cos_arccos (by linarith) htle1
  have hMle : sdist A M ≤ Real.pi / 2 := by
    unfold sdist
    exact Real.arccos_le_pi_div_two.mpr
      (by rw [show (⟪A, M⟫ : ℝ) = scos A M from rfl]; exact hscos_nn)
  have h2M_mem : 2 * sdist A M ∈ Set.Icc 0 Real.pi := by
    refine ⟨?_, by linarith [hMle]⟩
    have : (0:ℝ) ≤ sdist A M := by unfold sdist; exact Real.arccos_nonneg _
    linarith
  have hAB_mem : sdist A B ∈ Set.Icc 0 Real.pi :=
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hcoseq : Real.cos (2 * sdist A M) = Real.cos (sdist A B) := by rw [hcos2, hcosAB]
  have hfin : 2 * sdist A M = sdist A B := Real.injOn_cos h2M_mem hAB_mem hcoseq
  linarith [hfin]

/-- **The midpoint bisects the arc from the far endpoint too: `sdist (sMidpoint A B) B = ½ · sdist A B`.**
The companion of `sdist_sMidpoint_half`, giving the *other* half of the arc.  Obtained from the
`A`-side statement by symmetry (`sdist_comm`, `sMidpoint_comm`): swapping the roles of `A` and `B`
turns `sdist A (sMidpoint A B)` into `sdist B (sMidpoint A B)`, and `sdist A B` is symmetric. -/
theorem sdist_sMidpoint_half_right (A B : E) (hA : OnSphere A) (hB : OnSphere B)
    (hAB : A + B ≠ 0) :
    sdist (sMidpoint A B) B = sdist A B / 2 := by
  rw [sdist_comm, sMidpoint_comm,
      sdist_sMidpoint_half B A hB hA (by rwa [add_comm]), sdist_comm B A]

/-- **Spherical betweenness of the midpoint: `sdist A M + sdist M B = sdist A B`.**
For non-antipodal model points the spherical midpoint `M = sMidpoint A B` lies *on the minor
arc between* `A` and `B`: the two half-arcs it cuts off add up to the whole side.  This is the
*equality* case of the spherical triangle inequality (`sdist_triangle`), which in general only
gives `≤`; equality pins `M` to the geodesic segment `AB` and, together with the equidistance
`sdist_sMidpoint_eq`, uniquely characterises the midpoint (the equidistant antipode of `M`
would instead give the complementary sum `2π − sdist A B`).  Immediate from the two half-arc
computations `sdist_sMidpoint_half` and `sdist_sMidpoint_half_right`. -/
theorem sdist_sMidpoint_add (A B : E) (hA : OnSphere A) (hB : OnSphere B)
    (hAB : A + B ≠ 0) :
    sdist A (sMidpoint A B) + sdist (sMidpoint A B) B = sdist A B := by
  rw [sdist_sMidpoint_half A B hA hB hAB, sdist_sMidpoint_half_right A B hA hB hAB]
  ring

/-- **Existence of the spherical nine-point circle.**  Given a spherical triangle with
vertices `A, B, C` whose sides are non-degenerate (no two endpoints antipodal), its three
side-midpoints `sMidpoint B C`, `sMidpoint A C`, `sMidpoint A B` — the medial triangle — lie
on a common spherical circle `sCircle O ρ`.  This is the spherical nine-point circle,
obtained by feeding the medial triangle to the merged circumcircle primitive
`sphericalCircumcircle_exists`. -/
theorem sphericalNinePointCircle_exists [FiniteDimensional ℝ E]
    (A B C : E) (hBC : B + C ≠ 0) (hAC : A + C ≠ 0) (hAB : A + B ≠ 0)
    (hdim : 2 < Module.finrank ℝ E) :
    ∃ (O : E) (ρ : ℝ), OnSphere O ∧
      sMidpoint B C ∈ sCircle O ρ ∧ sMidpoint A C ∈ sCircle O ρ ∧
      sMidpoint A B ∈ sCircle O ρ :=
  sphericalCircumcircle_exists (sMidpoint B C) (sMidpoint A C) (sMidpoint A B)
    (onSphere_sMidpoint hBC) (onSphere_sMidpoint hAC) (onSphere_sMidpoint hAB) hdim

end FeuerbachsTheoremOQ04
