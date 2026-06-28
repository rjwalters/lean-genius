/-
Erdős Problem #1042 — open question oq-02:
"Can the result be extended to higher dimensions?"

The parent entry (#1042, resolved by Ghosh–Ramachandran 2024) studies polynomial
lemniscates {z : |f(z)| < 1} of one complex variable and records the
component-count answers as axioms. The sibling companion oq-03
(`Erdos1042OQ03.lean`) PROVES the elementary mechanism underneath every
component-count bound in ONE variable: the lemniscate is CONFINED to the union
of the open unit balls about the roots of `f`, hence is bounded, and each
bounded connected component must trap a root — the source of the classical
"at most n components" bound.

This companion addresses oq-02 by isolating *what survives* and *what fails*
when one passes from ℂ = ℂ¹ to ℂⁿ. We work with the natural multivariate
analogue of a monic factored polynomial: a finite product

    f(z) = ∏ⱼ (z (coordⱼ) − rootⱼ),    z ∈ ℂⁿ,

each factor reading off one coordinate and subtracting a root. When n = 1 this
is exactly the one-variable monic polynomial of oq-03 (`eval_one_dim`).

SURVIVES into higher dimensions (proved generally for ℂⁿ):
  • `continuous_eval` — the polynomial map is continuous;
  • `isOpen_lem`     — the lemniscate is open;
  • `mem_lem_of_eval_zero` — the zero locus of `f` lies inside the lemniscate.

FAILS in higher dimensions — the new phenomenon answering oq-02:
  • `cyl_unbounded` — in ℂ² the lemniscate of f(z₀,z₁) = z₀ is **unbounded**.
    The free second coordinate turns each would-be isolated "island" into an
    infinite tube, so the oq-03 confinement/boundedness (`isBounded_lem`) and
    the resulting finite-component bound have NO direct ℂⁿ analogue.
  • `isConnected_cyl` — that same lemniscate is moreover **connected**: the n
    separate components of the one-variable picture can merge into a single
    unbounded set.

So the answer to oq-02 is, in this precise sense, NEGATIVE for the confinement
mechanism: openness and the root-containment generalise verbatim, but the
geometric features (boundedness, component counting) that drive the #1042 story
are special to one complex variable.

All results below are axiom-free and self-contained; the structures are
re-declared locally so that nothing depends on the parent's axioms
(`transfiniteDiameter`, `ghosh_ramachandran_*`).
-/

import Mathlib

open BigOperators Metric

namespace Erdos1042OQ02

variable {n : ℕ}

/-- A multivariate "coordinate-factored" polynomial on `ℂⁿ`: a finite product of
affine factors, each factor reading off one coordinate (`coord j`) and
subtracting a root (`root j`):  `f(z) = ∏ⱼ (z (coord j) - root j)`.
When `n = 1` this is the one-variable monic polynomial of oq-03. -/
structure CoordPoly (n : ℕ) where
  degree : ℕ
  coord : Fin degree → Fin n
  root : Fin degree → ℂ

/-- Evaluation of the coordinate-factored polynomial at a point `z ∈ ℂⁿ`. -/
noncomputable def CoordPoly.eval (p : CoordPoly n) (z : Fin n → ℂ) : ℂ :=
  ∏ j : Fin p.degree, (z (p.coord j) - p.root j)

/-- The lemniscate of `p`, the open sublevel set `{z ∈ ℂⁿ : |f(z)| < 1}`. -/
def lem (p : CoordPoly n) : Set (Fin n → ℂ) :=
  {z | ‖p.eval z‖ < 1}

/-- **Reduction to one variable.** For a coordinate-factored polynomial on `ℂ¹`,
every factor reads off the unique coordinate `0`, so `eval` is exactly the
one-variable monic product `∏ⱼ (z 0 - rootⱼ)` of Erdős #1042 oq-03. The
multivariate framework therefore genuinely generalises the one-variable one. -/
theorem eval_one_dim (p : CoordPoly 1) (z : Fin 1 → ℂ) :
    p.eval z = ∏ j : Fin p.degree, (z 0 - p.root j) := by
  unfold CoordPoly.eval
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [Subsingleton.elim (p.coord j) (0 : Fin 1)]

/-- The polynomial map `z ↦ f(z)` is continuous (a finite product of the
continuous coordinate-evaluation maps `z ↦ z (coord j) - root j`). Survives to ℂⁿ. -/
theorem continuous_eval (p : CoordPoly n) : Continuous p.eval := by
  unfold CoordPoly.eval
  exact continuous_finset_prod _ fun j _ => (continuous_apply (p.coord j)).sub continuous_const

/-- The lemniscate is open: the preimage of `(-∞, 1)` under the continuous map
`z ↦ |f(z)|`. Survives to ℂⁿ. -/
theorem isOpen_lem (p : CoordPoly n) : IsOpen (lem p) := by
  have h : Continuous fun z => ‖p.eval z‖ := (continuous_eval p).norm
  show IsOpen ((fun z => ‖p.eval z‖) ⁻¹' Set.Iio 1)
  exact h.isOpen_preimage (Set.Iio 1) isOpen_Iio

/-- The zero locus of `f` lies in the lemniscate: if some factor vanishes at `z`
(`z (coord j) = root j`) then `f(z) = 0` and `|0| = 0 < 1`. Survives to ℂⁿ.
(In one variable the zero locus is the finite set of roots; in ℂⁿ it is a union
of hyperplanes — already a hint that the higher-dimensional geometry differs.) -/
theorem mem_lem_of_eval_zero (p : CoordPoly n) {z : Fin n → ℂ}
    (h : ∃ j : Fin p.degree, z (p.coord j) = p.root j) : z ∈ lem p := by
  obtain ⟨j, hj⟩ := h
  have h0 : p.eval z = 0 := by
    unfold CoordPoly.eval
    exact Finset.prod_eq_zero (Finset.mem_univ j) (sub_eq_zero.mpr hj)
  show ‖p.eval z‖ < 1
  rw [h0]; simp

/-! ### The higher-dimensional phenomenon (ℂ²)

We exhibit, in two variables, a lemniscate that is open and connected but
*unbounded* — the qualitative failure of the oq-03 confinement result. -/

/-- The two-variable example `f(z₀, z₁) = z₀`: a single factor in the first
coordinate only. Its lemniscate `{z : |z₀| < 1}` is an infinite "cylinder". -/
def cylExample : CoordPoly 2 where
  degree := 1
  coord := fun _ => 0
  root := fun _ => 0

/-- `cylExample` evaluates to the first coordinate: `f(z) = z₀`. -/
theorem cyl_eval (z : Fin 2 → ℂ) : cylExample.eval z = z 0 := by
  simp [CoordPoly.eval, cylExample]

/-- The lemniscate of `cylExample` is exactly the cylinder `{z : |z₀| < 1}`. -/
theorem lem_cyl_eq : lem cylExample = {z : Fin 2 → ℂ | ‖z 0‖ < 1} := by
  ext z
  simp only [lem, Set.mem_setOf_eq, cyl_eval]

/-- **Nonemptiness:** the cylinder contains the origin. -/
theorem cyl_nonempty : (lem cylExample).Nonempty := by
  refine ⟨0, ?_⟩
  rw [lem_cyl_eq]
  simp only [Set.mem_setOf_eq, Pi.zero_apply, norm_zero]
  norm_num

/-- **The new phenomenon (boundedness fails).** In ℂ² the lemniscate of
`f(z₀,z₁) = z₀` is UNBOUNDED: the second coordinate is free, so the points
`(0, t)` lie in the lemniscate for every `t ∈ ℝ` yet have norm `≥ |t| → ∞`.
Contrast oq-03's `isBounded_lem`, which holds for *every* one-variable
lemniscate. This is the core obstruction to extending #1042 to higher
dimensions: there is no confinement to balls about the roots. -/
theorem cyl_unbounded : ¬ Bornology.IsBounded (lem cylExample) := by
  rw [isBounded_iff_forall_norm_le]
  push_neg
  intro C
  refine ⟨![0, ((|C| + 1 : ℝ) : ℂ)], ?_, ?_⟩
  · rw [lem_cyl_eq, Set.mem_setOf_eq, Matrix.cons_val_zero, norm_zero]
    norm_num
  · have hle : ‖(![0, ((|C| + 1 : ℝ) : ℂ)] : Fin 2 → ℂ) 1‖
        ≤ ‖(![0, ((|C| + 1 : ℝ) : ℂ)] : Fin 2 → ℂ)‖ := norm_le_pi_norm _ 1
    have hval : (![0, ((|C| + 1 : ℝ) : ℂ)] : Fin 2 → ℂ) 1 = ((|C| + 1 : ℝ) : ℂ) := by
      simp [Matrix.cons_val_one]
    rw [hval, Complex.norm_of_nonneg (by positivity : (0:ℝ) ≤ |C| + 1)] at hle
    have hC : C < |C| + 1 := by have := le_abs_self C; linarith
    linarith

/-- The cylinder is convex (the preimage of the open unit ball in ℂ under the
ℝ-linear first-coordinate projection). -/
theorem convex_cyl : Convex ℝ (lem cylExample) := by
  have h : lem cylExample
      = (LinearMap.proj (0 : Fin 2) : (Fin 2 → ℂ) →ₗ[ℝ] ℂ) ⁻¹' Metric.ball (0 : ℂ) 1 := by
    rw [lem_cyl_eq]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, mem_ball_zero_iff, LinearMap.proj_apply]
  rw [h]
  exact (convex_ball (0 : ℂ) 1).linear_preimage _

/-- **Components merge.** The same ℂ² lemniscate is CONNECTED. Where the
one-variable `zⁿ + 1` has `n` disjoint island components, the free coordinate
fuses them into a single connected (indeed convex) unbounded set, so the
component-counting question of #1042 has no naive higher-dimensional analogue. -/
theorem isConnected_cyl : IsConnected (lem cylExample) :=
  convex_cyl.isConnected cyl_nonempty

/-- **Capstone (answer to oq-02).** Openness and root-containment extend verbatim
to ℂⁿ, but the geometric heart of #1042 does not: in ℂ² the lemniscate of
`f(z₀,z₁) = z₀` is open and connected yet UNBOUNDED, in direct contrast to the
one-variable confinement/boundedness theorem of oq-03. Hence the #1042
component-count results are genuinely a one-complex-variable phenomenon. -/
theorem higher_dim_confinement_fails :
    IsOpen (lem cylExample) ∧ IsConnected (lem cylExample) ∧
      ¬ Bornology.IsBounded (lem cylExample) :=
  ⟨isOpen_lem cylExample, isConnected_cyl, cyl_unbounded⟩

end Erdos1042OQ02
