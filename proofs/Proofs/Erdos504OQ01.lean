/-
  Erdős Problem #504 — Maximum Angle in Point Sets.
  Open question OQ-01: the higher-dimensional analogue.

  Erdős #504 (Blumenthal's problem, solved by Sendov 1993) concerns `α_n`, the
  largest angle `α` such that *every* `n`-point planar set contains three points
  forming an angle `≥ α`.  The natural higher-dimensional analogue asks the same
  in `ℝ^d`: for which `n` is one *forced* to have an angle exceeding `π/2`?

  The threshold is governed by the **Danzer–Grünbaum theorem (1962)**: the maximum
  number of points in `ℝ^d` with *all* angles non-obtuse (`≤ π/2`) is exactly `2^d`,
  realised by the vertices of a cube.  Equivalently, you cannot guarantee an obtuse
  angle until you have *more than* `2^d` points, so the `d`-dimensional analogue of
  `α_n` stays `≤ π/2` for all `n ≤ 2^d`.

  This file formalises the **sharp lower-bound (construction) half** of that theorem,
  which is fully elementary:

    * `inner_edge_nonneg` — for any three vertices `a, b, c ∈ {0,1}^d`, the edge
      vectors satisfy `⟪a - b, c - b⟫ ≥ 0`.  The inner product expands as a sum of
      per-coordinate products, each non-negative because, coordinate by coordinate,
      `a i - b i` and `c i - b i` always have the same sign (both `≥ 0` when `b i = 0`,
      both `≤ 0` when `b i = 1`).

    * `angle_le_pi_div_two` — consequently every angle `∠ a b c` at a cube vertex is
      `≤ π/2` (non-obtuse), via `Real.arccos_le_pi_div_two`.

    * `cubeVertices_card` — the cube has exactly `2^d` distinct vertices, and
      `cubeVertices_pairwise_nonobtuse` packages the construction: `2^d` points in
      `ℝ^d` with every angle non-obtuse.

  The matching upper bound (`2^d + 1` points *force* an obtuse angle) is the deep
  half of Danzer–Grünbaum and is left open here.

  Self-contained: `import Mathlib`, no axioms beyond Lean's foundational core,
  no `sorry`, no `native_decide`.
-/
import Mathlib

open scoped RealInnerProductSpace BigOperators
open Real

namespace Erdos504OQ01

variable {d : ℕ}

/-- A point of `ℝ^d` (here `EuclideanSpace ℝ (Fin d)`) is a **cube vertex** when
every coordinate is `0` or `1`. -/
def IsCubeVertex (v : EuclideanSpace ℝ (Fin d)) : Prop := ∀ i, v i = 0 ∨ v i = 1

/-- Each coordinate of a cube vertex is non-negative. -/
theorem coord_nonneg {v : EuclideanSpace ℝ (Fin d)} (h : IsCubeVertex v) (i : Fin d) :
    0 ≤ v i := by
  rcases h i with h | h <;> rw [h] <;> norm_num

/-- Each coordinate of a cube vertex, minus one, is non-positive. -/
theorem coord_sub_one_nonpos {v : EuclideanSpace ℝ (Fin d)} (h : IsCubeVertex v) (i : Fin d) :
    v i - 1 ≤ 0 := by
  rcases h i with h | h <;> rw [h] <;> norm_num

/-- The real inner product of two vectors of `EuclideanSpace ℝ (Fin d)` as a sum of
coordinatewise products. -/
theorem inner_eq_sum (x y : EuclideanSpace ℝ (Fin d)) :
    ⟪x, y⟫ = ∑ i, x i * y i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **Key elementary estimate.** For three cube vertices `a, b, c`, the edge vectors
`a - b` and `c - b` (emanating from `b`) have non-negative inner product. -/
theorem inner_edge_nonneg {a b c : EuclideanSpace ℝ (Fin d)}
    (ha : IsCubeVertex a) (hb : IsCubeVertex b) (hc : IsCubeVertex c) :
    0 ≤ (⟪a - b, c - b⟫ : ℝ) := by
  rw [inner_eq_sum]
  apply Finset.sum_nonneg
  intro i _
  simp only [PiLp.sub_apply]
  rcases hb i with hbi | hbi
  · -- `b i = 0`: both factors `a i`, `c i` are `≥ 0`.
    rw [hbi]
    have := mul_nonneg (coord_nonneg ha i) (coord_nonneg hc i)
    simpa using this
  · -- `b i = 1`: both factors `a i - 1`, `c i - 1` are `≤ 0`.
    rw [hbi]
    nlinarith [coord_sub_one_nonpos ha i, coord_sub_one_nonpos hc i]

/-- **Non-obtuse angle.** Any angle formed at a cube vertex by two other cube vertices
is at most `π/2`.  This is the construction half of the Danzer–Grünbaum theorem:
the `2^d` cube vertices realise a point set with no obtuse angle. -/
theorem angle_le_pi_div_two {a b c : EuclideanSpace ℝ (Fin d)}
    (ha : IsCubeVertex a) (hb : IsCubeVertex b) (hc : IsCubeVertex c) :
    EuclideanGeometry.angle a b c ≤ π / 2 := by
  rw [EuclideanGeometry.angle, InnerProductGeometry.angle, vsub_eq_sub, vsub_eq_sub,
    Real.arccos_le_pi_div_two]
  apply div_nonneg (inner_edge_nonneg ha hb hc)
  positivity

/-! ### The `2^d` cube vertices -/

/-- The cube vertex indexed by a subset `s ⊆ Fin d`: coordinate `i` is `1` iff `i ∈ s`. -/
noncomputable def cubeVertex (s : Finset (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => if i ∈ s then 1 else 0)

@[simp] theorem cubeVertex_apply (s : Finset (Fin d)) (i : Fin d) :
    cubeVertex s i = if i ∈ s then 1 else 0 := rfl

theorem cubeVertex_isCubeVertex (s : Finset (Fin d)) : IsCubeVertex (cubeVertex s) := by
  intro i
  rw [cubeVertex_apply]
  split <;> simp

theorem cubeVertex_injective : Function.Injective (cubeVertex (d := d)) := by
  intro s t h
  ext i
  have hi : cubeVertex s i = cubeVertex t i := by rw [h]
  rw [cubeVertex_apply, cubeVertex_apply] at hi
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp [hs, ht] at hi ⊢

/-- The finite set of all `2^d` cube vertices in `ℝ^d`. -/
noncomputable def cubeVertices : Finset (EuclideanSpace ℝ (Fin d)) :=
  Finset.univ.image cubeVertex

/-- The cube has exactly `2^d` vertices. -/
theorem cubeVertices_card : (cubeVertices (d := d)).card = 2 ^ d := by
  rw [cubeVertices, Finset.card_image_of_injective _ cubeVertex_injective, Finset.card_univ,
    Fintype.card_finset, Fintype.card_fin]

/-- Every vertex in the cube set is genuinely a cube vertex. -/
theorem mem_cubeVertices {v : EuclideanSpace ℝ (Fin d)} (hv : v ∈ cubeVertices) :
    IsCubeVertex v := by
  rw [cubeVertices, Finset.mem_image] at hv
  obtain ⟨s, _, rfl⟩ := hv
  exact cubeVertex_isCubeVertex s

/-- **Danzer–Grünbaum construction.** The `2^d` cube vertices form a configuration in
`ℝ^d` in which every angle is non-obtuse (`≤ π/2`). -/
theorem cubeVertices_pairwise_nonobtuse {a b c : EuclideanSpace ℝ (Fin d)}
    (ha : a ∈ cubeVertices) (hb : b ∈ cubeVertices) (hc : c ∈ cubeVertices) :
    EuclideanGeometry.angle a b c ≤ π / 2 :=
  angle_le_pi_div_two (mem_cubeVertices ha) (mem_cubeVertices hb) (mem_cubeVertices hc)

end Erdos504OQ01
