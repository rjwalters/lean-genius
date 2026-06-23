/-
Erdős Problem #504 — OQ-01: The higher-dimensional analogue (point sets in ℝ^d).

Parent problem (Erdős #504, Blumenthal's problem, solved by Sendov 1993):
in ℝ², let α_n be the largest angle α such that *every* set of n points contains
three points forming an angle ≥ α. The natural higher-dimensional open question is:
given n points in ℝ^d, what is the threshold angle that is always forced?

The key threshold is the right angle π/2.  A finite point set is called
**non-obtuse** if every angle ∠ a b c determined by three of its points is at
most π/2 (equivalently, never obtuse).  Danzer and Grünbaum (1962) determined
that the maximum size of a non-obtuse set in ℝ^d is exactly 2^d, with the
extremal configuration being the 2^d vertices of a hypercube.  Their lower-bound
construction is the cornerstone of every higher-dimensional version of #504:
it shows that 2^d points in ℝ^d need not force any obtuse angle, so the
right-angle threshold is *not* crossed until one has more than 2^d points.

This file formalises that construction, unconditionally and axiom-free:

  * `angle_le_pi_div_two_of_inner_nonneg` — a dimension-free criterion:
    a non-negative inner product forces a non-obtuse angle.  (Reusable.)
  * `cube_inner_nonneg` — for vertices a, b, c ∈ {0,1}^d the inner product
    ⟪a − b, c − b⟫ is ≥ 0, because in each coordinate the two factors share the
    sign of b_i.  This is the elementary heart of the argument.
  * `cube_angle_le_pi_div_two` — hence every angle of the hypercube is ≤ π/2.
  * `exists_cube_no_obtuse` — there is a set of 2^d points in ℝ^d with no
    obtuse angle (the Danzer–Grünbaum lower bound).
  * `cube_angle_pi_div_two_attained` — for d ≥ 2 the bound π/2 is *attained*,
    so it cannot be improved: the construction is sharp.

What is proved here is the construction (lower bound) direction.  The matching
upper bound — that 2^d + 1 points in ℝ^d always contain an obtuse angle — is the
harder half of Danzer–Grünbaum and is not attempted.
-/

import Mathlib

open Real
open scoped InnerProductSpace EuclideanGeometry

namespace Erdos504OQ01

/-- Points of `d`-dimensional Euclidean space. -/
abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A point is a **vertex of the unit hypercube** `{0,1}^d` when every coordinate
is `0` or `1`. -/
def IsCubeVertex {d : ℕ} (v : Point d) : Prop := ∀ i, v i = 0 ∨ v i = 1

/-! ### A dimension-free non-obtuse criterion -/

/-- **Non-negative inner product ⟹ non-obtuse angle.**  In any real inner product
space, if `⟪x, y⟫ ≥ 0` then the (unoriented) angle between `x` and `y` is at most
`π/2`.  This holds because the angle is `arccos (⟪x,y⟫ / (‖x‖‖y‖))` and the
argument of `arccos` is non-negative. -/
theorem angle_le_pi_div_two_of_inner_nonneg
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x y : V) (h : 0 ≤ ⟪x, y⟫_ℝ) :
    InnerProductGeometry.angle x y ≤ π / 2 := by
  unfold InnerProductGeometry.angle
  rw [Real.arccos_le_pi_div_two]
  exact div_nonneg h (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-! ### The hypercube has no obtuse angle -/

/-- The coordinatewise sign computation: if `bi, ai, ci ∈ {0,1}` then
`(ci − bi)·(ai − bi) ≥ 0`, because both factors share the sign of `bi`
(non-negative if `bi = 0`, non-positive if `bi = 1`). -/
lemma cube_term_nonneg {bi ai ci : ℝ}
    (hb : bi = 0 ∨ bi = 1) (ha : ai = 0 ∨ ai = 1) (hc : ci = 0 ∨ ci = 1) :
    0 ≤ (ci - bi) * (ai - bi) := by
  rcases hb with hb | hb <;> rcases ha with ha | ha <;> rcases hc with hc | hc <;>
    subst hb ha hc <;> norm_num

/-- **The hypercube inner product is non-negative.**  For cube vertices
`a, b, c ∈ {0,1}^d`, `⟪a − b, c − b⟫ ≥ 0`.  The inner product is the sum over
coordinates of `(a_i − b_i)(c_i − b_i)`, and every summand is non-negative by
`cube_term_nonneg`. -/
theorem cube_inner_nonneg {d : ℕ} (a b c : Point d)
    (ha : IsCubeVertex a) (hb : IsCubeVertex b) (hc : IsCubeVertex c) :
    0 ≤ ⟪a - b, c - b⟫_ℝ := by
  rw [PiLp.inner_apply]
  refine Finset.sum_nonneg (fun i _ => ?_)
  rw [PiLp.sub_apply, PiLp.sub_apply, RCLike.inner_apply, conj_trivial]
  exact cube_term_nonneg (hb i) (ha i) (hc i)

/-- **No obtuse angle in the hypercube.**  Every angle `∠ a b c` determined by
three vertices of `{0,1}^d` is at most `π/2`. -/
theorem cube_angle_le_pi_div_two {d : ℕ} (a b c : Point d)
    (ha : IsCubeVertex a) (hb : IsCubeVertex b) (hc : IsCubeVertex c) :
    ∠ a b c ≤ π / 2 := by
  unfold EuclideanGeometry.angle
  apply angle_le_pi_div_two_of_inner_nonneg
  rw [vsub_eq_sub, vsub_eq_sub]
  exact cube_inner_nonneg a b c ha hb hc

/-! ### The 2^d-point construction -/

/-- The set of all `2^d` vertices of the unit hypercube `{0,1}^d`, obtained as
the image of the boolean cube `Fin d → Bool`. -/
noncomputable def cubeVertices (d : ℕ) : Finset (Point d) :=
  Finset.univ.image
    (fun f : Fin d → Bool => WithLp.toLp 2 (fun i => if f i then (1 : ℝ) else 0))

lemma cubeVertices_injective (d : ℕ) :
    Function.Injective
      (fun f : Fin d → Bool => WithLp.toLp 2 (fun i => if f i then (1 : ℝ) else 0)) := by
  intro f g hfg
  have h2 := WithLp.toLp_injective 2 hfg
  funext i
  have hi := congrFun h2 i
  by_cases hf : f i <;> by_cases hg : g i <;> simp_all

lemma mem_cubeVertices_isCubeVertex {d : ℕ} {v : Point d}
    (hv : v ∈ cubeVertices d) : IsCubeVertex v := by
  rw [cubeVertices, Finset.mem_image] at hv
  obtain ⟨f, _, rfl⟩ := hv
  intro i
  rw [PiLp.toLp_apply]
  by_cases h : f i <;> simp [h]

/-- The hypercube vertex set has exactly `2^d` elements. -/
lemma cubeVertices_card (d : ℕ) : (cubeVertices d).card = 2 ^ d := by
  rw [cubeVertices, Finset.card_image_of_injective _ (cubeVertices_injective d)]
  simp [Finset.card_univ]

/-- **Danzer–Grünbaum lower bound (formalised).**  For every dimension `d` there
is a set of `2^d` points in ℝ^d in which no three points form an obtuse angle.
Hence `2^d` points in ℝ^d never force an angle exceeding `π/2`. -/
theorem exists_cube_no_obtuse (d : ℕ) :
    ∃ S : Finset (Point d), S.card = 2 ^ d ∧
      ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∠ a b c ≤ π / 2 := by
  refine ⟨cubeVertices d, cubeVertices_card d, fun a ha b hb c hc => ?_⟩
  exact cube_angle_le_pi_div_two a b c
    (mem_cubeVertices_isCubeVertex ha) (mem_cubeVertices_isCubeVertex hb)
    (mem_cubeVertices_isCubeVertex hc)

/-! ### Sharpness: the bound π/2 is attained -/

/-- The standard `i`-th unit vertex of the cube (`1` in coordinate `i`, else `0`). -/
noncomputable def unitVertex {d : ℕ} (i : Fin d) : Point d :=
  WithLp.toLp 2 (fun j => if j = i then 1 else 0)

@[simp] lemma unitVertex_apply {d : ℕ} (i j : Fin d) :
    unitVertex i j = if j = i then 1 else 0 := by
  rw [unitVertex, PiLp.toLp_apply]

lemma unitVertex_isCubeVertex {d : ℕ} (i : Fin d) : IsCubeVertex (unitVertex i) := by
  intro j; by_cases h : j = i <;> simp [h]

lemma zero_isCubeVertex {d : ℕ} : IsCubeVertex (0 : Point d) := by
  intro i; left; simp

/-- **Sharpness.**  In dimension `d ≥ 2` the bound `π/2` of `cube_angle_le_pi_div_two`
is attained: the origin together with two distinct unit vertices forms a right
angle.  Therefore the threshold `π/2` cannot be lowered — the hypercube genuinely
realises right angles and no smaller universal bound holds. -/
theorem cube_angle_pi_div_two_attained {d : ℕ} (hd : 2 ≤ d) :
    ∃ a b c : Point d, IsCubeVertex a ∧ IsCubeVertex b ∧ IsCubeVertex c ∧
      ∠ a b c = π / 2 := by
  have hne : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by
    intro h; simpa using congrArg Fin.val h
  refine ⟨unitVertex ⟨0, by omega⟩, 0, unitVertex ⟨1, by omega⟩,
    unitVertex_isCubeVertex _, zero_isCubeVertex, unitVertex_isCubeVertex _, ?_⟩
  rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, sub_zero, sub_zero,
    ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two, PiLp.inner_apply]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [RCLike.inner_apply, conj_trivial, unitVertex_apply, unitVertex_apply]
  rcases eq_or_ne i ⟨0, by omega⟩ with h | h
  · subst h; simp [hne]
  · simp [h]

end Erdos504OQ01
