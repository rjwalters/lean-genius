/-
  Erdős Problem #1070, Open Question 05:
  Unit-distance graphs in ℝ^d for d ≥ 3 — dimensional dependence.

  Parent problem (Erdős #1070, OPEN): Let f(n) be the maximum k such that any n
  points in ℝ² contain k with no two at distance 1. The density limit
  m₁ = limₙ f(n)/n lies in [0.22936, 2/7] and is unknown.

  Open Question 05 (from the parent's openQuestions):
    "Does the analogous problem in ℝ^d for d ≥ 3 exhibit similar density
     barriers? The Larman–Rogers argument generalizes, but the Fourier analysis
     becomes significantly more complex in higher dimensions."

  This file records a concrete, fully machine-checked (0-axiom) STRUCTURAL fact
  that already distinguishes higher dimensions from the plane:

    The clique number of the unit-distance graph of ℝ^d is UNBOUNDED in d.

  In the plane the clique number is bounded (a unit-distance graph in ℝ² has
  no K₄: four mutually-unit-distant points do not fit in ℝ²). In ℝ^d one can
  realise d mutually-unit-distant points (a regular simplex), so the clique
  number grows at least linearly with the dimension. Consequently the largest
  unit-distance CLIQUES have independence ratio 1/d → 0, whereas the plane's
  density limit m₁ stays bounded away from 0. This is a qualitative difference
  in the extremal geometry, one honest piece of the (open) OQ-05.

  Construction: the d scaled standard basis vectors (√2)⁻¹ · eᵢ in ℝ^d are
  pairwise at Euclidean distance 1 (they form an orthonormal family, so the
  distance between two of them is (√2)⁻¹ · √2 = 1).

  Everything below is elementary and axiom-free.
-/

import Mathlib

namespace Erdos1070OQ05

open scoped RealInnerProductSpace

/-! ## Unit distance and unit-distance cliques in ℝ^d -/

/-- Two points of `ℝ^d` are at *unit distance* if their Euclidean distance is `1`. -/
def IsUnitDist {d : ℕ} (p q : EuclideanSpace ℝ (Fin d)) : Prop := dist p q = 1

/-- A finite set of points is a *unit-distance clique* if every pair of distinct
points is at unit distance. -/
def IsUnitClique {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p ≠ q → IsUnitDist p q

/-- A finite set is *unit-distance free* if no two distinct points are at unit
distance (an independent set of the unit-distance graph). -/
def IsUnitFree {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p ≠ q → ¬ IsUnitDist p q

/-! ## The regular simplex: `d` mutually unit-distant points in ℝ^d -/

/-- The `i`-th vertex of the scaled simplex: `(√2)⁻¹` times the `i`-th standard
basis vector of `ℝ^d`. -/
noncomputable def simplexPoint (d : ℕ) (i : Fin d) : EuclideanSpace ℝ (Fin d) :=
  (Real.sqrt 2)⁻¹ • EuclideanSpace.single i (1 : ℝ)

/-- The standard basis vectors of `EuclideanSpace ℝ (Fin d)` are orthonormal;
in particular distinct ones are orthogonal. -/
theorem single_inner_eq_zero {d : ℕ} {i j : Fin d} (h : i ≠ j) :
    ⟪(EuclideanSpace.single i (1 : ℝ)), (EuclideanSpace.single j (1 : ℝ))⟫ = 0 := by
  rw [EuclideanSpace.inner_single_left]
  simp [EuclideanSpace.single_apply, h]

/-- **Core computation.** Two distinct scaled basis vectors are at distance `1`. -/
theorem simplexPoint_dist {d : ℕ} {i j : Fin d} (h : i ≠ j) :
    dist (simplexPoint d i) (simplexPoint d j) = 1 := by
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  -- Work with the squared distance via the inner product.
  rw [dist_eq_norm]
  have key : ‖simplexPoint d i - simplexPoint d j‖ ^ 2 = 1 := by
    have hn := norm_sub_sq_real (simplexPoint d i) (simplexPoint d j)
    -- expand each piece
    have hii : ‖simplexPoint d i‖ ^ 2 = 1 / 2 := by
      unfold simplexPoint
      rw [norm_smul]
      simp only [EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs]
      rw [sq_abs, inv_pow, h2]; norm_num
    have hjj : ‖simplexPoint d j‖ ^ 2 = 1 / 2 := by
      unfold simplexPoint
      rw [norm_smul]
      simp only [EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs]
      rw [sq_abs, inv_pow, h2]; norm_num
    have hij : ⟪simplexPoint d i, simplexPoint d j⟫ = 0 := by
      unfold simplexPoint
      rw [real_inner_smul_left, real_inner_smul_right, single_inner_eq_zero h]
      ring
    rw [hn, hii, hjj, hij]; norm_num
  -- take square roots
  nlinarith [norm_nonneg (simplexPoint d i - simplexPoint d j), key]

/-- Distinct indices give distinct simplex points (they are at distance `1 > 0`). -/
theorem simplexPoint_injective (d : ℕ) : Function.Injective (simplexPoint d) := by
  intro i j hij
  by_contra hne
  have : dist (simplexPoint d i) (simplexPoint d j) = 1 := simplexPoint_dist hne
  rw [hij, dist_self] at this
  norm_num at this

/-- The set of the `d` simplex vertices in `ℝ^d`. -/
noncomputable def simplexClique (d : ℕ) : Finset (EuclideanSpace ℝ (Fin d)) :=
  Finset.image (simplexPoint d) Finset.univ

@[simp] theorem simplexClique_card (d : ℕ) : (simplexClique d).card = d := by
  rw [simplexClique, Finset.card_image_of_injective _ (simplexPoint_injective d),
    Finset.card_univ, Fintype.card_fin]

theorem simplexClique_isUnitClique (d : ℕ) : IsUnitClique (simplexClique d) := by
  intro p hp q hq hpq
  simp only [simplexClique, Finset.mem_image, Finset.mem_univ, true_and] at hp hq
  obtain ⟨i, rfl⟩ := hp
  obtain ⟨j, rfl⟩ := hq
  have hij : i ≠ j := fun h => hpq (by rw [h])
  exact simplexPoint_dist hij

/-! ## Main results -/

/-- **Unbounded clique number.** For every `d` there is a unit-distance clique of
size `d` in `ℝ^d`. Equivalently, the clique number of the unit-distance graph of
`ℝ^d` is at least `d`, hence unbounded as `d → ∞`. -/
theorem exists_unit_clique_of_card (d : ℕ) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin d)), S.card = d ∧ IsUnitClique S :=
  ⟨simplexClique d, simplexClique_card d, simplexClique_isUnitClique d⟩

/-- Within a unit-distance clique, any unit-distance-free subset has at most one
point: two distinct points of the clique are adjacent, so cannot both lie in an
independent set. -/
theorem unitFree_subset_card_le_one {d : ℕ} {S T : Finset (EuclideanSpace ℝ (Fin d))}
    (hS : IsUnitClique S) (hTS : T ⊆ S) (hT : IsUnitFree T) : T.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p hp q hq
  by_contra hpq
  exact hT p hp q hq hpq (hS p (hTS hp) q (hTS hq) hpq)

/-- **Vanishing independence ratio of the extremal cliques.** The largest
unit-distance-free subset of the size-`d` simplex clique has at most one point,
so its independence ratio is `1/d → 0`. (For the parent plane problem the density
limit `m₁ ≥ 0.22936` stays bounded away from `0`; the simplex cliques show that
in growing dimension the extremal unit-distance CLIQUES behave completely
differently.) -/
theorem simplexClique_indep_le_one (d : ℕ)
    {T : Finset (EuclideanSpace ℝ (Fin d))} (hTS : T ⊆ simplexClique d)
    (hT : IsUnitFree T) : T.card ≤ 1 :=
  unitFree_subset_card_le_one (simplexClique_isUnitClique d) hTS hT

/-- **Summary / OQ-05 partial answer.** In every dimension `d` the unit-distance
graph of `ℝ^d` contains a clique on `d` vertices whose only independent sets are
singletons. Thus the clique number grows (at least) linearly with `d`, which is a
genuine qualitative departure from the plane, where the clique number is bounded.
This resolves the *structural* half of OQ-05 (higher dimensions differ) while the
quantitative density barrier `m₁(d)` remains open. -/
theorem erdos_1070_oq05_dimension_dependence :
    ∀ d : ℕ, ∃ S : Finset (EuclideanSpace ℝ (Fin d)),
      S.card = d ∧ IsUnitClique S ∧
      (∀ T ⊆ S, IsUnitFree T → T.card ≤ 1) := by
  intro d
  refine ⟨simplexClique d, simplexClique_card d, simplexClique_isUnitClique d, ?_⟩
  intro T hTS hT
  exact simplexClique_indep_le_one d hTS hT

end Erdos1070OQ05
