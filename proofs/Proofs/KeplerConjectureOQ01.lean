/-
  Kepler Conjecture OQ-01: Best-known sphere packing densities in dimensions 4-23

  **Open question** (parent gallery `kepler-conjecture`, open-question arm 01).
  The parent Kepler-Hales theorem settles the *optimal* sphere packing density
  in ℝ³ (the FCC density `π / (3√2) ≈ 0.7405`). The natural generalisation
  asks for the optimal density of congruent-sphere packings in higher
  dimensions. This is one of the deepest open problems in discrete geometry:
  the optimal density is known in only FIVE dimensions —
  `n = 1, 2, 3` (classical), `n = 8` (Viazovska 2016, the `E₈` lattice) and
  `n = 24` (Cohn-Kumar-Miller-Radchenko-Viazovska 2017, the Leech lattice).
  For every dimension in the band `4 ≤ n ≤ 23` *except* `n = 8` the optimal
  density is **open**; the best constructions known are specific lattices.

  **What this file proves (axiom-free).**
  Following the sibling entry `kepler-conjecture-oq-04`, we take the
  *best-known* lattice packing densities from the literature
  (Conway-Sloane, *Sphere Packings, Lattices and Groups*) as named real
  constants and prove rigorous relationships between them. We focus on the
  classical "root-lattice champions" in dimensions 4 through 8:

  | dim `n` | densest known lattice | packing density `Δₙ`            | `≈`     |
  |---------|-----------------------|---------------------------------|---------|
  | 4       | `D₄`                  | `π² / 16`                       | 0.61685 |
  | 5       | `D₅`                  | `π² √2 / 30`                    | 0.46526 |
  | 6       | `E₆`                  | `π³ √3 / 144`                   | 0.37295 |
  | 7       | `E₇`                  | `π³ / 105`                      | 0.29530 |
  | 8       | `E₈`                  | `π⁴ / 384`                      | 0.25367 |

  Each `Δₙ = δₙ · Vₙ`, the lattice's center density `δₙ` times the volume
  `Vₙ` of the unit `n`-ball (`V₄ = π²/2`, `V₅ = 8π²/15`, `V₆ = π³/6`,
  `V₇ = 16π³/105`, `V₈ = π⁴/24`); the center densities are
  `δ₄ = 1/8`, `δ₅ = 1/(8√2)`, `δ₆ = 1/(8√3)`, `δ₇ = δ₈ = 1/16`.
  Of these, only `D₄`'s density is conjectural-optimal and only `E₈` is a
  *theorem* (Viazovska); `D₅, E₆, E₇` are merely the best lattices known.

  **Headline theorem `density_strictly_decreasing_4_to_8`.**
  The champions form a strictly decreasing chain
  `Δ₄ > Δ₅ > Δ₆ > Δ₇ > Δ₈`, quantifying the elementary but important
  principle that sphere packing gets *sparser* as the dimension grows:
  even the densest known arrangements thin out. Each comparison divides out
  the common power of `π` (so the proofs are low-degree in `π`) and is closed
  by `nlinarith` from the Mathlib bounds `Real.pi_gt_3141592 / pi_lt_3141593`
  together with two-sided rational brackets for `√2` and `√3`.

  We additionally prove that every `Δₙ` is a genuine density
  (`0 < Δₙ < 1`), bracket each `Δₙ` between explicit rationals
  (`density_*_bounds`), and bundle the five champions into the parent's
  `PackingDensity` structure with the existence corollary
  `exists_dimension_8_optimal` (a `PackingDensity` realising the *proven*
  optimum `π⁴/384`).

  **Status of this file.**
  - 0 sorries, 0 axioms (every result is `nlinarith`/`norm_num`-discharged
    from Mathlib's `π` bounds; no new assumptions).
  - The numbers are *constructions* (lower bounds on the true optimum), so
    nothing here claims to resolve the open problem — it organises the
    best-known data and proves the monotonicity that motivates it.
-/

import Mathlib
import Proofs.KeplerConjecture

namespace KeplerConjectureOQ01

open Real KeplerConjecture

/-! ## Best-known packing densities in dimensions 4-8 -/

/-- `D₄` lattice packing density in ℝ⁴, `π²/16 ≈ 0.61685` (best known). -/
noncomputable def dim4Density : ℝ := π ^ 2 / 16

/-- `D₅` lattice packing density in ℝ⁵, `π²√2/30 ≈ 0.46526` (best known). -/
noncomputable def dim5Density : ℝ := π ^ 2 * Real.sqrt 2 / 30

/-- `E₆` lattice packing density in ℝ⁶, `π³√3/144 ≈ 0.37295` (best known). -/
noncomputable def dim6Density : ℝ := π ^ 3 * Real.sqrt 3 / 144

/-- `E₇` lattice packing density in ℝ⁷, `π³/105 ≈ 0.29530` (best known). -/
noncomputable def dim7Density : ℝ := π ^ 3 / 105

/-- `E₈` lattice packing density in ℝ⁸, `π⁴/384 ≈ 0.25367` (Viazovska 2016,
    *proven optimal*). -/
noncomputable def dim8Density : ℝ := π ^ 4 / 384

/-! ## Numeric infrastructure: brackets for `π`-powers and small surds -/

/-- `9.8695 < π² < 9.8697` (true value `π² ≈ 9.8696044`). -/
theorem pi_sq_bounds : 9.8695 < π ^ 2 ∧ π ^ 2 < 9.8697 := by
  refine ⟨?_, ?_⟩
  · nlinarith [Real.pi_gt_d6, Real.pi_lt_d6, Real.pi_pos,
      mul_pos (sub_pos.mpr Real.pi_gt_d6) Real.pi_pos]
  · nlinarith [Real.pi_gt_d6, Real.pi_lt_d6, Real.pi_pos,
      mul_pos Real.pi_pos (sub_pos.mpr Real.pi_lt_d6)]

/-- `31.006 < π³ < 31.008`. -/
theorem pi_cube_bounds : 31.006 < π ^ 3 ∧ π ^ 3 < 31.008 := by
  obtain ⟨h2lo, h2hi⟩ := pi_sq_bounds
  have hpos2 : (0:ℝ) < π ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · nlinarith [Real.pi_gt_d6, Real.pi_lt_d6, Real.pi_pos, h2lo, h2hi, hpos2]
  · nlinarith [Real.pi_gt_d6, Real.pi_lt_d6, Real.pi_pos, h2lo, h2hi, hpos2]

/-- `97.40 < π⁴ < 97.42`. -/
theorem pi_quart_bounds : 97.40 < π ^ 4 ∧ π ^ 4 < 97.42 := by
  obtain ⟨h3lo, h3hi⟩ := pi_cube_bounds
  have hpos3 : (0:ℝ) < π ^ 3 := by positivity
  refine ⟨?_, ?_⟩
  · nlinarith [Real.pi_gt_d6, Real.pi_lt_d6, Real.pi_pos, h3lo, h3hi, hpos3]
  · nlinarith [Real.pi_gt_d6, Real.pi_lt_d6, Real.pi_pos, h3lo, h3hi, hpos3]

/-- `1.41421 < √2 < 1.41422`. -/
theorem sqrt2_bounds : 1.41421 < Real.sqrt 2 ∧ Real.sqrt 2 < 1.41422 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨?_, ?_⟩
  · nlinarith [h2, hpos]
  · nlinarith [h2, hpos]

/-- `1.73205 < √3 < 1.73206`. -/
theorem sqrt3_bounds : 1.73205 < Real.sqrt 3 ∧ Real.sqrt 3 < 1.73206 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨?_, ?_⟩
  · nlinarith [h3, hpos]
  · nlinarith [h3, hpos]

/-! ## Each champion is a genuine density `0 < Δₙ < 1` -/

theorem dim4Density_pos : 0 < dim4Density := by
  unfold dim4Density; positivity

theorem dim5Density_pos : 0 < dim5Density := by
  unfold dim5Density
  have := Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)
  positivity

theorem dim6Density_pos : 0 < dim6Density := by
  unfold dim6Density
  have := Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num)
  positivity

theorem dim7Density_pos : 0 < dim7Density := by
  unfold dim7Density; positivity

theorem dim8Density_pos : 0 < dim8Density := by
  unfold dim8Density; positivity

theorem dim4Density_lt_one : dim4Density < 1 := by
  unfold dim4Density
  obtain ⟨_, h2hi⟩ := pi_sq_bounds
  linarith

theorem dim5Density_lt_one : dim5Density < 1 := by
  unfold dim5Density
  obtain ⟨_, h2hi⟩ := pi_sq_bounds
  obtain ⟨_, hshi⟩ := sqrt2_bounds
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [h2hi, hshi, hs, Real.pi_pos]

theorem dim6Density_lt_one : dim6Density < 1 := by
  unfold dim6Density
  obtain ⟨_, h3hi⟩ := pi_cube_bounds
  obtain ⟨_, hshi⟩ := sqrt3_bounds
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [h3hi, hshi, hs, Real.pi_pos]

theorem dim7Density_lt_one : dim7Density < 1 := by
  unfold dim7Density
  obtain ⟨_, h3hi⟩ := pi_cube_bounds
  linarith

theorem dim8Density_lt_one : dim8Density < 1 := by
  unfold dim8Density
  obtain ⟨_, h4hi⟩ := pi_quart_bounds
  linarith

/-! ## Rational brackets for each champion -/

/-- `0.6168 < Δ₄ < 0.6169`. -/
theorem dim4Density_bounds : 0.6168 < dim4Density ∧ dim4Density < 0.6169 := by
  unfold dim4Density
  obtain ⟨h2lo, h2hi⟩ := pi_sq_bounds
  constructor <;> linarith

/-- `0.4652 < Δ₅ < 0.4653`. -/
theorem dim5Density_bounds : 0.4652 < dim5Density ∧ dim5Density < 0.4653 := by
  unfold dim5Density
  obtain ⟨h2lo, h2hi⟩ := pi_sq_bounds
  obtain ⟨hslo, hshi⟩ := sqrt2_bounds
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨?_, ?_⟩
  · nlinarith [h2lo, h2hi, hslo, hshi, hs, Real.pi_pos]
  · nlinarith [h2lo, h2hi, hslo, hshi, hs, Real.pi_pos]

/-- `0.3729 < Δ₆ < 0.3730`. -/
theorem dim6Density_bounds : 0.3729 < dim6Density ∧ dim6Density < 0.3730 := by
  unfold dim6Density
  obtain ⟨h3lo, h3hi⟩ := pi_cube_bounds
  obtain ⟨hslo, hshi⟩ := sqrt3_bounds
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨?_, ?_⟩
  · nlinarith [h3lo, h3hi, hslo, hshi, hs, Real.pi_pos]
  · nlinarith [h3lo, h3hi, hslo, hshi, hs, Real.pi_pos]

/-- `0.2952 < Δ₇ < 0.2954`. -/
theorem dim7Density_bounds : 0.2952 < dim7Density ∧ dim7Density < 0.2954 := by
  unfold dim7Density
  obtain ⟨h3lo, h3hi⟩ := pi_cube_bounds
  constructor <;> linarith

/-- `0.2536 < Δ₈ < 0.2537`. -/
theorem dim8Density_bounds : 0.2536 < dim8Density ∧ dim8Density < 0.2537 := by
  unfold dim8Density
  obtain ⟨h4lo, h4hi⟩ := pi_quart_bounds
  constructor <;> linarith

/-! ## Headline: the champions strictly decrease in dimensions 4-8

Each comparison cancels the common power of `π` (`π² > 0` for `Δ₄ > Δ₅`,
`π² > 0` for `Δ₅ > Δ₆`, `π³ > 0` for `Δ₆ > Δ₇` and `Δ₇ > Δ₈`), so the
inequality reduces to a low-degree statement about `π` and a single surd. -/

/-- `Δ₄ > Δ₅`: the brackets `Δ₅ < 0.4653 < 0.6168 < Δ₄` separate the two. -/
theorem dim4_gt_dim5 : dim5Density < dim4Density := by
  have h5 := dim5Density_bounds.2
  have h4 := dim4Density_bounds.1
  linarith

/-- `Δ₅ > Δ₆`: the brackets `Δ₆ < 0.3730 < 0.4652 < Δ₅` separate the two. -/
theorem dim5_gt_dim6 : dim6Density < dim5Density := by
  have h6 := dim6Density_bounds.2
  have h5 := dim5Density_bounds.1
  linarith

/-- `Δ₆ > Δ₇`: the brackets `Δ₇ < 0.2954 < 0.3729 < Δ₆` separate the two. -/
theorem dim6_gt_dim7 : dim7Density < dim6Density := by
  have h7 := dim7Density_bounds.2
  have h6 := dim6Density_bounds.1
  linarith

/-- `Δ₇ > Δ₈`: the brackets `Δ₈ < 0.2537 < 0.2952 < Δ₇` separate the two. -/
theorem dim7_gt_dim8 : dim8Density < dim7Density := by
  have h8 := dim8Density_bounds.2
  have h7 := dim7Density_bounds.1
  linarith

/-- **Headline theorem.** The best-known lattice packing densities in
    dimensions 4 through 8 strictly decrease:
    `Δ₄ > Δ₅ > Δ₆ > Δ₇ > Δ₈`. -/
theorem density_strictly_decreasing_4_to_8 :
    dim5Density < dim4Density ∧ dim6Density < dim5Density ∧
      dim7Density < dim6Density ∧ dim8Density < dim7Density :=
  ⟨dim4_gt_dim5, dim5_gt_dim6, dim6_gt_dim7, dim7_gt_dim8⟩

/-! ## Bundling into the parent's `PackingDensity` structure -/

/-- `D₄` champion as a `PackingDensity`. -/
noncomputable def dim4Packing : PackingDensity where
  density := dim4Density
  nonneg := dim4Density_pos.le
  le_one := dim4Density_lt_one.le
/-- `D₅` champion as a `PackingDensity`. -/
noncomputable def dim5Packing : PackingDensity where
  density := dim5Density
  nonneg := dim5Density_pos.le
  le_one := dim5Density_lt_one.le
/-- `E₆` champion as a `PackingDensity`. -/
noncomputable def dim6Packing : PackingDensity where
  density := dim6Density
  nonneg := dim6Density_pos.le
  le_one := dim6Density_lt_one.le
/-- `E₇` champion as a `PackingDensity`. -/
noncomputable def dim7Packing : PackingDensity where
  density := dim7Density
  nonneg := dim7Density_pos.le
  le_one := dim7Density_lt_one.le
/-- `E₈` champion as a `PackingDensity` (the proven optimum). -/
noncomputable def dim8Packing : PackingDensity where
  density := dim8Density
  nonneg := dim8Density_pos.le
  le_one := dim8Density_lt_one.le

/-- There is a `PackingDensity` realising the dimension-8 *proven optimal*
    density `π⁴/384` (Viazovska 2016), and it is a genuine density. -/
theorem exists_dimension_8_optimal :
    ∃ p : PackingDensity, p.density = π ^ 4 / 384 ∧ 0 < p.density ∧ p.density < 1 :=
  ⟨dim8Packing, rfl, dim8Density_pos, dim8Density_lt_one⟩

/-- Final aggregation: all five champions are genuine densities
    (`0 < Δₙ < 1`) and they strictly decrease across dimensions 4-8. -/
theorem best_known_density_hierarchy_4_to_8 :
    (0 < dim4Density ∧ dim4Density < 1) ∧
    (0 < dim5Density ∧ dim5Density < 1) ∧
    (0 < dim6Density ∧ dim6Density < 1) ∧
    (0 < dim7Density ∧ dim7Density < 1) ∧
    (0 < dim8Density ∧ dim8Density < 1) ∧
    dim5Density < dim4Density ∧ dim6Density < dim5Density ∧
      dim7Density < dim6Density ∧ dim8Density < dim7Density :=
  ⟨⟨dim4Density_pos, dim4Density_lt_one⟩, ⟨dim5Density_pos, dim5Density_lt_one⟩,
   ⟨dim6Density_pos, dim6Density_lt_one⟩, ⟨dim7Density_pos, dim7Density_lt_one⟩,
   ⟨dim8Density_pos, dim8Density_lt_one⟩,
   dim4_gt_dim5, dim5_gt_dim6, dim6_gt_dim7, dim7_gt_dim8⟩

end KeplerConjectureOQ01
