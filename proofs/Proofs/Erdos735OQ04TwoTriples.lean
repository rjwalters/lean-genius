/-
  Erdős Problem #735, Open Question #04 (oq-04) — S8:
  Machine-checked refutation of the pre-S8 classification statement.

  Parent: `Proofs.Erdos735OQ04` (k-flat magic configurations in ℝ^d).

  ## Why this file exists

  The S5 ACT (2026-06-10) axiomatised the conjectured higher-dimensional
  extension of ABKPR 2008 with a class-4 predicate `IsIncenterConfigD` that
  was an admitted "structural skeleton": an injective `Fin (d + 2)`-family
  inside `P` plus a designated point, with `P.card = d + 3` — and NO
  affine-independence or metric condition.  That skeleton is
  **cardinality-trivial**: it holds for EVERY configuration of exactly
  `d + 3` points (`isIncenterSkeletonD_of_card` below).  So the pre-S8 axiom
  asserted, among other things, that every 6-point configuration in ℝ³ is
  1-flat magic.

  This file refutes that assertion.  The configuration

      a₁ = (0,0,0),  a₂ = (1,0,0),  a₃ = (2,0,0)      (triple on the x-axis)
      b₁ = (0,1,0),  b₂ = (1,1,0),  b₃ = (2,1,0)      (parallel triple at y = 1)

  — two parallel 3-point lines — is NOT 1-flat magic
  (`twoTriples_not_oneFlatMagic`), whence the pre-S8 classification statement
  is provably false (`skeleton_classification_false`).  The repaired class 4
  (`IsFailedFanoD`, the failed Fano configuration ABKPR 2008 actually proves)
  lives in `Proofs.Erdos735OQ04`; this file documents, as a theorem, why the
  repair was mandatory.

  ## Proof architecture (7-line linear-arithmetic route)

  If `w` were a magic weighting with constant `c > 0`, writing `αᵢ` for the
  weight of `aᵢ` and `βⱼ` for the weight of `bⱼ`, the seven configuration
  lines

      A   = {a₁,a₂,a₃}   (y = 0, z = 0):   α₁ + α₂ + α₃ = c
      B   = {b₁,b₂,b₃}   (y = 1, z = 0):   β₁ + β₂ + β₃ = c
      C₁₁ = {a₁,b₁}      (x = 0, z = 0):   α₁ + β₁ = c
      C₁₂ = {a₁,b₂}      (x − y = 0, z = 0):  α₁ + β₂ = c
      C₁₃ = {a₁,b₃}      (x − 2y = 0, z = 0): α₁ + β₃ = c
      C₂₁ = {a₂,b₁}      (x + y = 1, z = 0):  α₂ + β₁ = c
      C₃₁ = {a₃,b₁}      (x + 2y = 2, z = 0): α₃ + β₁ = c

  combine as (C₁₁+C₁₂+C₁₃ − B) and (C₁₁+C₂₁+C₃₁ − A) to give
  3α₁ = 2c and 3β₁ = 2c, whence C₁₁ reads 4c/3 = c, i.e. c = 0 —
  contradicting `c > 0`.  (Positivity of the individual weights is not even
  needed.)  `linarith` closes it.

  Each line is built as `AffineSubspace.mk'` over the kernel of a PAIR of
  linear functionals (`LinearMap.prod`), so every point membership is a
  two-equation coordinate check and the direction rank is 1 by rank-nullity —
  the k = 1 analogue of the S6b kernel-functional machinery.

  Counts: 0 axioms, 0 sorries.
-/

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Proofs.Erdos735OQ04

namespace Erdos735OQ04TwoTriples

open Erdos735OQ04
open scoped Classical

/- ## The pre-S8 class-4 predicate, restated verbatim -/

/-- The pre-S8 class-4 predicate `IsIncenterConfigD` (S5 ACT, 2026-06-10),
    restated verbatim under its honest name: an injective `(d+2)`-family
    inside `P`, one designated "incenter" point of `P`, and `P.card = d + 3`.
    No affine-independence or metric condition constrains any of the points,
    which is exactly the defect: see `isIncenterSkeletonD_of_card`. -/
def IsIncenterSkeletonD {d : ℕ} (P : PointConfigD d) : Prop :=
  ∃ simplex : Fin (d + 2) → EuclideanSpace ℝ (Fin d),
    ∃ incenter : EuclideanSpace ℝ (Fin d),
    (∀ i, simplex i ∈ P) ∧ incenter ∈ P ∧
    Function.Injective simplex ∧
    P.card = d + 2 + 1

/-- **The skeleton is cardinality-trivial**: every configuration of exactly
    `d + 3` points satisfies it — pick any `d + 2` distinct points as the
    "simplex" and any point as the "incenter". -/
theorem isIncenterSkeletonD_of_card {d : ℕ} {P : PointConfigD d}
    (h : P.card = d + 3) : IsIncenterSkeletonD P := by
  obtain ⟨S, hSP, hScard⟩ := Finset.exists_subset_card_eq
    (show d + 2 ≤ P.card by omega)
  obtain ⟨q, hq⟩ := Finset.card_pos.mp (show 0 < P.card by omega)
  refine ⟨fun i => ((S.equivFinOfCardEq hScard).symm i : EuclideanSpace ℝ (Fin d)),
    q, fun i => hSP ((S.equivFinOfCardEq hScard).symm i).2, hq, ?_, by omega⟩
  intro i j hij
  exact (S.equivFinOfCardEq hScard).symm.injective (Subtype.coe_injective hij)

/- ## The two-parallel-triples configuration -/

/-- Triple-A point `(0, 0, 0)`. -/
noncomputable def a₁ : EuclideanSpace ℝ (Fin 3) := !₂[0, 0, 0]
/-- Triple-A point `(1, 0, 0)`. -/
noncomputable def a₂ : EuclideanSpace ℝ (Fin 3) := !₂[1, 0, 0]
/-- Triple-A point `(2, 0, 0)`. -/
noncomputable def a₃ : EuclideanSpace ℝ (Fin 3) := !₂[2, 0, 0]
/-- Triple-B point `(0, 1, 0)`. -/
noncomputable def b₁ : EuclideanSpace ℝ (Fin 3) := !₂[0, 1, 0]
/-- Triple-B point `(1, 1, 0)`. -/
noncomputable def b₂ : EuclideanSpace ℝ (Fin 3) := !₂[1, 1, 0]
/-- Triple-B point `(2, 1, 0)`. -/
noncomputable def b₃ : EuclideanSpace ℝ (Fin 3) := !₂[2, 1, 0]

/-- Two parallel 3-point lines in the plane `z = 0` of ℝ³: 6 points. -/
noncomputable def twoTriplesConfig : PointConfigD 3 := {a₁, a₂, a₃, b₁, b₂, b₃}

/-- The vertical unit vector `(0, 0, 1)` (surjectivity witness for the
    rank computations; not a configuration point). -/
noncomputable def eZ : EuclideanSpace ℝ (Fin 3) := !₂[0, 0, 1]

/-- Two points of ℝ³ differing in some coordinate are distinct. -/
lemma ne_of_coord {x y : EuclideanSpace ℝ (Fin 3)} (j : Fin 3)
    (h : WithLp.ofLp x j ≠ WithLp.ofLp y j) : x ≠ y :=
  fun he => h (by rw [he])

/- Pairwise distinctness: the a's (and the b's) differ in coordinate 0;
   every aᵢ differs from every bⱼ in coordinate 1 (y = 0 vs y = 1). -/

lemma a12 : a₁ ≠ a₂ := ne_of_coord 0 (by norm_num [a₁, a₂, WithLp.ofLp_toLp])
lemma a13 : a₁ ≠ a₃ := ne_of_coord 0 (by norm_num [a₁, a₃, WithLp.ofLp_toLp])
lemma a23 : a₂ ≠ a₃ := ne_of_coord 0 (by norm_num [a₂, a₃, WithLp.ofLp_toLp])
lemma b12 : b₁ ≠ b₂ := ne_of_coord 0 (by norm_num [b₁, b₂, WithLp.ofLp_toLp])
lemma b13 : b₁ ≠ b₃ := ne_of_coord 0 (by norm_num [b₁, b₃, WithLp.ofLp_toLp])
lemma b23 : b₂ ≠ b₃ := ne_of_coord 0 (by norm_num [b₂, b₃, WithLp.ofLp_toLp])
lemma a1b1 : a₁ ≠ b₁ := ne_of_coord 1 (by norm_num [a₁, b₁, WithLp.ofLp_toLp])
lemma a1b2 : a₁ ≠ b₂ := ne_of_coord 1 (by norm_num [a₁, b₂, WithLp.ofLp_toLp])
lemma a1b3 : a₁ ≠ b₃ := ne_of_coord 1 (by norm_num [a₁, b₃, WithLp.ofLp_toLp])
lemma a2b1 : a₂ ≠ b₁ := ne_of_coord 1 (by norm_num [a₂, b₁, WithLp.ofLp_toLp])
lemma a2b2 : a₂ ≠ b₂ := ne_of_coord 1 (by norm_num [a₂, b₂, WithLp.ofLp_toLp])
lemma a2b3 : a₂ ≠ b₃ := ne_of_coord 1 (by norm_num [a₂, b₃, WithLp.ofLp_toLp])
lemma a3b1 : a₃ ≠ b₁ := ne_of_coord 1 (by norm_num [a₃, b₁, WithLp.ofLp_toLp])
lemma a3b2 : a₃ ≠ b₂ := ne_of_coord 1 (by norm_num [a₃, b₂, WithLp.ofLp_toLp])
lemma a3b3 : a₃ ≠ b₃ := ne_of_coord 1 (by norm_num [a₃, b₃, WithLp.ofLp_toLp])

/-- The configuration has exactly 6 = 3 + 3 points. -/
theorem twoTriplesConfig_card : twoTriplesConfig.card = 6 := by
  rw [twoTriplesConfig,
    Finset.card_insert_of_notMem (by simp [a12, a13, a1b1, a1b2, a1b3]),
    Finset.card_insert_of_notMem (by simp [a23, a2b1, a2b2, a2b3]),
    Finset.card_insert_of_notMem (by simp [a3b1, a3b2, a3b3]),
    Finset.card_insert_of_notMem (by simp [b12, b13]),
    Finset.card_insert_of_notMem (by simp [b23]),
    Finset.card_singleton]

/- ## Configuration lines as kernels of functional pairs -/

/-- Coordinate functional `x ↦ xⱼ` on ℝ³ (bundled linear map). -/
noncomputable def coordL (j : Fin 3) : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ :=
  EuclideanSpace.projₗ j

lemma coordL_apply (j : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) :
    coordL j x = WithLp.ofLp x j := rfl

/-- Membership in an affine subspace `mk' p (ker (g₁.prod g₂))` is the pair of
    linear equations `g₁ x = g₁ p ∧ g₂ x = g₂ p` — the two-functional (rank-1)
    analogue of the S6b `mem_mk'_ker_iff`. -/
lemma mem_mk'_ker_prod_iff (g₁ g₂ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)
    (p x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ AffineSubspace.mk' p (LinearMap.ker (g₁.prod g₂)) ↔
      g₁ x = g₁ p ∧ g₂ x = g₂ p := by
  rw [AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub, LinearMap.prod_apply]
  simp only [Pi.prod, Prod.mk_eq_zero, map_sub, sub_eq_zero]

/-- Rank-nullity: the kernel of an independent pair of functionals on ℝ³ is a
    rank-1 subspace.  Independence is certified by two explicit witnesses `u`,
    `v` on which the pair evaluates to `(1,0)` and `(0,1)`. -/
lemma rank_ker_prod_one (g₁ g₂ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)
    (u v : EuclideanSpace ℝ (Fin 3))
    (h1u : g₁ u = 1) (h2u : g₂ u = 0) (h1v : g₁ v = 0) (h2v : g₂ v = 1) :
    Module.rank ℝ (LinearMap.ker (g₁.prod g₂)) = ((1 : ℕ) : Cardinal) := by
  have hsurj : Function.Surjective (g₁.prod g₂) := by
    rintro ⟨s, t⟩
    exact ⟨s • u + t • v, by
      simp [LinearMap.prod_apply, map_add, map_smul, smul_eq_mul,
        h1u, h2u, h1v, h2v]⟩
  have hrange : LinearMap.range (g₁.prod g₂) = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have h := (g₁.prod g₂).finrank_range_add_finrank_ker
  rw [hrange, finrank_top, finrank_euclideanSpace_fin] at h
  have hprod : Module.finrank ℝ (ℝ × ℝ) = 2 := by
    simp [Module.finrank_prod]
  rw [hprod] at h
  have hk : Module.finrank ℝ (LinearMap.ker (g₁.prod g₂)) = 1 := by omega
  rw [← Module.finrank_eq_rank, hk]

/- The six functional pairs.  All seven configuration lines lie in the plane
   `z = 0`, so the second functional is always `coordL 2`; the first cuts the
   line inside that plane.  Lines A and B are parallel and share a kernel. -/

/-- `y`-functional (lines A and B). -/
noncomputable def gY : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ := coordL 1
/-- `x`-functional (line C₁₁). -/
noncomputable def gX : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ := coordL 0
/-- `x − y` functional (line C₁₂). -/
noncomputable def gXmY : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ := coordL 0 - coordL 1
/-- `x − 2y` functional (line C₁₃). -/
noncomputable def gXm2Y : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ :=
  coordL 0 - (2 : ℝ) • coordL 1
/-- `x + y` functional (line C₂₁). -/
noncomputable def gXpY : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ := coordL 0 + coordL 1
/-- `x + 2y` functional (line C₃₁). -/
noncomputable def gXp2Y : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ :=
  coordL 0 + (2 : ℝ) • coordL 1

/-- Line A: the x-axis `{y = 0, z = 0}`, through `a₁, a₂, a₃`. -/
noncomputable def lineA : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' a₁ (LinearMap.ker (gY.prod (coordL 2)))

/-- Line B: the parallel `{y = 1, z = 0}`, through `b₁, b₂, b₃`. -/
noncomputable def lineB : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' b₁ (LinearMap.ker (gY.prod (coordL 2)))

/-- Cross line C₁₁ `{x = 0, z = 0}`, through `a₁, b₁`. -/
noncomputable def lineC11 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' a₁ (LinearMap.ker (gX.prod (coordL 2)))

/-- Cross line C₁₂ `{x − y = 0, z = 0}`, through `a₁, b₂`. -/
noncomputable def lineC12 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' a₁ (LinearMap.ker (gXmY.prod (coordL 2)))

/-- Cross line C₁₃ `{x − 2y = 0, z = 0}`, through `a₁, b₃`. -/
noncomputable def lineC13 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' a₁ (LinearMap.ker (gXm2Y.prod (coordL 2)))

/-- Cross line C₂₁ `{x + y = 1, z = 0}`, through `a₂, b₁`. -/
noncomputable def lineC21 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' a₂ (LinearMap.ker (gXpY.prod (coordL 2)))

/-- Cross line C₃₁ `{x + 2y = 2, z = 0}`, through `a₃, b₁`. -/
noncomputable def lineC31 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' a₃ (LinearMap.ker (gXp2Y.prod (coordL 2)))

/- ## Membership characterisations -/

lemma mem_lineA_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ lineA ↔ WithLp.ofLp x 1 = 0 ∧ WithLp.ofLp x 2 = 0 := by
  rw [lineA, mem_mk'_ker_prod_iff]
  simp [gY, coordL_apply, a₁, WithLp.ofLp_toLp,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

lemma mem_lineB_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ lineB ↔ WithLp.ofLp x 1 = 1 ∧ WithLp.ofLp x 2 = 0 := by
  rw [lineB, mem_mk'_ker_prod_iff]
  simp [gY, coordL_apply, b₁, WithLp.ofLp_toLp,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

lemma mem_lineC11_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ lineC11 ↔ WithLp.ofLp x 0 = 0 ∧ WithLp.ofLp x 2 = 0 := by
  rw [lineC11, mem_mk'_ker_prod_iff]
  simp [gX, coordL_apply, a₁, WithLp.ofLp_toLp,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

lemma mem_lineC12_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ lineC12 ↔ WithLp.ofLp x 0 - WithLp.ofLp x 1 = 0 ∧ WithLp.ofLp x 2 = 0 := by
  rw [lineC12, mem_mk'_ker_prod_iff]
  simp [gXmY, LinearMap.sub_apply, coordL_apply, a₁, WithLp.ofLp_toLp,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

lemma mem_lineC13_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ lineC13 ↔
      WithLp.ofLp x 0 - 2 * WithLp.ofLp x 1 = 0 ∧ WithLp.ofLp x 2 = 0 := by
  rw [lineC13, mem_mk'_ker_prod_iff]
  simp [gXm2Y, LinearMap.sub_apply, LinearMap.smul_apply, coordL_apply, a₁,
    WithLp.ofLp_toLp, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

lemma mem_lineC21_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ lineC21 ↔
      WithLp.ofLp x 0 + WithLp.ofLp x 1 = 1 ∧ WithLp.ofLp x 2 = 0 := by
  rw [lineC21, mem_mk'_ker_prod_iff]
  simp [gXpY, LinearMap.add_apply, coordL_apply, a₂, WithLp.ofLp_toLp,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

lemma mem_lineC31_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ lineC31 ↔
      WithLp.ofLp x 0 + 2 * WithLp.ofLp x 1 = 2 ∧ WithLp.ofLp x 2 = 0 := by
  rw [lineC31, mem_mk'_ker_prod_iff]
  simp [gXp2Y, LinearMap.add_apply, LinearMap.smul_apply, coordL_apply, a₃,
    WithLp.ofLp_toLp, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

/- ## Direction ranks (all 1, by rank-nullity) -/

/-- Coordinate facts for the surjectivity witnesses: `a₂ = (1,0,0)`,
    `b₁ = (0,1,0)`, `eZ = (0,0,1)` evaluate under the six functionals by
    `norm_num` on the literal coordinates. -/
lemma rank_ker_Y : Module.rank ℝ (LinearMap.ker (gY.prod (coordL 2))) =
    ((1 : ℕ) : Cardinal) :=
  rank_ker_prod_one _ _ b₁ eZ
    (by simp [gY, coordL_apply, b₁, WithLp.ofLp_toLp])
    (by simp [coordL_apply, b₁, WithLp.ofLp_toLp,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
    (by simp [gY, coordL_apply, eZ, WithLp.ofLp_toLp])
    (by simp [coordL_apply, eZ, WithLp.ofLp_toLp,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])

lemma rank_ker_X : Module.rank ℝ (LinearMap.ker (gX.prod (coordL 2))) =
    ((1 : ℕ) : Cardinal) :=
  rank_ker_prod_one _ _ a₂ eZ
    (by simp [gX, coordL_apply, a₂, WithLp.ofLp_toLp])
    (by simp [coordL_apply, a₂, WithLp.ofLp_toLp,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
    (by simp [gX, coordL_apply, eZ, WithLp.ofLp_toLp])
    (by simp [coordL_apply, eZ, WithLp.ofLp_toLp,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])

lemma rank_ker_XmY : Module.rank ℝ (LinearMap.ker (gXmY.prod (coordL 2))) =
    ((1 : ℕ) : Cardinal) :=
  rank_ker_prod_one _ _ a₂ eZ
    (by simp [gXmY, LinearMap.sub_apply, coordL_apply, a₂, WithLp.ofLp_toLp])
    (by simp [coordL_apply, a₂, WithLp.ofLp_toLp,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
    (by simp [gXmY, LinearMap.sub_apply, coordL_apply, eZ, WithLp.ofLp_toLp])
    (by simp [coordL_apply, eZ, WithLp.ofLp_toLp,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])

lemma rank_ker_Xm2Y : Module.rank ℝ (LinearMap.ker (gXm2Y.prod (coordL 2))) =
    ((1 : ℕ) : Cardinal) :=
  rank_ker_prod_one _ _ a₂ eZ
    (by simp [gXm2Y, LinearMap.sub_apply, LinearMap.smul_apply, coordL_apply,
      a₂, WithLp.ofLp_toLp, smul_eq_mul])
    (by simp [coordL_apply, a₂, WithLp.ofLp_toLp,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
    (by simp [gXm2Y, LinearMap.sub_apply, LinearMap.smul_apply, coordL_apply,
      eZ, WithLp.ofLp_toLp, smul_eq_mul])
    (by simp [coordL_apply, eZ, WithLp.ofLp_toLp,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])

lemma rank_ker_XpY : Module.rank ℝ (LinearMap.ker (gXpY.prod (coordL 2))) =
    ((1 : ℕ) : Cardinal) :=
  rank_ker_prod_one _ _ a₂ eZ
    (by simp [gXpY, LinearMap.add_apply, coordL_apply, a₂, WithLp.ofLp_toLp])
    (by simp [coordL_apply, a₂, WithLp.ofLp_toLp,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
    (by simp [gXpY, LinearMap.add_apply, coordL_apply, eZ, WithLp.ofLp_toLp])
    (by simp [coordL_apply, eZ, WithLp.ofLp_toLp,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])

lemma rank_ker_Xp2Y : Module.rank ℝ (LinearMap.ker (gXp2Y.prod (coordL 2))) =
    ((1 : ℕ) : Cardinal) :=
  rank_ker_prod_one _ _ a₂ eZ
    (by simp [gXp2Y, LinearMap.add_apply, LinearMap.smul_apply, coordL_apply,
      a₂, WithLp.ofLp_toLp, smul_eq_mul])
    (by simp [coordL_apply, a₂, WithLp.ofLp_toLp,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
    (by simp [gXp2Y, LinearMap.add_apply, LinearMap.smul_apply, coordL_apply,
      eZ, WithLp.ofLp_toLp, smul_eq_mul])
    (by simp [coordL_apply, eZ, WithLp.ofLp_toLp,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])

lemma rank_lineA : Module.rank ℝ lineA.direction = ((1 : ℕ) : Cardinal) := by
  rw [lineA, AffineSubspace.direction_mk']; exact rank_ker_Y
lemma rank_lineB : Module.rank ℝ lineB.direction = ((1 : ℕ) : Cardinal) := by
  rw [lineB, AffineSubspace.direction_mk']; exact rank_ker_Y
lemma rank_lineC11 : Module.rank ℝ lineC11.direction = ((1 : ℕ) : Cardinal) := by
  rw [lineC11, AffineSubspace.direction_mk']; exact rank_ker_X
lemma rank_lineC12 : Module.rank ℝ lineC12.direction = ((1 : ℕ) : Cardinal) := by
  rw [lineC12, AffineSubspace.direction_mk']; exact rank_ker_XmY
lemma rank_lineC13 : Module.rank ℝ lineC13.direction = ((1 : ℕ) : Cardinal) := by
  rw [lineC13, AffineSubspace.direction_mk']; exact rank_ker_Xm2Y
lemma rank_lineC21 : Module.rank ℝ lineC21.direction = ((1 : ℕ) : Cardinal) := by
  rw [lineC21, AffineSubspace.direction_mk']; exact rank_ker_XpY
lemma rank_lineC31 : Module.rank ℝ lineC31.direction = ((1 : ℕ) : Cardinal) := by
  rw [lineC31, AffineSubspace.direction_mk']; exact rank_ker_Xp2Y

/- ## Point membership decisions (7 lines × 6 points) -/

section MembershipDecisions

/-- Coordinate shorthand for the six points, used by every decision below. -/
lemma coords_a₁ : WithLp.ofLp a₁ 0 = 0 ∧ WithLp.ofLp a₁ 1 = 0 ∧ WithLp.ofLp a₁ 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [a₁, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

lemma coords_a₂ : WithLp.ofLp a₂ 0 = 1 ∧ WithLp.ofLp a₂ 1 = 0 ∧ WithLp.ofLp a₂ 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [a₂, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

lemma coords_a₃ : WithLp.ofLp a₃ 0 = 2 ∧ WithLp.ofLp a₃ 1 = 0 ∧ WithLp.ofLp a₃ 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [a₃, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

lemma coords_b₁ : WithLp.ofLp b₁ 0 = 0 ∧ WithLp.ofLp b₁ 1 = 1 ∧ WithLp.ofLp b₁ 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [b₁, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

lemma coords_b₂ : WithLp.ofLp b₂ 0 = 1 ∧ WithLp.ofLp b₂ 1 = 1 ∧ WithLp.ofLp b₂ 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [b₂, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

lemma coords_b₃ : WithLp.ofLp b₃ 0 = 2 ∧ WithLp.ofLp b₃ 1 = 1 ∧ WithLp.ofLp b₃ 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [b₃, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

-- Line A (y = 0, z = 0): contains a₁, a₂, a₃; excludes b₁, b₂, b₃.
lemma hA_a₁ : a₁ ∈ lineA := (mem_lineA_iff a₁).mpr ⟨coords_a₁.2.1, coords_a₁.2.2⟩
lemma hA_a₂ : a₂ ∈ lineA := (mem_lineA_iff a₂).mpr ⟨coords_a₂.2.1, coords_a₂.2.2⟩
lemma hA_a₃ : a₃ ∈ lineA := (mem_lineA_iff a₃).mpr ⟨coords_a₃.2.1, coords_a₃.2.2⟩
lemma hA_b₁ : b₁ ∉ lineA := by
  rw [mem_lineA_iff, coords_b₁.2.1]; norm_num
lemma hA_b₂ : b₂ ∉ lineA := by
  rw [mem_lineA_iff, coords_b₂.2.1]; norm_num
lemma hA_b₃ : b₃ ∉ lineA := by
  rw [mem_lineA_iff, coords_b₃.2.1]; norm_num

-- Line B (y = 1, z = 0): contains b₁, b₂, b₃; excludes a₁, a₂, a₃.
lemma hB_a₁ : a₁ ∉ lineB := by
  rw [mem_lineB_iff, coords_a₁.2.1]; norm_num
lemma hB_a₂ : a₂ ∉ lineB := by
  rw [mem_lineB_iff, coords_a₂.2.1]; norm_num
lemma hB_a₃ : a₃ ∉ lineB := by
  rw [mem_lineB_iff, coords_a₃.2.1]; norm_num
lemma hB_b₁ : b₁ ∈ lineB := (mem_lineB_iff b₁).mpr ⟨coords_b₁.2.1, coords_b₁.2.2⟩
lemma hB_b₂ : b₂ ∈ lineB := (mem_lineB_iff b₂).mpr ⟨coords_b₂.2.1, coords_b₂.2.2⟩
lemma hB_b₃ : b₃ ∈ lineB := (mem_lineB_iff b₃).mpr ⟨coords_b₃.2.1, coords_b₃.2.2⟩

-- Cross line C₁₁ (x = 0, z = 0): contains a₁, b₁ only.
lemma hC11_a₁ : a₁ ∈ lineC11 := (mem_lineC11_iff a₁).mpr ⟨coords_a₁.1, coords_a₁.2.2⟩
lemma hC11_a₂ : a₂ ∉ lineC11 := by
  rw [mem_lineC11_iff, coords_a₂.1]; norm_num
lemma hC11_a₃ : a₃ ∉ lineC11 := by
  rw [mem_lineC11_iff, coords_a₃.1]; norm_num
lemma hC11_b₁ : b₁ ∈ lineC11 := (mem_lineC11_iff b₁).mpr ⟨coords_b₁.1, coords_b₁.2.2⟩
lemma hC11_b₂ : b₂ ∉ lineC11 := by
  rw [mem_lineC11_iff, coords_b₂.1]; norm_num
lemma hC11_b₃ : b₃ ∉ lineC11 := by
  rw [mem_lineC11_iff, coords_b₃.1]; norm_num

-- Cross line C₁₂ (x − y = 0, z = 0): contains a₁, b₂ only.
lemma hC12_a₁ : a₁ ∈ lineC12 := by
  rw [mem_lineC12_iff, coords_a₁.1, coords_a₁.2.1, coords_a₁.2.2]; norm_num
lemma hC12_a₂ : a₂ ∉ lineC12 := by
  rw [mem_lineC12_iff, coords_a₂.1, coords_a₂.2.1]; norm_num
lemma hC12_a₃ : a₃ ∉ lineC12 := by
  rw [mem_lineC12_iff, coords_a₃.1, coords_a₃.2.1]; norm_num
lemma hC12_b₁ : b₁ ∉ lineC12 := by
  rw [mem_lineC12_iff, coords_b₁.1, coords_b₁.2.1]; norm_num
lemma hC12_b₂ : b₂ ∈ lineC12 := by
  rw [mem_lineC12_iff, coords_b₂.1, coords_b₂.2.1, coords_b₂.2.2]; norm_num
lemma hC12_b₃ : b₃ ∉ lineC12 := by
  rw [mem_lineC12_iff, coords_b₃.1, coords_b₃.2.1]; norm_num

-- Cross line C₁₃ (x − 2y = 0, z = 0): contains a₁, b₃ only.
lemma hC13_a₁ : a₁ ∈ lineC13 := by
  rw [mem_lineC13_iff, coords_a₁.1, coords_a₁.2.1, coords_a₁.2.2]; norm_num
lemma hC13_a₂ : a₂ ∉ lineC13 := by
  rw [mem_lineC13_iff, coords_a₂.1, coords_a₂.2.1]; norm_num
lemma hC13_a₃ : a₃ ∉ lineC13 := by
  rw [mem_lineC13_iff, coords_a₃.1, coords_a₃.2.1]; norm_num
lemma hC13_b₁ : b₁ ∉ lineC13 := by
  rw [mem_lineC13_iff, coords_b₁.1, coords_b₁.2.1]; norm_num
lemma hC13_b₂ : b₂ ∉ lineC13 := by
  rw [mem_lineC13_iff, coords_b₂.1, coords_b₂.2.1]; norm_num
lemma hC13_b₃ : b₃ ∈ lineC13 := by
  rw [mem_lineC13_iff, coords_b₃.1, coords_b₃.2.1, coords_b₃.2.2]; norm_num

-- Cross line C₂₁ (x + y = 1, z = 0): contains a₂, b₁ only.
lemma hC21_a₁ : a₁ ∉ lineC21 := by
  rw [mem_lineC21_iff, coords_a₁.1, coords_a₁.2.1]; norm_num
lemma hC21_a₂ : a₂ ∈ lineC21 := by
  rw [mem_lineC21_iff, coords_a₂.1, coords_a₂.2.1, coords_a₂.2.2]; norm_num
lemma hC21_a₃ : a₃ ∉ lineC21 := by
  rw [mem_lineC21_iff, coords_a₃.1, coords_a₃.2.1]; norm_num
lemma hC21_b₁ : b₁ ∈ lineC21 := by
  rw [mem_lineC21_iff, coords_b₁.1, coords_b₁.2.1, coords_b₁.2.2]; norm_num
lemma hC21_b₂ : b₂ ∉ lineC21 := by
  rw [mem_lineC21_iff, coords_b₂.1, coords_b₂.2.1]; norm_num
lemma hC21_b₃ : b₃ ∉ lineC21 := by
  rw [mem_lineC21_iff, coords_b₃.1, coords_b₃.2.1]; norm_num

-- Cross line C₃₁ (x + 2y = 2, z = 0): contains a₃, b₁ only.
lemma hC31_a₁ : a₁ ∉ lineC31 := by
  rw [mem_lineC31_iff, coords_a₁.1, coords_a₁.2.1]; norm_num
lemma hC31_a₂ : a₂ ∉ lineC31 := by
  rw [mem_lineC31_iff, coords_a₂.1, coords_a₂.2.1]; norm_num
lemma hC31_a₃ : a₃ ∈ lineC31 := by
  rw [mem_lineC31_iff, coords_a₃.1, coords_a₃.2.1, coords_a₃.2.2]; norm_num
lemma hC31_b₁ : b₁ ∈ lineC31 := by
  rw [mem_lineC31_iff, coords_b₁.1, coords_b₁.2.1, coords_b₁.2.2]; norm_num
lemma hC31_b₂ : b₂ ∉ lineC31 := by
  rw [mem_lineC31_iff, coords_b₂.1, coords_b₂.2.1]; norm_num
lemma hC31_b₃ : b₃ ∉ lineC31 := by
  rw [mem_lineC31_iff, coords_b₃.1, coords_b₃.2.1]; norm_num

end MembershipDecisions

/- ## Filtered point sets of the seven lines -/

lemma filter_lineA : twoTriplesConfig.filter (· ∈ lineA) = {a₁, a₂, a₃} := by
  rw [twoTriplesConfig]
  rw [Finset.filter_insert, if_pos hA_a₁, Finset.filter_insert, if_pos hA_a₂,
    Finset.filter_insert, if_pos hA_a₃, Finset.filter_insert, if_neg hA_b₁,
    Finset.filter_insert, if_neg hA_b₂, Finset.filter_singleton, if_neg hA_b₃]

lemma filter_lineB : twoTriplesConfig.filter (· ∈ lineB) = {b₁, b₂, b₃} := by
  rw [twoTriplesConfig]
  rw [Finset.filter_insert, if_neg hB_a₁, Finset.filter_insert, if_neg hB_a₂,
    Finset.filter_insert, if_neg hB_a₃, Finset.filter_insert, if_pos hB_b₁,
    Finset.filter_insert, if_pos hB_b₂, Finset.filter_singleton, if_pos hB_b₃]

lemma filter_lineC11 : twoTriplesConfig.filter (· ∈ lineC11) = {a₁, b₁} := by
  rw [twoTriplesConfig]
  rw [Finset.filter_insert, if_pos hC11_a₁, Finset.filter_insert, if_neg hC11_a₂,
    Finset.filter_insert, if_neg hC11_a₃, Finset.filter_insert, if_pos hC11_b₁,
    Finset.filter_insert, if_neg hC11_b₂, Finset.filter_singleton, if_neg hC11_b₃]
  rfl

lemma filter_lineC12 : twoTriplesConfig.filter (· ∈ lineC12) = {a₁, b₂} := by
  rw [twoTriplesConfig]
  rw [Finset.filter_insert, if_pos hC12_a₁, Finset.filter_insert, if_neg hC12_a₂,
    Finset.filter_insert, if_neg hC12_a₃, Finset.filter_insert, if_neg hC12_b₁,
    Finset.filter_insert, if_pos hC12_b₂, Finset.filter_singleton, if_neg hC12_b₃]
  rfl

lemma filter_lineC13 : twoTriplesConfig.filter (· ∈ lineC13) = {a₁, b₃} := by
  rw [twoTriplesConfig]
  rw [Finset.filter_insert, if_pos hC13_a₁, Finset.filter_insert, if_neg hC13_a₂,
    Finset.filter_insert, if_neg hC13_a₃, Finset.filter_insert, if_neg hC13_b₁,
    Finset.filter_insert, if_neg hC13_b₂, Finset.filter_singleton, if_pos hC13_b₃]
  rfl

lemma filter_lineC21 : twoTriplesConfig.filter (· ∈ lineC21) = {a₂, b₁} := by
  rw [twoTriplesConfig]
  rw [Finset.filter_insert, if_neg hC21_a₁, Finset.filter_insert, if_pos hC21_a₂,
    Finset.filter_insert, if_neg hC21_a₃, Finset.filter_insert, if_pos hC21_b₁,
    Finset.filter_insert, if_neg hC21_b₂, Finset.filter_singleton, if_neg hC21_b₃]
  rfl

lemma filter_lineC31 : twoTriplesConfig.filter (· ∈ lineC31) = {a₃, b₁} := by
  rw [twoTriplesConfig]
  rw [Finset.filter_insert, if_neg hC31_a₁, Finset.filter_insert, if_neg hC31_a₂,
    Finset.filter_insert, if_pos hC31_a₃, Finset.filter_insert, if_pos hC31_b₁,
    Finset.filter_insert, if_neg hC31_b₂, Finset.filter_singleton, if_neg hC31_b₃]
  rfl

/- Non-membership facts for insert-chain card/sum computations. -/

lemma nA1 : a₁ ∉ ({a₂, a₃} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [a12, a13]
lemma nA2 : a₂ ∉ ({a₃} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [a23]
lemma nB1 : b₁ ∉ ({b₂, b₃} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [b12, b13]
lemma nB2 : b₂ ∉ ({b₃} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [b23]
lemma n11 : a₁ ∉ ({b₁} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [a1b1]
lemma n12 : a₁ ∉ ({b₂} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [a1b2]
lemma n13 : a₁ ∉ ({b₃} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [a1b3]
lemma n21 : a₂ ∉ ({b₁} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [a2b1]
lemma n31 : a₃ ∉ ({b₁} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [a3b1]

/- ## The seven lines as `ConfigKFlat 1 twoTriplesConfig` elements -/

lemma card_lineA : (twoTriplesConfig.filter (· ∈ lineA)).card ≥ 1 + 1 := by
  rw [filter_lineA, Finset.card_insert_of_notMem nA1,
    Finset.card_insert_of_notMem nA2, Finset.card_singleton]
  omega

lemma card_lineB : (twoTriplesConfig.filter (· ∈ lineB)).card ≥ 1 + 1 := by
  rw [filter_lineB, Finset.card_insert_of_notMem nB1,
    Finset.card_insert_of_notMem nB2, Finset.card_singleton]
  omega

lemma card_lineC11 : (twoTriplesConfig.filter (· ∈ lineC11)).card ≥ 1 + 1 := by
  rw [filter_lineC11, Finset.card_insert_of_notMem n11, Finset.card_singleton]

lemma card_lineC12 : (twoTriplesConfig.filter (· ∈ lineC12)).card ≥ 1 + 1 := by
  rw [filter_lineC12, Finset.card_insert_of_notMem n12, Finset.card_singleton]

lemma card_lineC13 : (twoTriplesConfig.filter (· ∈ lineC13)).card ≥ 1 + 1 := by
  rw [filter_lineC13, Finset.card_insert_of_notMem n13, Finset.card_singleton]

lemma card_lineC21 : (twoTriplesConfig.filter (· ∈ lineC21)).card ≥ 1 + 1 := by
  rw [filter_lineC21, Finset.card_insert_of_notMem n21, Finset.card_singleton]

lemma card_lineC31 : (twoTriplesConfig.filter (· ∈ lineC31)).card ≥ 1 + 1 := by
  rw [filter_lineC31, Finset.card_insert_of_notMem n31, Finset.card_singleton]

/- ## Main theorems -/

/-- **Two parallel 3-point triples are NOT 1-flat magic.**  The seven
    configuration lines force the magic constant to 0, contradicting `c > 0`.
    (Positivity of the individual weights is not needed.) -/
theorem twoTriples_not_oneFlatMagic : ¬ IsKFlatMagic 1 twoTriplesConfig := by
  rintro ⟨w, c, hc, hmagic⟩
  -- canonical membership proofs (fixed once, so weight atoms are shared)
  have hpa₁ : a₁ ∈ twoTriplesConfig := by simp [twoTriplesConfig]
  have hpa₂ : a₂ ∈ twoTriplesConfig := by simp [twoTriplesConfig]
  have hpa₃ : a₃ ∈ twoTriplesConfig := by simp [twoTriplesConfig]
  have hpb₁ : b₁ ∈ twoTriplesConfig := by simp [twoTriplesConfig]
  have hpb₂ : b₂ ∈ twoTriplesConfig := by simp [twoTriplesConfig]
  have hpb₃ : b₃ ∈ twoTriplesConfig := by simp [twoTriplesConfig]
  -- the seven line-sum equations
  have eA := hmagic ⟨lineA, rank_lineA, card_lineA⟩
  have eB := hmagic ⟨lineB, rank_lineB, card_lineB⟩
  have e11 := hmagic ⟨lineC11, rank_lineC11, card_lineC11⟩
  have e12 := hmagic ⟨lineC12, rank_lineC12, card_lineC12⟩
  have e13 := hmagic ⟨lineC13, rank_lineC13, card_lineC13⟩
  have e21 := hmagic ⟨lineC21, rank_lineC21, card_lineC21⟩
  have e31 := hmagic ⟨lineC31, rank_lineC31, card_lineC31⟩
  simp only [kFlatSum] at eA eB e11 e12 e13 e21 e31
  rw [filter_lineA, Finset.sum_insert nA1, Finset.sum_insert nA2,
    Finset.sum_singleton] at eA
  rw [filter_lineB, Finset.sum_insert nB1, Finset.sum_insert nB2,
    Finset.sum_singleton] at eB
  rw [filter_lineC11, Finset.sum_insert n11, Finset.sum_singleton] at e11
  rw [filter_lineC12, Finset.sum_insert n12, Finset.sum_singleton] at e12
  rw [filter_lineC13, Finset.sum_insert n13, Finset.sum_singleton] at e13
  rw [filter_lineC21, Finset.sum_insert n21, Finset.sum_singleton] at e21
  rw [filter_lineC31, Finset.sum_insert n31, Finset.sum_singleton] at e31
  simp only [dif_pos hpa₁, dif_pos hpa₂, dif_pos hpa₃, dif_pos hpb₁,
    dif_pos hpb₂, dif_pos hpb₃] at eA eB e11 e12 e13 e21 e31
  -- (C₁₁+C₁₂+C₁₃ − B) and (C₁₁+C₂₁+C₃₁ − A) give 3α₁ = 3β₁ = 2c;
  -- then C₁₁ reads 4c/3 = c, i.e. c = 0 — contradiction with hc : c > 0
  linarith

/-- **The pre-S8 classification statement is provably false.**  Because the
    skeleton class 4 is cardinality-trivial (`isIncenterSkeletonD_of_card`),
    the pre-repair axiom `oneflat_classification_higher_dim` (S5 ACT form,
    with `IsIncenterConfigD` = `IsIncenterSkeletonD`) asserted that the
    6-point two-triples configuration is 1-flat magic — refuted by
    `twoTriples_not_oneFlatMagic`.  This theorem is the machine-checked
    record of why the S8 repair (class 4 ↦ `IsFailedFanoD`) was mandatory:
    the environment containing the pre-S8 axiom was inconsistent. -/
theorem skeleton_classification_false :
    ¬ (∀ (d : ℕ), 3 ≤ d → ∀ P : PointConfigD d,
        IsKFlatMagic 1 P ↔
          IsCollinearD P ∨ IsGeneralPositionD P ∨ IsNearPencilD P ∨
            IsIncenterSkeletonD P) := by
  intro h
  exact twoTriples_not_oneFlatMagic
    ((h 3 le_rfl twoTriplesConfig).mpr
      (Or.inr (Or.inr (Or.inr (isIncenterSkeletonD_of_card
        (by rw [twoTriplesConfig_card]))))))

end Erdos735OQ04TwoTriples
