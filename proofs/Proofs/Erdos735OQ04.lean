/-
  Erdős Problem #735, Open Question #04 (oq-04):
  k-flat magic configurations in ℝ^d

  Parent: `Proofs.Erdos735Problem` (Murty conjecture, ABKPR 2008 — magic
  configurations on lines in ℝ²).

  This sub-OQ extends ABKPR 2008's plane classification to k-flats (affine
  subspaces of dimension k) in ℝ^d: classify point sets `P ⊂ ℝ^d` admitting
  positive weights such that every k-flat through at least k+1 points has the
  same weight-sum.

  This file declares the parameterised definitions, three trivial / reduction
  theorems proved in full, and one S5 axiom for the higher-dim classification:
    * `zero_flat_magic_trivial`                  (k = 0, trivial)
    * `ambient_flat_magic_trivial`               (k = d, trivial)
    * `oneflat_eq_parent`                        (d = 2, k = 1, parent reduction)
    * `oneflat_classification_higher_dim`        (d ≥ 3, k = 1, AXIOM, ABKPR ext.)

  Counts (S5 ACT, class-4 repaired in S8): 0 sorries, 1 axiom, 4 supporting
  class predicates (`IsCollinearD`, `IsGeneralPositionD`, `IsNearPencilD`,
  `IsFailedFanoD`).  Docker build-verified.

  ## S8 repair (2026-07-24): class 4 was wrong — and made the axiom FALSE

  The original S5 class 4 (`IsIncenterConfigD`) was an admitted "structural
  skeleton": an injective `Fin (d + 2)`-family inside `P` plus a designated
  point, with `P.card = d + 3` — and NO affine-independence or metric
  condition.  That skeleton is *cardinality-trivial*: it holds for EVERY
  configuration of exactly `d + 3` points
  (`Erdos735OQ04TwoTriples.isIncenterSkeletonD_of_card`).  Since two parallel
  triples in ℝ³ form a 6-point configuration that is provably NOT 1-flat magic
  (`Erdos735OQ04TwoTriples.twoTriples_not_oneFlatMagic`), the pre-repair axiom
  was refutable — the statement it asserted is provably false
  (`Erdos735OQ04TwoTriples.skeleton_classification_false`), so the axiom made
  the whole environment inconsistent.

  The repair replaces class 4 by the class ABKPR 2008 actually proves
  (Theorem 1 of "There are not too many magic configurations"): a **failed
  Fano** configuration — 7 points that are, up to a projective transformation,
  a triangle, its three edge midpoints, and its centroid (magic weights 1/4 on
  vertices and centroid, 1/2 on midpoints).  The widespread "triangle +
  incenter" description (also in this repo's earlier prose) coincides with the
  equilateral representative (midpoints = bisector feet, centroid = incenter)
  but is not the general class; the paper's own name is used here.
  `IsFailedFanoD` embeds a planar projective image of the reference failed
  Fano into a 2-flat of ℝᵈ via an injective affine map.

  The parent reduction `oneflat_eq_parent` (S4 ACT) was unblocked after the
  stale "parent is broken" claim was corrected (parent builds clean against
  Mathlib v4.26.0 per #20896). The proof is short and almost-definitional:
  `WeightingD P` and `Erdos735.Weighting P` unfold to the same body; the
  `ConfigKFlat 1 P` / `Erdos735.ConfigLine P` rank conditions differ only by
  `Nat.cast_one` (`((1 : ℕ) : Cardinal) = (1 : Cardinal)`), and the card
  condition `1 + 1 = 2` is also definitional; `kFlatSum` and `Erdos735.lineSum`
  have identical bodies modulo namespace.

  The polytope witnesses already designed but not Lean-realised:
    * Tetrahedron at alternate-cube-vertices (d=3, k=2, magic constant 3) —
      S6a PREP (PR #18486).
    * Octahedron + cube refutations (vertex-transitive O_h obstruction) —
      S6b PREP (PR #18541).

  The general higher-dim classification (S5 axiom, extension of ABKPR 2008
  beyond ℝ²) is genuinely open in the literature; this file's S5 ACT iteration
  ships the conjectural classification as `oneflat_classification_higher_dim`
  (lines case, `d ≥ 3`).  See the S5 PREP memo at
  `research/problems/erdos-735-oq-04/sessions/2026-06-05-s5-prep-conjecture-refinement.md`
  for the full design rationale.  The gallery entry uses `status: "axiomatized"`.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Proofs.Erdos735Problem

namespace Erdos735OQ04

open scoped Classical

/-- A point configuration in ℝ^d. The `d = 2` case is `Erdos735.PointConfig`
    (definitionally equal). Marked `abbrev` so the `Finset → Sort` coercion
    fires uniformly in downstream defs. -/
abbrev PointConfigD (d : ℕ) := Finset (EuclideanSpace ℝ (Fin d))

/-- A positive weighting on a point configuration. -/
def WeightingD {d : ℕ} (P : PointConfigD d) := {w : P → ℝ // ∀ p, w p > 0}

/-- A k-flat through ≥ k+1 points of P: an affine subspace of `EuclideanSpace ℝ
    (Fin d)` whose direction has rank `k` and which contains at least `k + 1`
    points of P. The `d = 2, k = 1` case generalises `Erdos735.ConfigLine`.
    Note: under Mathlib v4.26.0, `AffineSubspace.direction` returns a
    `Submodule` directly, and rank is accessed via `Module.rank ℝ` rather than
    `Submodule.rank`. -/
def ConfigKFlat {d : ℕ} (k : ℕ) (P : PointConfigD d) :=
  { F : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)) //
    Module.rank ℝ F.direction = (k : Cardinal) ∧
    (P.filter (· ∈ F)).card ≥ k + 1 }

/-- The weighted sum of points of P lying in a given k-flat. Marked
    `noncomputable` because membership in `P : Finset (EuclideanSpace ℝ (Fin d))`
    is decidable only via `Classical` (the underlying point type carries
    `Real.decidableEq`, which is `noncomputable`). -/
noncomputable def kFlatSum {d k : ℕ} (P : PointConfigD d) (w : WeightingD P)
    (F : ConfigKFlat k P) : ℝ :=
  (P.filter (· ∈ F.val)).sum fun p =>
    if h : p ∈ P then w.val ⟨p, h⟩ else 0

/-- A configuration is k-flat magic if it admits a positive weighting under which
    every k-flat (through ≥ k+1 points) has the same total weight. The
    `d = 2, k = 1` case is `Erdos735.IsMagic` (parent reduction `oneflat_eq_parent`
    deferred to S4 ACT, post-parent-repair). -/
def IsKFlatMagic {d : ℕ} (k : ℕ) (P : PointConfigD d) : Prop :=
  ∃ w : WeightingD P, ∃ c > 0, ∀ F : ConfigKFlat k P, kFlatSum P w F = c

/- ## S5: The Four Conjectured Magic Classes in ℝᵈ (k = 1 case) -/

/-- Class 1 — `ℝᵈ` analogue of `Erdos735.IsCollinear`: all points lie on a single
    1-flat. -/
def IsCollinearD {d : ℕ} (P : PointConfigD d) : Prop :=
  ∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)),
    Module.rank ℝ L.direction = 1 ∧ ∀ p ∈ P, p ∈ L

/-- Class 2 — `ℝᵈ` analogue of `Erdos735.IsGeneralPosition`: no three distinct
    points share a common 1-flat. -/
def IsGeneralPositionD {d : ℕ} (P : PointConfigD d) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P, p ≠ q → q ≠ r → p ≠ r →
    ¬ ∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)),
      Module.rank ℝ L.direction = 1 ∧ p ∈ L ∧ q ∈ L ∧ r ∈ L

/-- Class 3 — `ℝᵈ` analogue of `Erdos735.IsNearPencil`: all but one point lie
    on a common 1-flat, and the remaining point is off the flat. -/
def IsNearPencilD {d : ℕ} (P : PointConfigD d) : Prop :=
  ∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)),
    Module.rank ℝ L.direction = 1 ∧
    ∃ p ∈ P, p ∉ L ∧ (∀ q ∈ P, q ≠ p → q ∈ L)

/- ### Class 4 — the failed Fano configuration (S8 repair)

The pre-S8 class 4 (`IsIncenterConfigD`) was a cardinality-trivial skeleton
that made the classification axiom provably false; see the file header and
`Proofs.Erdos735OQ04TwoTriples` for the machine-checked refutation.  The
definitions below encode the class ABKPR 2008 actually proves. -/

/-- Homogenisation `ℝ² → ℝ³` into the affine chart `z = 1`:
    `(x, y) ↦ (x, y, 1)`. -/
def homogenize (p : EuclideanSpace ℝ (Fin 2)) : Fin 3 → ℝ :=
  ![WithLp.ofLp p 0, WithLp.ofLp p 1, 1]

/-- Dehomogenisation `ℝ³ ⇀ ℝ²` (meaningful on the chart `z ≠ 0`):
    `(x, y, z) ↦ (x/z, y/z)`. -/
noncomputable def dehomogenize (v : Fin 3 → ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[v 0 / v 2, v 1 / v 2]

/-- The reference **failed Fano** configuration (ABKPR 2008, Figure 1): a
    triangle `(0,0), (2,0), (0,2)`, its three edge midpoints, and its
    centroid — 7 points.  It is magic with weights `1/4` on the vertices and
    the centroid and `1/2` on the midpoints (every configuration line sums to
    `1`), and ABKPR 2008 Theorem 1 states these 7 points are — up to
    projective transformation — the ONLY magic configuration that is neither
    (near-)collinear nor in general position.  For the equilateral
    representative the midpoints are the bisector feet and the centroid is the
    incenter, which is where the folklore "triangle + incenter" description
    comes from. -/
noncomputable def failedFanoBase : PointConfigD 2 :=
  {!₂[0, 0], !₂[2, 0], !₂[0, 2], !₂[1, 0], !₂[0, 1], !₂[1, 1], !₂[2/3, 2/3]}

/-- `P ⊂ ℝ²` is a projective image of the failed Fano configuration: some
    nonsingular `3 × 3` matrix, acting on homogeneous coordinates with every
    image point remaining in the affine chart `z ≠ 0`, carries
    `failedFanoBase` onto `P`. -/
noncomputable def IsFailedFanoPlane (P : PointConfigD 2) : Prop :=
  ∃ M : Matrix (Fin 3) (Fin 3) ℝ, M.det ≠ 0 ∧
    (∀ p ∈ failedFanoBase, M.mulVec (homogenize p) 2 ≠ 0) ∧
    P = failedFanoBase.image (fun p => dehomogenize (M.mulVec (homogenize p)))

/-- Class 4 — `P ⊂ ℝᵈ` lies in an affinely embedded plane and is there a
    projective image of the failed Fano configuration.  (An injective affine
    map preserves collinearity in both directions, so the line-incidence
    structure — and hence 1-flat magicness — of the planar configuration is
    exactly reproduced inside the 2-flat `f '' ℝ²`.) -/
noncomputable def IsFailedFanoD {d : ℕ} (P : PointConfigD d) : Prop :=
  ∃ Q : PointConfigD 2, IsFailedFanoPlane Q ∧
    ∃ f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin d),
      Function.Injective f ∧ P = Q.image f

/-- **S5 axiom (S8-repaired) — extension of ABKPR 2008 to higher ambient
    dimension** (1-flat case only).  For `d ≥ 3`, a configuration `P ⊂ ℝᵈ` is
    1-flat magic iff it is collinear, in general position, a near-pencil, or a
    planar projective image of the failed Fano configuration.

    **Status**: research-level open.  No published proof of the higher-dim
    classification exists in any `ℝᵈ` for `d ≥ 3` to the formaliser's
    knowledge as of 2026-07.  The conjecture is the natural lift of ABKPR 2008
    Theorem 1 (whose planar classes are exactly: `n-1` or `n` collinear
    points, general position, failed Fano); a configuration spanning ≥ 3
    dimensions has only the collinear/general-position/near-pencil routes
    available (the failed Fano is planar), so the genuinely open content is
    that a magic configuration with a full-rank span and a 3-point line cannot
    exist.  Axiomatised pending future proof.

    **History**: the pre-S8 form of this axiom (over the cardinality-trivial
    `IsIncenterConfigD` skeleton) was provably FALSE — see
    `Erdos735OQ04TwoTriples.skeleton_classification_false` for the
    machine-checked refutation and the file header for the repair rationale.

    For `d = 2`, the corresponding statement is the parent's
    `Erdos735.magic_classification` composed with this slug's S4 ACT
    `oneflat_eq_parent` (but note the parent's own class-4 encoding has the
    analogous defect; see issue filed 2026-07-24). -/
axiom oneflat_classification_higher_dim {d : ℕ} (hd : 3 ≤ d) (P : PointConfigD d) :
    IsKFlatMagic 1 P ↔
      IsCollinearD P ∨ IsGeneralPositionD P ∨ IsNearPencilD P ∨ IsFailedFanoD P

/-- Trivial case k = 0. Every rank-0 affine subspace is a single ambient point
    `{x}`; the `card ≥ 1` constraint forces `x ∈ P`, so each `ConfigKFlat 0 P`
    is `{p}` for some `p ∈ P` and the constant-1 weighting gives sum 1 on each.
    Discharged in S3 ACT via S3 PREP-2 §6 recipe (bearers B1 + N1-N4). -/
theorem zero_flat_magic_trivial {d : ℕ} (P : PointConfigD d) :
    IsKFlatMagic 0 P := by
  refine ⟨⟨fun _ => (1 : ℝ), fun _ => zero_lt_one⟩, 1, zero_lt_one, ?_⟩
  intro Fcfg
  obtain ⟨F, hrk, hcard⟩ := Fcfg
  have hbot : F.direction = ⊥ := by
    apply Submodule.rank_eq_zero.mp
    simpa using hrk
  have hpos : 0 < (P.filter (· ∈ F)).card := by omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  have hp_P : p ∈ P := (Finset.mem_filter.mp hp).1
  have hp_F : p ∈ F := (Finset.mem_filter.mp hp).2
  have hfilter_eq : P.filter (· ∈ F) = {p} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hp, ?_⟩
    intro q hq
    have hqF : q ∈ F := (Finset.mem_filter.mp hq).2
    have hvsub : q -ᵥ p ∈ F.direction :=
      AffineSubspace.vsub_mem_direction hqF hp_F
    rw [hbot, Submodule.mem_bot] at hvsub
    exact vsub_eq_zero_iff_eq.mp hvsub
  show (P.filter (· ∈ F)).sum
    (fun p => if h : p ∈ P then (1 : ℝ) else 0) = 1
  rw [hfilter_eq, Finset.sum_singleton, dif_pos hp_P]

/-- Trivial case k = d. The only rank-d affine subspace of `EuclideanSpace ℝ
    (Fin d)` is the ambient space (= `⊤`), which contains all of P. Either
    `P.card < d + 1` (no qualifying d-flats, ∀ vacuous) or `P.card ≥ d + 1` (one
    d-flat with sum = `P.card` under uniform weight). Discharged in S3 ACT via
    S3 PREP-2 §6 recipe (bearers B3 + B4 + N5 + supporting). -/
theorem ambient_flat_magic_trivial {d : ℕ} (P : PointConfigD d) :
    IsKFlatMagic d P := by
  by_cases hcard : P.card ≥ d + 1
  · refine ⟨⟨fun _ => (1 : ℝ), fun _ => zero_lt_one⟩, (P.card : ℝ), ?_, ?_⟩
    · have h1 : 0 < P.card := by omega
      exact_mod_cast h1
    intro Fcfg
    obtain ⟨F, hrk, hcardF⟩ := Fcfg
    have hfr_F : Module.finrank ℝ F.direction = d := by
      apply Module.finrank_eq_of_rank_eq
      simpa using hrk
    have hfr_amb : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
      finrank_euclideanSpace_fin
    have hdir_top : F.direction = ⊤ :=
      Submodule.eq_top_of_finrank_eq (hfr_F.trans hfr_amb.symm)
    have hF_ne : (F : Set (EuclideanSpace ℝ (Fin d))).Nonempty := by
      have hpos : 0 < (P.filter (· ∈ F)).card := by omega
      obtain ⟨q, hq⟩ := Finset.card_pos.mp hpos
      exact ⟨q, (Finset.mem_filter.mp hq).2⟩
    have hF_top : F = ⊤ :=
      (AffineSubspace.direction_eq_top_iff_of_nonempty hF_ne).mp hdir_top
    show (P.filter (· ∈ F)).sum
      (fun p => if h : p ∈ P then (1 : ℝ) else 0) = (P.card : ℝ)
    have hfilter : P.filter (· ∈ F) = P := by
      rw [hF_top]
      exact Finset.filter_true_of_mem (fun p _ => AffineSubspace.mem_top ℝ _ p)
    rw [hfilter]
    rw [Finset.sum_congr rfl (fun p hp => dif_pos hp)]
    rw [Finset.sum_const, Nat.smul_one_eq_cast]
  · push_neg at hcard
    refine ⟨⟨fun _ => (1 : ℝ), fun _ => zero_lt_one⟩, 1, zero_lt_one, ?_⟩
    intro Fcfg
    obtain ⟨_F, _hrk, hcardF⟩ := Fcfg
    have hle : d + 1 ≤ P.card :=
      le_trans hcardF (Finset.card_filter_le _ _)
    omega

/-- **S4 ACT — parent reduction.** For `d = 2, k = 1`, the k-flat-magic property
    is definitionally the parent's `Erdos735.IsMagic` property. The weighting
    types `WeightingD P` and `Erdos735.Weighting P` unfold to the same body, and
    `ConfigKFlat 1 P` differs from `Erdos735.ConfigLine P` only by the
    `Nat.cast_one` rewrite on the rank condition (and a `1 + 1 = 2` card rewrite
    that omega/simp dispatches automatically). The `kFlatSum` / `Erdos735.lineSum`
    bodies are identical modulo namespace, so subsumption-of-witnesses through
    the AffineSubspace `.val` is by `rfl`. -/
theorem oneflat_eq_parent (P : PointConfigD 2) :
    IsKFlatMagic 1 P ↔ Erdos735.IsMagic P := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨w, hw⟩, c, hc, hmagic⟩
    refine ⟨⟨w, hw⟩, c, hc, ?_⟩
    rintro ⟨L, hrkL, hcardL⟩
    have hrk' : Module.rank ℝ L.direction = ((1 : ℕ) : Cardinal) := by
      simpa using hrkL
    exact hmagic ⟨L, hrk', hcardL⟩
  · rintro ⟨⟨w, hw⟩, c, hc, hmagic⟩
    refine ⟨⟨w, hw⟩, c, hc, ?_⟩
    rintro ⟨F, hrkF, hcardF⟩
    have hrk' : Module.rank ℝ F.direction = 1 := by
      simpa using hrkF
    exact hmagic ⟨F, hrk', hcardF⟩

end Erdos735OQ04
