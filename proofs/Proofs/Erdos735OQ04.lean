/-
  Erdős Problem #735, Open Question #04 (oq-04):
  k-flat magic configurations in ℝ^d

  Parent: `Proofs.Erdos735Problem` (Murty conjecture, ABKPR 2008 — magic
  configurations on lines in ℝ²).

  This sub-OQ extends ABKPR 2008's plane classification to k-flats (affine
  subspaces of dimension k) in ℝ^d: classify point sets `P ⊂ ℝ^d` admitting
  positive weights such that every k-flat through at least k+1 points has the
  same weight-sum.

  This file declares the parameterised definitions and proves the two
  trivial-case targets `zero_flat_magic_trivial` (k = 0) and
  `ambient_flat_magic_trivial` (k = d) in full — 0 sorries, 0 axioms,
  Docker build-verified against Mathlib v4.26.0.

  The third trivial target — the parent reduction
  `IsKFlatMagic 1 P ↔ Erdos735.IsMagic P` for `d = 2` (S4 ACT) — is deferred
  until the parent file `Proofs.Erdos735Problem` is repaired against Mathlib
  v4.26.0. The parent's `import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace`
  is broken on `origin/main` (Mathlib v4.26.0 split this module into
  `AffineSubspace/Basic.lean` + `AffineSubspace/Defs.lean`), and the parent's
  `def threeCollinear`/`def triangle` examples fail elaboration (matrix `![...]`
  notation no longer auto-coerces to `EuclideanSpace`). Tracking these as a
  separate doctor/mechanic task; out of scope for this S2 ACT scaffold.

  The polytope witnesses already designed but not Lean-realised:
    * Tetrahedron at alternate-cube-vertices (d=3, k=2, magic constant 3) —
      S6a PREP (PR #18486).
    * Octahedron + cube refutations (vertex-transitive O_h obstruction) —
      S6b PREP (PR #18541).

  The general higher-dim classification (S5 axiom, extension of ABKPR 2008
  beyond ℝ²) is genuinely open in the literature; future iterations will
  axiomatise it. The eventual gallery entry must use `status: "axiomatized"`.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

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

end Erdos735OQ04
