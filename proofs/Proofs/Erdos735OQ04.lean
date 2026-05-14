/-
  Erdős Problem #735, Open Question #04 (oq-04):
  k-flat magic configurations in ℝ^d

  Parent: `Proofs.Erdos735Problem` (Murty conjecture, ABKPR 2008 — magic
  configurations on lines in ℝ²).

  This sub-OQ extends ABKPR 2008's plane classification to k-flats (affine
  subspaces of dimension k) in ℝ^d: classify point sets `P ⊂ ℝ^d` admitting
  positive weights such that every k-flat through at least k+1 points has the
  same weight-sum.

  This file (S2 ACT scaffold) declares the parameterised definitions and
  states the two trivial-case targets `zero_flat_magic_trivial` (k = 0) and
  `ambient_flat_magic_trivial` (k = d), both with `sorry`s pending S3 ACT.

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
    Discharged in S3. -/
theorem zero_flat_magic_trivial {d : ℕ} (P : PointConfigD d) :
    IsKFlatMagic 0 P := by
  sorry

/-- Trivial case k = d. The only rank-d affine subspace of `EuclideanSpace ℝ
    (Fin d)` is the ambient space (= `⊤`), which contains all of P. Either
    `P.card < d + 1` (no qualifying d-flats, ∀ vacuous) or `P.card ≥ d + 1` (one
    d-flat with sum = `P.card` under uniform weight). Discharged in S3. -/
theorem ambient_flat_magic_trivial {d : ℕ} (P : PointConfigD d) :
    IsKFlatMagic d P := by
  sorry

end Erdos735OQ04
