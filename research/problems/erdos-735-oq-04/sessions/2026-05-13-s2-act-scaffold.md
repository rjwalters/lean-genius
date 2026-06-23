# S2 ACT — Lean scaffold (`proofs/Proofs/Erdos735OQ04.lean`)

**Date**: 2026-05-13
**Researcher**: researcher-12
**Mode**: ACT (Lean file)
**Phase target**: S2 ACT — definitions + trivial-case theorem signatures
**Status**: pristine — 0 open PRs at claim time, 4 merged (S1 OBSERVE, S6a PREP,
S6b PREP, STATE-SYNC); first Lean delta on this slug.

## What this iteration ships

`proofs/Proofs/Erdos735OQ04.lean` (NEW, 99 LOC) — the first Lean file under this
slug. Contains:

* `abbrev PointConfigD (d : ℕ) := Finset (EuclideanSpace ℝ (Fin d))` — the
  d-dimensional generalisation of `Erdos735.PointConfig`.
* `def WeightingD {d} (P : PointConfigD d) := {w : P → ℝ // ∀ p, w p > 0}` —
  positive weighting (identical signature to the parent).
* `def ConfigKFlat {d} (k : ℕ) (P : PointConfigD d)` — affine subspace of
  direction-rank `k` with at least `k + 1` points of `P`. Uses
  `Module.rank ℝ F.direction = (k : Cardinal)` per Mathlib v4.26.0 API
  (`AffineSubspace.direction` returns `Submodule ℝ V` directly, no
  `.toSubmodule` step; rank is `Module.rank` not `Submodule.rank`).
* `noncomputable def kFlatSum {d k} (P : PointConfigD d) (w : WeightingD P)
  (F : ConfigKFlat k P) : ℝ` — weighted sum over points lying in `F`.
* `def IsKFlatMagic {d} (k : ℕ) (P : PointConfigD d) : Prop` — the k-flat
  magic predicate (∃ positive weighting + ∃ positive constant + ∀ k-flat).
* `theorem zero_flat_magic_trivial {d} (P) : IsKFlatMagic 0 P` — `sorry`,
  pending S3 ACT.
* `theorem ambient_flat_magic_trivial {d} (P) : IsKFlatMagic d P` — `sorry`,
  pending S3 ACT.

`proofs/Proofs.lean` — adds `import Proofs.Erdos735OQ04`.

**Build result**: Docker-build clean — 3058 jobs, 2 expected `declaration uses 'sorry'`
warnings on the two trivial-case theorems (log:
`.loom/logs/researcher-12-erdos735-oq04-s2act-build5.log`).

## Mathlib v4.26.0 surface fixes (relative to parent file's idiom)

Four issues surfaced during the build-and-rebuild loop; each documented in
`Proofs/Erdos735OQ04.lean`'s doc-strings so future maintainers don't repeat the
investigation:

1. **`Mathlib.LinearAlgebra.AffineSpace.AffineSubspace` no longer exists** —
   split in v4.26.0 into `AffineSubspace/Basic.lean` (re-exports
   `AffineSubspace/Defs.lean`). New file imports `.Basic`.
2. **`Finset → Sort` coercion fails through `def`-aliases** — `def PointConfigD`
   was not transparent enough for the `WeightingD` subtype to elaborate
   (`type expected, got (P : PointConfigD d)`). Fix: `abbrev PointConfigD`.
3. **`AffineSubspace.direction.toSubmodule` invalid** — v4.26.0 returns
   `Submodule` directly; drop the `.toSubmodule` step. The `Submodule.rank`
   field is also gone — use `Module.rank ℝ F.direction = (k : Cardinal)`
   (and the natural-number → Cardinal coercion is no longer auto-inserted).
4. **`(P.filter (· ∈ F)).card` requires `DecidablePred (· ∈ F)`** — fixed
   namespace-wide with `open scoped Classical`. `kFlatSum` is `noncomputable`
   (membership in `Finset (EuclideanSpace ℝ (Fin d))` depends on
   `Real.decidableEq`, which is `noncomputable`).

## Parent-file regression (out of scope; flagged for follow-up)

`proofs/Proofs/Erdos735Problem.lean` is **broken on `origin/main`** under
Mathlib v4.26.0:

* `import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace` — same module-split
  issue as above (1-line fix: append `.Basic`).
* `def threeCollinear`/`def triangle` use `{![0, 0], ![1, 0], ![2, 0]}` /
  `{![0, 0], ![1, 0], ![0, 1]}` — the matrix `![...]` notation no longer
  auto-coerces to `EuclideanSpace ℝ (Fin 2)`. Mathlib v4.26.0 lost the
  implicit `(Fin n → ℝ) → EuclideanSpace ℝ (Fin n)` coercion in this
  literal-set context. Fix is multi-line (likely add `(· : EuclideanSpace ℝ
  (Fin 2))` casts).
* The parent file's `def Weighting (P : PointConfig) := {w : P → ℝ // ∀ p, w p > 0}`
  has the **same** `Finset → Sort` issue as my pre-fix `WeightingD`. Fix
  mirrors mine: `abbrev PointConfig`.
* The parent's `def ConfigLine (P : PointConfig) := { L : AffineSubspace ℝ _ //
  L.direction.toSubmodule.rank = 1 ∧ (P.filter (· ∈ L)).card ≥ 2 }` has the
  same `direction.toSubmodule.rank` + `DecidablePred (· ∈ L)` issues mine
  had. Fix mirrors mine.

Same three files have the same `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace`
import:

* `proofs/Proofs/Erdos105Problem.lean`
* `proofs/Proofs/Erdos209Problem.lean`
* `proofs/Proofs/Erdos210Problem.lean`

Whether the matrix-`![...]` / Weighting-subtype regressions hit these too:
not investigated this session.

**Recommended follow-up**: doctor or mechanic should pick up
`Erdos735Problem.lean` and the three sibling Erdős parents in one sweep. The
PR title pattern from `feedback_researcher_parent_file_build_unblocker_inpr_pattern`
applies, but for FOUR files it's too large for an in-PR build-unblocker and
should be a separate doctor PR.

This S2 ACT scaffold **does not depend on the parent file** (no
`import Proofs.Erdos735Problem`), so the parent regression does not block
S3/S4 ACT for OQ04 unless we want the parent-reduction theorem
`oneflat_eq_parent` (which is intentionally deferred to S4 ACT post-repair).

## Why this ACT instead of more PREP

After S1 OBSERVE + S6a/S6b PREP + STATE-SYNC, the slug had **4 consecutive
doc-only PRs**. Per MEMORY
(`feedback_researcher_docs_only_chain_silent_parent_regression`),
this is exactly the threshold where Docker-build verification should fire —
and indeed the build surfaced the parent regression that would otherwise have
remained invisible. Breaking the doc-only chain here was the right move
mathematically as well: the trivial-case theorem signatures need to exist
before S3 ACT can discharge them.

## Next iteration — S3 ACT

Discharge the two trivial cases:

* `zero_flat_magic_trivial`: use the constant-1 weighting (`fun _ => 1`) and
  `c = 1`. For each `F : ConfigKFlat 0 P`, show `F.val` is a singleton
  containing exactly one point of `P` (via rank-0 + filter cardinality ≥ 1),
  then `kFlatSum = 1 = c`. ~15-20 LOC; requires
  `Submodule.rank_eq_zero_iff` or `Module.rank_eq_zero_iff` to deduce
  `F.direction = ⊥`.
* `ambient_flat_magic_trivial`: split on `P.card ≥ d + 1` vs `<`. In the `<`
  case `ConfigKFlat d P` is empty so the `∀` is vacuous (pick `w = 1, c = 1`).
  In the `≥` case, the unique d-flat is `⊤`, and `(P.filter (· ∈ ⊤)).card =
  P.card`; pick `c = (P.card : ℝ)` and `w = 1`. ~20-30 LOC; requires
  `AffineSubspace.direction_eq_top_iff` or a `Module.rank_eq_finrank_iff`
  variant for `Fin d → ℝ`.

Expected total: ~35-50 LOC, 0 new sorries (closes both).

## Anti-targets (what this iteration does NOT do)

* Parent reduction `oneflat_eq_parent` — blocked on parent repair.
* Tetrahedron certificate from S6a PREP — separate ACT (S6a-ACT) once trivials
  land. Note: S6a PREP §1 already established `native_decide` is not viable
  for this; explicit witness construction is required.
* Octahedron/cube refutations from S6b PREP — separate ACTs (S6b-ACT, S6c-ACT).
* General-position uniform-weight theorem (S6e) — separate ACT.
* Higher-dim ABKPR extension axiom (S5) — separate doc-only PREP first to
  refine the conjectural form per S6a + S6b corrections (the "regular
  polytope" class is narrower than S1 OBSERVE proposed).

## Honesty

* New file: 99 LOC, **5 defs, 2 theorems with `sorry`, 0 axioms, 2 sorries**.
* Build verified: 3058-job Docker-build clean (excluding the 2 expected
  sorry warnings).
* Parent reduction NOT shipped — blocked on Mathlib v4.26.0 parent regression.
* The S5 axiom (genuinely open higher-dim ABKPR extension) remains undeclared;
  the eventual gallery entry must use `status: "axiomatized"`.
