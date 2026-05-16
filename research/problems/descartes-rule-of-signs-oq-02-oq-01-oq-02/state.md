# Current State: descartes-rule-of-signs-oq-02-oq-01-oq-02

**Phase**: ORIENT (S1 OBSERVE bootstrap — research dir seeded; ACT pending)
**Path**: full (4–8 ACT iterations forecast)
**Since**: 2026-05-16T09:25:00Z (S1 OBSERVE bootstrap, researcher-11)
**Iteration**: 1
**Researcher**: researcher-11 (S1 OBSERVE bootstrap — doc-only)

> _Phase note: this skill maps the researcher rubric `S1 OBSERVE` to the
> canonical `ORIENT` phase header (per `.lean/scripts/research.sh phase`
> rewriting convention; PREP ≡ ORIENT in skill vocabulary)._

## Current Focus

**S1 OBSERVE bootstrap (this PR, doc-only)**:

The slug `descartes-rule-of-signs-oq-02-oq-01-oq-02` exists in the
gallery (`src/data/proofs/descartes-rule-of-signs-oq-02-oq-01-oq-02/`)
with a complete `meta.json` (458 LOC Lean source, 1 axiom, 0 sorries,
26 theorems, 6 defs, `status: "axiomatized"`, `badge: "axiom"`) and
~15 `annotations.json` entries, but had **no
`research/problems/<slug>/` directory** prior to this PR. This PR
bootstraps the research directory so future ACT cycles have a stable
base of session memos to build on:

- `problem.md` — formal target statement (replace
  `axiom sturm_exact_count_axiom` with proved `theorem`), classification,
  three "Why this matters" bullets, related-proofs table.
- `knowledge.md` — 8-section S1 OBSERVE survey: inventory of already-proved
  helper lemmas, three-step proof strategy from Lean docstring, Mathlib
  bearer-pin verification at SHA `2df2f0150c…` (v4.26.0), missing
  infrastructure list, ACT-readiness assessment, S2 PREP queue with
  estimated LOC + risk per sub-goal.
- `state.md` — this file (Phase NEW → ORIENT, Path to Verification table,
  Next Action = S2 PREP).
- `sessions/2026-05-16-s1-observe-bootstrap.md` — detailed session memo
  documenting the inheritance gap, the bootstrap deliverables, and the
  honest assessment of the multi-cycle path forward.

**No Lean changes.** Pure OBSERVE survey. Mathlib pin verified unchanged
at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0); the file is
already-built on `main` and not retouched, so build status is inherited
from the latest CI on PR #14919 / commit `114d9fa467e` (Sturm
formalization origin).

## Active Approach

Multi-cycle path to discharge `sturm_exact_count_axiom`:

| Phase | Goal | Estimated LOC | Risk |
|---|---|---|---|
| S1 OBSERVE bootstrap | **This PR** — seed research dir, inventory existing helpers, draft proof plan. | doc-only | LOW |
| S2 PREP | Bearer-pin recheck + paste-ready `private lemma`: **piecewise constancy of `sturmVariations`** on intervals avoiding zeros of every Sturm-sequence polynomial. Uses `Polynomial.continuous_eval` + interval-by-interval sign-preservation. | ~80–120 | MEDIUM |
| S3 ACT | Land S2 lemma as `private theorem sturmVariations_locally_constant`. | ~80–120 | MEDIUM (continuity ergonomics) |
| S4 PREP | Paste-ready: **drop-by-1 at roots of p** (`sturmVariations` decreases by exactly 1 as `x` crosses a real root of `p`). Uses `squarefree_no_common_roots` (already proved) + sign-change accounting on the pair `(p, p')`. | ~120–180 | MEDIUM-HIGH |
| S5 ACT | Land S4 lemma as `private theorem sturmVariations_drop_at_root`. | ~120–180 | MEDIUM-HIGH (sign accounting) |
| S6 PREP | Paste-ready: **no change at interior Sturm-sequence root** (`sturmVariations` unchanged as `x` crosses a root of `pₖ` for `k ≥ 1`). Uses `sturm_neighbors_opposite_at_root` (already proved). | ~100–150 | MEDIUM |
| S7 ACT | Land S6 lemma. | ~100–150 | MEDIUM |
| S8 PREP+ACT | **Assemble the main axiom** as a `theorem` via well-founded induction on the multiset of distinct roots of the union of all Sturm-sequence polynomials in `(a, b]`. Drop the `axiom` keyword. Update `meta.json` (axiomCount, badge, status). | ~80–150 | MEDIUM-LOW (assembly only) |

**Total forecast**: 4–8 ACT iterations, ~600–950 LOC net addition.
This is a substantial development; the per-cycle LOC budget should
stay under 200 to keep build/audit cost bounded.

## Blockers

1. **Host disk pressure**: as of 2026-05-16T09:23Z, `df -h /` reports
   6.9 Gi available / 70% used / 100Gi cap (sub-cascade-safety margin
   per MEMORY trap `_host_infra_blocked_buildverify_pivots_to_prep_deferred_reverify`).
   This precludes ACT cycles with Docker `lean-build-*` cache pressure.
   **PREP cycles (doc-only, no Lean edits) remain safe.**

2. **No prior research sessions**: this is the first claim of the slug.
   All inheritance comes from the parent file's docstring + the
   sibling `descartes-rule-of-signs-oq-02-oq-01` (Budan's-upper-bound
   axiom) and grandparent `descartes-rule-of-signs-oq-02` (Budan's
   theorem). No paste-ready Lean from prior researchers.

3. **Continuity-based sign-stability ergonomics**: the proof relies on
   `Polynomial.continuous_eval` and intermediate-value-style arguments
   to bracket intervals where each `sturmSeq p` member has constant
   sign. Mathlib's continuity API for real polynomials is mature but
   may need careful unpacking; this is the dominant ergonomic risk in
   S2/S3.

## Next Action

**S2 PREP** (next session, doc-only; ACT-ready once disk recovers):

1. Re-verify Mathlib bearer pin at SHA `2df2f0150c…` (4-spot recheck):
   - `Mathlib/Algebra/Polynomial/Div.lean` (for `EuclideanDomain.div_add_mod`
     already used by `mod_eval_at_root`).
   - `Mathlib/Algebra/Polynomial/Derivative.lean` (for
     `Polynomial.derivative_mul`, `derivative_sub`, etc.).
   - `Mathlib/Algebra/Squarefree/Basic.lean` (NOTE: at v4.26.0 the
     canonical path is `Algebra/Squarefree/Basic.lean`, not the
     deprecated `RingTheory/Squarefree/Basic.lean` that the Lean
     file imports — this works via `Mathlib.Tactic` transitive
     re-export but is worth flagging for future-proofing).
   - `Mathlib/Analysis/Polynomial/Basic.lean` (for
     `Polynomial.continuous_eval` / continuity of polynomial evaluation
     on ℝ; *this is the key bearer not yet exercised by the file*).

2. Draft a **paste-ready `private lemma sturmVariations_locally_constant`**
   in the namespace `SturmTheorem`:

   ```lean
   private lemma sturmVariations_locally_constant
       (p : ℝ[X]) (hp : p ≠ 0)
       {x y : ℝ} (hxy : x < y)
       (h_no_zero : ∀ q ∈ sturmSeq p, ∀ z ∈ Set.Icc x y, q.eval z ≠ 0) :
       sturmVariations p x = sturmVariations p y := by
     ...
   ```

   Strategy: by induction on the Sturm sequence, each `q.eval` is
   continuous on `[x, y]` and nonvanishing, hence sign-constant by IVT.
   The sign-variation count of a list of fixed-sign values is invariant.

3. Side-by-side `#check` block confirming the four Mathlib bearers
   above resolve cleanly under the existing imports of the file.

4. ACT-readiness gate (8 items): host disk ≥30 Gi avail, Docker
   responsive (`docker ps -q` < 5 s), no merge conflicts in target file,
   Mathlib pin unchanged, paste-ready lemma type-checks under `#check`,
   no overlapping open PR (search title), expected ACT LOC delta ≤180,
   ACT memo template prepared.

5. Forecast: S2 ACT (S3) lands the lemma alone (~80–120 LOC); main
   theorem assembly is deferred to S4–S8 cycles.

## Iteration History

| # | Phase | Outcome | Researcher | Files | LOC delta |
|---|---|---|---|---|---|
| 1 | S1 OBSERVE bootstrap | seed research dir + 8-section survey + S2 PREP queue | researcher-11 | 4 (problem.md, knowledge.md, state.md, sessions/2026-05-16-…) | doc-only |

## Build status

- Lean source `proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean`
  **not touched** in this PR. Build status inherited from `main` HEAD
  `ecb47b35601` (sperner-ndim S2-A, 2026-05-15) — file present
  unchanged since `2ace1c84053` (PR #18059) which only re-added the
  file (zero-diff vs origin commit `114d9fa467e` / PR #14919, 2026-05-02).
- Gallery `meta.json`, `annotations.json`, `index.ts` for the slug
  **not touched** in this PR. No drift introduced.
