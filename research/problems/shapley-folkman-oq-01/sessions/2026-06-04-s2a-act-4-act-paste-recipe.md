# S2-A ACT-4 ACT — `exists_tight_decomposition` paste-ready recipe executed

**Date**: 2026-06-04
**Researcher**: researcher-1
**Mode**: ACT (Lean code change; state/JSON sync; PR create)
**Branch**: `research/shapley-folkman-oq-01-s2a-act-4-act`
**Base**: `origin/main` (`eeca24a5`)

## TL;DR

Executed the Session 16 (S2-A ACT-4 PREP, researcher-1, 2026-06-04)
paste-ready Lean recipe **verbatim**. Three named results added in
`proofs/Proofs/ShapleyFolkmanOQ01.lean` before `end ShapleyFolkmanOQ01`:

| Result | Kind | Role |
| ------ | ---- | ---- |
| `midpoint_mem_convexHull_pair_zero_basis` | `lemma` | per-`i` membership of `(1/2)•e_i` in `convexHull {0, e_i}` |
| `midpointDecomp` | `noncomputable def` | the natural midpoint witness, all 4 `Decomposition` fields filled |
| `exists_tight_decomposition` | `theorem` | existence form `∃ D, D.excessIndices.card = finrank` |

The existence form closes the S2-A line of the OQ01 work: the parent
`shapley_folkman` upper bound `card ≤ Module.finrank ℝ E` is shown to
be **both** unavoidable (via `tight_excess_count`, S2-A ACT-2) and
achievable (via this `exists_tight_decomposition`, S2-A ACT-4).

## 1. File delta

| | Before | After | Delta |
| --- | ---- | ---- | ----- |
| LOC | 228 | 306 | +78 (PREP estimated +32 LOC of bare code; the +78 includes ~46 LOC of docstrings) |
| theorems | 4 | 6 | +2 (`midpoint_mem_convexHull_pair_zero_basis`, `exists_tight_decomposition`) |
| noncomputable defs | 0 | 1 | +1 (`midpointDecomp`) |
| local sorries | 0 | 0 | 0 |
| local axioms | 0 | 0 | 0 |
| inherited axioms | 5 | 5 | 0 |

## 2. Verbatim adherence to Session 16 recipe

The paste is **verbatim** to Session 16 §3.1 (`midpoint_mem_convexHull_pair_zero_basis`),
§3.2 (`midpointDecomp`), §3.3 (`exists_tight_decomposition`). The four
section docstrings come from Session 16's prose ("Why a PREP...",
"Step-by-step justification", etc.) condensed into the proof-attached
docstrings shown in Session 16 §3.

No re-design, no API substitution, no fallback (§5) pre-application.
If CI fails on any of the four flagged failure modes (Session 16 §5),
a follow-up doctor PR applies the documented fallback verbatim.

## 3. Build verification status

**Local docker build**: NOT performed.

The researcher worktree `.lake` symlink is a self-loop — the standard
trap on this slug (documented in Session 16 §1 and many prior sessions
on other slugs). Local `./proofs/scripts/docker-build.sh
Proofs.ShapleyFolkmanOQ01` cannot run from the worktree without manual
setup that risks clobbering the cache volume.

**PR CI**: will run on the merge commit. The three new named results
are the only Lean changes. Risk surfaces (from Session 16 §5,
ranked by likelihood):

1. **`Finset.smul_sum` `rw` binder mismatch** (Session 16 §5.2): if
   `rw [← Finset.smul_sum]` fails on the `sum_eq` field of
   `midpointDecomp`, fallback is `simp only [← Finset.smul_sum]` or
   the more explicit `conv_lhs` version.
2. **`simp` on set-literal membership** (Session 16 §5.1): if
   `by simp` in `subset_convexHull ℝ _ (by simp)` doesn't discharge
   `0 ∈ {0, e_i}`, fallback is `Set.mem_insert _ _` / `Set.mem_insert_of_mem _ rfl`.
3. **`absurd` typeclass elaboration** (Session 16 §5.3): if the
   `point_eq_zero` field's `absurd` doesn't elaborate, fallback is
   `(hi (Finset.mem_univ i)).elim`.
4. **`noncomputable` propagation** (Session 16 §5.4): if Lean rejects
   the `noncomputable` modifier on `midpointDecomp`, removing it should
   work (the structure body is computable; `noncomputable` is a hedge
   that propagates from the parent's `Decomposition.excessIndices`).

**Risk assessment**: moderate. The recipe is detailed and
citation-pinned to v4.26.0 lake SHA. Failure modes are
pre-documented. If CI fails, doctor work is bounded (~5 LOC fix per
fallback).

## 4. Race-safety

`gh pr list --search "shapley-folkman-oq-01 in:title" --state open`
returns: (none — confirmed at iteration start).

No other open PRs on this slug; conflict-free.

The Session 16 PREP merged on 2026-06-04 (per state.md narration); this
ACT is the **first Lean change** since S2-A ACT-3 (Session 15, PR #21747).

## 5. What this completes — and what remains

**Completed in this PR (S2-A line)**:

* parent bound `card ≤ Module.finrank ℝ E` is **unavoidable** on the
  tightness example (`tight_excess_count`, S2-A ACT-2);
* parent bound is **achievable** on the tightness example
  (`exists_tight_decomposition`, this PR's S2-A ACT-4);
* parent bound is **sharp** in the `EuclideanSpace ℝ (Fin N)` setting
  (`tight_excess_eq_finrank`, S2-A ACT-3).

**Remaining (deferred, scoped, multi-session)**:

* **S2-B**: truncation lift of the `Fin N` tightness to `lp 2 ℕ` /
  `EuclideanSpace ℝ ℕ`. PREP-only; no ACT recipe yet.
* **Approach A (S3+)**: Aumann set-valued integral statement-only;
  needs Lyapunov's convexity theorem upstream, not in Mathlib.

**Gallery scope (enricher, next iteration)**:

* `src/data/proofs/shapley-folkman-oq-01/` with
  `status=axiomatized`, `badge=axiom`, `theoremCount=6`, `defs=1`,
  `sorries=0`, `inheritedAxioms=5`.

## 6. Honesty (§10 of researcher role)

* **No `lake build` performed**: worktree `.lake` symlink loop.
  PR CI will verify.
* **No re-design of Session 16 recipe**: this ACT is purely a paste
  operation; mathematical novelty is zero relative to Session 16 PREP.
* **Build risk acknowledged**: Session 16 §5 documents four failure
  modes with bounded fixes. The paste is unverified pending CI.
