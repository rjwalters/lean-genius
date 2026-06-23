# S5 PREP — Bridge build-verify forecast post-#19118 mechanic merge (doc-only)

**Date**: 2026-05-15 (PDT 2026-05-14 evening; UTC 2026-05-15)
**Researcher**: researcher-9 (claim `researcher-20585`, knowledge score 17 / RICH)
**Phase**: PREP (forecast for the build-verify state transition after mechanic PR #19118 merges)
**Builds on**:
- PR #18915 (S2 ACT — `rh_canonical_iff_pnt` bridge theorem, build pending, researcher-4, 2026-05-13)
- PR #18943 (S3 PREP — `zeta_conj` Schwarz-reflection bearer audit, researcher-5, 2026-05-13, MERGED)
- PR #19007 (S3 STATE-SYNC — log #18943 in state.md/JSON, researcher-9 prev session, 2026-05-14, **OPEN**)
- PR #19115 (S4 BUILD-DIAGNOSTIC — 4-error parent v4.26.0 regression + verified 1-LOC fix, **OPEN**)
- PR #19118 (mechanic fix — `Nonvanishing` import + `hs.ge` for `le_of_eq`, build-verified 3292 jobs, **OPEN**)

**Mathlib pin**: `proofs/lake-manifest.json` → mathlib4 SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).

**Scope**: doc-only memo in `sessions/`. **No edits** to `state.md`, JSON, `problem.md`, `knowledge.md`, any `.lean` file, or any previously-tracked file. Conflict-free with all three open PRs: #19007 owns `state.md` + JSON; #19115 owns its own `sessions/` file; #19118 owns parent `.lean`. This PREP touches only one **new** filename under `sessions/`.

## §0 — TL;DR

After PR #19118 (mechanic, parent file +1 import +1 LOC) merges, the slug-owned bridge file `proofs/Proofs/PrimeNumberTheoremOQ01OQ01.lean` (S2 ACT, "build pending" since 2026-05-13) **auto-becomes build-verified with zero further edits**. Both identifiers it consumes from the parent — `PrimeNumberTheoremOQ01.RiemannHypothesis` (def) and `PrimeNumberTheoremOQ01.rh_iff_re_half` (theorem) — have **signatures unchanged** by the mechanic fix; the fix only adds a transitive import and rewrites a single proof body (`no_zeros_on_line_one`, unused by the bridge).

S3 ACT (Schwarz-reflection discharge of `zeta_conj` axiom) remains the next slug-internal Lean target after the three open PRs land; this PREP does not advance that thread (the two open bearer audits from S3 PREP §1.1 / §1.2 still need resolution under live `gh api search/code`, which is rate-limit-exhausted at memo creation).

## §1 — The bridge file (signature-stable across #19118)

`proofs/Proofs/PrimeNumberTheoremOQ01OQ01.lean` (60 LOC, 0 axioms, 0 sorries, build pending since S2 ACT PR #18915):

```lean
import Proofs.RiemannHypothesis
import Proofs.PrimeNumberTheoremOQ01

namespace PrimeNumberTheoremOQ01OQ01

theorem rh_canonical_iff_pnt :
    RiemannHypothesis.RiemannHypothesis ↔ PrimeNumberTheoremOQ01.RiemannHypothesis :=
  RiemannHypothesis.RH_alt.trans PrimeNumberTheoremOQ01.rh_iff_re_half.symm

theorem rh_pnt_iff_canonical :
    PrimeNumberTheoremOQ01.RiemannHypothesis ↔ RiemannHypothesis.RiemannHypothesis :=
  rh_canonical_iff_pnt.symm

end PrimeNumberTheoremOQ01OQ01
```

**Parent identifiers consumed** (exhaustive list via `grep`):

| Identifier | Kind | Parent file location (pre-#19118) | Parent file location (post-#19118) | Signature delta |
|---|---|---|---|---|
| `PrimeNumberTheoremOQ01.RiemannHypothesis` | `def` | `PrimeNumberTheoremOQ01.lean:69-70` | `:70-71` | **unchanged** (+1-line drift from import) |
| `PrimeNumberTheoremOQ01.rh_iff_re_half` | `theorem` | `PrimeNumberTheoremOQ01.lean:73-79` | `:74-80` | **unchanged** (+1-line drift) |

The mechanic fix's two-LOC diff (from `gh pr diff 19118`) touches **only** the import block (line 1-2) and the `no_zeros_on_line_one` proof body at the old line 98 / new line 99 (`le_of_eq hs` → `hs.ge`). Neither modification affects the def `RiemannHypothesis` nor the theorem `rh_iff_re_half`.

## §2 — Bridge's parent-import chain at v4.26.0

The bridge does `import Proofs.PrimeNumberTheoremOQ01`. After PR #19118 merges, the parent file pulls:

| Parent import line | Module | Why |
|---|---|---|
| 1 | `Mathlib.NumberTheory.LSeries.RiemannZeta` | `riemannZeta` def + `riemannZeta_zero` + functional eq stubs |
| **2 (new)** | **`Mathlib.NumberTheory.LSeries.Nonvanishing`** | **`riemannZeta_ne_zero_of_one_le_re` (line 411 in module at SHA `2df2f015…`)** |
| 3 | `Mathlib.NumberTheory.PrimeCounting` | `Nat.primeCounting` for the asymptotic statements |
| 4-7 | analysis + measure-theory dependencies | unaffected |

`Mathlib.NumberTheory.LSeries.Nonvanishing.lean` at pin SHA `2df2f015…` line 6 reads `public import Mathlib.NumberTheory.LSeries.Dirichlet` (verified live via `gh api repos/leanprover-community/mathlib4/contents/Mathlib/NumberTheory/LSeries/Dirichlet.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`), so the single import addition makes both lemmas reachable transitively for the parent. The bridge, which `import`s the parent, sees `Nonvanishing` transitively as well — though it never references `riemannZeta_ne_zero_of_*` directly.

**No new bridge-direct imports needed**: the bridge's two-line theorem body only invokes `RH_alt.trans rh_iff_re_half.symm`, both of which type-check based on the `Iff` structure of `rh_iff_re_half` (parent line 73-79). No zeta non-vanishing lemma appears in the bridge's elaboration goal.

## §3 — Transitive build-closure forecast

When `proofs/lakefile.toml` triggers `lake build Proofs.PrimeNumberTheoremOQ01OQ01`, Lake builds the closure:

```
Proofs.PrimeNumberTheoremOQ01OQ01
├─ Proofs.RiemannHypothesis           ← already clean per PR #19115 ("⚠ [3317/3318] Built Proofs.RiemannHypothesis (7.2s)")
└─ Proofs.PrimeNumberTheoremOQ01      ← FAILS pre-#19118 (4 errors at lines 88/94/98/275); clean post-#19118 ("3292/3292 jobs, 3.2s")
   └─ Mathlib.NumberTheory.LSeries.Nonvanishing ← new transitive import (post-#19118)
   └─ Mathlib.NumberTheory.LSeries.Dirichlet    ← reached via Nonvanishing.public import
```

Pre-#19118: the bridge cannot build because the parent `.olean` is unavailable (parent has 4 errors).
Post-#19118: parent `.olean` builds clean → bridge `.olean` builds clean (the bridge's own elaboration has zero v4.26.0 risk; it predates v4.26.0 only by ~12 hours but uses only `Iff.trans` and `.symm`, which are entirely stable across Mathlib versions).

**Build-verified post-#19118 (forecast)**: `Proofs.PrimeNumberTheoremOQ01OQ01` will produce a green build with **exactly 1 new job** added on top of #19118's 3292 → **3293 jobs total** for the targeted `lake build Proofs.PrimeNumberTheoremOQ01OQ01` invocation, with `Proofs.PrimeNumberTheoremOQ01OQ01` being job 3293.

Numerical refinement: PR #19115's baseline run reported `[3317/3318]` total — the difference vs. #19118's `3292` is that #19115 targeted `Proofs.PrimeNumberTheoremOQ01OQ01` (pulling `Proofs.RiemannHypothesis` ≈ 4000 LOC, +26 jobs) while #19118 targeted `Proofs.PrimeNumberTheoremOQ01` (no RiemannHypothesis pull). Final expected job count for a targeted `lake build Proofs.PrimeNumberTheoremOQ01OQ01` post-#19118: **~3319 (3318 from #19115 + 1 if `RiemannHypothesis`-side has any drift; 0 if not)**.

## §4 — Cross-PR coordination + sequencing

Three open PRs touch this slug or the parent slug:

| PR | Slug | Files | Mergeable? | Status |
|---|---|---|---|---|
| #19007 | this slug | `state.md`, slug JSON | yes | OPEN (S3 STATE-SYNC) |
| #19115 | this slug | `sessions/<new>.md` | yes | OPEN (S4 BUILD-DIAGNOSTIC) |
| #19118 | parent slug `prime-number-theorem-oq-01` | `proofs/Proofs/PrimeNumberTheoremOQ01.lean` | yes | OPEN (mechanic fix, 3292 jobs) |

**File-overlap matrix** (none overlap):

| | #19007 | #19115 | #19118 | this PREP (#???) |
|---|---|---|---|---|
| `state.md` | ✓ | — | — | — |
| slug JSON | ✓ | — | — | — |
| `sessions/2026-05-14-s4-build-diagnostic-…` | — | ✓ | — | — |
| `sessions/2026-05-15-s5-prep-…` (this) | — | — | — | ✓ |
| `proofs/Proofs/PrimeNumberTheoremOQ01.lean` | — | — | ✓ | — |

All four PRs (#19007, #19115, #19118, and this) are pairwise conflict-free at the file level and can land in any order.

**Recommended merge order** (minimum-friction, doctor or champion):

1. **#19118 first** (mechanic fix). Build-verified at 3292 jobs. Unblocks parent slug + cascades to this slug's bridge.
2. **#19115 second** (BUILD-DIAGNOSTIC). Pure doc; explains why #19118 exists; references the verified fix.
3. **#19007 third** (STATE-SYNC). Catches state.md/JSON up after #18943 merged and before/after #19115 + #19118 cascade.
4. **This PREP fourth** (build-verify forecast). References #19118's merge as a precondition; documents the bridge's auto-clean status.

After all four land, this slug's `state.md` should next jump to iter 5 / phase "ACT (S3 ACT pending — Schwarz reflection)" — but that's S6 STATE-SYNC scope, not this PREP.

## §5 — Why this PREP does not advance the S3 ACT thread

S3 PREP (PR #18943, §1.1 + §1.2) left two bearer audits open:

- **R-4 preconnectedness of `ℂ \ {1}`**: candidate names `Set.preconnected_compl_of_singleton` / `IsPreconnected.compl_singleton` were 0-hits at S3 PREP authoring; route via `IsPathConnected.isPreconnected` + piecewise-linear path witness (~10-15 LOC).
- **R-3 holomorphy of `g := star ∘ riemannZeta ∘ star`**: `starRingEnd ℂ` is `ℂ`-antilinear; no canonical "antilinear ∘ holomorphic ∘ antilinear = holomorphic" lemma in Mathlib v4.26.0 per S3 PREP probe; ~20-30 LOC manual Fréchet derivative work.

Resolving either would require **fresh** `gh api search/code` calls to scan Mathlib's connected/path-connected and antilinear-derivative APIs at the pinned SHA. At memo authoring (2026-05-15T01:13 UTC), this token's `code_search` bucket reads `0 / 10` remaining (reset at 2026-05-15T01:50 UTC), so a definitive bearer survey for R-3 / R-4 is **deferred to the next S5 PREP-2 or S6 PREP session** when the rate limit window is fresh.

This memo's scope is strictly the bridge build-verify forecast — a no-API-needed analysis from local files only.

## §6 — Risk register for the build-verify forecast (low-risk)

| # | Risk | Likelihood | Mitigation |
|---|---|---|---|
| F-1 | Mechanic PR #19118 fails to merge (rebase conflict, review-requested label, etc.) | Low (currently `MERGEABLE`, no review-requested label) | Bridge stays "build pending"; this PREP's forecast holds the moment #19118 lands |
| F-2 | Bridge has latent compilation issue independent of parent (e.g., `RH_alt` signature drift in `RiemannHypothesis.lean`) | Very low — `RH_alt` is at line 132 with stable `(∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1/2)` signature; same target as `rh_iff_re_half` | Read `Proofs/RiemannHypothesis.lean:132-140` confirms signature stability |
| F-3 | Lake build cache invalidation causes spurious failures | Low | Per CLAUDE.md, use `./proofs/scripts/docker-build.sh Proofs.PrimeNumberTheoremOQ01OQ01` (Docker-isolated environment, cold cache from Mathlib pin) |
| F-4 | Cross-slug import cycle introduced by mechanic fix | Zero | `Mathlib.NumberTheory.LSeries.Nonvanishing` is a Mathlib module, not a slug-owned one; no cycle possible |
| F-5 | A sibling slug's `.lean` file uses `riemannZeta_ne_zero_of_one_*_re` without importing `Nonvanishing` (latent sibling regression) | Audited: see §7 | No fix in this PREP; see §7 for the audit table |

## §7 — Sibling-regression audit (in-tree `riemannZeta_ne_zero_of_one_*_re` consumers)

`grep -rn "riemannZeta_ne_zero_of_one_lt_re\|riemannZeta_ne_zero_of_one_le_re" proofs/Proofs/` returns 8 files. Per the v4.26.0 lemma locations (`Nonvanishing.lean:411` for `_le_re`, `Dirichlet.lean:325` for `_lt_re`):

| File (slug) | Uses `_le_re`? | Uses `_lt_re`? | Direct `Nonvanishing` import? | Direct `Dirichlet` import? | Transitive route present? | Verdict |
|---|---|---|---|---|---|---|
| `RiemannHypothesis.lean` (parent slug) | yes (lines 506, 531) | yes (line 182, 567) | yes (line 3) | yes (line 4) | n/a | clean |
| `RiemannHypothesisConsequences.lean` | yes (line 367) | yes (lines 336) | yes | yes | n/a | clean |
| `GeometricSeriesOQ03.lean` (slug `geometric-series-oq-03`) | no | yes (line 213) | no | no | yes — via `EulerProduct.DirichletLSeries.lean` `public import …Dirichlet` (verified at pin) | clean |
| `PrimeNumberTheoremOQ01.lean` (parent slug, **broken pre-#19118**) | yes (lines 94, 275) | yes (line 88) | no (pre-#19118) | no | no (no DirichletLSeries route) | **broken** — #19118 fix |
| `TestZetaNonzero.lean` | yes (line 90) | yes (line 26) | yes (line 4) | no | via Nonvanishing→Dirichlet | clean |
| `TestZeroStrip.lean` | check (`#check @riemannZeta_ne_zero_of_one_le_re`) | n/a | yes (line 3) | no | via Nonvanishing→Dirichlet | clean |

**Conclusion**: `PrimeNumberTheoremOQ01.lean` is the **only** in-tree file with the regression. PR #19118's surgical scope is correct. No sibling-regression follow-up mechanic kit needed.

`GeometricSeriesOQ03.lean` is initially-suspicious (uses `_lt_re` with only the `RiemannZeta` direct import) but **clean** by virtue of its `Mathlib.NumberTheory.EulerProduct.DirichletLSeries` import, whose v4.26.0 source begins `public import Mathlib.NumberTheory.EulerProduct.ExpLog` and `public import Mathlib.NumberTheory.LSeries.Dirichlet` (verified at pin SHA `2df2f015…`).

## §8 — Post-merge action checklist (for whoever lands these PRs)

1. **After #19118 lands**: invoke `./proofs/scripts/docker-build.sh Proofs.PrimeNumberTheoremOQ01OQ01` to confirm the bridge auto-clean (forecast: ~3319 jobs).
2. **After #19115 + #19118 land**: this PREP's §3 forecast becomes verifiable; recommend a 1-line state.md status flip from "build pending" → "build verified, 3319 jobs, post-#19118".
3. **After #19007 lands**: this PREP's footer reference to `state.md @ iter 3` is current.
4. **Next iter target (post-all-4)**: S3 ACT — Schwarz reflection discharge of `zeta_conj` axiom in `proofs/Proofs/RiemannHypothesis.lean:779`, per S3 PREP recipe (~80-120 LOC, R-3 + R-4 audits pending fresh `gh api search/code`).

**Recommended doctor / champion attention**: PR #19118 is the load-bearing fix. The other two open PRs (#19007 STATE-SYNC, #19115 BUILD-DIAGNOSTIC) are documentation that can land in any order without affecting build state.

## §9 — Coordination notes

- **No race on this slug** at PREP authoring: only 3 OPEN PRs (#19007, #19115, both author-friendly with this slug; #19118 on parent slug). This PREP adds only one new `sessions/` file, zero shared-file overlap.
- **No race on parent slug**: PR #19118 is the only OPEN mechanic on `prime-number-theorem-oq-01` parent at memo creation; this PREP does not edit any file on the parent slug.
- **Mathlib lake pin**: `proofs/lake-manifest.json` rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Two file fetches verified live during memo authoring:
  - `Mathlib/NumberTheory/LSeries/RiemannZeta.lean` — confirmed `riemannZeta_ne_zero_of_one_lt_re` NOT defined here (only the `riemannZeta` def + `HurwitzZeta` + `PSeriesComplex` `public import`s);
  - `Mathlib/NumberTheory/LSeries/Dirichlet.lean` — confirmed `riemannZeta_ne_zero_of_one_lt_re` at line 325 (regression-fix bearer for PR #19118's import addition).
- **`gh api search/code` rate-limit status at authoring**: `0 / 10` remaining for this token (reset 2026-05-15T01:50 UTC); `core` bucket fresh at `4951 / 5000`. R-3 / R-4 bearer audits deferred to a future session with a fresh rate-limit window.
- **Branch policy**: fresh `research/pnt-oq01-oq01-s5-prep-bridge-buildverify-forecast-1778799647` cut from `origin/main` via `git checkout -b … origin/main` inside this worktree.
- **Session cap status**: researcher-9 (this session) had one prior misfire — see §10. This PREP is the first ship of the session.

## §10 — Session prelude (transparency note)

This researcher-9 session began with two false-positive "stranded commit" rescue attempts caused by `gh pr list --search` returning `[]` due to the worktree's `gh` CLI default-repo drift (documented at memory `feedback_researcher_gh_default_repo_mathlib4_fork_trap.md`). The two false-positive rescue branches were:

- `research/shapley-folkman-oq01-s9-rescue-1778799647` → opened PR #19185 → discovered duplicate of OPEN PR #19003 → closed #19185 + deleted remote branch.
- `research/minkowski-oq02-oq03-rescue-1778799647` → cherry-pick of 3 commits → discovered all 3 had open PRs (#18991, #19046, #19181) → aborted before push, released claim.

The memory note `feedback_researcher_gh_default_repo_mathlib4_fork_trap.md` was updated with a confirmation entry for this incident.

This PREP is the first non-misfire deliverable of the session and uses `--repo rjwalters/lean-genius` on all gh-CLI invocations to avoid recurrence.
