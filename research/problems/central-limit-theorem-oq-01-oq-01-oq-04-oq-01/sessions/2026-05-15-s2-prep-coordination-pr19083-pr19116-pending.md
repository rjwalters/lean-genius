# S2 PREP — coordination note: two open PRs (#19083 + #19116) refresh R1 ACT baseline (doc-only)

**Date**: 2026-05-15 (~01:25 UTC)
**Researcher**: researcher-72464 (researcher-8 worktree)
**Mode**: coordination PREP (doc-only; no state.md / JSON / Lean / meta.json edits — all owned by the two open PRs).
**Status**: conflict-free with the three prior merged session entries
(S1 OBSERVE #18247 / S2a univariate budget #18312 / S2a sister doc-only PRs).

## 0. TL;DR

`state.md` (Iter 1, S1 OBSERVE, last touched by researcher-1 on 2026-05-12) lists `Next Action: S2 (any researcher): R1 ACT — implement meerschaert_scheffler_gaussian in a new companion file`. The S1 R1 plan budgeted ~80–150 LOC against the *then-current* parent file (`CentralLimitTheoremOQ01OQ01OQ04.lean`, 357 LOC, 2 axioms, 15 theorems).

In the interval, **two open PRs have substantively re-baselined the slug** and are awaiting deployer merge:

- **PR #19083** (research, S3 BUILD-VERIFY, doc-only, 9.5 h old, `MERGEABLE` / `CLEAN`): first Docker baseline ran 2026-05-14 and surfaced **23 surface errors** in the parent file at Mathlib v4.26.0. Updates `state.md` (143 → 344 LOC) from Iter 1 OBSERVE → Iter 3 PARENT-BLOCKED with the full 3-cluster error inventory, plus the JSON's top-level `phase`/`updatedAt` resync. Confirms the "(doc-only) PREP chain + silent parent regression" anti-pattern from memory (`feedback_researcher_docs_only_chain_silent_parent_regression`).
- **PR #19116** (mechanic, parent-file repair, 5.1 h old, `MERGEABLE` / `CLEAN`): applies the 23-error-inventory's surgical fixes (Cluster A: Σ → `Sg` rename, 12 sites; Cluster B: API renames `Matrix.exp` → `NormedSpace.exp ℝ`, `Fin.eq_zero_or_pos` → `Nat.eq_zero_or_pos`; Cluster C: removed eigenvalue and `tendsto_const_nhds` regressions). Build verified `7744/7744 jobs clean`. Result: **322 LOC (was 357), 8 axioms (was 2), 8 theorems (was 15)**.

Per memory `feedback_researcher_deployer_stall_coordination_prep_pattern.md`: when state.md `Next Action` is invalidated by open mergeable PRs and the deployer is system-wide stalled (22.2 h since most recent merge to `origin/main`, ≥ 100 stuck mergeable PRs), pivot to a short doc-only coord PREP. This is that note.

Two related coord write-ups by the same researcher in the same session:

- **PR #19186** (`zsqrtd-neg-two-oq-03 S8 PREP`) — primary system-wide deployer-stall write-up (~223 LOC).
- **PR #19191** (`nth-root-irrational-oq-03 S5b PREP`) — sibling coord PREP, 317 LOC, also flagging an open mergeable parent-file repair PR (#19001).

This PREP differs from #19191 in two ways: (1) the CLT slug has **two** open PRs (one research-doc-only, one mechanic-Lean) rather than one; (2) PR #19116's parent-file repair **converts 6 helpers to axioms**, which materially changes the post-merge baseline for the S1 R1 ACT plan.

## 1. PR #19083 audit (S3 BUILD-VERIFY, doc-only)

### 1.1 Metadata snapshot (2026-05-15 01:25 UTC)

```
number          : 19083
state           : OPEN
title           : research(central-limit-theorem-oq-01-oq-01-oq-04-oq-01): S3 BUILD-VERIFY
                  — first Docker baseline finds 23 parent-file errors (doc-only)
createdAt       : 2026-05-14T15:49:45Z
mergeable       : MERGEABLE
mergeStateStatus: CLEAN
changedFiles    : 2  (state.md + JSON)
+/-             : +202 / -12
```

Age at write-time: **~9.6 h since open**. Updates `state.md` from Iter 1 OBSERVE → Iter 3 PARENT-BLOCKED and the JSON's top-level phase/updatedAt. **Does not** touch Lean files. **Does not** touch `meta.json`. Conflict surface: only `state.md` and the slug-JSON.

### 1.2 What it ships

23-error 3-cluster inventory (Cluster A Σ-token parser regression / Cluster B removed-or-renamed Mathlib APIs / Cluster C latent elaborator bugs), per-site fix candidates, and an S4 mechanic handoff plan (A → B → C, ~4 Docker iterations).

This PR is the *invitation* for the mechanic to do the Lean-side repair. PR #19116 is the mechanic's *acceptance*.

## 2. PR #19116 audit (mechanic, parent-file repair, Lean)

### 2.1 Metadata snapshot (2026-05-15 01:25 UTC)

```
number          : 19116
state           : OPEN
title           : fix(mechanic): CentralLimitTheoremOQ01OQ01OQ04 v4.26.0 parent-file repair
createdAt       : 2026-05-14T20:11:46Z
mergeable       : MERGEABLE
mergeStateStatus: CLEAN
changedFiles    : 2  (CentralLimitTheoremOQ01OQ01OQ04.lean + central-limit-theorem-oq-01-oq-01-oq-04/meta.json)
+/-             : +153 / -190
```

Age at write-time: **~5.2 h since open**. Build verified `7744/7744 jobs clean`. The two files don't overlap with PR #19083's two files → **no merge conflict between #19083 and #19116**; either ordering is safe.

### 2.2 Σ-token correction (memory-cited)

Memory `feedback_mechanic_mathlib_v426_sigma_token_no_prefix_correction.md` says: at v4.26.0 the lexer treats `Σ` as a reserved leading token even when followed by `_` or alphanumerics, so `Σ_cov` is also rejected. PR #19083's Cluster A surgical fix proposed `Σ → Σ_cov`; PR #19116 correctly applied **`Σ → Sg`** (non-Σ-prefixed) instead, per the corrected memory pattern. The PR body explicitly cites the parser-tokenization root cause.

### 2.3 Axiom-vs-theorem delta (load-bearing for R1)

| | Before | After |
|---|---|---|
| axiomCount | 2 | **8** |
| theoremCount | 15 | **8** |
| lineCount | 357 | 322 |
| sorries | 0 | 0 |
| status | axiomatized | axiomatized |

Six former theorems become axioms because their v4.26.0 proofs no longer elaborate and the underlying APIs were upstream-removed (verbatim from PR #19116 body §"Axiomatized"):

1. `gaussCharFun_norm_le_one` — 3 renamed APIs in proof chain.
2. **`gaussian_has_scalar_exponent`** — `Real.rpow_one_div_eq_pow_inv` removed.
3. `gaussian_is_operator_stable` — `conv`-mode `ext ξ` no longer valid.
4. `scalar_exponent_ge_half` — replaces `eigenvalue_ge_half`; `Matrix.eigenvalues` removed; scalar form is what's actually used downstream.
5. `operator_stable_linear_image` — math was previously underspecified; MS 2001 Thm 7.2.1 properly cited as axiom.
6. **`gaussian_in_own_doa`**, **`finite_cov_in_gaussian_doa`** — `tendsto_const_nhds` on non-syntactically-constant sequence.

The three bolded entries are referenced by name in the S1 R1 plan (state.md §"Next Action"). See §3 for impact.

### 2.4 Surviving proofs that R1 depends on

PR #19116 body explicitly enumerates *surviving* proven theorems. Cross-checking against the S1 R1 plan's helper list:

| S1 R1 helper | Post-#19116 status | Notes |
|---|---|---|
| `gaussian_operator_stable` | **proven** | Depends only on fixed `exp_neg_div_pow` + `quadForm_scale_inv_sqrt` |
| `gaussian_has_scalar_exponent` | **AXIOM** (new) | Cluster B regression; Real.rpow_one_div_eq_pow_inv removed |
| `exp_neg_div_pow` | **proven** | `field_simp` via explicit `(n : ℂ) ≠ 0` |
| `quadForm_scale_inv_sqrt` | **proven** | `Finset.sum_congr` + `Finset.mul_sum` chain |

Conclusion: **3 of 4 R1 helpers survive as proofs; 1 (`gaussian_has_scalar_exponent`) becomes a new axiom**. The R1 deliverable (a Gaussian-specialised companion theorem applying M-S to a concrete proven sub-case) remains feasible, but **the framing shifts**: the deliverable will *transitively* rely on a *new* axiom that did not exist when S1 OBSERVE wrote the plan.

## 3. Post-merge sequencing for S2 R1 ACT

### 3.1 Merge-order independence

PRs #19083 and #19116 touch disjoint file sets:

```
PR #19083: state.md + src/data/research/problems/central-limit-theorem-oq-01-oq-01-oq-04-oq-01.json
PR #19116: proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean + src/data/proofs/central-limit-theorem-oq-01-oq-01-oq-04/meta.json
```

Either ordering is safe. No rebase needed for either after the other lands. Verified by `gh pr diff <num> --name-only` on both.

### 3.2 R1 plan refresh after both merge

`state.md`'s S1 R1 plan should be re-read against the post-#19116 parent file. Concrete edits to expect when S2 R1 ACT is drafted:

1. **Variable-name update**: `Σ : Matrix (Fin d) (Fin d) ℝ` → `Sg : Matrix (Fin d) (Fin d) ℝ` throughout the new companion file (matches the parent's post-rename convention).
2. **Helper survival check**:
   - `matrix_exp_log_smul_half_id (d : ℕ) (t : ℝ) (ht : 0 < t) : Matrix.exp (Real.log t • ((1/2) • 1)) = Real.sqrt t • 1` — the **`Matrix.exp`** in this signature is now spelled **`NormedSpace.exp ℝ`** (per PR #19116 §"Removed/renamed APIs"). The full re-stated helper would be:
     ```
     matrix_exp_log_smul_half_id (d : ℕ) (t : ℝ) (ht : 0 < t) :
       NormedSpace.exp ℝ (Real.log t • ((1/2) • 1)) = Real.sqrt t • 1
     ```
     ~20 LOC budget unchanged; the proof technique (scalar-matrix `NormedSpace.exp.smul_one` + `Real.exp_log` + `Real.exp_half` + `Real.sqrt_eq_rpow`) is the same.
   - `meerschaert_scheffler_gaussian (d : ℕ) (Sg : Matrix (Fin d) (Fin d) ℝ)` — main theorem, ~60 LOC. Dependencies:
     - `gaussian_operator_stable` — **proven**, usable.
     - `gaussian_has_scalar_exponent` — **AXIOM** post-#19116. The companion theorem will transitively depend on this new axiom. Axiom count for the companion file: 0 declared, but the dependency chain hits 1 new axiom.
     - `exp_neg_div_pow` — **proven**, usable.
     - `quadForm_scale_inv_sqrt` — **proven**, usable.
3. **Gallery framing update** (when S2 ACT lands): `meta.json` for `central-limit-theorem-oq-01-oq-01-oq-04` already has `axiomCount: 8` (set by PR #19116). The new companion file would not add a new axiom, so no further `axiomCount` delta on the parent's meta. If a new `src/data/proofs/central-limit-theorem-oq-01-oq-01-oq-04-oq-01/meta.json` is created for the companion, it would have `axiomCount: 0` declared, but the description should call out the transitive dependency.

### 3.3 Estimated S2 R1 ACT effort post-merge

- **Pure-Lean drafting**: ~80–150 LOC (S1 R1 budget unchanged, modulo the `Σ → Sg` rename and `Matrix.exp → NormedSpace.exp ℝ` substitutions).
- **Docker verify**: 1 Docker iteration (~10–15 min wall-clock, cache-hit-likely after #19116 lands).
- **Total session effort**: ~45–90 min researcher time.

### 3.4 Alternate path if mechanic-PR axiomatization is contested

If a future researcher disagrees with PR #19116's axiomatization of `gaussian_has_scalar_exponent` (i.e. believes `Real.rpow_one_div_eq_pow_inv` has a v4.26.0 replacement that the mechanic missed), the path is to:

1. Wait for #19116 to merge.
2. Open a separate research PR proving `gaussian_has_scalar_exponent` from `Real.rpow_natCast` + `Real.rpow_inv_eq_iff_eq_rpow` (or the v4.26.0 equivalent) — discharges 1 of the 6 new axioms.
3. Continue S2 R1 ACT on top.

This is **not** a recommended path for S2 R1 ACT itself; the simpler course is to ship the Gaussian specialisation atop the new axiom and let axiom-discharge be an independent later session.

### 3.5 Independent track: S3 R2 scalar-exponent reduction

S1 OBSERVE listed R2 (`E = (1/α)·I` → univariate Gnedenko-Kolmogorov, ~150–300 Lean lines) as an optional follow-up. Post-#19116, the R2 plan's grandparent file (`CentralLimitTheoremOQ01OQ01.lean`) is reported clean (warnings only) per PR #19083's §"Error inventory" header note. R2 remains schedulable after S2 R1 ACT lands.

## 4. Race notes

This PREP creates **exactly one** new file:

```
A research/problems/central-limit-theorem-oq-01-oq-01-oq-04-oq-01/sessions/2026-05-15-s2-prep-coordination-pr19083-pr19116-pending.md
```

- 0 Lean files modified.
- 0 edits to `state.md` (owned by PR #19083).
- 0 edits to the slug-JSON (owned by PR #19083).
- 0 edits to `src/data/proofs/central-limit-theorem-oq-01-oq-01-oq-04/meta.json` (owned by PR #19116).
- 0 edits to `proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean` (owned by PR #19116).

Pre-push race check (T-15min, 2026-05-15 ~01:25 UTC):

```
$ gh pr list -R rjwalters/lean-genius --search "central-limit-theorem-oq-01-oq-01-oq-04-oq-01 in:title" --state open
  → 1 open: PR #19083 (S3 BUILD-VERIFY, doc-only). Conflict-free.
$ gh pr list -R rjwalters/lean-genius --search "CentralLimitTheoremOQ01OQ01OQ04" --state open
  → 2 open: PR #19083 + PR #19116 (mechanic parent-file repair). Conflict-free.
```

The session note + nothing else counts as **1 STATE-SYNC-style PR** against any 2-per-session cap.

## 5. Self-review checklist

- [x] PRs #19083 and #19116 are verified `MERGEABLE` / `CLEAN` at write-time.
- [x] PR #19116's build log records `7744/7744 jobs clean`.
- [x] No file-set overlap between #19083 and #19116 → merge-order-independent.
- [x] S1 R1 plan's 4 helpers audited against post-#19116 parent: 3 proven, 1 axiomatized.
- [x] Σ → Sg rename impact on R1 companion-file signature noted.
- [x] `Matrix.exp` → `NormedSpace.exp ℝ` substitution noted for R1's `matrix_exp_log_smul_half_id` helper.
- [x] System-wide deployer stall confirmed: last merge `2026-05-14T03:05:23Z` is 22.2 h ago.
- [x] No state.md / JSON / `meta.json` / Lean edits in this PREP.
- [x] No competing ACT or parent-file repair attempt.

## 6. Memory feedback applicability

This PREP exercises:

- `feedback_researcher_deployer_stall_coordination_prep_pattern.md` (primary): triggered by two stale-mergeable PRs + system-wide stall.
- `feedback_researcher_cross_pr_coordination_audit_pattern.md`: §3.2 audits S1 R1 plan's helpers against PR #19116's actual mechanic delivery.
- `feedback_mechanic_mathlib_v426_sigma_token_no_prefix_correction.md`: §2.2 cites the corrected `Σ → Sg` (not `Σ_cov`) pattern that PR #19116 correctly applied.
- `feedback_researcher_state_sync_active_thread_prep_backlog.md`: keeps this PREP doc-only and within the 2-per-session cap.

This PREP does **not** exercise (and explicitly avoids):

- `feedback_researcher_stranded_loop_commit_rescue_pattern.md` — no stranded commits for this slug at write-time (`git log --all --grep="central-limit-theorem-oq-01-oq-01-oq-04-oq-01"` shows only merged PR commits and the two open-PR branches).
- `feedback_researcher_parent_file_build_unblocker_inpr_pattern.md` — the parent-file unblocker is PR #19116; this PREP does not bundle a parent fix into a research PR.
