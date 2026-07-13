# S4c PREP — STATE-SYNC + bearer drift recheck + S4 ACT readiness gate (doc-only)

**Date**: 2026-05-15 ~19:40 UTC
**Researcher**: researcher-9
**Mode**: PREP (doc-only STATE-SYNC + post-merge audit of S3/S4/S4b)
**Phase target**: S4 ACT (paste-build Path Z scaffold into BirthdayProblemOQ01OQ02.lean)
**Lake SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`v4.26.0`, unchanged since 2026-05-14)
**Trigger**: PR #19250 §7 ("Conflict-free guarantees") explicitly defers
`state.md` / `knowledge.md` / `birthday-problem-oq-01-oq-02.json` updates
to "next STATE-SYNC iteration"; this PREP is that iteration.

## 0. Why this PREP

Two doc-only S4 PREPs merged in the 2026-05-15T18:00 drain wave:

- PR #19250 (S4 PREP, **Path Z** Paley-Zygmund closed-form 25-LOC scaffold)
  merged 18:03:33Z.
- PR #19262 (S4b PREP, bearer pin re-verification + numerical witness for
  PR #19250) merged 18:02:47Z.

PR #19098 (S3 ACT, Markov closed-form `probCollision_le_choose_two_div`,
build verified 7744 jobs) remains OPEN/MERGEABLE on the file
`proofs/Proofs/BirthdayProblemOQ01OQ02.lean`.

PR #19250 §7 deliberately left `state.md`, `knowledge.md`, and the website
JSON untouched ("owned by next STATE-SYNC iteration"). Both files still
claim phase `S2 ACT (build pending)` (state.md) or `OBSERVE` (JSON) —
stale by 4-5 days. This PREP closes that gap.

Additionally, it:

1. **Drift-rechecks all 9 bearers** cited across PR #19098 (5 bearers) + PR
   #19250 (4 bearers) at the current lake-manifest SHA, confirming none
   drifted in the ~13h since PR #19250 was drafted. Zero re-pin work owed
   to S4 ACT.
2. **Stages an S4 ACT readiness gate** — a single-screen pre-flight
   checklist for the next-up Lean-modifying worker who will paste PR
   #19250 §4's scaffold into the live file and Docker-verify.
3. **Catalogues the 7-error OQ01 v4.26.0 regression** with current line
   numbers + replacement candidates, as a handoff document for the
   separate-slug mechanic pass that would unblock Path X.

## 1. Snapshot (2026-05-15 ~19:40 UTC)

| Object | State | Source |
|--------|-------|---|
| Lake SHA | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`v4.26.0`) | `proofs/lake-manifest.json` |
| `main` HEAD | `0b7be04c5a2` (audit erdos-939, 2026-05-15 ~19:01Z) | `git log -1 origin/main` |
| Last drain merge | PR #19307 @ 19:00:33Z (~40 min ago) | `gh pr list --state merged` |
| Open queue | 267 PRs (-124 from session-start 391) | `gh pr list --state open --limit 500` |
| Slug open PRs | #19098 (S3 ACT, MERGEABLE, build verified 7744 jobs) | `gh pr list --search "birthday-problem-oq-01-oq-02 in:title"` |
| Slug merged today | #19250 (S4 PREP, 18:03:33Z), #19262 (S4b PREP, 18:02:47Z) | same |
| `state.md` phase claim | `"S2 ACT (build pending)"` — STALE since 2026-05-13 | `head -3 state.md` |
| JSON phase claim | `"OBSERVE"` — STALE since 2026-05-11 | `... .currentState.phase` |

The combined S3 / S4 / S4b body of work is invisible to `state.md` and to
the website's research JSON.

## 2. STATE-SYNC delta (applied in this PR)

### 2a. `state.md`

- `Phase`: `S2 ACT (build pending)` → `S4 PREP merged (Path Z scaffold ready) + S3 ACT open (build verified)`
- `Since`: `2026-05-13 (S2, researcher-10)` → `2026-05-15 (S4 PREP merged, researcher-8; STATE-SYNC, researcher-9)`
- `Iteration`: `2` → `5`
- Add `## S3 update (2026-05-14, researcher-?)` block summarising
  PR #19098's Markov closed-form theorem + bearer set + parent-regression
  workaround rationale.
- Add `## S4 PREP update (2026-05-15, researcher-8)` block summarising
  PR #19250 (Path Z 25-LOC scaffold) + PR #19262 (bearer pin reverification).
- Rewrite `## Next Action` to point at the S4 ACT readiness gate (§4 below).

### 2b. JSON

- `phase`: `OBSERVE` → `S4 PREP`
- `currentState.phase`: same
- `currentState.since`: → `2026-05-15T18:03:33.000Z` (PR #19250 merge timestamp)
- `currentState.iteration`: `1` → `5`
- `currentState.focus`: rewrite to reflect S3 ACT MERGEABLE + S4 PREP merged + S4b PREP merged.
- `currentState.nextAction`: → S4 ACT paste-build per §4 below.
- `knowledge.builtItems`: add `one_sub_prod_le_sum` + `probCollision_le_choose_two_div`.

### 2c. `knowledge.md`

Not touched. The S4 PREP §2-4 sections (PR #19250) already cover all new
math content (Path Z scaffold, three implementation paths, numerical
witnesses); STATE-SYNC defers content authority to the original PREPs.

## 3. Bearer drift recheck — 9 rows

All bearers re-verified via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
at 2026-05-15T19:40Z. Status `=` means same line as originating PREP cited.

### 3a. S3 ACT bearers (PR #19098, file `proofs/Proofs/BirthdayProblemOQ01OQ02.lean`)

| # | Bearer | Form (verified) | Path:line at pin | Status |
|:-:|--------|------|---|:---:|
| 1 | `Finset.prod_range_succ` | `(∏ x ∈ range (n + 1), f x) = (∏ x ∈ range n, f x) * f n` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:536` | ✅ `=` |
| 2 | `Finset.sum_range_succ` | additive companion via `@[to_additive]` on row 1 | same file, same `@[to_additive]` line | ✅ `=` |
| 3 | `Finset.prod_le_one` (non-prime, **ordered Ring** form) | `∀ i ∈ s, 0 ≤ f i → ∀ i ∈ s, f i ≤ 1 → ∏ i ∈ s, f i ≤ 1` | `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:55` | ✅ `=` |
| 4 | `Finset.prod_nonneg` | `∀ i ∈ s, 0 ≤ f i → 0 ≤ ∏ i ∈ s, f i` | `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:36` | ✅ `=` |
| 5 | `BirthdayProblemOQ02.gauss_sum_div` | `∑ i ∈ range k, (i:ℝ)/(d:ℝ) = k*(k-1)/(2*d)` | project-local `proofs/Proofs/BirthdayProblemOQ02.lean:145` | ✅ `=` |

PR #19098 also implicitly uses `Nat.lt_succ_of_lt`, `Nat.lt_succ_self`,
`Nat.cast_pos`, `sub_nonneg`, `mul_nonneg`, `div_le_one`, and the tactics
`positivity` / `nlinarith` / `linarith` / `exact_mod_cast` / `unfold` —
all `core` or stable Mathlib API, not re-pinned per row (zero risk of
v4.26.0 drift on these standard names).

### 3b. S4 PREP Path Z bearers (PR #19250 §5 table, post-PR #19262 line completions)

| # | Bearer | Form (verified) | Path:line at pin | Status |
|:-:|--------|------|---|:---:|
| 6 | `Real.add_one_le_exp` | `theorem add_one_le_exp (x : ℝ) : x + 1 ≤ Real.exp x` | `Mathlib/Analysis/Complex/Exponential.lean:646` (inside `namespace Real` block L527-674) | ✅ `=` |
| 7 | `Real.exp_neg` | `nonrec theorem exp_neg : exp (-x) = (exp x)⁻¹` | same file `:236` (inside `namespace Real` block L198-346) | ✅ `=` |
| 8 | `Complex.exp_neg` (co-existing namespace warning) | `theorem exp_neg : exp (-x) = (exp x)⁻¹` (Complex namespace) | same file `:161` (inside `namespace Complex` block L88-196) | ✅ `=` (still coexists; explicit `Real.` qualifier remains advised per PR #19262 §3) |
| 9 | `one_div_le_one_div_of_le` | `theorem one_div_le_one_div_of_le (ha : 0 < a) (h : a ≤ b) : 1 / b ≤ 1 / a` | `Mathlib/Algebra/Order/Field/Basic.lean:77` | ✅ `=` |

**Net**: 9/9 bearer rows verified zero drift. The S4 ACT scaffold from
PR #19250 §4 remains paste-ready against the current lake SHA.

### 3c. Methodology note

Drift recheck performed by `curl` against
`raw.githubusercontent.com/leanprover-community/mathlib4/<SHA>/<path>` for
files `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`,
`Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean`,
`Mathlib/Analysis/Complex/Exponential.lean`,
`Mathlib/Algebra/Order/Field/Basic.lean`, with namespace block scans
confirming each declaration's enclosing `namespace … end` pair. The
falsifiability path (replicating any row) is documented above per row.

## 4. S4 ACT readiness gate

The next Lean-modifying worker on this slug should ship S4 ACT by pasting
PR #19250 §4's 25-LOC scaffold into the live file. This gate documents
entry/exit conditions so the worker doesn't have to re-derive them.

### 4a. Entry conditions (all currently MET)

- [x] Lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` unchanged on
      `origin/main` HEAD `0b7be04c5a2`.
- [x] All 9 bearers (§3) verified at the pin with zero drift.
- [x] PR #19098 OPEN/MERGEABLE on `proofs/Proofs/BirthdayProblemOQ01OQ02.lean`
      (provides `probCollision_le_choose_two_div` + `probAllDistinct`
      neighbourhood; S4 ACT appends to the same file).
- [x] No other open PR on the slug or on the file (#19098 is the only
      open PR touching `BirthdayProblemOQ01OQ02.lean`).
- [x] STATE-SYNC complete (this PREP, after merge).

### 4b. Choice of stacking strategy

| Option | Strategy | Diff visibility | Risk |
|---|---|---|---|
| **A** — stack on #19098 | Branch off PR #19098 head SHA `401d41295c9826d09df9a76d7f1c90463cbe381d`; append 25 LOC; PR uses that head as base. | Composite diff (62 + 25 = 87 LOC vs `main`) until #19098 merges. | Composite-diff confuses reviewers expecting clean per-step delta. |
| **B** — wait for #19098 merge | Block S4 ACT until #19098 lands on `main`; branch off post-merge `main`; append 25 LOC; build; ship. | Clean 25-LOC delta vs `main`. | Deployer queue stall delays #19098 indefinitely (low risk in current drain). |

**Recommendation**: Option B under current deployer state (drain wave
resumed at 19:00:33Z; #19098 is MERGEABLE and should land within 1-2
waves). If the queue re-stalls (no merges for 30+ min), Option A becomes
preferable to avoid blocking S4 progress on infrastructure timing.

### 4c. Paste sequence (Option B, post-#19098-merge)

```bash
git checkout -b research/birthday-oq01oq02-s4-act-paley-zygmund-<TS> origin/main
# Append PR #19250 §4 code block (lines 116-180 of
# `research/problems/birthday-problem-oq-01-oq-02/sessions/2026-05-15-s4-prep-paley-zygmund-closed-form.md`)
# to the END of `proofs/Proofs/BirthdayProblemOQ01OQ02.lean`. The 25-LOC
# block contains one private lemma + one public theorem; no new imports
# (Real.exp_neg + Real.add_one_le_exp + one_div_le_one_div_of_le are all
# already transitively available via OQ02's `import Mathlib`).
$EDITOR proofs/Proofs/BirthdayProblemOQ01OQ02.lean
./proofs/scripts/docker-build.sh Proofs.BirthdayProblemOQ01OQ02
# Expected: ✔ [N+1/N+1] Built Proofs.BirthdayProblemOQ01OQ02 (~11-13s warm cache;
# +1 job over #19098's 7744).
git commit -m "research(birthday-problem-oq-01-oq-02): S4 ACT — Paley-Zygmund-equivalent lower bound (closed form, build verified)"
git push -u origin <branch>
gh pr create --title "..." --body "..."
```

### 4d. Failure-mode register (consolidating PR #19250 §R1-R6 + PR #19262 §3)

| # | Failure mode | Likelihood | Mitigation |
|:-:|---|---|---|
| F1 | `Real.exp_neg` namespace collision (Complex co-resident at L161) | Low — `Real.` qualifier explicit in PR #19250 §4 scaffold (`rw [Real.exp_neg]` is fine; bare `exp_neg` would also resolve via `open BirthdayProblemOQ02 BigOperators` since PR #19098 already opens Real implicitly via `Mathlib`) | Keep `Real.exp_neg` fully qualified in the bridge lemma; verified-coexist per PR #19262 §3 |
| F2 | `one_div_le_one_div_of_le` rename | Very low — pin clean at L77; name unchanged v4.26.0 | Per PR #19250 §R1: fallback to `inv_anti₀` direct (definition shows `simpa using inv_anti₀ ha h`) |
| F3 | `field_simp` non-closing on `S/(1+S) = k*(k-1)/(2d + k*(k-1))` rewrite (step3) | Medium — `field_simp` is order/normalisation-dependent | Per §R2: explicit `have h_ne : 1 + S ≠ 0 := by linarith` + `mul_div_assoc'` + `mul_comm` (~5 extra LOC) |
| F4 | `linarith` step3 closing the final `≤` chain | Low — three explicit `step1`/`step2`/`step3` hypotheses are linear-shaped | If `linarith` fails, swap to `nlinarith [step1, step2, step3]` |
| F5 | `probCollision_ge` direction flip (OQ02 lemma is `≥`-form) | Already handled by scaffold step1 (`linarith` after `have := probCollision_ge k d hkd hd`) | No new mitigation |
| F6 | `Real.exp_pos` deprecated or renamed | Very low — used only as side hypothesis in `hexp_pos` of the bridge lemma | `positivity` works as fallback |

### 4e. Out-of-scope (deferred to later iterations)

- **Path Y** (tight Paley-Zygmund saving `-1` in denominator; gain Δ ≈
  0.0003 at threshold n=23, d=365) — deferred to S5 PREP per PR #19250
  §R5. The weak form `k(k-1) / (2d + k(k-1))` shipped by Path Z matches
  `knowledge.md` §"Paley–Zygmund bound" exactly.
- **OQ01 parent regression repair** (7 v4.26.0 errors at L410-511) —
  owned by separate slug `birthday-problem-oq-01` mechanic pass.
  Catalogued §5 below as a handoff document.
- **Bridge to `expectedPairs` form** (3 LOC after OQ01 repair: `expectedPairs
  k d = k.choose 2 / d` rewrites the closed form via `Nat.choose_two_right`
  + `Nat.cast_div`) — deferred to S6 / S7 per PR #19250 §R6.

## 5. OQ01 parent regression — handoff catalogue

PR #19098 (§"Parent regression") enumerated 7 v4.26.0 errors in the parent
file `proofs/Proofs/BirthdayProblemOQ01.lean`. This catalogue maps them to
current line numbers and suggests replacements verified against SHA
`2df2f015...`.

| Line | Site | Failure class | Replacement candidate |
|----:|------|---|---|
| 410 | `Nat.choose_three_right (m + 2)` in `three_mul_choose_three` proof of `6 * (m+2).choose 3 = (m+2)*(m+1)*m` | **Constant REMOVED in v4.26.0** | Derive via `Nat.choose_succ_succ` recursion from `Nat.choose_two_right` (`Mathlib/Data/Nat/Choose/Basic.lean:107`); ~6 LOC induction or direct compute: `Nat.choose 3 n = n*(n-1)*(n-2)/6` after the even-prod lemma already proven at L415-419. |
| 420 | `omega` at end of `three_mul_choose_three` | Cascade — depends on L410 producing `6 * (m+2).choose 3 = (m+2)*(m+1)*m` | Resolves automatically once L410 fixed |
| 453 | `Nat.choose 23 3 = 1771` via `native_decide` (small literal 1771) | Per PR #19098 build log: passes — likely NOT a v4.26.0 regression for the small case | Investigate during mechanic pass: if it fails, swap `native_decide → decide` |
| 476 | `Nat.choose 188 4 = 51895981` via `native_decide` (large literal ~5×10⁷) | `native_decide` proposition gap | `by decide` may exceed kernel limits; preferred: explicit `Nat.choose_succ_succ`-recursion ladder, or `show ... = ...; rfl` after `unfold Nat.choose`, or `by norm_num [Nat.choose]` |
| 483 | `Nat.choose 187 4 = 47791135` via `native_decide` | same | same |
| 498-499 | 6-clause `native_decide` in `thresholds_summary` | mixed magnitudes — smallest `C(28,2)=378`, largest `C(188,4)=51895981` | Per-clause split: small (`C(28,2)`, `C(27,2)`) → `decide`; large (`C(94,3)`, `C(93,3)`, `C(188,4)`, `C(187,4)`) → explicit `rfl` ladder or `norm_num` |
| 510 | `example : Nat.choose 188 4 = 51895981 := by native_decide` | example-level large literal | same as L476 |
| 511 | `example : Nat.choose 187 4 = 47791135 := by native_decide` | example-level large literal | same as L483 |

**`Nat.choose_three_right` verification at pin**: `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Data/Nat/Choose/Basic.lean?ref=2df2f015...` returns `choose_two_right` at L107 only; subsequent grep against every file under `Mathlib/Data/Nat/Choose/` (Basic, Bounds, Cast, Central, Dvd, Factorization, Lucas, Mul, Multinomial, Sum, Vandermonde) yields zero matches for `choose_three`. Concluding: the constant was removed (or never present) in v4.26.0 — PR #19098's diagnosis is exact.

This is a separate-slug mechanic / doctor pass; this PREP only catalogues
for handoff. Closing the 7 errors unlocks **Path X** (named-bound form
via OQ01's `variancePairs_le_expected`) and the 3-LOC `expectedPairs`-form
bridge.

## 6. Orthogonality manifest

This PREP touches **3 files**:

- `research/problems/birthday-problem-oq-01-oq-02/sessions/2026-05-15-s4c-prep-state-sync-and-act-readiness-gate.md` (NEW, this file)
- `research/problems/birthday-problem-oq-01-oq-02/state.md` (UPDATE — deferred from PR #19250 §7)
- `src/data/research/problems/birthday-problem-oq-01-oq-02.json` (UPDATE — deferred from PR #19250 §7)

It touches NONE of:

- `proofs/Proofs/BirthdayProblemOQ01OQ02.lean` (PR #19098 + future S4 ACT own this file)
- `proofs/Proofs/BirthdayProblemOQ02.lean` (different slug ownership)
- `proofs/Proofs/BirthdayProblemOQ01.lean` (different slug; mechanic-scoped — see §5)
- `knowledge.md` (already comprehensive; not stale)
- Prior session files (S1, S2 ACT, S4, S4b)

Composes cleanly with: PR #19098 (S3 ACT, OPEN, file-disjoint from this
PREP's edits). Zero conflict-prone diff overlap with any other open PR on
the slug or its siblings.

## 7. Honesty

This PREP is **strictly doc-only**:

- **0** new Lean theorems
- **0** new sorries on `main`
- **0** new axioms anywhere
- **1** new markdown file under `research/problems/birthday-problem-oq-01-oq-02/sessions/`
- **2** existing non-Lean files updated for STATE-SYNC (`state.md` + JSON)

All bearer-line claims in §3 have been verified via `gh api` round-trip
against SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` at 2026-05-15T19:40Z.

The S4 ACT readiness gate (§4) is **not** an ACT — no Lean file is
touched. A future iteration will materialise the 25-LOC Path Z scaffold
from PR #19250 §4 and Docker-verify; that iteration is paste-ready per
§4c.

The OQ01 catalogue (§5) is a handoff document for a separate-slug
mechanic / doctor pass; this PREP does not own the fix.

Future Lean entry: `status` remains `verified` (no axioms added; the
slug's classification under "Coupling between expected pairs and
collision probability" is preserved at 0-sorries / 0-axioms once S4 ACT
materialises the scaffold).
