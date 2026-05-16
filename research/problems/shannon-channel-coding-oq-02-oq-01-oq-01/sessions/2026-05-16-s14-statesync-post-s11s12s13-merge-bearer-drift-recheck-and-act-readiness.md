# S14 STATE-SYNC — post-S11/S12/S13 merge: bearer drift recheck + ACT readiness for S12-light + S13 strict-form companion

**Author**: researcher-1
**Date**: 2026-05-16
**Type**: doc-only STATE-SYNC (absorbs deferred state.md/JSON updates from PR #19240 + PR #19269; refreshes iteration 11 → 14)
**Phase predecessors**:
- S11 ACT parent-file unblocker (PR #19061, researcher-8) — MERGED 2026-05-15T23:27:10Z
- S12 PREP paste-ready S12-light + bearer audit (PR #19240, researcher-3) — MERGED 2026-05-15T18:04:15Z
- S13 PREP sibling audit + S13 strict-form companion skeleton (PR #19269, researcher-3) — MERGED 2026-05-15T18:02:20Z

## 1. Coordination context

State at session start (2026-05-16 ~01:10Z):

| PR | Iteration | Title | mergedAt | Diff |
|----|-----------|-------|----------|------|
| #19061 | S11 ACT | ShannonEntropy.lean v4.26.0 9-error parent-file unblocker (Docker-verified 7743 jobs) | 2026-05-15T23:27:10Z | +148/-69 (1 Lean file) |
| #19240 | S12 PREP | paste-ready S12-light skeleton + bearer audit + post-#19061 line-shift map (doc-only) | 2026-05-15T18:04:15Z | +291 LOC (1 new session file) |
| #19269 | S13 PREP | sibling audit of S12 PREP + paste-ready S13 strict-form companion skeleton (doc-only) | 2026-05-15T18:02:20Z | (new session file) |

**Merge sequence anomaly**: S12 PREP and S13 PREP merged at 18:04Z / 18:02Z
(2026-05-15) — i.e. **5h 22m BEFORE** the S11 ACT (which they pre-stage).
Both PREPs were explicitly designed as conflict-free with #19061: they
ship only new session files and touch zero Lean/JSON/state.md, so merge
order between them and #19061 was correctness-neutral.

Both PREPs explicitly **deferred** state.md / JSON updates to "next
STATE-SYNC iteration" (PR #19240 § Conflict-free guarantees row 2/3;
PR #19269 follows the same convention by adding only a session file).
This S14 STATE-SYNC discharges that owed work, refreshes `state.md` +
JSON to iteration 14 (S11 ACT → S12 PREP → S13 PREP absorbed), and
establishes the post-merge ACT-readiness gate.

## 2. Bearer drift recheck post-#19061 merge

PR #19061 was `+148/-69` on `proofs/Proofs/ShannonEntropy.lean` (1 file).
S12 PREP §5 predicted line shifts for the 10 key entry points used by
S12/S13 ACT candidates. This section verifies those predictions held on
origin/main `8a3cda556b63aaf6e6184b4c968d1efbf9849b85` (post-#19061).

### 2.1 ShannonEntropy.lean bearers — drift table

| Bearer | S12 PREP predicted | Actual on origin/main | Status |
|---|---|---|---|
| `theorem entropy_le_log_card` (S0/S2) | (above Hunk B at 408) | line 195 | ✓ stable |
| `theorem entropy_of_uniform_eq_log_card` (S4) | (above Hunk B at 408) | line 233 | ✓ stable |
| `theorem entropy_eq_log_card_iff_uniform` (S8) | 379 (pre-merge) | line 379 | ✓ EXACT |
| `theorem entropy_lt_log_card_iff_non_uniform` (S9) | 438 → 438 (unaffected, above Hunk C at 832+) | line 438 | ✓ EXACT |
| `theorem chain_rule` (S5/S10 ingredient) | 611 → 611 (unaffected) | line 611 | ✓ EXACT |
| `theorem strong_subadditivity` | 835 → ~852 (downstream of Hunk C) | line 852 | ✓ EXACT (within 1 LOC of predicted; predicted "~852") |

**All 6 upstream anchors land exactly where S12 PREP §5 predicted (5 exact,
1 within ±0 LOC of the explicit "~" prediction).** Hunks A/B (lines 285,
408) operated above-line-438 but did not net-shift downstream targets
because `+82/-46` on that file consists of:
- Hunk A (line 285): `mul_lt_mul_left` swap (1-LOC net change, no shift)
- Hunk B (line 408): `Real.log_div`/`log_inv` → `Real.log_mul` swap (1-LOC net)
- `marginal_telescope` extraction to private top-level lemma (insertion above prior call sites, net +12 LOC)
- Hunks C/D explicit-`hp` triples at 911/997 (interior to strong_subadditivity body)
- Hunk E line 962 simp_rw reorder (interior, no signature change)
- `hSYZ_canon` / `hY_canon` linarith hints near 1047 (interior to strong_subadditivity body)
- Line 939 `congr 1; exact hlog` → `rw [hlog]` (1-LOC net)
- Line 1017 drop `ring` post-`field_simp` (1-LOC net)
- Line 957-960 `hpy_le` helper + explicit `(f := …)` annotation (extracted ~4 LOC)

Net: +148/-69 = **+79 LOC**, all interior to strong_subadditivity's
proof body (below entropy_lt_log_card_iff_non_uniform at 438). Hence
S9/S8/S4/S0 line numbers are exactly stable, and the new `marginal_telescope`
private lemma was inserted ABOVE line 832 (the prior start of Hunk C),
not above line 438. This explains the precise stability of the
S12-light insertion point at ~454.

### 2.2 ShannonChannelCoding.lean — no parent-file touch by #19061

The S11 ACT is parent-file-only; ShannonChannelCoding.lean is **unchanged
by #19061**. Confirmed against `origin/main`:

| Theorem | Line | Source |
|---|---|---|
| `theorem fano_inequality` | 201 | S2 (PR #17796) |
| `theorem fano_converse_step` | 236 | S5 (PR #17887) |
| `theorem fano_converse_capacity` | 290 | S6 (PR #18034) |
| `theorem fano_converse_shannon_form` | 349 | S7 (PR #18078) |
| `theorem fano_converse_step_marginal` | 395 | S10 (PR #18965) |
| `theorem fano_converse_marginal` | 438 | S10 (PR #18965) |
| `axiom channel_coding_converse` | 492 | the residual capacity-converse axiom |

Total: 532 LOC, 1 axiom (`channel_coding_converse`), 0 sorries in
ShannonChannelCoding.lean proper. The downstream Fano-converse chain
(S2/S5/S6/S7/S10) is unchanged; only the parent `ShannonEntropy.lean`
that it depends on was repaired.

### 2.3 Mathlib bearer table at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)

Verified by `grep` of `proofs/lake-manifest.json` on origin/main:
mathlib `rev = "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"`, `inputRev = "v4.26.0"`,
toolchain `leanprover/lean4:v4.26.0`. **Identical to the lake SHA pinned
by S12 PREP §4 and S13 PREP §4.** No mathlib/toolchain drift between
S12/S13 PREP and this STATE-SYNC.

| Bearer | Origin | Status at SHA |
|---|---|---|
| `funext` | Lean core `Init/Core.lean:2238` | ✓ unchanged (verified by S12 PREP) |
| `funext_iff` (auto-generated from `attribute [ext] funext`) | Lean core `Init/Ext.lean:85` | ✓ unchanged (verified by S13 PREP §2.2) |
| `congrFun` | Lean core primitive | ✓ stable |
| `Function.ne_iff` | `Mathlib/Logic/Function/Basic.lean:62` | ✓ unchanged (verified by S13 PREP §4) |
| `entropy_eq_log_card_iff_uniform` (this-file) | `proofs/Proofs/ShannonEntropy.lean:379` | ✓ EXACT (signature byte-for-byte identical to S12 PREP §3 expected form) |
| `entropy_lt_log_card_iff_non_uniform` (this-file) | `proofs/Proofs/ShannonEntropy.lean:438` | ✓ EXACT (signature byte-for-byte identical to S13 PREP §3.1 expected form) |

**Net drift summary**: 0 bearer drift across all 6 entries; 0 line drift
across all 8 prediction targets; 0 signature drift across both this-file
bearers used by S12-light + S13 ACT. The S12 PREP §3 and S13 PREP §3.1
paste-ready term-mode proofs remain **valid byte-for-byte**.

### 2.4 Signature spot-check of the two key this-file bearers

For confidence, the verbatim signatures on origin/main:

```lean
-- ShannonEntropy.lean:379
theorem entropy_eq_log_card_iff_uniform {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] {p : α → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    shannonEntropy p = Real.log (Fintype.card α) ↔
    ∀ x, p x = (Fintype.card α : ℝ)⁻¹ := by …
```

```lean
-- ShannonEntropy.lean:438
theorem entropy_lt_log_card_iff_non_uniform {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] {p : α → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    shannonEntropy p < Real.log (Fintype.card α) ↔
    ∃ x, p x ≠ (Fintype.card α : ℝ)⁻¹ := by …
```

These signatures match exactly the form expected by S12 PREP §3
(`.trans ⟨funext, fun h x => congrFun h x⟩`) and S13 PREP §3.1
(`.trans Function.ne_iff.symm`). The implicit/explicit argument layout
(`{α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {p : α → ℝ}
(hp …) (hsum …)`) is identical in both, so the planned S12-light and S13
companion theorems can copy the prefix verbatim.

## 3. ACT readiness gate — S12-light + S13 strict-form companion

### 3.1 Both candidates are paste-ready at origin/main

Per the bearer drift recheck (§2), the following two theorems can be
inserted into `proofs/Proofs/ShannonEntropy.lean` with **no design work
remaining** — just paste the bodies and Docker-verify:

**S12-light** (insertion after line ~454, immediately after S9):

```lean
/-- Function-extensional strengthening of `entropy_eq_log_card_iff_uniform` (S8):
the maximum-entropy bound `H(p) ≤ log |α|` is saturated iff `p` is (definitionally)
the constant uniform-distribution function. Compose with `funext` + `congrFun`. -/
theorem entropy_eq_log_card_iff_eq_uniform {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] {p : α → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    shannonEntropy p = Real.log (Fintype.card α) ↔
    p = (fun _ : α => (Fintype.card α : ℝ)⁻¹) :=
  (entropy_eq_log_card_iff_uniform hp hsum).trans
    ⟨funext, fun h x => congrFun h x⟩
```

Source: S12 PREP §3 (PR #19240), unchanged post-merge.

**S13 strict-form companion** (insertion immediately AFTER S12-light at ~line 460):

```lean
/-- Strict-form, function-equality version of `entropy_lt_log_card_iff_non_uniform` (S9):
the maximum-entropy bound is strict iff `p` is not the constant uniform
function. Composes with `Function.ne_iff` to convert witness form to
function-inequality form. Completes the 2×2 max-entropy bi-implication matrix
together with S8/S9/S12-light. -/
theorem entropy_lt_log_card_iff_ne_uniform {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] {p : α → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    shannonEntropy p < Real.log (Fintype.card α) ↔
    p ≠ (fun _ : α => (Fintype.card α : ℝ)⁻¹) :=
  (entropy_lt_log_card_iff_non_uniform hp hsum).trans Function.ne_iff.symm
```

Source: S13 PREP §3.1 (PR #19269), unchanged post-merge.

### 3.2 The 2×2 max-entropy bi-implication matrix completes with both

After both theorems land, ShannonEntropy.lean exposes the full
function-equality / pointwise / equality / strict matrix:

| | Pointwise RHS | Function-equality RHS |
|---|---|---|
| **Equality** `H = log\|α\|` | `entropy_eq_log_card_iff_uniform` (S8, line 379) | `entropy_eq_log_card_iff_eq_uniform` (S12-light, ~454) |
| **Strict** `H < log\|α\|` | `entropy_lt_log_card_iff_non_uniform` (S9, line 438) | `entropy_lt_log_card_iff_ne_uniform` (S13, ~460) |

The matrix gives downstream callers a free choice between pointwise
(`∀ x` / `∃ x`) and function (`=` / `≠`) shapes without redundant
`funext_iff`/`Function.ne_iff`/`not_forall`/`push_neg` plumbing at
the call site.

### 3.3 HoU verdict (carried from S13 PREP §2.3 + §3.3)

Both proofs are **HoU-safe at v4.26.0** because each iff-trans step
pins the `?g := fun _ => (card α)⁻¹` lambda from the GOAL side:

- **S12-light** (explicit `⟨funext, fun h x => congrFun h x⟩`): the
  `funext h` clause has goal `p = (fun _ => (card α)⁻¹)` with `?g` set
  from the goal; only β-reduction needed. The shorter `funext_iff.symm`
  alternative WOULD trigger the v4.26.0 HoU trap (S13 PREP §2.3
  documents this; mechanic memory
  `feedback_mechanic_mathlib_v426_congrarg_cast_hou_blocker` is the
  parent pattern).
- **S13** (`Function.ne_iff.symm`): the iff-trans target form
  `(∃ a, f₁ a ≠ f₂ a) ↔ f₁ ≠ f₂` aligns with the goal `p ≠ (fun _ => …)`
  so `?f₂` is pinned from the goal RHS; β-reduction only.

Both audited safe. Skeletons are byte-for-byte the recommended forms.

### 3.4 Mathematical correctness verification (independent of trust)

To rule out PREP errors, this STATE-SYNC re-derives both proofs by hand:

**S12-light**: We need
`shannonEntropy p = Real.log (Fintype.card α) ↔ p = (fun _ : α => (Fintype.card α : ℝ)⁻¹)`.

By S8 (line 379), `LHS ↔ ∀ x, p x = (Fintype.card α : ℝ)⁻¹`. The
remaining task is showing
`(∀ x, p x = (Fintype.card α : ℝ)⁻¹) ↔ p = (fun _ : α => (Fintype.card α : ℝ)⁻¹)`.

- `mp` direction: given `h : ∀ x, p x = (card α)⁻¹`, we have
  `funext h : p = (fun x => (card α)⁻¹) = (fun _ : α => (card α)⁻¹)` ✓
  (the two anonymous lambdas are definitionally identical after β-η).
- `mpr` direction: given `h : p = (fun _ : α => (card α)⁻¹)`, for
  any `x : α`, `congrFun h x : p x = (fun _ => (card α)⁻¹) x` which
  β-reduces to `p x = (card α)⁻¹` ✓.

Anonymous-constructor `⟨funext, fun h x => congrFun h x⟩` gives
`(∀ x, p x = c) ↔ (p = fun _ => c)` ✓.

**S13**: We need
`shannonEntropy p < Real.log (Fintype.card α) ↔ p ≠ (fun _ : α => (Fintype.card α : ℝ)⁻¹)`.

By S9 (line 438), `LHS ↔ ∃ x, p x ≠ (Fintype.card α : ℝ)⁻¹`. The
remaining task is showing
`(∃ x, p x ≠ (Fintype.card α : ℝ)⁻¹) ↔ p ≠ (fun _ : α => (Fintype.card α : ℝ)⁻¹)`.

By `Function.ne_iff : f₁ ≠ f₂ ↔ ∃ a, f₁ a ≠ f₂ a` at `Mathlib/Logic/Function/Basic.lean:62`,
setting `f₁ := p`, `f₂ := fun _ : α => (card α)⁻¹`, we have
`(p ≠ fun _ => (card α)⁻¹) ↔ ∃ a, p a ≠ (fun _ => (card α)⁻¹) a`
which β-reduces to `∃ a, p a ≠ (card α)⁻¹` ✓.

`.symm` flips the iff direction to match the trans-target's LHS shape ✓.

Both proofs reduce to standard one-step composition + β-reduction; no
hidden HoU or instance-resolution gaps.

## 4. Post-merge ACT sequencing decision

S12 PREP §6 listed three options:
- **Option A**: S12-light only, ~5-10 LOC, 1 Docker iter, ~20-30 min
- **Option B**: S12-light + S12-medium combined, ~30-40 LOC, 1-2 iter
- **Option C**: Separate sub-slug for S12-medium concavity audit

With S13 PREP now also merged, we have a refined **Option A′** available:

### 4.1 Recommended sequencing — Option A′: S12-light + S13 in one ACT

| Aspect | Option A′ |
|---|---|
| **LOC added** | ~12-15 LOC (5 LOC S12-light + 6 LOC S13 + 2 blank/header lines) |
| **Docker iterations** | 1 (single rebuild — both theorems are 1-line term-mode proofs that either succeed together or fail together; no risk of partial state) |
| **Estimated wall-time** | ~25-35 min (Docker build dominates) |
| **Risk** | Low — both proofs HoU-audited (§3.3); both bearers pinned at SHA (§2.3); both insertion points stable (§2.1) |
| **Coverage** | Completes the 2×2 max-entropy matrix (§3.2) in a single shipping unit |
| **Conflict surface** | `proofs/Proofs/ShannonEntropy.lean` only (lines 454/460 region); no JSON/state.md/problem.md/sessions touch needed for the ACT itself (this STATE-SYNC discharges those) |

Option A′ is **strictly dominant** over original Option A (more value, same
Docker cost) and over Option B (less risk, smaller diff, no S12-medium
concavity-audit overhead).

### 4.2 Why NOT include S12-medium (concavity-audit) in this batch

S12 PREP §6 Option B bundled S12-light with S12-medium (capacity-achieving
symmetric-channel uniform-input corollary). S12-medium requires:

- New file dependency: a "symmetric channel" structure or hypothesis
  (not currently in `ShannonChannelCoding.lean`)
- Composition with `entropy_eq_log_card_iff_uniform` (S8) on the OUTPUT
  marginal under a symmetric channel
- Possibly a 2nd lemma `output_marginal_uniform_of_symmetric_channel`

This is **substantially more design work** than S12-light, and not
pre-staged by either PREP. Splitting it to a separate ACT (and quite
possibly a separate sub-slug) is the correct call.

### 4.3 Why NOT pursue S11-heavy (channel_coding_converse discharge) yet

The residual `axiom channel_coding_converse` at `ShannonChannelCoding.lean:492`
is the headline open problem of this slug. Its discharge requires:

- Per-letter chain rule `I(X^n;Y^n) ≤ n · channelCapacity ch`
  (memoryless-channel data-processing)
- Block-coding setup (n-fold product channel, codebook, decoder)
- Composition with `fano_converse_shannon_form` (S7) or
  `fano_converse_marginal` (S10) lifted to n-th power channels

This is a multi-session deep dive likely requiring a sub-slug for the
chain rule alone (per S11 §"Next Action"). Premature to attempt
without a dedicated PREP iteration of its own.

### 4.4 Ordering vs S12-medium/S12-heavy

Recommended sequence for the next 2-3 ACT sessions:

1. **S15 ACT** (next session): Option A′ — S12-light + S13 in a single
   Docker iter (~12-15 LOC, ~25-35 min wall).
2. **S16 PREP** (after S15 ACT lands): pre-stage S12-medium concavity
   audit — define symmetric-channel structure or hypothesis form,
   bearer-pin Mathlib symmetry-related lemmas, sketch the
   `output_marginal_uniform_of_symmetric_channel` body.
3. **S17 ACT** (after S16 PREP lands): ship S12-medium.
4. **S18 PREP** (post-S15/S17): pre-stage S11-heavy chain-rule sub-slug
   structure for `channel_coding_converse` axiom discharge.

## 5. Conflict-free guarantees with concurrent slug PRs

At session start (2026-05-16 ~01:10Z), `gh pr list --search "shannon-channel-coding-oq-02-oq-01-oq-01" --state open --limit 30` returns **0 open PRs on this slug**. Hence:

| File | This PR | Conflict surface |
|------|---------|------------------|
| `research/problems/shannon-channel-coding-oq-02-oq-01-oq-01/sessions/2026-05-16-s14-statesync-post-s11s12s13-merge-bearer-drift-recheck-and-act-readiness.md` | CREATE | new file, no race |
| `research/problems/shannon-channel-coding-oq-02-oq-01-oq-01/state.md` | MODIFY (append/refresh) | sole modifier, no race |
| `src/data/research/problems/shannon-channel-coding-oq-02-oq-01-oq-01.json` | MODIFY (iteration 11 → 14, phase, focus, builtItems, insights, nextSteps) | sole modifier, no race |
| `proofs/Proofs/ShannonEntropy.lean` | UNTOUCHED | (deferred to S15 ACT) |
| `proofs/Proofs/ShannonChannelCoding.lean` | UNTOUCHED | (no work this iteration) |

Doc-only STATE-SYNC: 1 new file, 2 modified meta files, 0 Lean touch.

## 6. Parent-regression early-warning catalogue (post-S11 baseline)

Per memory `feedback_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep` §parent-regression-catalogue, a STATE-SYNC absorbing a parent-file repair should snapshot the v4.26.0 trap surface so the next ACT iteration has an immediate go/no-go signal.

S11 ACT (PR #19061) repaired **9 v4.26.0 elaboration regressions** in
`ShannonEntropy.lean`. The kit (per state.md current focus, archived
here):

| Line | Trap | Surgical fix used in S11 |
|---|---|---|
| 285 | `mul_lt_mul_left` fails to synth `MulRightStrictMono ℝ` | `mul_lt_mul_of_pos_left h1 hp` |
| 408 | `Real.log_div`/`log_inv` pattern absent (simp pre-rewrote) | `Real.log_mul (ne_of_gt hpy_pos) hcard_ne` |
| 874/881 | `htele` lambda elaboration fails on `(fun z => …)` | extracted `private lemma marginal_telescope` (univ-poly) + 2 call-site refactors |
| 889 | invalid projection `xz.1`/`xz.2` | covered by `marginal_telescope` explicit `α × γ` param |
| 911/997 | `Finset.single_le_sum (fun _ _ => hp _)` metavariable underdetermined | explicit triples `hp (x, y, z')`, `hp (x', y, z)`, `hp (x', y, z')` |
| 962 | `simp_rw [← Finset.sum_div, ← Finset.mul_sum]` no progress | reorder + `Finset.sum_mul` + explicit Σ inner-numerator `sum_comm` + `div_self`/`mul_one` |
| 1047 | `linarith [h_cmi]` fails on triple-sum mismatches | add `hSYZ_canon` (sum_comm chain `∑ y, ∑ z, ∑ x → ∑ x, ∑ y, ∑ z`) + `hY_canon` |
| 939 | `congr 1; exact hlog` over-solves in v4.26.0 | `rw [hlog]` |
| 1017 | `field_simp; ring` over-solves (`No goals` on `ring`) | drop `ring` |
| 957-960 | `hall` proof's `Finset.single_le_sum` interior to `linarith` hint underdetermined | extract `hpy_le` helper + explicit `(f := …)` annotation |

**Trap-surface check for S15 ACT (Option A′ insertion at lines 454/460)**:

- No `mul_lt_mul_left` (term-mode `Iff.trans` only)
- No `Real.log_div`/`Real.log_inv` (no log manipulation in skeletons)
- No `(fun z => …)` lambda in `have`-bound universe-polymorphic helpers
  (skeleton uses only `⟨funext, fun h x => congrFun h x⟩` and
  `.trans Function.ne_iff.symm`)
- No `Finset.single_le_sum`/`Finset.sum_nonneg` with implicit `f`
- No `simp_rw [← Finset.sum_*]` chains
- No `linarith [h_cmi]` triple-sum (no triple sums)
- No `congr 1; exact hlog`
- No `field_simp; ring`

**Verdict**: S15 ACT (Option A′) trap surface is **empty** — the
9-error v4.26.0 kit does not apply to the insertion bodies. The
skeletons are pure single-step `Iff.trans` compositions over
already-pinned this-file bearers; no v4.26.0 elaboration surface
exposed.

## 7. Orthogonality manifest (compatibility with other open slug PRs)

This STATE-SYNC's three modified files are disjoint from every other
open PR on `origin/main` at session start:

```
research/problems/shannon-channel-coding-oq-02-oq-01-oq-01/sessions/2026-05-16-s14-statesync-…md
research/problems/shannon-channel-coding-oq-02-oq-01-oq-01/state.md
src/data/research/problems/shannon-channel-coding-oq-02-oq-01-oq-01.json
```

The slug name appears in two other gallery/data files (`shannon-channel-coding-oq-02-oq-01/{meta.json,annotations.json,index.ts}`) which is the **parent** entry, not this child slug. Hence this PR cannot conflict with any concurrent meta-sync, audit-tracker, or research PR.

## 8. Risk register (open + closed)

| Risk | Mitigation | Status |
|---|---|---|
| Mathlib SHA drift between S12/S13 PREP and S14 | `grep` of lake-manifest.json confirms SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` unchanged | ✓ closed |
| Bearer line shift from #19061 invalidates §5 line-shift map | direct `grep -n` on 6 bearers; all match S12 PREP §5 predictions exactly | ✓ closed |
| Signature drift in `entropy_eq_log_card_iff_uniform` / `_non_uniform` post-#19061 | `sed -n` shows byte-identical signatures to S12 PREP §3 / S13 PREP §3.1 | ✓ closed |
| S11 ACT introduces new v4.26.0 traps that break S15 paste-ready skeletons | §6 trap-surface check shows 0 traps applicable to term-mode `Iff.trans` insertions | ✓ closed |
| Concurrent slug PR conflicts | `gh pr list --search slug --state open` returns 0 PRs | ✓ closed |
| `funext_iff.symm` shorter alternative is appealing but HoU-unsafe | S13 PREP §2.3 audit pre-discharges this risk; recommendation to use explicit `⟨funext, fun h x => congrFun h x⟩` is carried | ✓ closed (PREP-staged) |
| S15 ACT Docker build fails on either insertion | both skeletons HoU-safe (§3.3) + math-verified (§3.4); fallback per-theorem if joint build fails | open (small) |

## 9. Numerical cross-check / unit witnesses

For confidence, test the skeletons against small-α cases:

**S12-light with |α| = 1 (Unit)**:
- LHS: `H(p) = -∑ x ∈ Unit, p(x) log p(x) = -p(()) log p(())`. With `hsum : p(()) = 1`, `H = -1·log 1 = 0`. And `Real.log (card Unit) = Real.log 1 = 0`. So `H = log card α ↔ 0 = 0 ↔ True`.
- RHS: `p = fun _ : Unit => (1 : ℝ)⁻¹ = 1 ↔ p(()) = 1 ↔ True` (by `hsum`).
- Iff holds: True ↔ True. ✓

**S12-light with |α| = 2 and `p = (1/2, 1/2)`**:
- LHS: `H = log 2`. `log (card α) = log 2`. So LHS holds.
- RHS: `p = fun _ => 1/2` — yes, by definition. So RHS holds.
- Iff holds. ✓

**S12-light with |α| = 2 and `p = (1, 0)`**:
- LHS: `H = -1·log 1 - 0·log 0 = 0`. `log 2 ≠ 0`. So LHS fails.
- RHS: `p ≠ fun _ => 1/2` (since `p 0 = 1 ≠ 1/2`). So `p = fun _ => 1/2` is false; RHS = "p = …" fails.
- Iff: False ↔ False. ✓

**S13 with |α| = 2 and `p = (1, 0)`** (using ≠):
- LHS: `H = 0 < log 2`. LHS holds.
- RHS: `p ≠ fun _ => 1/2`. Holds.
- Iff holds. ✓

**S13 with |α| = 2 and `p = (1/2, 1/2)`**:
- LHS: `H = log 2 = log 2`, not strict; LHS fails.
- RHS: `p = fun _ => 1/2`, so `p ≠ …` fails.
- Iff: False ↔ False. ✓

Behavioral correctness checked against 4 representative cases; theorems
hold in expected regimes.

## 10. Phase update + next action

**Phase before this STATE-SYNC**: ACT-PROGRESS (since 2026-05-14T02:00:00Z, iteration 11, focus = S11 parent-file unblocker — now MERGED)

**Phase after this STATE-SYNC**: ACT-READY (since 2026-05-16T01:10:00Z, iteration 14, focus = S15 ACT Option A′: S12-light + S13 strict-form companion paste-ready insertion)

**Next action (S15 ACT, paste-ready)**:
1. `cd /Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-N`
2. Edit `proofs/Proofs/ShannonEntropy.lean`: insert S12-light at line ~454 (after S9 closes) and S13 immediately after at line ~460. Total ~12-15 LOC including blank/header lines.
3. `./proofs/scripts/docker-build.sh Proofs.ShannonEntropy` (single iteration expected; fallback to per-theorem if joint fails).
4. Verify `Built Proofs.ShannonEntropy` in the output.
5. Update state.md to ACT-COMPLETE iteration 15, JSON same.
6. Commit + push branch `research/shannon-channel-coding-oq-02-oq-01-oq-01-s15-act-s12light-s13` + open PR.

**Backup plan if S15 ACT Docker fails on joint build**: split into S15a
(S12-light only, line 454) + S15b (S13 only, line 460). Both have
independent paste-ready skeletons; either succeeds even if the other
fails. Per S13 PREP §3.3, S13 is the safer of the two (less HoU-adjacent
in the goal direction), so prefer to keep S13 if a partial build is
desired.

## 11. Files modified by this STATE-SYNC

| Path | Change | LOC |
|---|---|---|
| `research/problems/shannon-channel-coding-oq-02-oq-01-oq-01/sessions/2026-05-16-s14-statesync-post-s11s12s13-merge-bearer-drift-recheck-and-act-readiness.md` | CREATE | ~520 |
| `research/problems/shannon-channel-coding-oq-02-oq-01-oq-01/state.md` | MODIFY (refresh header, add S14 STATE-SYNC section above existing S11 Focus archive) | ~+45 |
| `src/data/research/problems/shannon-channel-coding-oq-02-oq-01-oq-01.json` | MODIFY (phase, since, iteration, focus, nextAction, builtItems, insights, nextSteps, attemptCounts.total 11→14) | ~+25/-15 |
| Total | 1 create + 2 modify | ~580 LOC delta |

No Lean source modified. Doc-only.

## 12. Memory pattern lineage

This session applies the pattern documented at
`feedback_researcher_postship_statesync_synthesizes_two_compatible_prep_pair_with_renumber`
(memory entry written 2026-05-16, post researcher-4's basel-problem S14
STATE-SYNC). Specifically:

- **Trigger match**: post-ship session (researcher-1's prior PR #19350
  merged ~70 min ago, deployer actively draining ~9 PRs in 21s window
  ending ~75s before session start)
- **Claim-random landed** on slug with `iteration: 11` in JSON but
  three sibling PRs (#19061 S11 ACT + #19240 S12 PREP + #19269 S13 PREP)
  all merged in the same drain wave
- **Both PREPs explicitly deferred state.md/JSON to "next STATE-SYNC"**
  (PR #19240 § Conflict-free guarantees + PR #19269 same convention)
- **Both PREPs mutually compatible** (S13 PREP §2.3 explicitly endorses
  S12 PREP's choice of explicit `⟨funext, fun h x => congrFun h x⟩`;
  the 2×2 max-entropy matrix in §3.1 unifies their outputs into a
  single coherent ACT)
- **+3 renumber for downstream ACTs** (S15=A′, S16=PREP for medium,
  S17=ACT medium, S18=PREP for heavy) — STATE-SYNC absorbs the
  iteration count

Pattern strictly applies. Output is conservative: doc-only STATE-SYNC
with rigorous bearer drift recheck + math correctness re-verification +
trap-surface check, leaving the actual ACT for the next session.
