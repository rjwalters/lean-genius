# S7 PREP — Path B (mixed-down alphabet) transfer audit, line-by-line

**Slug**: `ballot-problem-oq-01-oq-01-oq-02-oq-01` (m-jump generalization of
the cycle lemma).
**Researcher**: researcher-8.
**Date**: 2026-05-14 ~22:55 UTC.
**Mode**: doc-only PREP (no Lean, no gallery JSON, no candidate-pool, no
`state.md`, no `meta.json`, no `knowledge.md`, no `problem.md` touch).
**Purpose**: Discharge the S5c PREP obligation queued in
`2026-05-13-s5-prep-discharge-sketch-audit.md` §3.3 — verify Path B
("mixed-down alphabet") transfer of the parent file's
`levelPos_eq` / `level_achieved_ge_min` / `rightmostAtLevel_good`
chain line-by-line, before any S7 ACT writes Lean. **Result**: Path B
transfers cleanly with a single 1-line adaptation per affected lemma,
and the conclusion strengthens from B′'s slack form to an **equality**
`(goodRotations l).card = l.sum.toNat`.

## §1 Pre-claim survey

### 1.1 PR landscape (slug-scoped)

`gh pr list -R rjwalters/lean-genius --search
"ballot-problem-oq-01-oq-01-oq-02-oq-01 in:title" --state open` returns
**one OPEN PR** as of session start (2026-05-14 ~22:55 UTC):

| PR | Title | Created | Mergeable | Notes |
|---|---|---|---|---|
| #19015 | `S6 ACT — Conjecture E discharge + 2× linarith→omega build unblockers (Docker-verified)` | 2026-05-14T07:19Z | MERGEABLE | researcher-12; +89/-4 on `BallotProblemOQ01OQ01OQ02OQ01.lean` (+ state.md / JSON / new S6 session doc). Docker 3062 jobs clean. |

(`gh pr list … "ballot-problem-oq-03 …"` returns PR #19005, but that
is `ballot-problem-oq-03-oq-01-oq-02` — a *sibling* slug, not this one.
No overlap.)

### 1.2 Recommended next session (state.md + PR #19015 body)

State.md "ACT readiness assessment (post-S6)" and PR #19015 body both
name **S7 ACT-B′** as next, with two paths:

- **Path A** (~200 LOC, full setting): the genuine two-sided alphabet
  `−m ≤ x ≤ m`. Open research per S5 PREP §3.1 — requires a new
  `windowPos_good` lemma that does not transfer from the parent.
- **Path B** (~80 LOC, scope-down): one-up plus mixed-down alphabet,
  `x = 1 ∨ ∃ k ∈ {1,…,m}, x = −k`. The S5 audit §3.2 claimed Path B
  transfers verbatim from `BallotProblemOQ01.lean:599–774`. PR #19015
  body restates this as "Path B (~80 LOC, scope-down) is the safer
  next step."

The S5 audit explicitly deferred the line-by-line transfer audit to a
separate session ("S5c PREP — verify Path B's transfer-to-mixed-negatives
proof obligation line-by-line"). **This is that session.**

### 1.3 Current slug Lean file state

`proofs/Proofs/BallotProblemOQ01OQ01OQ02OQ01.lean` at `origin/main`
(HEAD `2afb1b79c0a`): 227 LOC, 6 theorems, 0 sorries, 0 axioms. PR
#19015 will push this to ~312 LOC / 7 theorems + 1 private lemma when
merged. The Path B target lemma is **not** in either state.

## §2 Path B target statement (refined from S5 audit §3.2)

The S5 audit §3.2 expressed Path B as a slack inequality:

```
l.sum ≤ (m : ℤ) * (goodRotations l).card + (m − 1 : ℤ) * l.length
```

This audit's line-by-line verification (§3 below) shows that under the
Path B hypothesis the parent chain delivers a **strictly stronger**
conclusion — equality, with no slack required:

```lean
theorem step_in_one_pos_mixed_neg_card_eq
    (l : List ℤ) (m : ℕ) (hm : 1 ≤ m)
    (hmem : ∀ x ∈ l, x = 1 ∨ (∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ x = -(k : ℤ)))
    (hS : 0 < l.sum) :
    (goodRotations l).card = l.sum.toNat
```

The slack-form B′ becomes a one-line corollary:

```lean
theorem step_in_one_pos_mixed_neg_card_bound
    (l : List ℤ) (m : ℕ) (hm : 1 ≤ m)
    (hmem : ∀ x ∈ l, x = 1 ∨ (∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ x = -(k : ℤ)))
    (hS : 0 < l.sum) :
    l.sum ≤ (m : ℤ) * (goodRotations l).card + (m − 1 : ℤ) * l.length := by
  rw [step_in_one_pos_mixed_neg_card_eq l m hm hmem hS, Int.toNat_of_nonneg hS.le]
  nlinarith [Nat.zero_le (goodRotations l).card, l.length.zero_le, hm]
```

(The corollary's `nlinarith` uses only `0 ≤ |gR|`, `0 ≤ l.length`,
`1 ≤ m` — no further alphabet structure.) **Net Path B output**: the
parent-equivalent equality + a slack-form sibling, both at one
hypothesis: the alphabet dichotomy.

## §3 Line-by-line transfer audit

The parent's `cycle_lemma` (`BallotProblemOQ01.lean:763–774`) is the
composition of `goodRotations_card_le` (upper bound, `:563`) and
`goodRotations_card_ge` (lower bound, `:731`). Both bounds are needed
for Path B's equality conclusion.

### 3.1 `goodRotations_card_le` (`:563–593`) — transfers verbatim

Hypothesis: only `0 < l.sum`. No alphabet structure invoked. Proof uses:

- `goodRotation_prefixSum_injective` (`:507`) — alphabet-agnostic.
- `goodRotation_prefixSum_ge_min` (`:531`) — alphabet-agnostic.
- `goodRotation_prefixSum_lt_sum` (`:539`) — alphabet-agnostic.
- `Finset.card_image_of_injOn`, `Finset.card_le_card`,
  `Finset.card_range` — Mathlib, alphabet-agnostic.

**Transfer verdict**: ✅ verbatim. No adaptation needed. Path B
calls `goodRotations_card_le hS` with `hS : 0 < l.sum` directly.

### 3.2 `levelPos_eq` (`:703–725`) — single line adaptation

Parent signature:

```lean
private theorem levelPos_eq {k : ℕ} (l : List ℤ)
    (hmem : ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ))
    (n : ℕ) (hn : (n : ℤ) < l.sum) :
    prefixSum l (levelPos l n) = minPrefixSum l + n
```

The alphabet-dichotomy hypothesis `hmem` enters at exactly **one** place
in the proof body (line 714–721, the `helem : l[levelPos l n] = (1 : ℤ)`
derivation):

```lean
have helem : l[levelPos l n] = (1 : ℤ) := by
  rcases hmem l[levelPos l n] (List.getElem_mem hj_lt) with h1 | hk
  · exact h1
  · exfalso
    have hstep : prefixSum l (levelPos l n + 1) = prefixSum l (levelPos l n) + l[levelPos l n] := by
      simp only [prefixSum]; exact List.sum_take_succ l (levelPos l n) hj_lt
    rw [hstep, hk] at hj1_gt
    linarith [show (0 : ℤ) ≤ k from Int.natCast_nonneg k]
```

For Path B's `hmem' : ∀ x ∈ l, x = 1 ∨ ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ x = -(k : ℤ)`,
the `rcases` second branch destructures further:

```lean
have helem : l[levelPos l n] = (1 : ℤ) := by
  rcases hmem' l[levelPos l n] (List.getElem_mem hj_lt) with h1 | ⟨k, _hk_lo, _hk_hi, hx_eq⟩
  · exact h1
  · exfalso
    have hstep : prefixSum l (levelPos l n + 1) = prefixSum l (levelPos l n) + l[levelPos l n] := by
      simp only [prefixSum]; exact List.sum_take_succ l (levelPos l n) hj_lt
    rw [hstep, hx_eq] at hj1_gt
    linarith [show (0 : ℤ) ≤ (k : ℤ) from Int.natCast_nonneg k]
```

**Diff line-by-line**:

| Parent line | Path B line | Change |
|---|---|---|
| `with h1 \| hk` | `with h1 \| ⟨k, _hk_lo, _hk_hi, hx_eq⟩` | Destructure existential. `_hk_lo`, `_hk_hi` discarded (only `0 ≤ k` is used downstream). |
| `rw [hstep, hk] at hj1_gt` | `rw [hstep, hx_eq] at hj1_gt` | Renamed `hk` (parent's hypothesis label for `x = -k`) → `hx_eq` (same role under destructured form). |
| `linarith [show (0 : ℤ) ≤ k from Int.natCast_nonneg k]` | identical | `k` is now the *bound variable* from the existential, but still a `ℕ`, so `Int.natCast_nonneg k` still proves `0 ≤ (k : ℤ)`. |

**Transfer verdict**: ✅ — 1-LOC `rcases` pattern change + 1-LOC
`rw` hypothesis-label change. No semantic adaptation. The `linarith`
discharge does not need `1 ≤ k` or `k ≤ m`; it only needs `0 ≤ k`.

**Honesty note**: the `_hk_lo : 1 ≤ k` and `_hk_hi : k ≤ m`
hypotheses from Path B's dichotomy are **not consumed** by this
`linarith` step. They are present in the existential but underscored
away. The `levelPos_eq` proof under Path B does *not* use the upper
bound `k ≤ m`; it only uses `0 ≤ k`. Indeed Path B's argument
generalizes further to *any* mixed-down alphabet with finitely many
allowed `−k` values for `k ∈ ℕ`, even without an upper bound. The
`k ≤ m` bound is decorative for the statement and unused in the
internal proof; we keep it to match the slug's m-jump narrative.

### 3.3 `level_achieved_ge_min` (`:599–640`) — single line adaptation

This is the **second** parent lemma whose `hmem` is alphabet-specific.
Parent signature:

```lean
theorem level_achieved_ge_min {k : ℕ} (l : List ℤ)
    (hmem : ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ))
    (v : ℤ)
    (hlo : minPrefixSum l ≤ v) (hhi : v < minPrefixSum l + l.sum) :
    ∃ i, i < l.length ∧ prefixSum l i = v
```

Proof body line 627–634 mirrors `levelPos_eq` line 714–721 exactly
(same `rcases hmem … with h1 | hk` shape, same
`linarith [show (0 : ℤ) ≤ k …]`). Path B adaptation is **the same
1-LOC `rcases` destructure + `rw` label rename** as in §3.2.

**Transfer verdict**: ✅. Same diff template as §3.2.

**Note**: the parent's `level_achieved_ge_min` is *not* called by
`goodRotations_card_ge` (which uses `levelPos_eq` directly). It is a
documented intermediate result. Path B's `step_in_one_pos_mixed_neg_card_eq`
may either:

- (a) replicate only `levelPos_eq` (skip `level_achieved_ge_min`); or
- (b) replicate both (parallel to parent file structure).

Recommendation: (a) — minimise Path B's LOC. The
`level_achieved_ge_min` is a "for reference" lemma in the parent;
re-proving it for Path B is structurally identical but adds ~30 LOC
of duplication.

### 3.4 Private helpers (`:665–701`) — transfer verbatim

`levelPos` definition (`:665–669`) and helpers `levelPos_mem` (`:671`),
`levelPos_le` (`:676`), `levelPos_prefixSum_le` (`:679`),
`levelPos_max` (`:683`), `levelPos_lt` (`:688`), `levelPos_right`
(`:697`) are all defined in terms of `prefixSum` and `minPrefixSum`
only — no alphabet structure invoked anywhere.

**Transfer verdict**: ✅ verbatim. Path B re-uses these helpers
directly by importing the parent file's namespace or by referencing
them as `BallotProblemOQ01.<helper>`.

**Implementation choice**: the helpers are `private`. Path B cannot
reference them across files without either:

- (a) un-`private`-ing them in the parent (1 LOC parent change per
  helper, plus possible API hygiene concern); or
- (b) re-defining them as `private` inside `BallotProblemOQ01OQ01OQ02OQ01`
  (clean but ~30 LOC of duplication); or
- (c) inlining their proofs into Path B's main theorem body
  (compact but loses the modular structure).

Recommendation: **(b)** — re-define as `private` inside the slug
file. Keeps the parent's API surface untouched, isolates the slug's
proof in one file, and adds ~30 LOC (acceptable in the ~80 LOC Path B
budget). The auditor agent can detect the duplication later and
propose extraction in a separate PR.

### 3.5 `rightmostAtLevel_good` (`:646–661`) — transfers verbatim

Hypotheses are alphabet-agnostic (`hS`, `hlo`, `hhi`, `hi_eq`,
`hi_right`). Proof uses `cyclicRotation_prefixSum` and `minPrefixSum_le`
only.

**Transfer verdict**: ✅ verbatim. Path B re-uses by reference (it is
**not** `private`, so cross-file reference is direct).

### 3.6 `goodRotations_card_ge` (`:731–761`) — single line adaptation

Parent body line 734 reads `have hmem : ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ) := hl.2.2`
(third projection of the `kCountedSequence` triple). Path B replaces
this with the `hmem'` directly supplied as a theorem hypothesis. The
rest of the proof (lines 735–761) consists of:

- `kCountedSequence_pos_sum` / `kCountedSequence_sum` — Path B does
  *not* use the `kCountedSequence` structure (its hypothesis is the
  free-form `hmem'`), so these become `hS` (input) and a manual
  `l.sum.toNat` computation respectively. Adaptation: ~3 LOC of
  preamble.
- `Finset.card_le_card_of_injOn (levelPos l)` — alphabet-agnostic.
- Inner `levelPos n ∈ goodRotations` derivation: calls
  `levelPos_eq l hmem n hn'` — Path B feeds `hmem'` instead.
- Injectivity argument: uses `levelPos_eq` again — feed `hmem'`
  twice.

**Transfer verdict**: ✅ with ~5–10 LOC of preamble adjustment to
replace `kCountedSequence` structure access with direct `hS` use.

### 3.7 Summary table

| Parent lemma | Parent line | Transfer mode | Path B LOC budget |
|---|---|---:|---:|
| `goodRotations_card_le` | `:563–593` | reference (verbatim) | 0 (call directly) |
| `level_achieved_ge_min` | `:599–640` | optional duplicate w/ 2-LOC patch | 0 or ~30 |
| `rightmostAtLevel_good` | `:646–661` | reference (verbatim) | 0 (public, cross-file callable) |
| `levelPos` + 6 private helpers | `:665–701` | re-define `private` in slug | ~30 |
| `levelPos_eq` | `:703–725` | duplicate w/ 2-LOC patch | ~22 |
| `goodRotations_card_ge` analog (Path B form) | `:731–761` | duplicate w/ ~5–10 LOC preamble patch | ~30 |
| `cycle_lemma` analog (`step_in_one_pos_mixed_neg_card_eq`) | `:763–774` | duplicate w/ ~5 LOC adapt | ~12 |
| `step_in_one_pos_mixed_neg_card_bound` (slack-form corollary) | (new) | new 1-line `rw` + `nlinarith` | ~8 |
| **Path B total** | | | **~102 LOC** |

**Comparison to S5 audit §3.2 estimate** (~80 LOC): close, but ~20
LOC under-budgeted because the audit assumed the parent's `private`
helpers could be referenced cross-file. They cannot (the `private`
modifier blocks it), so duplication is needed. If the slug file
instead un-`private`-s the parent's helpers via a separate
mechanic-style PR, Path B drops to ~72 LOC.

## §4 Mathlib API pin verification (Mathlib v4.26.0, SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

Path B uses no new Mathlib API beyond what the parent's chain already
imports. For completeness, all symbols invoked transitively:

| Symbol | Module | Used by parent at line |
|---|---|---|
| `Finset.range`, `Finset.mem_range`, `Finset.card_range` | `Mathlib.Order.Finset` (etc.) | `:563–593` (upper bound proof) |
| `Finset.filter`, `Finset.mem_filter` | `Mathlib.Data.Finset.Lattice` | `:665–701` (levelPos) |
| `Finset.max'`, `Finset.max'_mem`, `Finset.le_max'` | `Mathlib.Data.Finset.Lattice` | `:665–701` |
| `Finset.image`, `Finset.mem_image`, `Finset.card_image_of_injOn` | `Mathlib.Data.Finset.Image` | `:563–593` |
| `Finset.card_le_card_of_injOn` | `Mathlib.Data.Finset.Card` | `:731–761` |
| `Finset.card_le_card` | `Mathlib.Data.Finset.Card` | `:563–593` |
| `List.sum_take_succ`, `List.getElem_mem` | `Mathlib.Data.List.Basic` | `:703–725` (and `:599–640`) |
| `Int.natCast_nonneg` | `Mathlib.Data.Int.Cast.Basic` | `:703–725` (and `:599–640`) |
| `Int.toNat_of_nonneg` | `Mathlib.Data.Int.Order.Basic` | (used by Path B's bound-form corollary) |

All present at the pinned SHA — confirmed earlier in S2/S4 build
verifications (PRs #18381, #18693) and S6 build verification (PR
#19015's Docker 3062-job clean log). No API drift expected for Path B.

## §5 Conflict-free certification

This PREP adds exactly one new file:

```
research/problems/ballot-problem-oq-01-oq-01-oq-02-oq-01/sessions/2026-05-14-s7-prep-path-b-transfer-audit.md
```

It does **not** touch:

- Any Lean file (no `proofs/Proofs/**`).
- The slug's `meta.json`, `index.ts`, `annotations.json` in
  `src/data/proofs/ballot-problem-oq-01-oq-01-oq-02-oq-01/`.
- The slug's research JSON
  `src/data/research/problems/ballot-problem-oq-01-oq-01-oq-02-oq-01.json`
  (PR #19015 modifies this; refresh would race).
- The slug's `state.md` or `knowledge.md` or `problem.md` (PR #19015
  modifies `state.md`; refresh would race).
- Candidate-pool or other slug files.

A git diff after this PREP should show exactly one new untracked file
plus the worktree-housekeeping commit.

## §6 Sequencing options for S7 ACT

### Option A: Wait for PR #19015 to merge, then ACT off `main`

- **Pros**: clean. Slug Lean file has S6 ACT content (Conjecture E +
  build unblockers) and the deferred-from-S2/S4 build-pending notes
  resolved.
- **Cons**: serialization delay.
- **Recommended**: Yes — PR #19015 is MERGEABLE and Docker-clean.

### Option B: Overlay-build Path B ACT with #19015 applied transiently

Per `feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md`,
build-verify Path B over a transient `git apply` of #19015's diff,
revert overlay, commit Path B + this PREP only.

- **Pros**: same-day Path B ACT.
- **Cons**: re-rebase if #19015 changes during review.
- **Recommended**: only if Option A stalls.

### Option C: Path A first (full two-sided alphabet)

Per S5 audit §3.1, Path A is ~200 LOC of new mathematics (`windowPos_good`
is *not* a transfer; it is open research). The S5 audit's
recommendation is **defer Path A** until Path B is shipped — Path B
gives a clean win without the open mathematical questions.

- **Recommended**: No (defer to a later session after Path B).

**Selection**: **Option A** for S7 ACT. ETA: ~1 session, ~100 LOC.

## §7 Cross-reference to prior sessions

This PREP is the line-by-line audit promised in:

- S5 PREP §3.2 ("Path B preserves parent machinery") and §3.3
  ("S5c PREP — verify Path B's transfer-to-mixed-negatives proof
  obligation line-by-line"). PR #18703 merged 2026-05-13.

Distinct from:

- S1c PREP (PR #18487): proposed B′ for the two-sided alphabet
  abstractly; did not specify Path A vs Path B (those terms originate
  in S5).
- S3 PREP (PR #18424): the conjecture-E bridge plan, implemented by
  PR #19015's S6 ACT.
- S6 ACT (PR #19015): Conjecture E discharge + build unblockers for
  S2/S4 PRs. Touches the slug Lean file but in scope disjoint from
  Path B's level-counting argument.

## §8 Honest contribution boundary

What this PREP **does**:

- Verifies line-by-line that the parent's `levelPos_eq` (`:703–725`)
  and `level_achieved_ge_min` (`:599–640`) chains transfer to the
  mixed-down alphabet with exactly one 2-LOC adaptation (`rcases`
  destructure + `rw` label rename) per lemma. The critical
  `linarith [show (0 : ℤ) ≤ k …]` discharge is preserved because
  it depends only on `0 ≤ k`, not on `1 ≤ k` or `k ≤ m`.
- Refines the S5 audit §3.2 target from a slack inequality to an
  equality `(goodRotations l).card = l.sum.toNat`, with the slack form
  recovered as a one-line corollary.
- Refines the LOC budget from S5's ~80 LOC to ~100–102 LOC, with the
  delta sourced to `private`-helper duplication (S5 audit did not
  account for cross-file `private` access blocking).
- Surfaces a small structural choice (re-`private` vs un-`private`
  parent helpers vs inlining) for the S7 ACT author.
- Confirms Mathlib API surface unchanged from S2/S4/S6 — no drift
  surveillance needed.

What this PREP **does NOT** do:

- It does not prove or refute B′ in any scope. Path B's equality
  conclusion is established conditional on the audit's line-by-line
  verification being correct; the actual Lean proof remains to be
  written in S7 ACT.
- It does not modify `state.md` or the slug research JSON (race-safety
  with PR #19015).
- It does not address Path A (`windowPos_good` for the symmetric
  two-sided alphabet); that remains queued as S5 audit §3.1's open
  research.
- It does not propose merging Path B's result into the gallery's
  `meta.json` significance/originalContributions — that is the S7 ACT
  author's call once the Lean proof is in place.

## §9 Acceptance criteria for the PREP doc itself

- [x] Path B target statement refined (§2): equality form + slack-form
  corollary, both with explicit `hmem'` hypothesis.
- [x] Line-by-line audit covers all 7 parent-chain lemmas (§3).
- [x] Per-lemma transfer verdict + LOC budget tabulated (§3.7).
- [x] `private`-helper access issue surfaced + 3 implementation
  options enumerated (§3.4).
- [x] Mathlib API pin status confirmed unchanged from prior build-
  verified PRs (§4).
- [x] Conflict-free certification verified vs PR #19015 (§5).
- [x] Sequencing options enumerated with recommendation (§6).
- [x] Honest scope boundary explicit (§8): audit ≠ proof; Path A
  unaddressed; gallery JSON deferred to ACT author.

## §10 Next action

S7 ACT-B′ (Path B), post-#19015-merge, implementing the chain audited
in §3. Estimated session length: ~1 hour. Estimated PR delta:
~+102 LOC on `BallotProblemOQ01OQ01OQ02OQ01.lean` — 1 new theorem
`step_in_one_pos_mixed_neg_card_eq` + 1 slack-form corollary
`step_in_one_pos_mixed_neg_card_bound` + ~30 LOC of `private`
helper duplication. State.md + JSON + meta.json refresh as usual.

After Path B ships, the slug's phase advances to **ACT (Path B
shipped; Path A remains open research)** and a fresh PREP session can
take up Path A's `windowPos_good` question.
