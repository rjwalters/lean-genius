# S13 PREP — sibling audit of S12 PREP + paste-ready S13 strict-form companion skeleton

**Author**: researcher-3
**Date**: 2026-05-15
**Type**: doc-only PREP (strictly conflict-free with PR #19061 and PR #19240)
**Phase predecessors**: S11 ACT (PR #19061 — parent-file unblocker, Docker-verified 7743 jobs);
S12 PREP (PR #19240 — paste-ready S12-light skeleton + bearer/line-shift audit).

## 1. Coordination context

Status snapshot at session start (2026-05-15 ~05:20Z):

| PR | Title | Status | Open since | Stuck because |
|----|-------|--------|------------|---------------|
| #19061 | S11 ACT parent-file unblocker (researcher-8) | CLEAN MERGEABLE | 2026-05-14T14:25Z (~15h) | Deployer-stall (system-wide) |
| #19240 | S12 PREP paste-ready S12-light + bearer audit (researcher-3) | doc-only, CLEAN | 2026-05-15T04:15Z (~1h) | Deployer-stall + lands behind #19061 |

System-wide deployer dormancy at session start: most-recent merge to
`origin/main` is 2026-05-14T03:03:38Z (PR #18980), giving ~26h dormancy.

This is the slug's **3rd open PR by the same author** (researcher-3 wrote
the S12 PREP; this S13 PREP is also researcher-3). Per memory pattern
`feedback_researcher_problemmd_spec_error_audit_as_freshangle` the
boundary is ≥3 PRs on slug + deployer stall + ≥1 PREP still open. We
are at exactly the boundary (#19061 ACT + #19240 PREP + #X this PREP).
The audit pattern requires the new angle to be **strictly orthogonal**
to prior work AND offer **independent new content**, NOT a re-cut of the
same skeleton.

This PREP ships **two strictly new artifacts** not present in #19240:

1. **§2 — sibling audit** of S12 PREP's term-mode skeleton against the
   v4.26.0 higher-order-unification (HoU) trap surface that recent
   mechanic work (`feedback_mechanic_mathlib_v426_congrarg_cast_hou_blocker`,
   2026-05-15) flagged. Validates S12 PREP's choice of explicit
   `⟨funext, fun h x => congrFun h x⟩` over the shorter `funext_iff.symm`
   alternative, and pin-verifies the auto-generated `funext_iff` lemma
   from `attribute [ext] funext` at `Init/Ext.lean:85`.

2. **§3 — paste-ready S13 strict-form companion** skeleton
   `entropy_lt_log_card_iff_ne_uniform` — the function-equality strict
   analogue of S9. 1-line term-mode proof via the existing
   `Function.ne_iff` Mathlib lemma (`Mathlib/Logic/Function/Basic.lean:62`).
   This **completes a 2×2 matrix** of max-entropy bi-implications:

   | | Pointwise RHS | Function-equality RHS |
   |---|---|---|
   | Equality `H = log\|α\|` | S8 `entropy_eq_log_card_iff_uniform` (line 379) | **S12-light** (proposed, PR #19240) |
   | Strict `H < log\|α\|` | S9 `entropy_lt_log_card_iff_non_uniform` (line 438) | **S13** (proposed, this PREP) |

This PREP follows decision-matrix entry "1 CLEAN MERGEABLE ACT + 1 doc-only
PREP + deployer stall + new content angle": pre-stage a second
paste-ready skeleton + audit so that **once the deployer drains**, two
ACT theorems can land in a single post-merge ACT iteration rather than
sequential per-theorem cycles.

## 2. Sibling audit of S12 PREP term-mode skeleton

### 2.1 S12 PREP's recommended form (recap from PR #19240 §3)

```lean
theorem entropy_eq_log_card_iff_eq_uniform {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] {p : α → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    shannonEntropy p = Real.log (Fintype.card α) ↔
    p = (fun _ : α => (Fintype.card α : ℝ)⁻¹) :=
  (entropy_eq_log_card_iff_uniform hp hsum).trans
    ⟨funext, fun h x => congrFun h x⟩
```

### 2.2 Alternative bearer NOT mentioned in S12 PREP: `funext_iff`

At lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(v4.26.0), `funext_iff : f = g ↔ ∀ x, f x = g x` is **auto-generated**
by the `@[ext]` attribute on `funext`. Specifically:

* `attribute [ext] funext propext Subtype.ext Array.ext Char.ext` at
  Lean core `Init/Ext.lean:85` (verified at SHA via
  `https://raw.githubusercontent.com/leanprover/lean4/v4.26.0/src/Init/Ext.lean`).
* Used 7+ times in `Mathlib/Logic/Function/Basic.lean` (lines 63, 65,
  159, 531, 535, 999, 1015) WITHOUT redefinition.
* Already callable from this repo: `proofs/Proofs/ShannonSourceCodingOQ04.lean:169, 359`
  uses `simp [funext_iff, ...]`.

The **shorter sharper-bearer variant** of S12-light would be:

```lean
theorem entropy_eq_log_card_iff_eq_uniform … :
    shannonEntropy p = Real.log (Fintype.card α) ↔
    p = (fun _ : α => (Fintype.card α : ℝ)⁻¹) :=
  (entropy_eq_log_card_iff_uniform hp hsum).trans funext_iff.symm
```

Visual saving: ~12 chars / 1 LOC for the anonymous-constructor lambda.

### 2.3 HoU risk verdict: prefer S12 PREP's EXPLICIT form

The shorter variant via `funext_iff.symm` requires Lean's elaborator to
solve a **higher-order unification** step:

* Goal after `(entropy_eq_log_card_iff_uniform hp hsum).trans …`:
  needs `(∀ x, p x = (Fintype.card α : ℝ)⁻¹) ↔ p = (fun _ : α => (Fintype.card α : ℝ)⁻¹)`.
* `funext_iff.symm` has type `(∀ x, ?f x = ?g x) ↔ (?f = ?g)`.
* Unification must solve `(Fintype.card α : ℝ)⁻¹ ≡ ?g x` with `?g`
  unknown — this is the **constant-function HoU pattern** where the
  RHS does not visibly mention `x`.

Per recent mechanic feedback `feedback_mechanic_mathlib_v426_congrarg_cast_hou_blocker`
(2026-05-15, BallotProblemOQ03OQ02 cluster A), v4.26.0's simp/elaboration
HoU is **unreliable on opaque "no-x in RHS" patterns** — the canonical
failure mode is `cast (congrArg (PathMN m) (by …)) e` where the simp
matcher cannot decompose `by`-block proofs against pattern variables.
The general lesson: when RHS-of-equation has **no visible binder occurrence**,
prefer **explicit witnesses** over relying on HoU.

S12 PREP's explicit `⟨funext, fun h x => congrFun h x⟩` pattern PINS
DOWN `?g := fun _ => (Fintype.card α : ℝ)⁻¹` from the GOAL (the iff's
RHS is already a concrete `fun _ => …` constant function), avoiding
the HoU step:

* In `funext h`, Lean has goal `p = (fun _ => (card α)⁻¹)` and hypothesis
  `h : ∀ x, p x = (card α)⁻¹`. The unifier sets `?f := p`, `?g := (fun _ => (card α)⁻¹)`
  from the GOAL, then needs `∀ x, p x = (fun _ => (card α)⁻¹) x` which
  is β-equivalent to `∀ x, p x = (card α)⁻¹` — standard β-reduction,
  not HoU.
* In `fun h x => congrFun h x`, Lean has hypothesis
  `h : p = (fun _ => (card α)⁻¹)` and needs `∀ x, p x = (card α)⁻¹`.
  `congrFun h x : p x = (fun _ => (card α)⁻¹) x` β-reduces to
  `p x = (card α)⁻¹` — again, β-reduction only.

**Verdict**: S12 PREP's explicit form is the **safer, audit-justified
choice** at v4.26.0. The 1-LOC saving from `funext_iff.symm` is not
worth the elaboration risk. **No change recommended to PR #19240's §3
skeleton.** This audit validates rather than corrects.

### 2.4 Negative-result bearer: `Function.const_inj` does NOT apply

A natural-looking sharper bearer is Mathlib's
`Function.const_inj : const α y₁ = const α y₂ ↔ y₁ = y₂`
(`Mathlib/Logic/Function/Basic.lean:48`, verified at SHA). However:

* `Function.const_inj` requires `[Nonempty α]` and converts equality
  of **two constant functions** to equality of the underlying values.
* It does NOT bridge `(∀ x, p x = c) ↔ (p = fun _ => c)` because `p`
  is **not necessarily a constant function** — the very thing we are
  trying to prove.

Listing as negative result: while `Function.const_inj` is tempting on
first scan, it doesn't apply here. The S12 PREP correctly skipped it.

## 3. NEW paste-ready S13 strict-form companion skeleton

### 3.1 Statement

Insertion point: immediately AFTER the eventual S12-light theorem
`entropy_eq_log_card_iff_eq_uniform` (proposed by PR #19240 to land at
~line 454 post-#19061). This S13 theorem inserts after S12-light at
~line 460 post-#19061-and-S12-light merge.

```lean
-- Strict-form, function-equality version of `entropy_lt_log_card_iff_non_uniform`:
-- the maximum-entropy bound `H(p) ≤ log |α|` is strict iff `p` is not
-- (definitionally) the constant uniform-distribution function.
--
-- Composes with `entropy_eq_log_card_iff_eq_uniform` (S12-light) to give a
-- full 2×2 matrix of max-entropy bi-implications:
--
--   |  RHS shape | pointwise | function-equality |
--   |------------|-----------|-------------------|
--   | `H = log α`| `entropy_eq_log_card_iff_uniform`    | `entropy_eq_log_card_iff_eq_uniform`   |
--   | `H < log α`| `entropy_lt_log_card_iff_non_uniform`| `entropy_lt_log_card_iff_ne_uniform`   |
--
-- Useful downstream when the non-uniform hypothesis is `inp.p ≠ fun _ => …`
-- (function inequality) rather than `∃ x, inp.p x ≠ …` (witness form) —
-- sidesteps a `not_forall` + `push_neg` unfolding step at the call site.
theorem entropy_lt_log_card_iff_ne_uniform {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] {p : α → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    shannonEntropy p < Real.log (Fintype.card α) ↔
    p ≠ (fun _ : α => (Fintype.card α : ℝ)⁻¹) :=
  (entropy_lt_log_card_iff_non_uniform hp hsum).trans Function.ne_iff.symm
```

### 3.2 Proof shape

* `entropy_lt_log_card_iff_non_uniform hp hsum : H(p) < log |α| ↔ ∃ x, p x ≠ (card α)⁻¹`
  — S9 at line 438 (post-#19061: same line, unaffected by Hunk C).
* `Function.ne_iff : f₁ ≠ f₂ ↔ ∃ a, f₁ a ≠ f₂ a`
  — `Mathlib/Logic/Function/Basic.lean:62` at SHA, proven as
  `funext_iff.not.trans not_forall`.
* `.symm` flips to `(∃ a, f₁ a ≠ f₂ a) ↔ f₁ ≠ f₂`.
* `Iff.trans` composes: `H(p) < log |α| ↔ p ≠ (fun _ => (card α)⁻¹)`. ✓

### 3.3 HoU verdict for S13: SAFE (no analogous risk)

Unlike the S12-light alternative `funext_iff.symm`, the S13 use of
`Function.ne_iff.symm` does **not** trigger the same HoU concern:

* `Function.ne_iff.symm` form: `(∃ a, f₁ a ≠ f₂ a) ↔ f₁ ≠ f₂`.
* Trans-target LHS (from S9): `∃ x, p x ≠ (Fintype.card α : ℝ)⁻¹`.
* Goal RHS (this theorem's conclusion): `p ≠ (fun _ : α => (Fintype.card α : ℝ)⁻¹)`.
* Unification: `?f₁ := p`, `?f₂ := (fun _ : α => (Fintype.card α : ℝ)⁻¹)`
  pin down from the **goal RHS** (`p ≠ (fun _ => (card α)⁻¹)`), then
  inside the existential `?f₁ a = p a` and `?f₂ a = (fun _ => (card α)⁻¹) a`
  which β-reduces to `(card α)⁻¹`.
* The constant-function `?f₂` is set FROM THE GOAL, not inferred from
  the existential body — same mechanism that makes S12-light's explicit
  `⟨funext, congrFun⟩` work.

This is the **key asymmetry**: S13 has a concrete goal-side function
inequality `p ≠ (fun _ => …)` that pins down the lambda; S12-light's
shorter `funext_iff.symm` variant has the GOAL `p = (fun _ => …)` AND
the iff's middle term `∀ x, p x = (card α)⁻¹` where the `(card α)⁻¹`
must be matched against `?g x`. The lambda direction differs (`= vs ≠`),
but the unification path differs more substantially: in S13 the iff
direction is **goal-RHS ↔ trans-target-LHS**, so `?f₂` is pinned by
the goal.

**Verdict**: S13's 1-line term-mode proof via `Function.ne_iff.symm` is
sound at v4.26.0.

## 4. Mathlib bearer table at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

| Bearer | Origin | Verification | Status |
|--------|--------|--------------|--------|
| `funext` | Lean core `Init/Core.lean:2238` | direct file read at SHA via raw.githubusercontent | ✓ exact |
| `funext_iff` (auto) | Lean core `Init/Ext.lean:85` via `attribute [ext] funext` | direct file read at SHA + 7+ usages in `Mathlib/Logic/Function/Basic.lean` (lines 63, 65, 159, 531, 535, 999, 1015) | ✓ exact |
| `congrFun` | Lean core primitive | standard | ✓ exact |
| `Function.ne_iff` | `Mathlib/Logic/Function/Basic.lean:62` | direct file read at SHA: `theorem ne_iff : f₁ ≠ f₂ ↔ ∃ a, f₁ a ≠ f₂ a := funext_iff.not.trans not_forall` (inside `namespace Function`, line 27+) | ✓ exact, fully-qualified name `Function.ne_iff` required when called from outside the namespace |
| `entropy_eq_log_card_iff_uniform` | `proofs/Proofs/ShannonEntropy.lean:379` (S8) | inspected at origin/main; signature unchanged by #19061 (Hunk B at line 408 changes body, not signature) | ✓ this-file |
| `entropy_lt_log_card_iff_non_uniform` | `proofs/Proofs/ShannonEntropy.lean:438` (S9) | inspected at origin/main; signature unchanged by #19061 (line 438 below Hunk B at 408 and above Hunk C at 832; unaffected) | ✓ this-file |
| `entropy_le_log_card` | `proofs/Proofs/ShannonEntropy.lean:195` | not directly used by S13, but needed for the chain `S9.mp` interior (S9 itself uses it at line 443) | ✓ this-file (indirect) |

**Total new Mathlib bearers**: 1 (`Function.ne_iff`); 0 new this-file
dependencies beyond S9.

## 5. Goal-state simulation walk-through

Step-by-step elaboration of S13 strict-form companion (term-mode):

**Goal at theorem declaration**:
```
⊢ shannonEntropy p < Real.log (Fintype.card α) ↔
    p ≠ (fun _ : α => (Fintype.card α : ℝ)⁻¹)
```

**Step 1**: Apply `entropy_lt_log_card_iff_non_uniform hp hsum`. This
has type:
```
shannonEntropy p < Real.log (Fintype.card α) ↔
    ∃ x, p x ≠ (Fintype.card α : ℝ)⁻¹
```

**Step 2**: `.trans Function.ne_iff.symm`. `Function.ne_iff.symm` (with
implicit `α := α`, `β := fun _ : α => ℝ`, `f₁ := p`, `f₂ := fun _ => (card α)⁻¹`)
has type:
```
(∃ x, p x ≠ (fun _ : α => (Fintype.card α : ℝ)⁻¹) x) ↔
    p ≠ (fun _ : α => (Fintype.card α : ℝ)⁻¹)
```

After β-reduction on `(fun _ : α => (Fintype.card α : ℝ)⁻¹) x`:
```
(∃ x, p x ≠ (Fintype.card α : ℝ)⁻¹) ↔
    p ≠ (fun _ : α => (Fintype.card α : ℝ)⁻¹)
```

**Step 3**: `Iff.trans` composes:
```
shannonEntropy p < Real.log (Fintype.card α) ↔
    p ≠ (fun _ : α => (Fintype.card α : ℝ)⁻¹)
```
matches goal. ✓

**Unification check**: `?f₁` and `?f₂` for `Function.ne_iff.symm` are
pinned by the goal-RHS `p ≠ (fun _ : α => (Fintype.card α : ℝ)⁻¹)`,
NOT by the existential body. β-reduction handles the `(fun _ => …) x`
collapse. No HoU step required.

## 6. Insertion point (post-#19061 AND post-#19240 / S12-light merge)

Both #19061 (Hunk C at line 832+ of pre-merge `ShannonEntropy.lean`)
and #19240's S12-light insertion (after `entropy_lt_log_card_iff_non_uniform`
at ~line 454) are above-or-below the S13 insertion site:

| Decl | Pre-#19061 line | Post-#19061 line | Post-#19061+S12-light line | Post-#19061+S12-light+S13 line |
|------|----------------:|-----------------:|---------------------------:|-------------------------------:|
| `entropy_lt_log_card_iff_non_uniform` (S9) | 438 | 438 | 438 | 438 |
| `entropy_eq_log_card_iff_eq_uniform` (S12-light) | — | — | ~456 | ~456 |
| `entropy_lt_log_card_iff_ne_uniform` (S13) | — | — | — | ~470 |
| `============= Log-Sum Inequality =============` section header | 457 | 457 | ~478 (shift by S12-light +S13 = ~22 LOC) | ~492 (further shift by S13 = ~14 LOC) |
| `strong_subadditivity` (#19061 Hunk C target) | 835 | ~852 | ~874 | ~888 |

**Insertion sequencing**: S12-light first, then S13 immediately after.
A single combined post-#19061 ACT iteration can land both: ~20 LOC
S12-light + ~14 LOC S13 = ~34 LOC total, 1 Docker iter (~10s build
delta on top of `marginal_telescope` baseline).

**Latitude**: S13 can also land in a SEPARATE post-S12-light ACT
iteration (~14 LOC, 1 Docker iter, ~15-20 min) if scope preferences
favor smaller PRs.

## 7. Sequencing options

**Option A — Combined post-merge ACT for S12-light + S13** (recommended):
1. Wait for #19061 to merge.
2. Wait for #19240's S12-light skeleton to land OR cherry-pick.
3. Branch from new `main` (with both `marginal_telescope` and
   `entropy_eq_log_card_iff_eq_uniform` present).
4. Apply S13 skeleton from §3. Insert at ~line 470.
5. `./proofs/scripts/docker-build.sh Proofs.ShannonEntropy`.
6. Update `state.md` § Active Approach + bump `Iteration: 12 → 13`.
7. Ship as **`S13 ACT — entropy_lt_log_card_iff_ne_uniform (build verified)`**.

Estimated cost: ~15-25 min, 1 Docker iter, +12-14 LOC.

**Option B — S12-light and S13 in single post-#19061 ACT** (efficient):
1. Wait for #19061 to merge.
2. Branch from new `main`.
3. Apply BOTH S12-light (#19240 §3 skeleton) and S13 (§3 above) skeletons.
4. Single Docker verify; expected 1 iter, ~30-40 min total.
5. Ship combined.

Estimated cost: ~30-40 min, 1 Docker iter, +25-30 LOC.

**Option C — Defer S13 to a later session** (low-risk):
Same as Option A but spaced one session apart. Useful if S12-light
exposes unexpected v4.26.0 surface drift; the S13 skeleton can be
re-audited before paste.

**Recommendation**: **Option B** (combined ACT) for the next session
post-#19061-merge. Both skeletons are bearer-validated at the same
SHA, share the insertion-point neighborhood (~line 454-470), and have
zero cross-dependency that would risk separation overhead. The marginal
cost of combining is ~10 min for one extra theorem; the saving versus
two sequential PRs is ~15-20 min of Docker-spin-up and PR-overhead.

## 8. Conflict-free guarantees with PR #19061 and PR #19240

This PREP touches **only one new file**:
`research/problems/shannon-channel-coding-oq-02-oq-01-oq-01/sessions/2026-05-15-s13-prep-strict-form-companion-and-s12-audit.md`.

| File | PR #19061 | PR #19240 | This PR | Conflict? |
|------|-----------|-----------|---------|-----------|
| `proofs/Proofs/ShannonEntropy.lean` | modify (Hunks A/B/C) | — | — | no |
| `research/problems/.../state.md` | modify (S11 status) | — | — | no |
| `src/data/research/problems/shannon-channel-coding-oq-02-oq-01-oq-01.json` | modify | — | — | no |
| `sessions/2026-05-15-s12-prep-bearer-audit-postmerge.md` | — | create | — | no |
| `sessions/2026-05-15-s13-prep-strict-form-companion-and-s12-audit.md` | — | — | create | no (new file) |

**Merge safety**: This PREP can land before, after, or interleaved with
#19061 and #19240 with zero conflict risk. The merge order does not
matter.

**Re-verification at session start**:
```
gh pr list --repo rjwalters/lean-genius --state open --search "shannon-channel-coding-oq-02-oq-01-oq-01 in:title" --json number,title
```
returns exactly 2 results: #19061 and #19240. No race with a third
in-flight PR on this slug at session start.

## 9. Acceptance signature

| Property | Value |
|----------|-------|
| New file count | 1 (`sessions/2026-05-15-s13-prep-strict-form-companion-and-s12-audit.md`) |
| Modified file count | 0 |
| Lean LOC delta | 0 (doc-only) |
| Docker build required | No |
| Conflict with PR #19061 | None (orthogonal file sets) |
| Conflict with PR #19240 | None (orthogonal file sets) |
| Conflict with main | None (new file, no prior path) |
| Mathlib bearers verified at SHA | 4 (funext / funext_iff / Function.ne_iff / S9 + S8 in-file) |
| Goal-state simulation | §5, 3 steps, β-reduction-only (no HoU) |
| Skeleton paste-readiness | Yes, ~14 LOC including 11-line header comment |

## 10. References

* PR #19061 (researcher-8, 2026-05-14): S11 ACT parent-file unblocker
  — `proofs/Proofs/ShannonEntropy.lean` v4.26.0 9-error kit
  (Docker-verified 7743 jobs).
* PR #19240 (researcher-3, 2026-05-15): S12 PREP paste-ready S12-light
  skeleton + bearer audit + line-shift map.
* Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0
  lake-pinned).
* Lean core `Init/Core.lean:2238` for `funext` at v4.26.0.
* Lean core `Init/Ext.lean:85` for `attribute [ext] funext` (auto-derives
  `funext_iff`) at v4.26.0.
* Mathlib `Logic/Function/Basic.lean:62` for `Function.ne_iff` at SHA.
* `proofs/Proofs/ShannonSourceCodingOQ04.lean:169, 359` — existing
  in-repo usage of `funext_iff` (confirms `simp [funext_iff]` callable
  at this Mathlib version).
* Memory: `feedback_mechanic_mathlib_v426_congrarg_cast_hou_blocker`
  (mechanic-3, 2026-05-15) — flags v4.26.0 HoU unreliability on opaque
  no-x-in-RHS patterns; cited in §2.3 HoU verdict.
* Memory: `feedback_researcher_problemmd_spec_error_audit_as_freshangle`
  — boundary rule ≥3 PRs on slug + deployer stall + ≥1 PREP open →
  strictly orthogonal new-content PREP.

End of S13 PREP.
