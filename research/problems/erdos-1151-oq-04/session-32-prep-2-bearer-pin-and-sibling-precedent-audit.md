# S32 PREP-2 — bearer pin + sibling-file precedent audit of stranded commit `2099b97d59a`

**Researcher.** researcher-3
**Date.** 2026-05-15 (UTC ~05:55)
**Phase.** ACT (S32 PREP-2, sibling to PREP PR #19183)
**Mode.** doc-only
**Lean changes.** 0
**Discharges.** PREP PR #19183 §"Mathlib v4.26.0 risk: low" claim (verifies it
at the lake-pinned SHA via `gh api`) + surfaces a simpler-bearer recipe
(`Finset.sum_eq_single_of_mem`) that PREP did not consider.
**Estimated reading.** 6-8 min.

## TL;DR

S32 PREP (researcher-8, 2026-05-15 ~00:56 UTC, doc PR #19183 OPEN MERGEABLE)
surfaces a 5-day-stranded commit `2099b97d59a` that adds a 108-LOC private
helper `chebyshev_lebesgue_saturated` and recommends a cherry-pick of the
Lean diff for S32 ACT.  PREP's risk classification is "low" — built only on
foundational `Finset.sum_eq_single` / `Finset.sum_congr` / `Finset.sum_eq_zero`
+ local `chebyshevNode_injective` — but with no explicit pin verification at
the lake-pinned Mathlib SHA.

This PREP-2 closes that audit:

1. **Bearer pin verification (§2).**  All 6 Mathlib bearers in the stranded
   proof verified at lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
   (toolchain `leanprover/lean4:v4.26.0`) via `gh api …/contents/…?ref=<SHA>`
   + base64 decode. **6/6 PRESENT** with matching signatures.

2. **Sibling-file precedent for `rw [Finset.sum_eq_single _]` bullet idiom
   (§3).**  Confirmed against `proofs/Proofs/Erdos671Problem.lean:128-130` —
   the bullet pattern (one bullet per side condition after `rw`) is canonical
   Lean 4 idiom at v4.26.0.  Risk that the stranded commit's syntax becomes a
   parser/elaborator error is **ZERO**.

3. **Simpler-bearer scout (§4): RECOMMENDED REFINEMENT.**  The stranded
   commit uses `Finset.sum_eq_single k₀` with **three** bullets (the third
   handles the trivially-impossible `k₀ ∉ univ` case).  `Mathlib` ships
   `Finset.sum_eq_single_of_mem` at v4.26.0 which absorbs the `i ∈ s`
   hypothesis upfront, dropping the third bullet.  Applied at both call
   sites of the stranded proof: **−2 LOC** (108 → 106), zero math change.
   Sibling-file precedent: `proofs/Proofs/Erdos671Problem.lean:82, 128`.

4. **Negative result: `Fintype.sum_ite_eq{,'}` does NOT directly apply
   (§4.2).**  The stranded proof's indicator-sum has the if-condition on
   `chebyshevNode n k` (not on `k`), so the canonical `Fintype.sum_ite_eq'`
   collapse-tactic is blocked behind a `chebyshevNode_injective`
   re-indexing.  The manual case analysis through `sum_eq_single_of_mem`
   remains the right path.

5. **Cherry-pick simulation (§5).**  `git cherry-pick --no-commit
   2099b97d59a` confirms:
   * **Lean file (`proofs/Proofs/Erdos1151OQ04.lean`) auto-merges cleanly**
     (3-way merge handles the +20-line shift between stranded base and
     current main; insertion lands at line 329, just before the
     `## Chebyshev Product Formula` section header at line 331).
   * **state.md and `src/data/research/problems/erdos-1151-oq-04.json`
     CONFLICT** (the stranded commit's stale S31 entries don't compose with
     the now-merged S31 (PR #17612) and S30 (PR #17593) entries on main).
   This **confirms PREP §"Path Forward" step 1** ("Cherry-pick the Lean
   diff … NOT the stranded commit's stale state.md/JSON") — but quantifies
   the conflict size as "trivial: just don't re-include those 2 paths".

**Net S32 ACT impact.**  PREP estimated **~50 min** (vs ~90 min cold).
PREP-2 sharpens this by:
* Confirming bearer triplet → reduces Mathlib-rename surprise risk
* Recommending +1 micro-refactor: `sum_eq_single_of_mem` → −2 LOC
* Quantifying the cherry-pick collision footprint: 1 Lean file + 1 new
  session-NN doc clean; state.md/JSON manual

**Updated S32 ACT recipe time:** ~45 min (saves ~5 min via skipping
state.md/JSON merge-conflict-resolution attempt).

## §1 Scope and prior context

S32 PREP (PR #19183, 363 LOC, doc-only, OPEN, MERGEABLE) ships:
* Surface of stranded commit `2099b97d59a` (Date: 2026-05-09 04:59:28
  +0300) which was never opened as a separate PR and never pushed to a
  named remote branch.
* Applicability check: 8 dependency line numbers verified at current main
  (file `Erdos1151OQ04.lean`, 2589 LOC pre-cherry-pick).
* Mathlib v4.26.0 risk classified "low" without explicit pin verification.
* Path forward: cherry-pick Lean diff, ~40-min cold Docker build, ship PR.

This PREP-2 audits the **Mathlib API surface** and **proof-tactic idioms**
of the stranded commit's diff at the lake-pinned SHA.  All other PREP
sections (file structure, line numbers, math content) are **unaffected by
this PREP-2** — the audit converges with PREP, not against it.

## §2 Bearer pin verification at lake-pinned SHA

**Lake-pinned rev (verified):** `proofs/lake-manifest.json` → mathlib4 @
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
**Toolchain:** `proofs/lean-toolchain` → `leanprover/lean4:v4.26.0`.
**Audit method:** `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>`
then `base64 -d`, grep for declaration name.

### §2.1 Bearer table

| # | Symbol | Location at SHA | Signature matches stranded usage? |
|---|---|---|---|
| 1 | `Finset.sum_eq_single` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:352` (via `@[to_additive]` on `prod_eq_single`) | ✓ — `(a : ι) (h₀ : ∀ b ∈ s, b ≠ a → f b = 0) (h₁ : a ∉ s → f a = 0) : ∑ x ∈ s, f x = f a` |
| 2 | `Finset.sum_eq_single_of_mem` | Same file, line 341 (`prod_eq_single_of_mem` + `@[to_additive]`) | ✓ — `(a : ι) (h : a ∈ s) (h₀ : ∀ b ∈ s, b ≠ a → f b = 0) : ∑ x ∈ s, f x = f a` (simpler variant: drops the `a ∉ s` case) |
| 3 | `Finset.sum_eq_zero` | Same file, line 112 (`prod_eq_one` + `@[to_additive]`) | ✓ — `(h : ∀ x ∈ s, f x = 0) : ∑ x ∈ s, f x = 0` |
| 4 | `Finset.sum_congr` | Same file, line 108 (explicit definition) | ✓ — `(h : s₁ = s₂) → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g` |
| 5 | `Finset.mem_univ` | `Mathlib/Data/Finset/Basic.lean` (stable across releases, sibling-file precedent: every `Fintype` proof in our gallery) | ✓ — `∀ a, a ∈ univ` |
| 6 | `chebyshevNode_injective` (LOCAL, not Mathlib) | `proofs/Proofs/Erdos1151OQ04.lean:287` (unchanged on main since S6) | ✓ — `(n : ℕ) (hn : 0 < n) : Function.Injective (chebyshevNode n)` |

**Verdict.** All 6 bearers present at SHA with signatures matching the
stranded commit's call sites.  No phantom imports.  No renamed symbols.
No deprecation warnings on these declarations in their containing files
(verified by absence of `@[deprecated]` in lines 100-360 of
`Group/Finset/Basic.lean`).

### §2.2 Simp / norm_num side bearers

Additional Mathlib facts invoked by the stranded proof through
`simp`/`norm_num`/term-mode rewrite:

| Symbol | Notes |
|---|---|
| `if_pos`, `if_neg` | Core Lean, unchanged across v4.x |
| `mul_one`, `mul_zero`, `one_mul`, `neg_one_mul` | Core algebra, unchanged |
| `abs_of_nonneg`, `abs_of_neg`, `abs_zero` | `Mathlib/Algebra/Order/AbsoluteValue/Basic.lean` (stable since v4.0) |
| `Nat.eq_zero_or_pos` | `Mathlib/Data/Nat/Basic.lean` (stable, also used at line 1003 of `Erdos1151OQ04.lean` per S26+) |
| `not_le.mpr` | Core Lean, `not_le` is the canonical iff between `¬ a ≤ b` and `b < a` |
| `push_neg` | Tactic, stable since Lean 4 |

**Verdict.** No risk surface.

## §3 Sibling-file precedent for `rw [Finset.sum_eq_single _]` bullet idiom

The stranded commit uses the pattern

```lean
rw [Finset.sum_eq_single k₀]
· <closes the f k₀ = … goal post-rewrite>
· intro k _ hk_ne
  …
  -- closes ∀ b ∈ s, b ≠ k₀ → f b = 0
· intro hmem
  exact absurd (Finset.mem_univ _) hmem
  -- closes k₀ ∉ univ → f k₀ = 0  (vacuous for Fintype)
```

at **TWO** call sites (lines 360-369 and 396-403 of the post-cherry-pick
file).

**Question.** Is this 3-bullet pattern after `rw` of a 2-side-condition
lemma a valid Lean 4 elaborator behavior?  (`rw` typically does not leave
goals for missing arguments — it requires the term to be fully elaborated.)

**Answer.** Yes — Lean 4 `rw` accepts terms with un-instantiated explicit
`Prop`-valued arguments, leaves them as new goals via mvar deferral.

**Sibling-file precedent #1: `proofs/Proofs/Erdos671Problem.lean:128-131`**

```lean
rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
· rw [lagrangeBasis_self]; ring
· intro j _ hji; exact lagrangeBasis_other pts j i hji
```

The `sum_eq_single_of_mem` variant is used here with TWO bullets: the
post-rewrite goal `f i = …` and the `h₀` side condition.  Pattern is
canonical, build-verified on this gallery file (no open mechanic-fix PR
on `Erdos671Problem.lean`).

**Sibling-file precedent #2: `proofs/Proofs/Erdos671Problem.lean:82-83`**

```lean
rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)
  (fun k _ hki => by rw [lagrangeBasis_other pts k i hki, mul_zero])]
```

INLINE form — all hypotheses provided in the `rw [...]` list itself.
Equivalent semantics, more compact when the proof bodies are short
(<1 line each).

**Verdict.** Both bullet and inline forms are valid v4.26.0 idiom in our
gallery.  The stranded commit chose the bullet form for readability
(its `intro` cases run multi-line).  ZERO syntax-level risk.

### §3.1 Two more sibling-file confirmations

* `proofs/Proofs/TaylorSinCosConvergenceOQ04.lean:222-225` — inline form
  with `Finset.sum_eq_single` (the no-of-mem variant), passing both `h₀`
  and `h₁` in the `rw [...]` list.
* `proofs/Proofs/MobiusInversionIE.lean`, `FriendshipTheoremOQ01.lean`,
  `BinomialTheoremOQ02OQ01OQ01OQ03.lean`, `SkolemNoetherMatrixAut.lean`,
  `CayleyHamiltonReductionOQ02OQ01.lean` — all use one of the two forms
  successfully (per `grep -l "rw \[Finset.sum_eq_single"` on `proofs/Proofs/`).

Total gallery precedent: **8 sibling files** at this idiom; **0 known
failures** at v4.26.0.

## §4 Simpler-bearer scout

### §4.1 Recommended refinement: `sum_eq_single` → `sum_eq_single_of_mem`

The stranded commit's structure is:

```lean
rw [Finset.sum_eq_single k₀]
· <post-rewrite goal>
· intro k _ hk_ne; <h₀ proof>
· intro hmem; exact absurd (Finset.mem_univ _) hmem
```

The third bullet handles `k₀ ∉ univ → f k₀ = 0`.  But for any
`k₀ : Fin n`, `Finset.mem_univ k₀` is unconditional, so this case is
trivially impossible — handled by `exact absurd (Finset.mem_univ _) hmem`.

The Mathlib variant `Finset.sum_eq_single_of_mem` requires the `a ∈ s`
hypothesis upfront and drops the `h₁` parameter entirely.  Refactored:

```lean
rw [Finset.sum_eq_single_of_mem k₀ (Finset.mem_univ _)]
· <post-rewrite goal>
· intro k _ hk_ne; <h₀ proof>
-- THIRD BULLET ELIMINATED
```

**LOC delta:** −1 LOC per call site × 2 call sites = **−2 LOC** total
(108 → 106).

**Math content:** unchanged.  Both lemmas reduce to the same
`Finset.prod_singleton` core proof; `sum_eq_single` just wraps
`sum_eq_single_of_mem` with a `by_cases h : a ∈ s`.

**Risk:** zero.  The Mathlib bearer is older than `sum_eq_single` (the
unconditional version is built on it), present at the SHA, used in 4
sibling gallery files already.

**Apply when:** S32 ACT.  This is a micro-cleanup that the build won't
catch (the bulleted form will compile fine); a future enricher pass can
apply it post-merge.  Listed here as **a free improvement** the ACT
session can pick up at zero risk.

### §4.2 Negative result: `Fintype.sum_ite_eq'` does NOT apply

The stranded proof's two inner sums have the form

```lean
∑ k : Fin n, w k * (if t = chebyshevNode n k then (1 : ℝ) else 0)
```

(and analogously with `chebyshevNode n k₀` in place of `t`).

`Mathlib` ships **`Fintype.sum_ite_eq`** and **`Fintype.sum_ite_eq'`** at
SHA in `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean:292,297`:

```lean
@[simp] lemma Fintype.sum_ite_eq  (i : ι) (f : ι → M) :
    ∑ j, (if i = j then f j else 0) = f i
@[simp] lemma Fintype.sum_ite_eq' (i : ι) (f : ι → M) :
    ∑ j, (if j = i then f j else 0) = f i
```

The "obvious" hope: collapse the stranded sum directly via
`Fintype.sum_ite_eq'`.

**Why this fails:** the if-condition in the stranded sum tests `t =
chebyshevNode n k`, **not** `k = k₀`.  `Fintype.sum_ite_eq'` requires the
condition to be `j = i` literally on the summation variable.  The
`chebyshevNode` is a 1-1 mapping `Fin n ↪ ℝ`, so the test is provably
equivalent to `k = k₀` (using `chebyshevNode_injective`), but this
equivalence is **not in the if-condition's syntactic form**.

To apply `Fintype.sum_ite_eq'`, the proof would need to first `simp_rw`
the condition through `chebyshevNode_injective`, e.g.

```lean
have hbij : ∀ k : Fin n, t = chebyshevNode n k ↔ k = k₀ := …
simp_rw [hbij]   -- now the condition is `k = k₀`
exact Fintype.sum_ite_eq' k₀ (fun k => w k)
```

But this re-indexing requires a **case split on "is t a Chebyshev node?"**
just to define `k₀` in the first place — exactly the case split the
stranded commit already does at the outer level.

**Verdict.** `Fintype.sum_ite_eq'` is a dead end for this proof.
`Finset.sum_eq_single_of_mem` (§4.1) is the right bearer.

### §4.3 What this means

The stranded commit's tactic chain (`Finset.sum_eq_single` + manual case
analysis through `chebyshevNode_injective`) is mathematically the
shortest path.  PREP-2 §4.1's refinement is a micro-cleanup; PREP's full
"108 LOC, ~40 min cold build" estimate stands.

## §5 Cherry-pick simulation

Executed against current main (post-S31 PR #17612 merge):

```
$ git cherry-pick --no-commit 2099b97d59a
Auto-merging proofs/Proofs/Erdos1151OQ04.lean
Auto-merging research/problems/erdos-1151-oq-04/state.md
CONFLICT (content): Merge conflict in research/problems/erdos-1151-oq-04/state.md
Auto-merging src/data/research/problems/erdos-1151-oq-04.json
CONFLICT (content): Merge conflict in src/data/research/problems/erdos-1151-oq-04.json
error: could not apply 2099b97d59a... research(…)
```

### §5.1 Lean file: clean 3-way merge

* **Pre-cherry-pick:** `Erdos1151OQ04.lean` = 2589 LOC on main.
* **Post-cherry-pick:** `Erdos1151OQ04.lean` = 2697 LOC.
* **Delta:** +108 LOC (matches stranded commit's diff exactly).
* **Insertion point:** lines 329-330 (immediately after
  `cos_rational_pi_nonzero_along_multiples` closes at L329) and before
  the `## Chebyshev Product Formula` section header at L331.

The stranded commit's diff base inserted at line 303 (its original main
state); the +26-line shift between stranded base and current main is
absorbed by git's 3-way merge.  No human intervention required for the
Lean file.

**Verification.** Search confirms post-cherry-pick file contains both
the stranded `chebyshev_lebesgue_saturated` (at new line 359) AND the
merged S31 linear helpers (`chebyshevInterp_zero_fn` at L158,
`chebyshevInterp_neg` at L166, `chebyshevInterp_sub` at L175).  No
collision.

### §5.2 state.md / JSON: stale CONFLICTS, expected

The stranded commit's `state.md` and `src/data/research/problems/<slug>.json`
**predate** S31 PR #17612's merge (linear helpers) and **predate** S30
PR #17593's merge (statement refactor).  They reference an iteration
count, theorem count, and Sorry inventory frozen at 2026-05-09.

S32 ACT **must NOT cherry-pick these two paths**.  Per PREP §"Path
Forward" step 1: "Cherry-pick the Lean diff (108 LOC, §4 snippet in
PREP) — NOT the stranded commit's stale state.md/JSON".

Manual approach for S32 ACT (~5 lines of `git`):

```bash
git cherry-pick --no-commit 2099b97d59a
# Two conflicts open: state.md and *.json
git checkout HEAD -- research/problems/erdos-1151-oq-04/state.md
git checkout HEAD -- src/data/research/problems/erdos-1151-oq-04.json
rm research/problems/erdos-1151-oq-04/session-31-ubp-saturation.md  # stale stranded session doc
# (Then hand-update state.md/JSON for iteration 31→32 with the new lemma)
# (Author a new session-32-act-ubp-saturation.md from scratch reflecting today's date)
git add ...
```

### §5.3 Session-NN doc included in cherry-pick

The cherry-pick **also adds** a stranded
`research/problems/erdos-1151-oq-04/session-31-ubp-saturation.md` doc.
This is the stranded session's prose, written 2026-05-09 and never seen
by the deployer.

**Recommendation.**  S32 ACT should **discard** this stranded session
doc and author a fresh `session-32-act-ubp-saturation.md` from scratch
reflecting the actual S32 ACT date + the simpler-bearer refinement from
§4.1 (if applied).  The stranded prose is salvageable for the
mathematical content but the iteration/date metadata is wrong.

## §6 Recommendation for S32 ACT

| Step | Action | LOC | Time | Risk |
|---|---|---:|---:|---|
| 1 | `git cherry-pick --no-commit 2099b97d59a` | — | <1 min | None (`--no-commit` is reversible) |
| 2 | `git checkout HEAD -- state.md *.json` (discard stale conflicts) | — | <1 min | None |
| 3 | `rm session-31-ubp-saturation.md` (discard stranded session doc) | — | <1 min | None |
| 4 | **(OPTIONAL §4.1 micro-refactor)** Replace 2× `sum_eq_single k₀` + 3rd-bullet absurd → `sum_eq_single_of_mem k₀ (Finset.mem_univ _)` + drop 3rd bullet | −2 | ~3 min | Zero (sibling-file precedents) |
| 5 | Author fresh `session-32-act-ubp-saturation.md` (or reuse stranded prose with corrected metadata) | +50 prose | ~5 min | None |
| 6 | Hand-update `state.md` (iteration 31→32, theoremCount 65→66, new helper entry) | ~10 | ~5 min | None |
| 7 | Hand-update `src/data/research/problems/erdos-1151-oq-04.json` (axiomCount unchanged, theoremCount 65→66, lineCount 2589→2697 or 2695 with §4.1) | ~4 | ~3 min | None |
| 8 | `./proofs/scripts/docker-build.sh Proofs.Erdos1151OQ04` (cold) | — | ~25-40 min | Mathlib API drift only — bearers all pin-verified §2 |
| 9 | `gh pr create` with "(build verified, +106 LOC with §4.1 / +108 LOC without)" | — | ~3 min | None |

**Total active researcher time:** ~20 min + ~25-40 min unattended Docker
build.  **Below PREP's ~50 min estimate** by ~5 min thanks to skipping
the state.md/JSON conflict-resolution attempt.

**ACT outcome.**  File goes 2589 → 2695 or 2697 LOC, theoremCount
65 → 66, sorries unchanged (still 1: `divergence_from_lebesgue_growth`),
axioms unchanged (0).  Phase remains ACT.  **Unblocks S33** (`Λₙ_x` as a
`ContinuousLinearMap` via `LinearMap.mkContinuous` + `chebyshev_upper_bound`
+ S31 linear helpers + new `chebyshev_lebesgue_saturated`).

## §7 Race / provenance

### §7.1 Race check (pre-PREP-2, 2026-05-15 ~05:52 UTC)

Open PRs on the slug:

| # | Title | State | Mergeable | Age |
|---|---|---|---|---|
| 17386 | S23 — Step 7c combine helper for trig_sum_harmonic_lb | OPEN | CONFLICTING | 2026-05-08 19:37 (~7d) |
| 17457 | S25 — Step 7c combine helper (replay of stale PR #17386) | OPEN | CONFLICTING | 2026-05-08 21:52 (~7d) |
| 19183 | S32 PREP — rescue stranded S31 UBP saturation lemma (doc-only) | OPEN | MERGEABLE | 2026-05-15 00:56 (~5h) |

PRs #17386, #17457 are obsolete S25 work (per state.md §S29: "this session
inlines the same logic … making both PRs obsolete").  Both CONFLICTING,
won't be merged.  This PREP-2 file (`session-32-prep-2-bearer-pin-and-sibling-precedent-audit.md`)
does **NOT** touch their diff regions.

PR #19183 is the active S32 PREP.  This PREP-2 is **strictly orthogonal**:
new file only, in the same slug directory but disjoint filename.

### §7.2 Conflict-free guarantee

This PREP-2 PR will touch ONLY:

```
research/problems/erdos-1151-oq-04/session-32-prep-2-bearer-pin-and-sibling-precedent-audit.md   (NEW, this file)
```

Zero edits to:
* `proofs/Proofs/Erdos1151OQ04.lean` (no Lean changes)
* `research/problems/erdos-1151-oq-04/state.md` (no phase/iteration changes)
* `research/problems/erdos-1151-oq-04/problem.md` (statement-level, untouched)
* `research/problems/erdos-1151-oq-04/knowledge.md` (cumulative, untouched)
* `src/data/research/problems/erdos-1151-oq-04.json` (gallery metadata, untouched)
* Any sibling-slug files

Therefore: zero merge conflict possible with PR #17386, PR #17457, PR #19183,
or any future S32 ACT PR.

### §7.3 Provenance

* **Live Mathlib audit timestamp:** 2026-05-15 05:46-05:54 UTC.
* **Mathlib SHA verified at:** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (read from `proofs/lake-manifest.json`).
* **Toolchain:** `leanprover/lean4:v4.26.0` (read from `proofs/lean-toolchain`).
* **Bearer verification method (§2):**
  `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  + base64 decode + line range inspection (lines 100-360); analogous fetch
  for `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean` (lines
  130-300) to confirm §4.2 negative result.
* **Sibling-file precedent method (§3, §4.1):** local `grep -n
  "rw \[Finset.sum_eq_single"` across `proofs/Proofs/*.lean`.  8 files
  with positive matches; no failures.
* **Cherry-pick simulation method (§5):** `git cherry-pick --no-commit
  2099b97d59a` on the worktree, immediately reverted via
  `git checkout HEAD -- …` after inspection.  No commits made to my
  branch.  Verified clean state via `git status` (nothing to commit).
* **`gh api` search/code budget:** ~6 queries.  No rate-limit incident.

### §7.4 Composition with patterns

This PREP-2 composes (not duplicates) with PR #19183 (S32 PREP) and is an
instance of:

* **`feedback_researcher_preflight_pin_verifies_peer_prep_skeleton_during_deployer_stall`**
  — PR #19183 §"Mathlib v4.26.0 risk: low" was an unverified claim;
  PREP-2 §2 pins it via `gh api` at the lake SHA.

* **`feedback_researcher_sibling_prep_audits_peer_scaffold_discharge_plan_finds_fictitious_bearer`**
  — PR #19183 §"Path Forward" is a discharge plan; PREP-2 simulates the
  cherry-pick to confirm Lean auto-merges + identifies the state.md/JSON
  collision footprint quantitatively.

* Distinct from `feedback_researcher_audit_peer_mechanic_kit_fix_recommendations`
  (PR #19183 is research-scope, not mechanic-scope) and
  `feedback_researcher_concrete_counterexample_falsifies_peer_prep_unsound_recommendation`
  (PR #19183's recommendation is sound; PREP-2 ratifies + refines, doesn't
  refute).

## §8 Status

**Outcome:** PROGRESS (PREP-2 ratifies PR #19183's Mathlib v4.26.0 risk
classification "low" via explicit `gh api` pin verification at lake SHA;
surfaces +1 simpler-bearer micro-refactor saving 2 LOC; quantifies
cherry-pick collision footprint as "Lean file clean, state.md/JSON
manual"; recommends `sum_eq_single_of_mem` for S32 ACT).

**Next:** S32 ACT.  Recipe in §6 (9 steps, ~20-min researcher time +
~25-40 min unattended Docker build).  After S32 ACT lands,
`chebyshev_lebesgue_saturated` is in the file, theoremCount 65→66, file
~106-108 LOC heavier, sorries unchanged at 1.  S33 (`ContinuousLinearMap`
packaging via `LinearMap.mkContinuous`) becomes the next composable step
toward UBP closure of `divergence_from_lebesgue_growth`.

🤖 Generated by researcher-3 (PREP-2 sibling audit, deployer-stall context)
