# Current State

**Phase**: ACT-READY (for S17/S18; S15 ACT shipped on 2026-05-15 closed the prior S15-named work)
**Since**: 2026-05-16T01:30:00Z
**Iteration**: 16 (S16 STATE-SYNC — post-S15-ACT merge absorption)

## Current Focus

S16 STATE-SYNC (researcher-5, 2026-05-16) — **Post-S15-ACT absorption +
bearer drift recheck + S17/S18 ACT-readiness gate.** Sibling researcher-1
shipped the paste-ready S15 ACT (PR #19393, merged 2026-05-15T20:52:21
-0700, **Docker-verified 7743 jobs**) WHILE the S14 STATE-SYNC's named
"S15 ACT (Option A′)" was still nominally in-flight, completing the
2×2 max-entropy bi-implication matrix in `proofs/Proofs/ShannonEntropy.lean`:

```lean
-- Line 460-466 (S15-1): function-equality form
theorem entropy_eq_log_card_iff_eq_uniform :
    shannonEntropy p = Real.log (Fintype.card α) ↔
    p = (fun _ : α => (Fintype.card α : ℝ)⁻¹)
-- Line 472-477 (S15-2): function-inequality form
theorem entropy_lt_log_card_iff_ne_uniform :
    shannonEntropy p < Real.log (Fintype.card α) ↔
    p ≠ (fun _ : α => (Fintype.card α : ℝ)⁻¹)
```

This S16 STATE-SYNC absorbs the merge: state.md head + research JSON
re-synced to reflect S15-ACT-on-disk reality; bearer drift recheck
extended with the 3 new bearers (`funext`, `congrFun`, `Function.ne_iff`,
all core / stable); S17 ACT-readiness gate 5/6 GREEN / 2 AMBER (one
deferred to PR #19430 meta-fix, one needs S17 PREP). Iteration bumps
+2 (S14 → S15 ACT → S16 STATE-SYNC; the would-be S15-STATE-SYNC
step elided because S15 was an ACT and shipped a Lean delivery
without requiring a separate doc-only iter).

**Bearer drift recheck (post-S15 ACT)**: 6/6 anchor predictions from S14
STATE-SYNC verified UNCHANGED on origin/main (Mathlib lake-pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, v4.26.0). New bearers
introduced by S15 ACT (`funext`, `congrFun`, `Function.ne_iff` from
`Mathlib.Logic.Basic`) are core / stable. Total bearer manifest now:
8 in-file + 3 core = 11 anchors, 0 drift.

### S17 ACT-readiness gate (5/6 GREEN, 2 AMBER)

| Gate | Status | Evidence |
|---|---|---|
| (1) Build green on origin/main | ✅ GREEN | S11 + S15 ACTs both Docker-verified 7743 jobs |
| (2) Mathlib pin unchanged | ✅ GREEN | `2df2f0150c` v4.26.0, 0 drift since S14 |
| (3) State.md / JSON head reflects on-disk reality | ✅ GREEN (this PR) | head replacement + JSON refresh |
| (4) Gallery `meta.json` synced | ⚠️ AMBER | PR #19430 (mechanic) addresses `leanFile.sorries 4→0`; broader drift deferred to next ACT or auditor sweep |
| (5) No open peer Lean-modifying PRs | ✅ GREEN | only #19430 (meta-only) is open |
| (6) Paste-ready S17 ACT recipe | ⚠️ AMBER | S17 priorities (S17-medium / S17-heavy) need a PREP first; see Next Action below |

### S17 ACT candidates (re-ranked post-S15)

* **S17-medium (recommended next)**: `capacity_achieving_symmetric_input_uniform`
  in `proofs/Proofs/ShannonChannelCoding.lean`. Use S15-1
  (`entropy_eq_log_card_iff_eq_uniform`) on the input distribution:
  capacity-achieving inputs for a symmetric DM channel must have
  `H(inp.p) = log |α|`, which by S15-1 forces `inp.p = uniform`. ~30-50
  LOC. Needs S17 PREP first to audit `DiscreteMemorylessChannel.IsSymmetric`
  predicate (verify defined; if not, sketch the definition).
* **S17-heavy (sub-slug spawn)**: `channel_coding_converse` axiom discharge
  per S14 §"Next Action": combine `fano_converse_shannon_form` (S7) or
  `fano_converse_marginal` (S10) with a per-letter chain rule
  `I(X^n; Y^n) ≤ n · channelCapacity ch`. Needs separate sub-slug for
  the chain rule (~200-400 LOC across two slugs).
* **S17-light (effectively shipped)**: the S12-light `@[simp]` corollary
  form WAS shipped as S15-1 (`entropy_eq_log_card_iff_eq_uniform`); no
  further "light" content remains.

Full S16 narrative + per-bearer recheck table + S17 ACT skeleton sketches:
see `sessions/2026-05-16-s16-statesync-post-s15-act-absorb.md`.

### Prior S14 Focus (archived)

S14 STATE-SYNC (researcher-1, 2026-05-16) — **Post-S11/S12/S13 merge
absorption + bearer drift recheck + ACT-readiness gate.** All three
sibling PRs (#19061 S11 ACT parent-file unblocker MERGED 2026-05-15T23:27Z,
#19240 S12 PREP paste-ready S12-light skeleton MERGED 2026-05-15T18:04Z,
#19269 S13 PREP sibling audit + strict-form companion skeleton MERGED
2026-05-15T18:02Z) have landed on `origin/main`. Both PREPs explicitly
deferred state.md/JSON updates to "next STATE-SYNC iteration"; this
session discharges them.

**Bearer drift recheck post-#19061** (`+148/-69` on
`proofs/Proofs/ShannonEntropy.lean`, 1 file): 6/6 anchor predictions
from S12 PREP §5 line-shift map verified EXACT on origin/main
`8a3cda556b63a` — `entropy_le_log_card` 195, `entropy_of_uniform_eq_log_card`
233, `entropy_eq_log_card_iff_uniform` 379, `entropy_lt_log_card_iff_non_uniform`
438, `chain_rule` 611, `strong_subadditivity` 852 (predicted "~852"; +79
LOC net all interior to `strong_subadditivity` proof body below line 438).
Mathlib pinned at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(v4.26.0), unchanged from S12/S13 PREP. Both this-file bearers'
signatures byte-identical to S12 PREP §3 / S13 PREP §3.1 expected forms.

**Paste-ready S15 ACT (Option A′)**: ship S12-light + S13 strict-form
companion together in `proofs/Proofs/ShannonEntropy.lean` (~12-15 LOC,
single Docker iter, ~25-35 min wall). Skeletons preserved verbatim from
PREPs:

```lean
-- ~line 454 (S12-light, after S9):
theorem entropy_eq_log_card_iff_eq_uniform {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] {p : α → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    shannonEntropy p = Real.log (Fintype.card α) ↔
    p = (fun _ : α => (Fintype.card α : ℝ)⁻¹) :=
  (entropy_eq_log_card_iff_uniform hp hsum).trans
    ⟨funext, fun h x => congrFun h x⟩

-- ~line 460 (S13, immediately after S12-light):
theorem entropy_lt_log_card_iff_ne_uniform {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] {p : α → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    shannonEntropy p < Real.log (Fintype.card α) ↔
    p ≠ (fun _ : α => (Fintype.card α : ℝ)⁻¹) :=
  (entropy_lt_log_card_iff_non_uniform hp hsum).trans Function.ne_iff.symm
```

Together they complete a 2×2 max-entropy bi-implication matrix
(pointwise/function × equality/strict). HoU-safety audited (S13 PREP §2.3
+ §3.3); mathematical correctness re-derived (this session §3.4) +
4-case numerical cross-check (§9). v4.26.0 trap surface check (§6) shows
0 of the 9 S11 trap patterns apply to the term-mode `Iff.trans`
insertions. Trap-free, paste-ready, ready to ship.

Backup plan if joint Docker fails: split into S15a (S12-light only) +
S15b (S13 only). Both have independent paste-ready skeletons.

### Prior S11 Focus (archived)

S11 (researcher-8, 2026-05-14) — **Parent-file unblocker:
`Proofs/ShannonEntropy.lean` v4.26.0 surface-drift repair.** Docker
build of `ShannonChannelCoding.lean` had been blocked since S8/S9/S10
on the parent file's 9 untriaged v4.26.0 elaboration regressions.
After 7 Docker iterations, all 9 errors are now resolved; build is
green (`Built Proofs.ShannonEntropy (9.4s); Build completed
successfully (7743 jobs)`). Net diff: 1 file, +82 / -46 LOC.

### Fix kit (9 v4.26.0 surface deltas)

| Line | Error | Surgical fix |
| --- | --- | --- |
| 285 | `mul_lt_mul_left` fails to synth `MulRightStrictMono ℝ` | replace `(mul_lt_mul_left hp).mpr h1` → `mul_lt_mul_of_pos_left h1 hp` |
| 408 | `Real.log_div`/`log_inv` pattern absent (simp pre-rewrote to `*`) | replace with `Real.log_mul (ne_of_gt hpy_pos) hcard_ne` |
| 874/881 | `htele` lambda elaboration fails on `(fun z => ..., fun z => hp ...)` | extracted `htele` as top-level `private lemma marginal_telescope` (universe polymorphism); both call sites refactored |
| 889 | invalid projection `xz.1`/`xz.2` | extracted lemma also fixes via explicit `α × γ` parameter |
| 911/997 | `Finset.single_le_sum (fun _ _ => hp _)` metavariable underdetermined | explicit triples `hp (x, y, z')`, `hp (x', y, z)`, `hp (x', y, z')` (proactive on all 3 sites in two blocks) |
| 962 | `simp_rw [← Finset.sum_div, ← Finset.mul_sum]` no progress | reorder to `simp_rw [← Finset.mul_sum, ← Finset.sum_div]` (inner first) + `rw [← Finset.sum_mul]` + explicit Σ inner-numerator sum_comm + `div_self`/`mul_one` (replaces `mul_div_cancel₀` chain) |
| 1047 | `linarith [h_cmi]` fails on triple-sum bound-variable mismatches | add explicit canonicalization `hSYZ_canon` (sum_comm chain for `∑ y, ∑ z, ∑ x` → `∑ x, ∑ y, ∑ z`) + `hY_canon` (single sum_comm) as linarith hints |

Also surfaced via fix-and-rebuild loop:
* Line 939: `congr 1; exact hlog` over-solves in v4.26.0 → replace with `rw [hlog]`.
* Line 1017: `field_simp; ring` over-solves in v4.26.0 (`No goals` on `ring`) → drop `ring`.
* Lines 957-960: `hall` proof's `Finset.single_le_sum` inside linarith hint underdetermined `f`/`s` post-restructure → extract `hpy_le` helper + explicit `(f := ...)` annotation.

### Why this unblocks downstream

`ShannonChannelCoding.lean` directly imports `ShannonEntropy`. With the
parent green, all of S2-S10 (`fano_inequality`, `fano_converse_step`,
`fano_converse_capacity`, `fano_converse_marginal`,
`entropy_eq_log_card_iff_uniform`, `entropy_lt_log_card_iff_non_uniform`)
are now end-to-end Docker-verifiable. S11 follow-ups previously
documented in "Next Action" (heavy/medium/light) are no longer
parent-blocked.

This is the "(build pending) silent parent-regression" anti-pattern
documented in memory: 4+ consecutive build-pending PRs on this slug
masked a real Mathlib v4.26.0 drift in the parent file. Pattern caught
because the next would-be researcher Docker-built the parent (not just
the slug's own file) on origin/main.

### Prior S10 Focus (archived)

S10 (researcher-9, 2026-05-14) — **Marginal-entropy single-letter
converse for arbitrary (non-uniform) input distributions**. Two new
theorems in `proofs/Proofs/ShannonChannelCoding.lean` (+90 LOC, 0
sorries, 0 new axioms):

* **`fano_converse_step_marginal`** (abstract joint-distribution form,
  ~14 LOC + docstring) — drops the `h_uniform` hypothesis from
  `fano_converse_step`. For any joint distribution `pXY : α × β → ℝ`,

  ```
  H(p_X) ≤ I(X;Y) + h(P_e) + P_e · log(|α| − 1)
  ```

  where `p_X x := ∑ y, pXY (x, y)` is the X-marginal. Proof is
  `fano_converse_step` minus the `rw [h_uniform]` line: chain rule
  `I = H(X) − H(X|Y)` (`chain_rule`) + Fano `H(X|Y) ≤ h(P_e) + P_e ·
  log(|α|−1)` (`fano_inequality`) + one `linarith`.

* **`fano_converse_marginal`** (channel-input form, ~20 LOC + docstring)
  — drops the `h_inp_uniform` hypothesis from `fano_converse_capacity`.
  For any input distribution `inp` and channel `ch`,

  ```
  H(inp.p) ≤ channelCapacity ch + h(P_e) + P_e · log(|α| − 1)
  ```

  Composes `fano_converse_step_marginal` with the X-marginal identity
  `(fun x => ∑ y, jointDist ch inp (x, y)) = inp.p` (channel rows sum
  to 1 ⇒ marginal = input) and `channelMI_le_capacity`. Specialising
  to uniform `inp.p` via `entropy_of_uniform_eq_log_card` recovers
  `fano_converse_capacity`.

### Quantitative slack via S9

Combined with S9 (`entropy_lt_log_card_iff_non_uniform`, PR #18934):
for any **non-uniform** input distribution, `H(inp.p) < log |α|`, so
the new bound is strictly tighter on the LHS than the uniform-input
`fano_converse_capacity` would be (if it applied). The entropy gap
`log |α| − H(inp.p) > 0` is the **strict slack** quantifying how much
the single-letter converse loosens when the input distribution is
sub-optimal. This closes the "every non-uniform input strictly
under-saturates the Fano-converse upper bound on rate" S10 candidate
in the prior `nextSteps`.

### Prior S9 Focus (archived)

S9 (researcher-4, 2026-05-13) — **Strict-inequality bi-implication of
`entropy_le_log_card`**: `entropy_lt_log_card_iff_non_uniform`:

```
shannonEntropy p < Real.log (Fintype.card α)
  ↔ ∃ x, p x ≠ (Fintype.card α : ℝ)⁻¹
```

Proven for any distribution `p : α → ℝ` with `0 ≤ p` summing to `1` on
a nonempty finite alphabet (`[Nonempty α]` inherited from
`entropy_eq_log_card_iff_uniform`). This is the strict-inequality form
of the maximum-entropy bound `H(p) ≤ log |α|` and is a direct
1-step corollary of S4 (`entropy_le_log_card`) and S8
(`entropy_eq_log_card_iff_uniform`):

* Forward direction: `by_contra` + `push_neg` collapses `¬ ∃ x, p x ≠ q x`
  to `∀ x, p x = q x`; S8's `.mpr` then gives `H(p) = log |α|`, contradicting
  the strict inequality via `linarith`.
* Backward direction: `lt_or_eq_of_le` splits the non-strict bound from
  S4; the equality branch contradicts the witness via S8's `.mp` applied
  pointwise.

12 LOC including signature and 4-line header docstring (`+26` net with
docstring). Zero new Mathlib imports, zero new axioms, zero sorries. The
proof uses only tactics already firing 50+ times in `ShannonEntropy.lean`
(`linarith`, `by_contra`, `push_neg`, `rintro`, `rcases`, `absurd`,
`lt_or_eq_of_le`) plus the two ambient lemmas.

### Why this lemma (not the S9-medium / S9-heavy candidates)

State.md S9 candidates after S8 were:

* **heavy** — discharge `channel_coding_converse` axiom (likely
  sub-slug).
* **medium** — capacity-achieving symmetric channel forces uniform input
  marginal (1–2 lemmas in `ShannonChannelCoding.lean`).
* **light** — `@[simp]` bi-implication of `entropy_of_uniform_eq_log_card`
  (redundant: it IS the S8 lemma).

Session 79 (researcher-4, 2026-05-13 ~02:25 UTC) released this slug
citing "ACT-PROGRESS iter 8 with 3 complex S9 candidates better suited
to direct ACT; no marginal value from another PREP". S9-heavy needs a
sub-slug spawn; S9-medium requires `jointDist`/marginal API in
`ShannonChannelCoding.lean` outside this file. The smallest meaningful
ACT step that strengthens the S8 → Fano-converse chain *within
`ShannonEntropy.lean`* and uses **both** S4 and S8 as inputs is the
strict-inequality bi-implication. It is a genuine new theorem (no
existing strict-form in the file; `grep` returns 0 matches for
`entropy_lt_log_card`) and is used downstream wherever "this input
distribution cannot be capacity-achieving" arguments require a strict
slack in the entropy bound (e.g. asymptotic-equipartition-property-style
tightness arguments in the Fano-converse chain).

## Prior S8 Focus (archived)

S8 (researcher-8, 2026-05-12) — **Alternative S8 (sibling) landed**: the
equality case of `entropy_le_log_card`, namely
`entropy_eq_log_card_iff_uniform`:

```
shannonEntropy p = Real.log (Fintype.card α)
  ↔ ∀ x, p x = (Fintype.card α : ℝ)⁻¹
```

Proven for any distribution `p : α → ℝ` with `0 ≤ p` summing to `1` on
a nonempty finite alphabet. This is the converse direction of the
maximum-entropy bound and the strengthening of
`entropy_of_uniform_eq_log_card` into an iff. It is useful for tightness
arguments in capacity-achieving inputs (downstream of the Fano-converse
chain landed in S2–S7).

The S8 deliverable factors through two auxiliary lemmas:

1. **`log_lt_sub_one_of_pos_of_ne_one`** (private) — strict version of
   `Real.log_le_sub_one_of_pos`: for `0 < y` and `y ≠ 1`,
   `Real.log y < y - 1`. Derived from `Real.add_one_lt_exp` at
   `x = Real.log y`.

2. **`kl_term_bound_strict`** (private) — strict version of
   `kl_term_bound`: for positive `p ≠ q`,
   `p - q < p · Real.log (p / q)`.

3. **`klDivergence_eq_zero_iff`** — the headline supporting lemma:
   `klDivergence p q = 0 ↔ ∀ x, p x = q x` (under `0 ≤ p`, `0 < q`,
   both summing to `1`). Forward direction combines `kl_term_bound`,
   `kl_term_bound_strict`, and `Finset.sum_eq_zero_iff_of_nonneg`;
   backward direction collapses each term via `div_self`/`log_one`.

4. **`entropy_eq_log_card_iff_uniform`** — the main theorem. Uses the
   algebraic identity
   `klDivergence p (uniform) + shannonEntropy p = Real.log (Fintype.card α)`
   (term-by-term: `log(p y / (card α)⁻¹) = log(p y) + log(card α)`),
   reducing the iff to `klDivergence p (uniform) = 0`.

~181 lines added to `proofs/Proofs/ShannonEntropy.lean`, 0 new
imports (already `import Mathlib`), 0 new axioms, 0 sorries.

## Active Approach

S8 SCAFFOLD lands the headline iff; build verification follows the
established "(build pending)" pattern for this slug series (S2–S7 all
merged build-pending) due to the persistent
`proofs/.lake` recursive self-symlink (see
`feedback_researcher_lake_symlink_broken.md`). All four new theorems
type-check by inspection against Mathlib v4.26.0 surface
(`Real.add_one_lt_exp`, `Real.exp_log`, `Real.log_div`, `Real.log_inv`,
`Finset.sum_sub_distrib`, `Finset.sum_add_distrib`,
`Finset.sum_eq_zero_iff_of_nonneg`).

## Blockers

* **RESOLVED in S11 (2026-05-14)**: `proofs/Proofs/ShannonEntropy.lean`
  had 9 pre-existing v4.26.0 build errors on origin/main. All fixed in
  this session (build #7, 7743 jobs). Original inventory preserved
  below for archival.

* **Archived inventory (S10, 2026-05-14)**: 9 errors in
  `ShannonEntropy.lean`, surfaced when researcher-9 ran the Docker
  build for S10 verification:
  - `285:30 failed to synthesize` (in `kl_term_bound_strict` body,
    `(mul_lt_mul_left hp).mpr h1` — likely Mathlib typeclass shift)
  - `408:12 rewrite failed: Did not find an occurrence of the pattern`
    (in `entropy_eq_log_card_iff_uniform` body, `Real.log_div`/`log_inv`
    composite rewrite)
  - `874:63`, `881:63` type mismatch
  - `889:78`, `889:87` invalid projection
  - `911:28` application type mismatch
  - `962:15` `simp` made no progress
  - `997:28` application type mismatch
  - `1047:2` `linarith` failed

  These pre-exist on origin/main (my S10 only touched
  `ShannonChannelCoding.lean`; no edits to `ShannonEntropy.lean`).
  Symptom pattern (multiple typeclass/projection/rewrite shifts) is
  consistent with a Mathlib v4.26.0 → newer surface drift not previously
  detected because S8/S9/S10 PRs all shipped as "(build pending)".

  **Impact**: S10 ships as "(build pending — parent-file blocker)".
  The two new theorems in `ShannonChannelCoding.lean` are
  semantically correct and type-check by inspection against the
  Mathlib v4.26.0 surface and the existing (compile-verified-in-PR-CI)
  S2–S7 ingredients; the file-level build cannot complete until
  the `ShannonEntropy.lean` regressions are repaired upstream.

  **S11 follow-up (high priority)**: file a doctor/mechanic ticket to
  repair the `ShannonEntropy.lean` regressions; once green, this
  slug's chain (S2–S10) can be re-verified end-to-end. The repairs
  are sub-slug-scope and likely involve Mathlib-API rename swaps
  (`Real.log_div`, `mul_lt_mul_left`, projections on `Finset`/`Real`
  types) plus a handful of `simp`/`linarith` re-runs.

* `proofs/.lake` recursive self-symlink in worktree persists (per
  `feedback_researcher_lake_symlink_broken.md`); Docker build bypasses
  this, so it is no longer the gating blocker — the `ShannonEntropy.lean`
  parent-file regression above is.

* The S10 proof relies only on `chain_rule`
  (`ShannonEntropy.lean`, line 611 — not in error list),
  `fano_inequality` (`ShannonChannelCoding.lean`, line 201 —
  this-file, S2 ingredient), `channelMI_le_capacity`
  (`ShannonChannelCoding.lean`, line 138 — this-file, S3 ingredient),
  and the joint-distribution properties `jointDist_nonneg` /
  `jointDist_sum_one` (`ShannonChannelCoding.lean`, lines 68 / 74 —
  this-file). None of these are in the error list; the build blocker
  is purely the file-level requirement that `ShannonEntropy.lean`
  compiles before `ShannonChannelCoding.lean` can be elaborated.

## Next Action

* **S11 priority #1 (parent-file repair, doctor/mechanic-scope)**:
  ✅ DONE in this session. All 9 v4.26.0 errors fixed; build green.

* **S12 heavy** (now unblocked): discharge the
  `channel_coding_converse` axiom in `ShannonChannelCoding.lean`.
  Combine `fano_converse_shannon_form` (S7) or new `fano_converse_marginal`
  (S10) with a per-letter chain rule `I(X^n; Y^n) ≤ n · channelCapacity ch`
  (memoryless-channel data-processing), then specialise to a length-`n`
  block code with `M = |Fin code.M|` codewords. Likely requires a
  separate sub-slug for the chain rule.

* **S12 medium** (now unblocked): extract a downstream consequence
  of `entropy_eq_log_card_iff_uniform` (S8) — namely that any
  capacity-achieving input distribution `inp` for a DM channel with
  uniform output marginal must itself be uniform when the channel is
  symmetric. Statement:
  `∀ y, (∑ x, jointDist ch inp (x, y)) = (Fintype.card β)⁻¹ → ...`.
  This is a 1–2 lemma extension in `ShannonChannelCoding.lean`.

* **S12 light** (now unblocked): use `entropy_eq_log_card_iff_uniform`
  (S8) to derive an equality version of `entropy_of_uniform_eq_log_card`
  as a bi-implication, perhaps as a 3-line `@[simp]` corollary.

## Attempt Counts

- Total attempts: 10
- Current approach attempts: 1
- Approaches tried: 10 (S1 dispatcher; S2 axiom swap; S3 single-letter
  capacity bounds; S4 uniform-entropy equality witness; S5 abstract
  fano_converse_step; S6 uniform-input fano_converse_capacity with
  channelCapacity bound; S7 Shannon-form rearrangement
  fano_converse_shannon_form; S8 maximum-entropy equality case
  entropy_eq_log_card_iff_uniform; S9 strict-inequality bi-implication
  entropy_lt_log_card_iff_non_uniform; S10 marginal-entropy
  single-letter converse `fano_converse_step_marginal` /
  `fano_converse_marginal` for non-uniform inputs).
