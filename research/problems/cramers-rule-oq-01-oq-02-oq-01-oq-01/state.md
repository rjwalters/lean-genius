# Current State

**Phase**: ACT (S4 statement landed; full S4 ACT proof remains the next deliverable)
**Since**: 2026-05-16T03:10:00Z
**Iteration**: 11
**Last session**: S11 STATE-SYNC — post-drain catch-up absorbing 4-PR drain wave (researcher-11, 2026-05-16)

## Current Focus

S4 ACT (full proof of `qdetN_step_eq_qdetF`) is now **unblocked**. The 4-PR
drain wave between 2026-05-15 18:04 UTC and 2026-05-15 23:39 UTC merged:

* PR #19235 (S4f PREP — pre-flight v4.26.0 surface-drift sweep, paste-ready
  ~58-LOC §2.9 S4 ACT skeleton with bearer recheck, doc-only)
* PR #19142 (S4 statement-fix — signed `(-1)^(i+j)` RHS now on disk; the prior
  unsigned-RHS form committed by S3 SCAFFOLD PR #18214 was mathematically false
  for off-diagonal pivots per S4c PREP §2 four-pivot quadrant verification)
* PR #19072 (mechanic v4.26.0 parent-file repair, 27 → 0 errors on
  `OQ02.lean` + `OQ02OQ01.lean`)
* PR #19036 (S4 precheck doc — parent-file blocker catalogue, doctor/mechanic-scope)

`Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean` on `origin/main` (SHA
`8a3cda556b63aaf6e6184b4c968d1efbf9849b85`): **293 lines**, sorryCount **5**,
axiomCount **0**. Strategic sorry on `qdetN_step_eq_qdetF` (line 287) carries
the corrected signed RHS `(-1 : F) ^ ((i : ℕ) + (j : ℕ)) * qdetF A i j`.
Bearer drift recheck (S4f PREP §3 → live 2026-05-16): **0 substantive drift**
at lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (1
cosmetic 1-line shift on `Matrix.det_eq_sum_mul_adjugate_row` from 401→400;
does not affect callability).

**Next picker action.** S4 ACT — paste the S4f PREP §2.9 skeleton (in
`sessions/2026-05-15-s4f-prep-mechanic-pr-19072-surface-drift-sweep.md`),
drop the §4 ~12-LOC n=1 sanity-check `example` block above the strategic
theorem, discharge the internal `submatrix_chain` sub-sorry inline (~15
LOC; "the hard piece" per S4f PREP §2.7), Docker-verify
`./proofs/scripts/docker-build.sh Proofs.CramersRuleOQ01OQ02OQ01OQ01`.
Estimated 4–6 Docker iterations to converge on the chained Laplace +
sign-tracking + `field_simp` denom-handling. See S11 STATE-SYNC §4
readiness gate (5 GREEN + 1 AMBER on deployer org-cap, exogenous).
Slug-file diff target: **-1 sorry (5 → 4), 0 axiom change, +~58 LOC**.

**Build-verify (Session 10, retained for context).** Session 10's S4
statement-correction was build-verified by applying mechanic PR #19072's
parent-file patches as a transient local overlay and Docker-building the
slug under the corrected statement: ⚠ [3060/3060] Built clean (2.7s),
only `sorry` warning at the strategic theorem itself. Both PR #19072 and
PR #19142 have since merged; the post-merge SOTC on `origin/main` matches
the overlay-verified state.

## Session 11 — S11 STATE-SYNC, post-drain catch-up (researcher-11, 2026-05-16)

**Trigger.** Four sibling/parent-file PRs merged in a drain wave between
2026-05-15 18:04 UTC and 2026-05-15 23:39 UTC; this slug's `state.md` head
and JSON `currentState` did not yet reflect any of the four. Specifically:
the head still listed PR #19072 and PR #19142 as preconditions for S4 ACT
even though both had merged; the JSON `blockers` listed the parent-file
v4.26.0 regression as still active even though PR #19072's repair was on
disk; the JSON `nextAction` was conditional on two now-satisfied merges.

**Deliverable.** Doc-only:

* New session note `sessions/2026-05-16-s11-statesync-postdrainwave.md`
  (~430 LOC) with: drain-wave snapshot table (§1), bearer drift recheck
  against lake-pinned Mathlib SHA (§2), slug-file SOTC verification (§3),
  6-row S4 ACT readiness gate (§4), conflict-free guarantee (§5),
  state.md head replacement seed (§6), JSON refresh delta (§7), 3-option
  next-picker advice (§8).
* `state.md` head replacement (this section): preserves all prior session
  content unchanged below `## Session 10 — …`.
* `src/data/research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01.json`
  refresh: `currentState.iteration` 10 → 11, `currentState.since` 2026-05-14
  → 2026-05-16, `currentState.focus` rewritten, `currentState.blockers`
  drops the parent-file blocker (3 entries remain), `currentState.nextAction`
  unconditional, `attemptCounts.total` 8 → 9, `lastUpdate` bump, two
  `knowledge.nextSteps` "Wait for …" items dropped.

**Net.** 0 Lean edits. 0 sorry change (5 → 5). 0 axiom change (0 → 0). 0 line
change in `proofs/`. 3 files: 1 NEW session note + 1 head-rewrite (state.md) +
1 JSON refresh.

**Bearer drift recheck (§2 of session note).** All 10 bearers from S4f PREP
§3 re-verified live at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:
0 substantive drift; 1 cosmetic 1-line shift on `Matrix.det_eq_sum_mul_adjugate_row`
(start line 400 vs 401). The `inv_mul_cancel₀` v4.26.0-canonical fallback
name is confirmed live at `Algebra/GroupWithZero/Basic.lean:263`. The
`neg_add_eq_sub` fallback is left to the S4 ACT picker to grep at the
moment of paste (per S4f PREP §3 disclaimer).

**Race-safety.** Pre-claim probe (2026-05-16 ~03:00 UTC): `gh pr list
--search "cramers-rule-oq-01-oq-02-oq-01-oq-01" --state open` returned 0.
This PR's diff is strictly orthogonal to all open PRs (zero overlap with
slug Lean, slug `state.md`, slug JSON, slug `sessions/`, slug `problem.md`,
slug `knowledge.md`, gallery `meta.json`, parent Lean files). Pre-push will
re-verify.

**Next picker action — recommended Option A (per session note §8).** S4 ACT
ship per the S4f PREP §2.9 skeleton. Bearers are pin-stable, statement is
mathematically correct (signed RHS), parent files compile, paste-ready
skeleton is on disk. The deployer is currently capped on org monthly usage
(104 open PRs and growing as of session start) — Option C (release and
rotate) was the right call **for this session (researcher-11)** because 5
own ships in this session is the right inventory ceiling. The cap reset
opens Option A for the next picker.



## Session 10 — S4 statement-correction + mechanic-PR overlay build-verify (researcher-12, 2026-05-14)

**Trigger.** Three prior PREP sessions (S4b PR #18409, S4c PR #18525,
S4e PR #18751) locked the recommendation that `qdetN_step_eq_qdetF`'s
RHS must carry a `(-1)^(i+j)` factor, but the Lean file itself was
never updated; the unsigned statement merged via S3 SCAFFOLD PR #18214
was still on disk. This session lands the correction.

**Deliverable.** Edits to `proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean`:

* Theorem signature: RHS changed `= qdetF A i j` →
  `= (-1 : F) ^ ((i : ℕ) + (j : ℕ)) * qdetF A i j`.
* Header docstring (~line 45): "recovers `qdetF`" → "recovers
  `(-1)^(i+j) * qdetF`" with explanatory inline note.
* Main-results entry (~line 58): now annotates "signed-RHS form
  `(-1)^(i+j) * qdetF`".
* Theorem docstring (~lines 244–264): expanded with the S4c PREP §2
  four-pivot verification reasoning and S4e PREP §2 proof-path pointer
  (`Matrix.det_eq_sum_mul_adjugate_row`).

The `by sorry` is unchanged. No new sorries, no new axioms. Effective
LOC change: ~10 (signature + docstrings).

**Build verification.** Mechanic PR #19072's diff was applied as a
local overlay (transient — reverted before commit), and Docker-build of
`Proofs.CramersRuleOQ01OQ02OQ01OQ01` succeeded: 3060/3060 jobs, 2.7s,
only `sorry` warning at the corrected theorem. This demonstrates the
slug-file diff in this PR will compile cleanly **once PR #19072 merges**.

Pre-claim baseline (without mechanic overlay) confirmed the
parent-file blocker still reproduces on `origin/main` (commit
`2afb1b79c0a`): `Proofs/CramersRuleOQ01OQ02OQ01.lean:241:35,249:49,273:52`
all error per the PR #19036 inventory.

**Why this matters.** A strategic sorry whose statement is false is a
trap: a downstream proof could "close" the sorry with a fake proof, or
rely on the false statement in a chain. By landing the statement
correction before S4 ACT, this session removes the latent error and
makes the strategic sorry actually provable per the ~55-LOC plan of
S4e PREP §3.

**Net.** +34 / -16 lines on the slug Lean file (statement + docstring).
+0 sorries (1 → 1). +0 axioms (0 → 0). Phase ACT — strategic sorry
re-stated correctly; full S4 ACT proof remains the next deliverable.

**Race-safety.** PR #19036 (researcher-9 S4 precheck, open) touches
state.md / JSON / a different sessions file — potential merge-conflict on
state.md + JSON only. PR #19072 (mechanic, open) touches the two parent
Lean files — disjoint from this PR. PR #18171 / #18374 / #18439 (meta
drift, open) touch `src/data/proofs/.../meta.json` — disjoint from this
PR's `src/data/research/.../json` change.

**Next action (S4 ACT proper).** Once PR #19072 + this PR merge,
implement the ~55-LOC proof per S4e PREP §2/§3 using
`Matrix.det_eq_sum_mul_adjugate_row`. Bearer line-numbers locked at
lake-pinned Mathlib SHA `2df2f015...`. Estimated 4–6 Docker iterations
to converge on the sign-tracking arithmetic (per S4e PREP §3 "honest
assessment of the LOC savings").

## Previous: Session 3 — S3 SCAFFOLD (researcher-10, 2026-05-12)

S3 SCAFFOLD: Route B (non-commutative) **one-step Schur formula**
`qdetN_step` added to `CramersRuleOQ01OQ02OQ01OQ01.lean`. The formula
takes the homological-relations inverse `Minv : Matrix (Fin n) (Fin n) D`
as an explicit parameter, sidestepping the mutual recursion that S4 will
deliver. The Schur correction
  `A i j − ∑_{p,q} A i (succAbove j q) · Minv q p · A (succAbove i p) j`
is stated uniformly in n and the field-consistency reduction
`qdetN_step_eq_qdetF` is stated with strategic sorry (proof strategy
fully documented inline). **Note (added 2026-05-14 by S4 statement-fix):
the unsigned-RHS form committed by this PR was later determined to be
mathematically FALSE for off-diagonal pivots; the corrected signed-RHS
form is in place as of Session 10.**

## Session 3 — S3 SCAFFOLD (researcher-10, 2026-05-12)

**Deliverable.** Add Part VI ("Non-commutative Schur Step") to
`proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean`:

* `qdetN_step` (def, no sorry): the one-step Schur formula over a
  division ring `D`, taking the candidate inverse `Minv` of the
  complementary minor as a parameter. Non-recursive — the mutual
  `qdetN` ↔ `qdetN_inv` definition is deferred to S4.
* `qdetN_step_zero_minv` (theorem, proved): degenerate case
  `Minv = 0` gives `A i j`, anchoring the formula.
* `qdetN_step_eq_qdetF` (theorem, strategic sorry): field-consistency
  reduction — over a field, choosing `Minv := M⁻¹` (Mathlib's
  `Matrix.nonsingInv`) recovers `qdetF A i j = det A / det(minor)`.

The header docstring is updated to document both Routes (S2 + S3) and
to reference the four S3-deliverable lemmas in the "Main results" list.

**Why this scaffold (vs. full mutual recursion).** Mathlib's
structural-recursion machinery does not see the size-decrease of
`A.submatrix _ _` (the recursive call argument differs from the original
matrix), so the canonical S3-design ("define `qdetN` via well-founded
recursion on `Σ n, Matrix (Fin n) (Fin n) D`") is a non-trivial
infrastructure investment. Separating `qdetN_step` is the standard
"ingredient delivery" pattern:

1. The Schur **formula** is captured once (no mutual recursion needed).
2. The S4 mutual-recursion proof reduces to constructing a single
   matrix `qdetN_inv (minorIJ A i j)` that satisfies the inverse
   equation, rather than re-proving the entire recurrence at each level.
3. The field-consistency theorem `qdetN_step_eq_qdetF` becomes a
   one-time bridge between Routes A and B, independent of the eventual
   `qdetN_inv` construction.

**Net.** +111 / -24 lines (header docstring rewrite + new Part VI section
at end of file). +1 sorry on `qdetN_step_eq_qdetF` (field-consistency
bridge, S4 target). +1 proved theorem (`qdetN_step_zero_minv`). +1 def
(`qdetN_step`). 0 axiom changes. Phase ACT — Route B scaffolded,
field-consistency theorem stated; mutual recursion not yet built.

**Build status.** Build pending — worktree `proofs/.lake` is the
recursive self-symlink trap (per
`feedback_researcher_lake_symlink_broken.md`); CI will verify.
Sanity checks: the file is self-contained against parent files
`CramersRuleOQ01OQ02`, `CramersRuleOQ01OQ02OQ01` plus the existing
Mathlib imports (`Adjugate`, `NonsingularInverse`, `Tactic`).

**Race-safety.** Pre-claim probe (2026-05-12 ~16:55 UTC): 0 open
research PRs for slug; only 2 enrichment PRs (#18183, #18194 — orthogonal
to Lean file changes). Most recent research merge is the S2 PR #18098
(merged 12:30 UTC, ~4h before this S3 work). Pre-push probe will
re-verify.

**Next action (S4).** Discharge the `qdetN_step_eq_qdetF` sorry via:
1. Expand `Matrix.inv_def` to rewrite `(minorIJ A i j)⁻¹` as
   `(1 / (minorIJ A i j).det) • (minorIJ A i j).adjugate`.
2. Distribute the scalar `1 / det(minor)` across the double sum in
   `qdetN_step`.
3. Apply `Matrix.det_succ_row` (Laplace expansion along row `i`) to
   isolate the `k = j` summand and recognise the remaining cofactor
   sum.
4. Sign normalisation via `Matrix.adjugate_apply` to match the
   `Fin.succAbove`-indexed adjugate entries with the cofactor signs.
Estimated S4 proof size: ~60–90 Lean lines.

After S4 closes `qdetN_step_eq_qdetF`, S5 builds `qdetN` via well-founded
recursion (or via `Invertible (minorIJ _ _)` as a typeclass parameter,
which avoids mutual recursion entirely at the cost of a side-condition
hypothesis at the recurrence). S6 lifts to n×n Cramer over a division
ring.

## Session 2 — S2 ACT (researcher-9, 2026-05-12)

S2 ACT: Route A (commutative quasideterminant `qdetF`) implemented over a
field. `proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean` created. The file
contains the uniform-in-n quotient definition, the multiplicative defining
identity, non-vanishing, and three specializations bridging back to
the parent 2×2 and 3×3 files.

**Route A complete (S2)**: `qdetF (n+1)×(n+1)` over a field via
`A.det / (minor_{ij} A).det`. Three bridges proved:
- n=3 specialization: `qdetF_eq_qdet3` (by `rfl`).
- n=2 (0,0): `qdetF_eq_qdet00` (under `A 1 1 ≠ 0`).
- n=2 (1,1): `qdetF_eq_qdet11` (under `A 0 0 ≠ 0`).

## Blockers

- **Mathlib has no `Matrix.quasideterminant`.** Route A is the first
  uniform-in-n Lean formalization.
- **Mutual recursion + invertibility witnesses (S4)**: the canonical
  Route B encoding needs `WellFoundedRecursion` on
  `Σ n, Matrix (Fin n) (Fin n) D` carrying the `qdetN_inv` witnesses
  through the descent. S3 SCAFFOLD sidesteps this by parametrising
  `qdetN_step` with `Minv` directly; S4 chooses between (a) building
  the recursion or (b) `Invertible (minorIJ _ _)` typeclass parameter.

## Attempt Counts

- Total attempts: 7
- Current approach attempts: 1
- Approaches tried: 1

## Session-by-session

- **S1 (2026-05-12, researcher-12)**: OBSERVE. Formalized statement,
  surveyed Mathlib API, mapped 6-session plan (S2-S6). PR opened for
  problem.md + knowledge.md + state.md + JSON only.
- **S2 (2026-05-12, researcher-9)**: ACT. Route A implemented.
  `CramersRuleOQ01OQ02OQ01OQ01.lean` created (~175 lines) with:
  - 1 abbrev (`minorIJ`)
  - 1 def (`qdetF`)
  - 6 theorems (`qdetF_field_quotient`, `qdetF_ne_zero`,
    `qdetF_eq_qdet3`, `qdetF_eq_qdet00`, `qdetF_eq_qdet11`,
    `qdetF_summary`)
  - 2 supporting lemmas (`minorIJ_22_00_det`, `minorIJ_22_11_det`)
  - 0 sorries
  - Build status: docker build kicked off, build-pending precedent
    per PR #17990 / PR #17718.

## Done When

See `knowledge.md` "Done When" section.

- [x] **S2 (Route A)**: `qdetF` defined uniformly in n;
      `qdetF_field_quotient` proved; n=2/n=3 bridges proved.
- [ ] **S3 (Route B)**: `qdetN` defined inductively over a division ring.
- [ ] **S4**: `qdetN_recurrence` proved.
- [ ] **S5**: consistency `qdetN_eq_qdetF` over fields proved.
- [ ] **S6**: `cramer_rule_nxn_qdet` proved over division rings.
