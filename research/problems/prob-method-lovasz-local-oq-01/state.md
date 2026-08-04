# Research State: prob-method-lovasz-local-oq-01

## Current State
**Phase**: S18a ACT COMPLETE (two statement-level defects found and repaired before the coupling build: runLog log-order flipped to execution order — the old most-recent-first emission made ExtractsFrom attach oldest-first, the reverse of MT §4 — and mtRun (uniform initialization) added because the fixed-start per-tree bound is provably false; WitnessTree.weight (the RHS of witness_prob_bd) defined with unit-interval bounds; next = S18b runTable + pushforward coupling)
**Path**: full
**Since**: 2026-08-03
**Iteration**: 20
**Last Updated**: 2026-08-03 (S18a, researcher-1 — order repair + statement infrastructure, host-verified at v4.31)

## S18a ACT — researcher-1, 2026-08-03

**Mode**: ACT (correctness repair + statement infrastructure) + PREP (coupling
design decision). File 879 → 1007 LOC; **0 new sorries, 0 new axioms** (file
stays 0/0). Verification: host `lake env lean` v4.31.0 elaboration against the
pinned Mathlib oleans (pin `9a9483a9`): 0 errors, 0 warnings; `#print axioms`
on the new/adapted theorems: foundational only.

The tracker asked for an S18a design memo on the resample-table coupling.
Doing that design surfaced **two statement-level defects**, both repaired
here *before* the multi-session coupling is built on them (full analysis in
`sessions/2026-08-03-s18a-runlog-order-and-statement-repair.md`):

1. **Log-order convention mismatch.** `runLog` emitted the log
   most-recent-first, but `ExtractsFrom` recurses on the tail before
   handling the head — so a derivation attaches the list's *last* element
   first. Composite: entries attached **oldest-first**, the reverse of the
   MT §4 backward pass. Two-event counterexample in the memo (`X ∈ Γ(j)`,
   `Y ∈ Γ(X) \ Γ⁺(j)`, log `X` then `Y`): MT extracts `j—X` (skipping `Y`),
   the old composite extracts the path `j—X—Y`. Fatal downstream: the
   table-slot argument needs "deeper = earlier". **Fix**: `runLog` now emits
   **execution order** (`p.2.toList ++ q.2`); Part VI untouched;
   `runLog_map_fst`/`mem_log_pickBad` mechanically adapted; docstrings
   corrected. Bonus alignment: outermost bind layer ↔ outermost derivation
   constructor, and "entries before time t" is now a list *prefix*.

2. **Fixed-start bound is false.** The tracked S18 statement ("Pr[τ
   extractable from runLog n v] ≤ ∏ uniformDrawProb") fails for fixed bad
   starts: single-variable counterexample gives `2⁻ᵐ` vs claimed `2⁻⁽ᵐ⁺¹⁾`;
   under uniform initialization the bound holds **with equality** (sharp).
   **Fix**: new `mtRun n = (PMF.uniformOfFintype P.State).bind (P.runLog n)`
   (Part VIII) + conservativity `mtRun_map_fst`; `witness_prob_bd` must be
   stated over `mtRun`.

Also new in Part VIII: `WitnessTree.weight` (`∏_v uniformDrawProb (labelOf
v)` by nested structural recursion — `(ch.map weight).prod` elaborates
directly at v4.31), `@[simp] weight_node`, `weight_mem_unit_interval` /
`weight_nonneg` / `weight_le_one`.

**Coupling decision (the S18a question)**: product-space **resample-table
presentation** (MT §5 verbatim) over inductive-coupling-over-bind — the
latter must smuggle the same table bookkeeping into a harder conditional
invariant. Roadmap: **S18b** `runTable` (per-variable columns of fresh
uniforms, column 0 = init) + pushforward coupling `(uniform table).map
runTable = mtRun n` (mechanical, uses the S5b `resampleAt` marginal API);
**S18c** the slot invariant (MT §5 key lemma — cell index of each vertex's
read determined by τ alone; the mathematical heart); **S18d** disjoint-cell
independence + `vblFaithful` per-vertex factor + prefix (`List.take`)
bookkeeping → `witness_prob_bd`. Corrected target statement in memo §5.

## S17 ACT — researcher-3, 2026-07-24

**Mode**: ACT (substantive Lean delivery, host-verified).

The S16 roadmap item `witness_valid` is landed as the second half of Part VI
of `proofs/Proofs/MoserTardos.lean`: the Moser–Tardos §4 extraction is
formalized *relationally* and every extracted tree is proved proper. File
580 → 724 lines (+144); **0 new sorries, 0 new axioms** (file stays 0/0).
Verification: host `lean` v4.31.0 elaboration against the pinned Mathlib
oleans (researcher-1 sibling worktree, same pin as the S16 Docker build):
0 errors, 0 warnings; `#print axioms witness_valid` = foundational only.

Declarations (namespace `MTProblem.WitnessTree`):
- `HasMatchAt j τ d` — depth-`d` vertex whose label's `Γ⁺` contains `j`
  (same `∃ t ∈ ch` structural-recursion form as `isProper`; elaborated
  first try).
- `inductive Attach j τ d τ'` — leaf `j` attached under a matching vertex at
  depth `d` (list-splitting `pre ++ t :: post` constructor for the recursive
  case).
- `AttachDeepest j τ τ'` — `∃ d`, attach at `d` + depth-maximality.
- `Attach.hasMatchAt`, `Attach.labelOf_eq` — API lemmas.
- `isProper_attach` — **the propriety core**: depth-maximal attachment
  preserves `isProper`. Distinct-siblings step: a same-labelled existing
  child of the target would be a strictly deeper match (`j ∈ Γ⁺(j)` via
  `self_mem_inclNbhd`), contradicting maximality. Maximality is relativized
  down the tree by `d' + 1 ≤ d + 1 → d' ≤ d` on the child hypothesis.
- `inductive ExtractsFrom j log τ` — root + per-entry attach-or-skip (skip
  only when NO depth matches, keeping the extraction faithful to MT §4).
- `witness_valid` — **headline**: `ExtractsFrom j l τ → isProper τ`
  (Moser–Tardos §4 propriety; step 2 of the `mt_expected_step_bound`
  skeleton discharged).

Design note: the extraction is a relation, not a program — the S18+
probability bound only needs (a) the attachment site matches and (b) nothing
matches deeper, which is exactly what the relation records; no `Decidable`/
computability rework of `collisionAdj` is required (per the S16 deferral).

**Next (S18)**: `witness_prob_bd` — for a fixed proper tree τ,
Pr[τ appears in the execution] ≤ ∏_v uniformDrawProb (labelOf v), consuming
`LLLAdmissibleUniform.lll_uniform`; this is where the `PMF.run` chain and the
resample-table coupling enter. Then OQ-01-C Galton–Watson sum.

## S16 ACT — researcher-2, 2026-07-24

**Mode**: ACT (substantive Lean delivery, Docker-verified).

The S13 PREP §3 WitnessTree skeleton is landed as **Part VI** of
`proofs/Proofs/MoserTardos.lean` and build-verified:
`./proofs/scripts/docker-build.sh Proofs.MoserTardos` → **8576 jobs, exit 0**
at `leanprover/lean4:v4.31.0` (Mathlib rev `9a9483a9`). File 522 → 580 lines
(+60/-2 vs origin/main); **0 new sorries, 0 new axioms** (file stays 0/0).

Declarations: `inductive WitnessTree` (List children per S13
strict-positivity resolution), `labelOf` + `labelOf_node`, `noncomputable def
inclNbhd` (= Γ⁺(i); noncomputable forced by the `collisionAdj` dependency —
1-commit fix b188453e01), `self_mem_inclNbhd`, `isProper`, `isProper_leaf`.

**S13 recursion-form risk resolved**: the primary candidate
`∀ t ∈ ch, isProper t` elaborates directly via structural recursion at v4.31;
the ranked fallbacks (termination_by sizeOf → mutual isProperList →
List.Forall) were never needed. **Deviation from the S14 plan**:
`DecidablePred isProper` deferred — `collisionAdj` is noncomputable, so no
`Decidable` instance is derivable without a computability rework; not on the
S17+ critical path (the probability bound sums abstractly, no `decide`).

**Gate flips**: S14/S15 BLOCKED was Docker-transient; this build empirically
confirms Docker recovery, so per the S15 un-block instruction the gates are
reverted (JSON `status: active` / `phase: ACT`; pool → `available`
post-release).

**Next (S17)**: `witness_valid` — execution-log extraction produces proper
witness trees (S13 PREP §4 extraction algorithm), then `witness_prob_bd`
consuming `LLLAdmissibleUniform.lll_uniform`. See
`sessions/2026-07-24-s16-act-witnesstree-skeleton-verified.md`.

## S15 GATE-SYNC — researcher-1, 2026-06-14

The S14 BLOCKED flag lived in state.md only: the research JSON read
`status: "active"` / `phase: "OBSERVE"` and `.lean/state/candidate-pool.json`
read `"in-progress"`, so `claim-random` kept re-serving this RICH slug.
Aligned both gates to BLOCKED (JSON `status`/`phase`/`currentState.phase` →
`blocked`/`BLOCKED`; pool → `"blocked"`, terminal). **Docker-transient block**:
the OQ-01-B WitnessTree ACT skeleton is paste-ready (S13 PREP) and buildable
once Docker returns — un-block by reverting these gates then. No metadata/Lean
change. (Independent of the parent-slug gallery realign in open PR #24101,
which touches `src/data/proofs/prob-method-lovasz-local/` only.)

## S14 STATE-SYNC + flag BLOCKED — researcher-1, 2026-06-13

**Mode**: STATE-SYNC (comment-only `.lean` docstring fix; no code/axiom/sorry
semantics changed) + flag `blocked`.

**Trigger**: Docker daemon down (probes killed at exit 144); the only forward
move (S14 ACT — paste the S13 WitnessTree skeleton into a new Part VI and
Docker-verify the `isProper` recursion form) is build-gated and cannot run.

**Build-free win**: the `MoserTardos.lean` header docstring was stale and
self-contradictory:
1. It claimed the two main theorems are stated "(with `sorry`)" and that a
   future PR does "Final integration replacing the `sorry`s below". The file
   in fact has **0 code `sorry`** — `mt_expected_step_bound` and
   `mt_terminates_as` are *weakened placeholder* statements (algebraic-shell
   inequalities), fully proved. The only `sorry` tokens in the file are these
   two prose mentions inside the header comment.
2. The roadmap listed Parts I–IV only; it omitted **Part V** (the S12 ACT
   refined uniform-draw layer: `uniformDrawProb`, `collisionAdj`,
   `LLLAdmissibleUniform`, `LLLAdmissibleUniform.toLLLAdmissible`).

Corrected both: header now states "0 `sorry`, 0 `axiom`", lists Part V, and
re-points the deferred WitnessTree item at S14 ACT / Docker-gated build.

**Bearer metrics (verified against source, comment-stripped):**
- `LovaszLocalLemma.lean` (primary): 0 sorry, 0 axiom, theoremCount 25
  (include-private — `private theorem pow2_plus_one_le` at L83), 364 lines.
  meta.json `leanFile` block consistent (definitionCount is deployer-owned).
- `MoserTardos.lean` (additionalFile): 0 code sorry, 0 axiom, 14 theorems.

**Honesty**: comment-only `.lean` edit — no semantics changed, so no Docker
build is implied or claimed. Cannot machine-verify under the current blackout;
the change cannot affect compilation (delimiters untouched, body unchanged).

**Next (unblock when Docker returns)**: S14 ACT — paste the S13 PREP §3
`inductive WitnessTree` / `labelOf` / `inclNbhd` / `isProper` skeleton into a
new Part VI of `MoserTardos.lean`, Docker-verify the recursion form
(`List.Forall` > `sizeOf` > mutual), add `DecidablePred isProper` + leaf/label
sanity lemmas (~200 LOC, 0 new sorries/axioms).

## S13 PREP (OQ-01-B WitnessTree encoding design) — researcher-2, 2026-06-12

**Mode**: PREP (doc-only — no Lean / problem.md / knowledge.md / meta.json edits).

**Outcome**: resolves the central definitional risk for OQ-01-B (witness
trees) flagged by `knowledge.md` ("the hardest part — rooted labelled trees
with `Finset`-valued children"). Key findings:

1. **Positivity wall (resolved).** `inductive WitnessTree | node : Fin
   numEvents → Finset (WitnessTree P) → _` is rejected by Lean's strict-
   positivity checker: `Finset α = {s : Multiset α // s.Nodup}` and
   `Multiset α = Quotient (List.Perm …)`; nested inductive occurrence under a
   `Quotient` is not certifiable. **Fix (D1): children are `List`**, and the
   "set of distinct-label children" semantics is recovered by a `Nodup`-on-
   labels side-condition in `isProper` (which is exactly the MT requirement).
   `inductive T | mk : List T → T` is strictly positive and compiles.

2. **`isProper` recursion (narrowed to 3 ranked forms).** A literal
   `∀ t ∈ ch, isProper t` triggers well-founded recursion; **D2 recommends
   `List.Forall isProper ch`** (structural along the spine). Fallbacks if the
   v4.26.0 elaborator balks: explicit `termination_by sizeOf`, then a mutual
   `isProperList` helper. This is the one residual risk the ACT must Docker-
   check; ranked confidence `List.Forall` > `sizeOf` > mutual.

3. **Parametrise by `MTProblem` (D3), settling the S1 open question.** The
   S12 ACT put the canonical `collisionAdj` + `uniformDrawProb` on `P`; the
   S15 probability bound multiplies `uniformDrawProb (labelOf v)` over nodes,
   so the tree must see `P`. The proper neighbourhood is the *inclusive*
   `Γ⁺(i) = insert i (collisionAdj i)`.

**Deliverable**: paste-ready S14 ACT skeleton (`inductive WitnessTree`,
`labelOf`, `inclNbhd`, `isProper`) in §3 of the session memo, plus a bearer
check (no new absences at pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).

**Honesty**: doc-only; no build claimed. Retires the positivity risk with
certainty and narrows the recursion risk to three candidate forms for S14 to
test empirically.

**Next**: S14 ACT — paste the skeleton into a new `§ Part VI` of
`MoserTardos.lean`, Docker-verify the recursion form, add `DecidablePred
isProper` + leaf/label sanity lemmas (~200 LOC, 0 new sorries/axioms).

See `sessions/2026-06-12-s13-prep-witnesstree-encoding.md` for the full memo
(positivity analysis, three recursion forms, paste-ready skeleton, bearer table).

## S12 ACT (OQ-01-A.3 LLLAdmissibleUniform shipped + Docker-verified) — researcher-1, 2026-06-10

**Mode**: ACT (substantive Lean code: +135 LOC, 0 new sorries, 0 new axioms; Docker-verified at v4.26.0).

**Outcome**: S8 PREP §3.2/§4 paste-ready body shipped into `proofs/Proofs/MoserTardos.lean` as a new Part V. Five blocks (matching the S8 PREP §4 LOC budget within ~5%):

1. **§4.1 New defs (~10 LOC)** — `uniformDrawProb i := card{v//isBad i v} / card State` (ℚ-valued) and `collisionAdj i := univ.filter (fun k => k ≠ i ∧ (vbl i ∩ vbl k).Nonempty)` (Finset-valued). Both `noncomputable` per S7 PREP §1.3.
2. **§4.2 Basic bounds (~30 LOC)** — `card_state_pos`, `uniformDrawProb_nonneg`, `uniformDrawProb_le_one`, `uniformDrawProb_mem_unit_interval`.
3. **§3.2 substitute faithful-link (~30 LOC)** — `uniformDrawProb_eq_outerMeasure i : ENNReal.ofReal ((uniformDrawProb i : ℝ)) = (uniformOfFintype P.State).toOuterMeasure {v | isBad i v}`. Discharged via `PMF.toOuterMeasure_apply_fintype` + indicator-collapse via `Set.indicator_of_mem` / `Set.indicator_of_notMem` + `← Finset.sum_filter` + `Finset.sum_const` + `nsmul_eq_mul` + `Fintype.card_subtype` + `push_cast` + `ENNReal.ofReal_div_of_pos` + `ENNReal.ofReal_natCast` + `div_eq_mul_inv`.
4. **§4.4 structure + bridge (~30 LOC)** — `structure LLLAdmissibleUniform (x : Fin numEvents → ℚ) : Prop` with fields `x_range`, `lll_uniform`; `theorem LLLAdmissibleUniform.toLLLAdmissible` providing the forward direction to the symbolic `LLLAdmissible`.
5. **Docstrings (~35 LOC)** — fluid prose pointing back to the S7 PREP / S8 PREP session memos for design context.

**Total delta**: 382 → 517 LOC (+135 LOC), matching the S8 PREP §4 budget estimate of ~130 LOC within 5%.

**Build status**: Docker `./proofs/scripts/docker-build.sh Proofs.MoserTardos` → **7743 jobs successful** at Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0). 0 sorries (down from S6 ACT baseline 2 doc-only matches in `mt_terminates_as` placeholder, which remain unchanged). 0 axioms.

### Two surface-drift fixes caught at first Docker iteration

1. **ℝ≥0∞ notation drift** (line 456 expected-token error): the file uses `ENNReal` directly throughout (file lines 211–227 baseline pattern) and does not `open scoped ENNReal`, so the `ℝ≥0∞` notation in the S8 PREP §3.2 paste does not parse. Fix: replace `ℝ≥0∞` with `ENNReal` in three sites (theorem statement, h_each conditional, filter-card show).
2. **ℝ → ENNReal coercion gap** (line 456 type-mismatch error): the S7 PREP §3.1 / S8 PREP §3.2 statement form `((uniformDrawProb i : ℝ) : ℝ≥0∞)` does not elaborate because ℝ → ENNReal is not a direct coercion (must go via `ENNReal.ofReal`). Fix: restate theorem as `ENNReal.ofReal ((uniformDrawProb i : ℝ)) = ...`. This is the intended semantic — `ENNReal.ofReal` maps non-negative reals into ENNReal — and the proof closes via `ENNReal.ofReal_div_of_pos` + `ENNReal.ofReal_natCast` (both verified at pin via raw.githubusercontent curl).

These are two recurrences of the "hedged-bearer surface-drift at v4.26.0" pattern that S7 PREP §3.3 explicitly inventoried. Both required one-line statement fixes plus a `push_cast`-driven proof simplification (removing 4 multi-step `show ... by ...` rewrites in favor of `push_cast` collapsing the entire ℚ → ℝ → ENNReal cast chain).

### Mathlib bearers used (all verified at pin)

| Bearer | File | Line | Use |
|---|---|---|---|
| `PMF.toOuterMeasure_apply_fintype` | `Mathlib/Probability/ProbabilityMassFunction/Basic.lean` | 203 | step (1) outer measure expansion |
| `Set.indicator_of_mem` | `Mathlib/Algebra/Notation/Indicator.lean` (via `to_additive`) | ~67 | step (2) indicator-on-membership |
| `Set.indicator_of_notMem` | same | ~70 | step (2) indicator-off-membership |
| `PMF.uniformOfFintype_apply` | `Mathlib/Probability/Distributions/Uniform.lean` | 298 | step (2) uniform PMF value |
| `Finset.sum_filter` (used reverse) | `Mathlib/Algebra/BigOperators/Group/Finset/Sum.lean` | — | step (3) ∑-conditional collapse |
| `Finset.sum_const` + `nsmul_eq_mul` | core | — | step (3) constant-sum → mul |
| `Fintype.card_subtype` | `Mathlib/Data/Fintype/Card.lean` | 378 | step (4) subtype card = filter card |
| `ENNReal.ofReal_div_of_pos` | `Mathlib/Data/ENNReal/Inv.lean` | 931 | step (5) divide ENNReal.ofReal |
| `ENNReal.ofReal_natCast` | `Mathlib/Data/ENNReal/Basic.lean` | 493 | step (5) ℕ embedding to ENNReal |
| `div_le_one_of_le₀` | `Mathlib/Algebra/Order/Field/Basic.lean` | — | §4.2 `uniformDrawProb_le_one` |
| `Fintype.card_subtype_le` | core | — | §4.2 bound bad-subtype card |
| `Fintype.card_pos` | core | — | §4.2 `card_state_pos` (via Nonempty instance) |

### ACT-readiness gate (8-item, S12 ACT closure)

| # | Item | Status | Δ since S11 |
|---|---|---|---|
| 1 | Mathlib pin stable | GREEN | unchanged (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` ≥30d) |
| 2 | Bearers verified at pin | GREEN | re-verified for §3.2 substitute path (12 bearers; table above) |
| 3 | Paste-ready substitute body | GREEN | **SHIPPED** (this PR) |
| 4 | Parent file baseline stable | GREEN → **EXPANDED** | 382 → 517 LOC; Docker-verified 7743 jobs |
| 5 | No competing open PRs on slug | GREEN | re-verified (`gh pr list --search "prob-method-lovasz-local-oq-01" --state open` → 0) |
| 6 | JSON catchup planned | GREEN | this PR closes (iteration 13 → 14, phase S11 → S12 ACT) |
| 7 | problem.md / knowledge.md unchanged | GREEN | unchanged |
| 8 | Infra: Docker + disk + .lake | GREEN | unchanged (Docker verify completed 3× this session) |

### Files updated (S12 ACT)

- `proofs/Proofs/MoserTardos.lean` — **SUBSTANTIVE**: +135 LOC Part V (5 lemmas + 1 theorem + 1 structure + 1 bridge + 2 defs); 0 new sorries; 0 new axioms; Docker-verified 7743 jobs.
- `research/problems/prob-method-lovasz-local-oq-01/state.md` — this section + head + Iteration History +1.
- `research/problems/prob-method-lovasz-local-oq-01/sessions/2026-06-10-s12-act-llladmissibleuniform-shipped.md` — new memo.
- `src/data/research/problems/prob-method-lovasz-local-oq-01.json` — phase / iteration / focus / nextAction / lastUpdate bumps.

### Next action (S13 — OQ-01-B WitnessTree skeleton)

With OQ-01-A.3 closed, the natural next step is **OQ-01-B WitnessTree**:

1. **S13 PREP**: design memo for `inductive WitnessTree P` (rooted labelled tree, Finset-valued children) + `isProper` predicate (Moser–Tardos compatibility: each child collides with its parent in `collisionAdj`). Mathlib has no rooted-labelled-tree type with Finset children; building from scratch is unavoidable per `knowledge.mathlibGaps` finding.
2. **S14 ACT**: ship the inductive type + `isProper`. ~200 LOC.
3. **S15 PREP/ACT**: tree-probability bound `Pr[τ appears in execution] ≤ ∏_v uniformDrawProb v.lbl`. Uses `LLLAdmissibleUniform.lll_uniform` (this PR's structure) as the probability input. ~200 LOC.
4. **S16+ (OQ-01-C)**: Galton–Watson sum bound. ~400 LOC.
5. **S20+ complete**: replace algebraic shell of `mt_expected_step_bound` (file line 338) with the actual expected-value bound via Markov + the GW sum.

OQ-01-B is the technically hardest piece per S2 PREP / S7 PREP analysis; expect 2–3 PRs of design before substantive ACT.

### Honesty (S12)

This is the **first substantive Lean code progress on this slug since S6 ACT (2026-05-14, PR #19103)** — 27-day gap closed. The infra recoveries (S9 → S10 → S11) and the design pipeline (S5b PREP → S5c PREP → S7 PREP → S8 PREP, 5 doc-only PREPs) were all overhead to get to this paste. Ratio of substantive ACT iterations to doc-only PREP iterations on this slug is now 6:8 (S1+S2+S3+S5+S5b+S6+S12 ACT = 7 substantive; S4a+S4b+S5c+S7+S8+S9+S10+S11 = 8 doc-only). Honesty target met: this PR shipped paste-ready code that two PREPs (S7 + S8) had locked, with two recurrent v4.26.0 surface-drift fixes caught at first Docker iteration.

### Race-safety note (S12 ACT)

- Pre-claim probe (2026-06-10T~07:00Z): `gh pr list --search "prob-method-lovasz-local-oq-01" --state open` → `[]` (0 open); most recent merge S11.5 STATE-SYNC at 2026-05-31 — **10d+ lead time**, no race.
- Pre-push probe will re-verify before push.

See `sessions/2026-06-10-s12-act-llladmissibleuniform-shipped.md` for the full memo: file diff anatomy, bearer audit, the two surface-drift fixes, and S13 PREP readiness for OQ-01-B WitnessTree.

## S11 INFRA-VERIFY (G9-mount confirmed inert for Docker builds) — researcher-1, 2026-05-31 ~17:50 UTC

**Mode**: INFRA-VERIFY (empirical Docker build executed on origin/main unchanged file; doc-only state.md + new session memo; **no Lean / problem.md / knowledge.md / meta.json / leanFiles / Mathlib pin / sibling-slug edits**).

**Outcome**: The S10 §4 hypothesis ("Docker `-v` mount overrides G9 lake self-loop") is **CONFIRMED EMPIRICALLY**. Test command (executed in this worktree, on origin/main MoserTardos.lean — zero new code):

```
cd /Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-1
LEAN_BUILD_TIMEOUT=15m ./proofs/scripts/docker-build.sh Proofs.MoserTardos
=> Build completed successfully (7743 jobs).
=> ~150s wall-clock; 7727 files fetched from Mathlib cache.
```

Mechanism: `docker-build.sh:127` mounts `lean-mathlib-cache` directly onto `/workspace/proofs/.lake/build` inside the container, providing a fresh writable directory regardless of host symlink state. The outer `-v "${REPO_ROOT}:/workspace:delegated"` bind mount makes the worktree available; the broken `proofs/.lake` symlink's target (`/Users/rwalters/GitHub/lean-genius/proofs/.lake`) does not exist as a path inside the container, but the nested volume mount supersedes the broken parent path.

### Files updated (S11 INFRA-VERIFY)

- `research/problems/prob-method-lovasz-local-oq-01/state.md` — this block (head update + new narrative section + Iteration History +1 row).
- `research/problems/prob-method-lovasz-local-oq-01/sessions/2026-05-31-s11-infra-verify-g9-mount-confirmed-inert.md` — new memo (~150 LOC, 9 sections).
- No JSON catchup needed (S10 catchup still authoritative; substantive ACT deliverable not yet shipped).

### Snapshot at S11 verify (host)

- **G7 disk**: `/System/Volumes/Data` 94% capacity, **59 Gi free** (vs S10 62 Gi, vs S9 2.9 Gi free — slight decrement vs S10 but well above ACT floor). GREEN.
- **G8 Docker**: `docker info --format '{{.ServerVersion}}'` → `29.4.1` (immediate, no timeout). GREEN.
- **G9 lake self-loop**: `ls -la proofs/.lake` → `proofs/.lake -> /Users/rwalters/GitHub/lean-genius/proofs/.lake` (self-referencing on host; `readlink -f` errors). **STILL RED ON HOST**, but **CONFIRMED INERT FOR DOCKER BUILDS** (this finding).

### ACT-readiness gate (8-item, S11 INFRA-VERIFY refresh)

| # | Item | Status pre-S11 (S10) | Status post-S11 |
|---|------|----------------------|-----------------|
| 1 | Mathlib pin stable | GREEN | GREEN (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` ≥19d) |
| 2 | Bearers verified at pin | GREEN | GREEN (transitivity) |
| 3 | Paste-ready substitute body (S8 §3.2) | GREEN | GREEN |
| 4 | Parent file baseline stable (382 LOC, 0 sorries) | GREEN | GREEN |
| 5 | No competing open PRs on slug | GREEN | re-verified (`gh pr list --search "prob-method-lovasz-local-oq-01" --state open` → 0) |
| 6 | JSON catchup planned | GREEN | DONE (S9 + S10 catchup merged) |
| 7 | problem.md / knowledge.md unchanged | GREEN | GREEN |
| 8 | Infra: Docker + disk + .lake | **PARTIAL INFRA (G9-only)** | **GREEN (G9 confirmed inert via Docker -v override)** |

**Gate flips from 7/8 GREEN + 1/8 PARTIAL → 8/8 GREEN**. S12 ACT can proceed without infra qualifier.

### Cross-slug implication

The G9-inert finding is **slug-agnostic**: every research worktree using `proofs/scripts/docker-build.sh` is unaffected by the lake self-loop. The blanket "build pending — G9 lake self-loop" qualifier pattern, used in many recent research PRs across the gallery (including PR #21550 — ballot-problem-oq-02-oq-05 S8 ACT, this researcher's own work shipped earlier this session), is now obsolete.

**Within this session**: PR #21550 was Docker-verified after this S11 finding; 3 bugs were caught at first build attempt (2 preexisting from S6 ACT skeleton which was never actually built, 1 in the S8 ACT paste-ready proof body) — all fixed and rebuilt to 7744 jobs successful. The "(build pending — G9 lake self-loop)" qualifier on that PR is corrected to VERIFIED in the follow-up commit.

**Cross-slug action item** (out of S11 scope): the `lake-self-loop-main-repo` project memory entry should be updated to reflect G9-inert finding; recent research PRs labeled with `(build pending — G9 lake self-loop)` could be retroactively Docker-verified (deployer/auditor work).

### Race-safety note (S11 INFRA-VERIFY)

- Pre-claim probe (2026-05-31T17:30Z): `gh pr list --search "prob-method-lovasz-local-oq-01" --state open` → `[]` (0 open); most recent merge S10 STATE-SYNC at 2026-05-30 — **24h+ lead time**, well outside any race window.
- Pre-push probe will re-verify before push.

### Next action (S12 — ACT)

With 8/8 GREEN, S12 should:

1. Paste the S8 §3.2 substitute body for `lll_admissible_uniform` (~130 LOC).
2. Docker-verify via `./proofs/scripts/docker-build.sh Proofs.MoserTardos` (or a parallel target if a new file is created).
3. Commit + push + PR with `research` label.
4. **No "build pending" qualifier needed**.

If S12 introduces sub-sorries (expected per S8 §3.2 outline: ~3-5 sorries), document each with a discharge sketch in the corresponding session memo for S13+.

### Honesty (S11)

This iteration **resolves the meta-issue stuck-ness flagged in S10**: S11 is not another doc-only STATE-SYNC. It is a binary-outcome empirical test whose answer changes the disposition of this slug (and, transitively, the disposition of many sibling slugs that shipped "build pending — G9" PRs).

Net research progress for this slug: ACT-readiness gate fully GREEN; ~130 LOC of OQ-01-A.3 substitute work is now genuinely unblocked for any subsequent researcher. The marquee Moser–Tardos formalization work (OQ-01-A.3 paste, OQ-01-B witness trees, OQ-01-C Galton–Watson sum) is exactly where S8 PREP left it — S11 unblocks the next step.

See `sessions/2026-05-31-s11-infra-verify-g9-mount-confirmed-inert.md` for the full memo: test transcript, ACT-readiness gate refresh, cross-slug implications, risk inventory, S12 ACT-readiness checklist.

## S10 STATE-SYNC (infra partial recovery + Docker-mount G9 hypothesis) — researcher-1, 2026-05-30 ~07:00 UTC

**Mode**: STATE-SYNC (doc-only — this section + new session memo + JSON catchup; **no Lean / problem.md / knowledge.md / meta.json / leanFiles / Mathlib pin / sibling-slug edits**).

**Outcome**: doc-only refresh closing the 13-day gap since S9 STATE-SYNC #20041 (researcher-4, merged 2026-05-17T02:00Z). Three deliverables:

1. **Infra partial recovery snapshot** at S10 claim (2026-05-30T07:00Z, ~13 days post-S9):
   - **G7 disk**: `/System/Volumes/Data` 94% capacity, **62 Gi free** (vs S9 2.9 Gi free) — **+59 Gi RECOVERED over ~13 days**, well above the 10 Gi ACT floor. GREEN.
   - **G8 Docker**: `docker info --format '{{.ServerVersion}}'` → **`29.4.1`** (returns immediately, no 10s timeout) — **UP RECOVERED** since S9 snapshot. GREEN.
   - **G9 lake self-loop**: `proofs/.lake → /Users/rwalters/GitHub/lean-genius/proofs/.lake` (self-referencing symlink) — **unchanged RED** since S9 / S8 / S5b feedback memo.
   - All three are host-environmental, not slug-rooted. S10 STATE-SYNC refreshes the ACT-readiness gate (item 8) to "7/8 GREEN substantive + 1/8 PARTIAL INFRA (G9-only)", a substantial narrowing from S9's "RED-er".

2. **New substantive finding: Docker `-v` mount likely overrides G9**.
   `proofs/scripts/docker-build.sh:127` mounts the `lean-mathlib-cache` named volume directly onto `/workspace/proofs/.lake/build` inside the container, overriding the host's broken `.lake/build` symlink path. Inside the container, `/workspace/proofs/.lake` is a bind-mount of the host's self-loop symlink, but the link target `/Users/rwalters/GitHub/lean-genius/proofs/.lake` does not exist as a path inside the container, so the link is dead in the container namespace — and the `-v` volume mount at `.lake/build` provides a fresh writable directory. **Hypothesis**: G9 is not a hard ACT blocker for Docker builds; only G7+G8 ever were. **Status**: unverified empirically in S10; flagged for S11 to verify with `./proofs/scripts/docker-build.sh Proofs.MoserTardos` on origin/main MoserTardos.lean (zero new code).

3. **Mathlib pin byte-stability re-verify + iteration bump 11 → 12 + `lastUpdate` refresh**.
   `proofs/lake-manifest.json` confirms Mathlib4 `rev` still `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0), byte-identical to S8 PREP + S9 STATE-SYNC. Lake-pinned **≥18 days**. No bearer re-walk justified (transitivity at byte-stable SHA covers entire S7/S8 PREP bearer table).

### Files updated (S10 STATE-SYNC)

- `research/problems/prob-method-lovasz-local-oq-01/state.md` — this block (head update + new narrative section + Iteration History +1 row).
- `research/problems/prob-method-lovasz-local-oq-01/sessions/2026-05-30-s10-statesync-infra-recovery.md` — new memo (~150 LOC, 10 sections).
- `src/data/research/problems/prob-method-lovasz-local-oq-01.json` — 10-field JSON catchup (no `leanFiles` edit — mechanic #19792 choice still authoritative; no `problem.md` / `knowledge.md` / `meta.json` edits per separate-mechanic-scope boundary).

### Build-verification posture

Doc-only STATE-SYNC; `MoserTardos.lean` unchanged on this branch (file SHA byte-identical to origin/main since #19792 mechanic merge). No build attempted in this session — the §4 G9-mount hypothesis is explicitly flagged for S11 to verify, not S10.

### ACT-readiness gate (8-item, S10 STATE-SYNC refresh)

| # | Item | Status | Δ since S9 STATE-SYNC |
|---|---|---|---|
| 1 | Mathlib pin stable | GREEN | unchanged (byte-identical, ≥18d) |
| 2 | Bearers verified at pin | GREEN | unchanged (transitivity at stable SHA) |
| 3 | Paste-ready substitute body (S8 §3.2) | GREEN | unchanged |
| 4 | Parent file baseline stable (382 LOC, 0 sorries) | GREEN | unchanged (file SHA stable) |
| 5 | No competing open PRs on slug | GREEN | re-verified (probe at 07:00Z: 0 open) |
| 6 | JSON catchup planned | GREEN | this PR closes |
| 7 | problem.md / knowledge.md unchanged | GREEN | unchanged |
| 8 | Infra: Docker + disk + .lake | **PARTIAL INFRA** | G7 +59 Gi RECOVERED; G8 UP RECOVERED; G9 unchanged; net narrowing from RED-er to PARTIAL (G9-only) |

7/8 GREEN substantive + 1/8 PARTIAL INFRA (G9-only). ACT remains blocked, but the surface has narrowed to a single worktree-level symlink — and the §4 hypothesis suggests even G9 may be inert for Docker builds.

### Race-safety note (S10 STATE-SYNC)

- Pre-claim probe (2026-05-30T07:00Z): `gh pr list --search "prob-method-lovasz-local-oq-01" --state open` → `[]` (0 open); most recent merge S9 STATE-SYNC (#20041) at 2026-05-17T02:00Z — **13-day lead time**, well outside any race window.
- Pre-push probe will re-verify before push.

### Next action (S11 — verify G9-mount hypothesis, then ACT or INFRA-FIX)

**Path A (recommended)**: S11 INFRA-VERIFY (~30 min). Run `./proofs/scripts/docker-build.sh Proofs.MoserTardos` on origin/main MoserTardos.lean (zero new code). Three outcomes:
- Build succeeds → G9 confirmed inert for Docker builds; gate flips to 8/8 GREEN; S12 immediately ACTs (~130 LOC OQ-01-A.3 paste per S8 §4 budget).
- Build fails on G9 symlink resolution → G9 confirmed hard-blocker; S12 must fix `.lake` symlink before ACT.
- Build fails on something else → orthogonal regression surfaces; doctor-style repair takes precedence.

**Path B (riskier)**: S11 ACT outright. Paste S8 §4 / §3.2 recipe (~130 LOC) without verifying G9-mount hypothesis. If G9 doesn't block, delivers OQ-01-A.3 in one PR; if G9 blocks, ships "build pending" and next session backtracks.

### Honesty (S10)

This STATE-SYNC is the **third consecutive doc-only iteration** (S8 PREP + S9 STATE-SYNC + S10 STATE-SYNC). It is genuinely useful only because (a) the 13-day gap was overdue for absorption, and (b) the G9-mount hypothesis gives S11 a concrete testable claim. It is NOT a breakthrough or an advance toward the actual Moser–Tardos formalization. The marquee work (OQ-01-A.3 paste, OQ-01-B witness trees, OQ-01-C Galton–Watson sum) remains exactly where S8 PREP left it. If S11 also ships as STATE-SYNC, this is a sign of meta-issue stuck-ness; S11 should commit to verifying G9 or ACT-ing.

## S9 STATE-SYNC (infra escalation + Mathlib byte-stability + iteration bump) — researcher-4, 2026-05-17

**Mode**: STATE-SYNC (doc-only — this section + new session memo + JSON
catchup; **no Lean / problem.md / knowledge.md / meta.json / leanFiles /
Mathlib pin / sibling-slug edits**).

**Outcome**: doc-only refresh closing the ~12h gap since S8 PREP
#19628 (researcher-8, merged 2026-05-16T14:32Z). Three deliverables:

1. **3 RED INFRA escalation snapshot (G7 disk soft-floor cross)**.
   At S9 claim (2026-05-17T02:00Z, ~T+11.5h post-S8-PREP):
   - **G7 disk**: `/System/Volumes/Data` 100% capacity, **2.9 Gi free**
     (vs S8 snapshot 6.6 Gi free) — **−3.7 Gi over ~11.5h**, below the
     5 Gi soft-floor observed in concurrent researcher sessions (ballot
     S80 at 4.5→2.9 Gi same window; minkowski S29 at 6.7→3.4 Gi same
     window). Cross-validates a host-rooted disk leak, not a self-cycle.
   - **G8 Docker**: `docker info` 10s timeout, `ServerVersion: <empty>`
     — **unchanged RED** since S8 snapshot (≥11.5h hung; consistent with
     ballot S80 + minkowski S29 cross-agent reports of Docker daemon
     hung since 06:01Z, ~20h cumulative at S9 claim).
   - **G9 lake self-loop**: `proofs/.lake → /Users/rwalters/GitHub/
     lean-genius/proofs/.lake` (self-referencing symlink) — **unchanged
     RED** since S8 snapshot.
   - All three are host-environmental, not slug-rooted; S9 STATE-SYNC
     refreshes the snapshot row of the ACT-readiness gate (item 8) and
     restates the S9 ACT block status as "still blocked on infra".

2. **Mathlib pin byte-stability re-verify**.
   `proofs/lake-manifest.json` confirms the Mathlib4 dependency `rev` is
   still `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0 release SHA),
   byte-identical to S8 PREP. Lake-pinned ≥4.5 days. No re-walk of S7/S8
   PREP bearer table justified (transitivity at byte-stable SHA covers
   `PMF.toOuterMeasure_apply_fintype` Basic.lean:203, `MeasurableSet.of_
   discrete` Defs.lean:549, `Fintype.card_subtype.symm` Card.lean:378,
   `Equiv.piSplitAt` Logic/Equiv/Prod.lean:479).

3. **Iteration bump 10 → 11; lastUpdate refresh**.
   `currentState.{iteration, since, focus, nextAction, lastUpdate,
   attemptCounts.total}` + `knowledge.{progressSummary prepend,
   nextSteps[0] minor refresh}` + top-level `lastUpdate`.

### Files updated (S9 STATE-SYNC)

- `research/problems/prob-method-lovasz-local-oq-01/state.md` — this
  block (head update + new narrative section + Iteration History +1 row).
- `research/problems/prob-method-lovasz-local-oq-01/sessions/2026-05-17-s09-statesync-infra-escalation.md`
  — new memo (~340 LOC, 10 sections).
- `src/data/research/problems/prob-method-lovasz-local-oq-01.json` —
  10-field JSON catchup (no leanFiles edit; mechanic #19792 deliberate
  choice honored per separate scope boundary).

### Build-verification posture

Doc-only STATE-SYNC; `MoserTardos.lean` unchanged on this branch (file
SHA byte-identical to origin/main post-S8 PREP + mechanic #19792).
No build attempted (Docker daemon hung; would not succeed even if
attempted, per cross-agent G8 reports).

### ACT-readiness gate (8-item, S9 STATE-SYNC refresh)

| # | Item | Status | Δ since S8 PREP |
|---|---|---|---|
| 1 | Mathlib pin stable | GREEN | unchanged (byte-identical, ≥4.5d) |
| 2 | Bearers verified at pin | GREEN | unchanged (transitivity at stable SHA) |
| 3 | Paste-ready substitute body | GREEN | unchanged |
| 4 | Parent file baseline stable (382 LOC, 0 algorithmic sorries) | GREEN | unchanged (file SHA stable) |
| 5 | No competing open PRs on slug | GREEN | unchanged (probe 2026-05-17T02:00Z: 0 open) |
| 6 | JSON catchup planned | GREEN | this PR closes |
| 7 | problem.md / knowledge.md unchanged | GREEN | unchanged |
| 8 | Infra: Docker + disk | **RED-er INFRA** | G7 6.6→2.9 Gi (-3.7 Gi/11.5h soft-floor cross); G8 hung continuous ≥20h cumulative; G9 unchanged |

7/8 GREEN substantive + 1/8 **RED-er** INFRA. ACT remains blocked
strictly on infra (Docker daemon + disk pressure).

### leanFiles[1] mechanic-choice respect note (S9 STATE-SYNC §1)

Mechanic PR #19792 (researcher unknown, merged 2026-05-16T20:21Z, T-6h
at S9 claim) deliberately set `leanFiles[1]` (`MoserTardos.lean`) to
`{lineCount: 382, theoremCount: 5, axiomCount: 0, defCount: 5,
sorryCount: 0}` with explicit PR-body rationale:
- `theoremCount=5` via regex `^(theorem|lemma) ` excluding `private`
  prefix (`marginal_uniformOfFintype_pi` line 175 is the excluded one);
- `sorryCount=0` via "both remaining grep matches are docstring mentions
  on lines 7 + 22 (file-level `/- ... -/`), not tactic sites".

Per the separate-mechanic-scope-boundary feedback memo:
S9 STATE-SYNC **does not re-flip** these counts even though a different
canonical regex (`^(?:protected|private|noncomputable )*(theorem|lemma) `
yielding 6, and raw `\bsorry\b` yielding 2) would produce different
values. Mechanic's explicit deliberate choice 6h ago is the authoritative
recent statement; same-slug ping-pong avoided.

### Race-safety note (S9 STATE-SYNC)

- Pre-claim probe (2026-05-17T01:36Z): `gh pr list --search prob-method-
  lovasz-local-oq-01 --state all --limit 8` shows 0 open PRs on slug;
  most recent merge S8 PREP (#19628) at 2026-05-16T14:32Z (T-11.5h
  lead); mechanic #19792 at 2026-05-16T20:21Z (T-6h lead, leanFiles
  fix). No competing open work.
- Pre-push probe will re-verify before push.

### Next action (S10 — either ACT post-infra-recovery, or another STATE-SYNC if infra still RED)

If infra recovers (G7 ≥10 Gi + G8 Docker daemon up + G9 .lake
re-initialized): proceed with S9-original-spec ACT (OQ-01-A.3 paste,
~130 LOC) per S8 PREP §4 budget. Recipe unchanged.

If infra remains RED in next claim window: re-STATE-SYNC iter 11→12 with
further escalation if disk crosses 1 Gi (host-critical floor) or
emergency-release if disk crosses 0.5 Gi.

## S8 PREP (faithful-link bearer-gap + sum-form substitute + STATE-SYNC catchup) — researcher-8, 2026-05-16

**Mode**: PREP (doc-only — this section + S7 PREP retro block below + new
session memo + JSON catchup; **no Lean / problem.md / knowledge.md /
meta.json / Mathlib pin edits**).

**Outcome**: doc-only progress on three axes.

1. **Bearer-gap finding (S7 PREP §3.3(c) hedge resolved at pin
   `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)**.
   `MeasurableSet.of_discrete` **EXISTS** at
   `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean:549`, BUT requires
   `[MeasurableSpace α] [DiscreteMeasurableSpace α]`, neither of which
   fires on `P.State = (j : Fin numVars) → P.alphabet j` because
   `P.alphabet j : Type` has only `[Fintype]` + `[Nonempty]`
   field-instances (no `[MeasurableSpace]`). The prerequisite chain is
   one layer deeper than S7 PREP's `gh api` scope caught.
2. **Cheaper-than-fallback substitute (the "upside surprise")**.
   `PMF.toOuterMeasure_apply_fintype` at
   `Mathlib/Probability/ProbabilityMassFunction/Basic.lean:203` requires
   only `[Fintype α]` (no `[MeasurableSpace]`, no `MeasurableSet s`):
   ```lean
   theorem toOuterMeasure_apply_fintype [Fintype α] :
       p.toOuterMeasure s = ∑ x, s.indicator p x
   ```
   The outer-measure form is mathematically equivalent for LLL purposes
   (upper bound on outer ≤ upper bound on inner via
   `toOuterMeasure_apply_le_toMeasure_apply` at Basic.lean:217). The
   substitute faithful-link lemma is `uniformDrawProb_eq_outerMeasure`,
   paste-ready ~25 LOC body in session memo §3.2.
3. **STATE-SYNC catchup**. state.md head had not been updated since S6
   ACT (iter 8); S7 PREP #19111 (iter 9) merged 2026-05-15T22:58 was
   absent from narrative + JSON. This PREP retro-adds the S7 PREP block
   (below) + this new S8 PREP block; iteration 8 → 10.

**Revised S7 PREP §4 LOC budget**: ~130 LOC unchanged (substitute is
drop-in replacement for §4.3; §4.1/§4.2/§4.4 unchanged; §4.3a optional
`toMeasure` corollary +8-10 LOC only if downstream needs it; §4.5
boundary lemmas optional).

### Files updated (S8 PREP)

- `research/problems/prob-method-lovasz-local-oq-01/sessions/2026-05-16-s08-prep-faithful-link-bearer-gap-substitute.md`
  — new memo, ~600 LOC (10 sections + appendix).
- `research/problems/prob-method-lovasz-local-oq-01/state.md` — this
  block + S7 PREP retro block (below) + head update + Iteration History
  +2 rows; iteration 8 → 10.
- `src/data/research/problems/prob-method-lovasz-local-oq-01.json` —
  `currentState.{phase, iteration, since, focus, nextAction, lastUpdate}`
  + `attemptCounts.total` 6 → 8 + `progressSummary` prepend +
  `insights` +2 entries + `nextSteps` refresh.

### Build-verification posture

Doc-only PREP; `MoserTardos.lean` unchanged on this branch. All Mathlib
bearers verified at lake-pinned SHA via direct `curl
raw.githubusercontent.com` (session memo §A.1–§A.5).

### ACT-readiness gate (8-item)

| # | Item | Status |
|---|---|---|
| 1 | Mathlib pin stable | ✅ GREEN |
| 2 | Bearers verified at pin | ✅ GREEN |
| 3 | Paste-ready substitute body | ✅ GREEN |
| 4 | Parent file baseline stable (382 LOC, 0 algorithmic sorries) | ✅ GREEN |
| 5 | No competing open PRs on slug | ✅ GREEN |
| 6 | JSON catchup planned | ✅ GREEN |
| 7 | problem.md / knowledge.md unchanged | ✅ GREEN |
| 8 | Infra: Docker + disk | 🔴 **RED INFRA** (Docker `info` ServerVersion empty in ≤10s; `/System/Volumes/Data` 100% capacity, 6.6 Gi free) |

7/8 GREEN substantive + 1/8 RED INFRA. ACT blocked on infra only.

### Race-safety note (S8 PREP)

- Pre-claim probe (~13:30 UTC): 0 open PRs on slug; most recent merge
  S7 PREP (#19111) at 22:58 UTC on 2026-05-15 — ~14.5h lead time.
- Pre-push probe will re-verify before push.

### Next action (S9 ACT — OQ-01-A.3 paste, post-infra-recovery)

Drop into Part V (new file end) of `proofs/Proofs/MoserTardos.lean`:

- **§4.1** (S7 PREP) — `uniformDrawProb` + `collisionAdj` defs, ~10 LOC.
- **§4.2** (S7 PREP) — `uniformDrawProb_nonneg` + `uniformDrawProb_le_one`
  + `card_state_pos`, ~30 LOC.
- **§3.2** (this PREP) — `uniformDrawProb_eq_outerMeasure` faithful-link
  substitute, ~25 LOC + fallbacks documented in §3.3.
- **§4.4** (S7 PREP) — `LLLAdmissibleUniform` structure +
  `toLLLAdmissible` forward bridge, ~30 LOC.
- **§4.3a** (this PREP, optional) — `_eq_toMeasure` corollary, +8-10 LOC,
  only if downstream OQ-01-B needs `toMeasure` form.
- **§4.5** (S7 PREP, optional) — `_eq_zero_iff` / `_eq_one_iff` boundary
  lemmas, +20 LOC, only if OQ-01-B needs case-splits.

Net target: ~130 LOC, 0 new sorries, 0 new axioms. Build-verify via
`./proofs/scripts/docker-build.sh Proofs.MoserTardos`.

## S7 PREP (LLLAdmissibleUniform structure design) — researcher-3, 2026-05-14 ~19:46 UTC (retro-add)

**Mode**: PREP (doc-only — single new session memo, ~635 LOC).
**PR**: #19111 (merged 2026-05-15T22:58).

**Outcome**: comprehensive design memo for OQ-01-A.3, the
`LLLAdmissibleUniform` structure refinement of the existing
`LLLAdmissible`. Locks the signature, the faithful-link lemma signature,
the Mathlib bearer (`PMF.toMeasure_uniformOfFintype_apply`
Uniform.lean:318), and a ~150-LOC paste-ready implementation skeleton
broken into 5 blocks (§4.1 defs, §4.2 basic bounds, §4.3 faithful-link,
§4.4 structure + forward bridge, §4.5 optional boundary lemmas).

**Three v4.26.0 elaboration pitfalls documented (§3.3)**:
- (a) `Rat.cast` namespace ambiguity → explicit `((... : ℝ) : ℝ≥0∞)` ascription.
- (b) `push_cast` may need explicit lemma hints → 5-name `simp only` fallback.
- (c) `MeasurableSet.of_discrete` "may not exist by that exact name" → 3
  fallback chains listed (subsingleton / compl_iff / Trivial-class /
  manual `MeasurableSet.of_eq`). **NOT verified at pin** (gap closed by
  S8 PREP §1.2 — lemma exists, but prerequisite chain
  `[MeasurableSpace α] [DiscreteMeasurableSpace α]` does not fire on
  `P.State`; see S8 PREP §3 for the substitute via `toOuterMeasure`).

### Files updated (S7 PREP)

- `research/problems/prob-method-lovasz-local-oq-01/sessions/2026-05-14-s7-prep-lll-admissible-uniform-design.md`
  — new memo, ~635 LOC.
- (No state.md / JSON updates by S7 PREP; STATE-SYNC was deferred and
  caught up by S8 PREP this cycle.)

### Build-verification posture (S7 PREP)

Doc-only PREP; `MoserTardos.lean` unchanged. Bearers verified at lake
pin SHA via `curl raw.githubusercontent.com` (memo §A); the
`MeasurableSet.of_discrete` hedge was the one bearer that S8 PREP
re-audited and found a deeper gap on.

### Race-safety note (S7 PREP)

PR #19111 opened 2026-05-14T19:46, ~1h after S6 ACT #19103 opened
(2026-05-14T18:41). Both PRs touched orthogonal files (S6 ACT modified
the Lean file; S7 PREP added a session memo). No conflict; both merged
together 2026-05-15T22:58/22:59.

## S6 ACT (build-verify repair) — researcher-8, 2026-05-14 ~18:35 UTC

**Mode**: ACT (`MoserTardos.lean` net +20/-20 LOC, structurally unchanged;
build VERIFIED 7743 jobs, 4 Docker iterations).

**Outcome**: first Docker baseline of `MoserTardos.lean` since the S5 ACT
(#18629) and S5b ACT (#18960) merges shipped with `(build pending)`
surfaced a **6-error 4-cluster regression**. All four clusters were
elaboration-level latent bugs masked by absence of build validation —
NOT v4.26.0 surface renames; the S4a/S4b/S5b/S5c PREP bearer audits
remain valid.

**Cluster summary:**

| Cluster | Sites | Class | Fix |
|---|---|---|---|
| A | 163, 247, 276 | `rw [h_const/h_proj]` post-`map_comp` eta/composition shape mismatch | Rewrite `h_const`/`h_proj` LHS in `∘` form; add `Function.comp` to `simp` lemma list |
| B | 211 | `ℝ≥0∞` notation tokenization fails inside `rw [...]` followed by `i]` | Lift to `have hprod; rw [hprod]`; rename `ℝ≥0∞` → `ENNReal` identifier |
| C | 179 | Downstream unsolved goal from B | Resolves automatically once B fixed |
| D | 291 | Recursive `P.run n` field-notation strip on `def run` body | Drop prefix: `run n` (with `P` auto-bound from variable) |

Full kit, error-by-error fix recipes, and lessons-learned in
`sessions/2026-05-14-s06-act-build-verify-repair.md`.

### Files updated (S6 ACT)

- `proofs/Proofs/MoserTardos.lean` — net +20/-20 LOC (structurally
  unchanged at 382 LOC), all surgical:
  - `resampleAt_apply_outside` lines 154-164: cluster A
  - `marginal_uniformOfFintype_pi` lines 207-227: cluster B
  - `resampleAt_apply_inside` lines 239-249: cluster A
  - `resampleAt_indep` lines 264-276: cluster A
  - `run` line 290: cluster D
- `research/problems/prob-method-lovasz-local-oq-01/state.md` — this
  section; iteration 7 → 8.
- `research/problems/prob-method-lovasz-local-oq-01/sessions/2026-05-14-s06-act-build-verify-repair.md`
  — new session note (~210 LOC).
- `src/data/research/problems/prob-method-lovasz-local-oq-01.json` —
  `currentState.iteration` 7 → 8, `phase` S5b ACT → S6 ACT,
  `focus`/`nextAction` updated, `lastUpdate`,
  `attemptCounts.total` 5 → 6.

### Build verification

```bash
./proofs/scripts/docker-build.sh Proofs.MoserTardos
# build 1 (baseline): 6 errors, 4 clusters
# build 2 (clusters A + D v1): 3 errors persist; cluster B + new D variant
# build 3 (B `have/rw` workaround + D `run n`): cluster B persists at ℝ≥0∞
# build 4 (B ℝ≥0∞ → ENNReal): ✓ 7743 jobs clean
```

### Race-safety note (S6 ACT)

- Pre-claim probe (~18:00 UTC): 0 ACT-tier open PRs on slug; only
  doc-only S5 PREP STATE-SYNC #18984 carryover.
- Pre-push probe will re-verify before push.

### Next action (S7 PREP — OQ-01-A.3 or OQ-01-B)

With the file actually building clean, the OQ-01-A.3 / OQ-01-B branches
are now strictly unblocked:

- **(a) S7 PREP OQ-01-A.3** — `LLLAdmissibleUniform` refinement of
  `LLLAdmissible` whose `prob : Fin numEvents → ℝ` field is the
  uniform-draw probability `Pr_{v ~ uniformOfFintype State}[isBad i v]`,
  plus the faithful-link lemma. ~150 LOC.

- **(b) S7 PREP OQ-01-B** — `WitnessTree` inductive type + `isProper`
  predicate (the OQ-01-B half), ~500 LOC across 2-3 PRs.

The repaired marginal/independence pack
(`resampleAt_apply_outside`, `resampleAt_apply_inside`, `resampleAt_indep`,
helper `marginal_uniformOfFintype_pi`) is the load-bearing API for
OQ-01-B's witness-tree probability bound.

## S5b ACT (helper + `_inside` + `_indep`) — researcher-12, 2026-05-14 ~00:35 UTC

**Mode**: ACT (`MoserTardos.lean` +113 LOC; build pending).

**Outcome**: shipped the four-step recipe from S5c PREP §9 (PR #18930) +
S5b PREP §7 (PR #18683) + S4b PREP §6/§7 (PR #18580). Net delta:
**+113 LOC** to `proofs/Proofs/MoserTardos.lean` (269 → 382 LOC), 0 new
sorries, 0 new axioms, 0 new imports.

### What I added

Three new declarations between `resampleAt_apply_outside` (existing
L150–L163) and `step` (now L282):

1. **`private lemma marginal_uniformOfFintype_pi`** — reusable Mathlib-style
   helper stating the marginal of `PMF.uniformOfFintype` on a dependent
   product is the uniform PMF on the factor. ~52 LOC of body. Proof:
   `ext + map_apply + uniformOfFintype_apply + tsum_fintype + sum_filter
   + sum_const + nsmul_eq_mul` to reduce to a fiber-card×inverse-card
   product, then a 22-LOC `h_fiber` block via
   `Fintype.card_subtype.symm + Fintype.card_congr + Equiv.piSplitAt`,
   then `push_cast [Fintype.card_pi] + Fintype.prod_eq_mul_prod_subtype_ne`
   to peel off the i-th factor, then a 4-`have` positivity/finiteness
   pack feeding `ENNReal.mul_inv + mul_left_comm + ENNReal.mul_inv_cancel
   + mul_one`.

2. **`lemma resampleAt_apply_inside`** — ~17 LOC including docstring.
   `unfold + PMF.map_comp + funext + simp [dif_pos hj]` reduces the
   glue-function to a single-coordinate projection, then `exact
   marginal_uniformOfFintype_pi ⟨j, hj⟩` closes it (one-line discharge,
   matching S4b PREP §6).

3. **`lemma resampleAt_indep`** — ~20 LOC including docstring. Same
   structural pattern as `_outside` lifted from one coordinate to a
   `Finset T`: every `k : ↥T` has `k.val ∉ S` (by `Finset.disjoint_left.mp
   hT`), the glue function reduces to a constant `v` on all of `T`, then
   `PMF.map_const` finishes.

### Deviations from the PREP recipes (intentional)

- **`mul_left_comm` instead of `← mul_assoc` + `one_mul`** in the
  ENNReal cancellation (last 3 lines of the helper). The S5b PREP §2
  recipe used `← mul_assoc, ENNReal.mul_inv_cancel ..., one_mul`, but the
  associativity direction does not match the cancellation target after
  `ENNReal.mul_inv` distributes the inverse. Substituting `mul_left_comm`
  (which rewrites `a * (b * c) = b * (a * c)`) puts the
  cancellable pair `(∏ k≠i, ...) * (∏ k≠i, ...)⁻¹` adjacent for the
  `ENNReal.mul_inv_cancel` rewrite, ending with `mul_one` rather than
  `one_mul`.
- **`Or.inl h_card_i_ne_top` instead of `Or.inl h_pi_ne_top`** as the
  second argument to `ENNReal.mul_inv`. The signature is
  `(h : a ≠ 0 ∨ b ≠ ⊤) → (h' : a ≠ ⊤ ∨ b ≠ 0) → (a * b)⁻¹ = a⁻¹ * b⁻¹`;
  with `a = card (β i)` and `b = ∏ k≠i, ...`, the second disjunction
  needs `a ≠ ⊤` (i.e. `h_card_i_ne_top`), not `b ≠ ⊤` (which would be
  `h_pi_ne_top` but doesn't fit either disjunct).

Both deviations are mechanical algebraic refinements of the documented
recipe; the underlying strategy (helper via piSplitAt + factor-out-i-th
via `prod_eq_mul_prod_subtype_ne` + ENNReal cancellation) is unchanged.

### Files updated (S5b ACT)

- `proofs/Proofs/MoserTardos.lean` — +113 LOC, 3 new declarations
  inserted after `resampleAt_apply_outside`. File: 269 → 382 LOC.
- `research/problems/prob-method-lovasz-local-oq-01/state.md` — this
  section; iteration 6 → 7; phase S5c PREP → S5b ACT.
- `research/problems/prob-method-lovasz-local-oq-01/sessions/2026-05-14-s05b-act-helper-and-pack.md`
  — new session note documenting the three deviations above + the
  remaining risks for doctor verification.
- `src/data/research/problems/prob-method-lovasz-local-oq-01.json` —
  `currentState.iteration` 6 → 7, `phase` PREP → S5b ACT, `focus` /
  `nextAction` updated, `progressSummary` prepended, `lastUpdate`,
  `attemptCounts.total` 4 → 5.

### Build-verification posture

Build pending. The worktree's `proofs/.lake` is the recursive
self-referential symlink documented in
`feedback_researcher_lake_symlink_loop_and_wipe.md`; local Docker build
would require a ~45-min cold Mathlib clone. CI / doctor is the ground
truth. Each named bearer in the new code is verified at lake-pinned
SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`v4.26.0`) per the
S4a/S4b/S5b/S5c PREP audits.

### Race-safety note (S5b ACT)

- Pre-claim probe (~00:30 UTC, 2026-05-14): 0 open PRs on slug; most
  recent merge S5c PREP (#18930) at 23:06 UTC ~1.5h lead time, well
  outside the 30-min same-slug race window.
- Pre-push probe will re-verify before push.

### Next action (S6 ACT or OQ-01-A.3)

Per the road map in `state.md:301-313`:

- **S6 PREP (OQ-01-A.3)**: Define `LLLAdmissibleUniform` (a refinement of
  `LLLAdmissible` whose `prob` field is the uniform-draw probability of
  `A_i`); prove the faithful-link lemma `prob i = (... uniform measure of
  isBad i ...)`. ~150 LOC.

- **Alternative — S6 PREP (OQ-01-B)**: Begin `WitnessTree` inductive type
  + `isProper` predicate (the OQ-01-B half). The marginal/independence
  pack delivered here is exactly the input it needs.

The helper `marginal_uniformOfFintype_pi` is reusable across both
directions; future ACT iterations should treat it as part of the
file-local API surface.

## S5c PREP (`h_fiber` audit) — researcher-5, 2026-05-13 ~22:25 UTC

**Mode**: PREP (doc-only; no `.lean` diff).

**Outcome**: produced
`sessions/2026-05-13-s05c-prep-h-fiber-card-equiv-audit.md` — closes the
single remaining bearer-audit uncertainty in the S4b PREP / S5b PREP
helper-proof template for `PMF.marginal_uniformOfFintype_pi`.

### What this resolves

S4b PREP §3.2 / §9.4 + S5b PREP §2.2 risk #5 both flagged
`Finset.card_eq_of_equiv_fintype` as the bridge from
`(Finset.univ.filter p).card` to `Fintype.card { x // p x }` but
explicitly deferred verification ("Verify at S5b ACT time").

This PREP **completes that verification**:

- **Negative**: `Finset.card_eq_of_equiv_fintype` does **not** exist
  at the pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (`v4.26.0`) — verified by `gh api` grep of `Finset/Card.lean`,
  `Fintype/Card.lean`, `Logic/Equiv/Finset.lean`.
- **Positive**: canonical replacement is
  `Fintype.card_subtype.symm` (Card.lean L378) → `Fintype.card_congr`
  (Card.lean L67), feeding an explicit
  `{f // b = f i} ≃ ∀ k : {k // k ≠ i}, β k` built from
  `Equiv.piSplitAt` (Prod.lean L479, re-verified).

### What the doc contains

- §2: pinned-SHA audit table for 3 replacement bearers (Card.lean L378,
  Fintype/Card.lean L67, Prod.lean L479) — file path, blob context,
  line number, verbatim signature.
- §3: **~22 LOC sorry-free Lean rewrite of S4b PREP §3.2's `h_fiber`
  block** using only the verified bearers. Drops directly into the
  helper-proof template at the §3 position.
- §4: updated LOC accounting for S5b ACT — helper now ~44 LOC
  (S4b §3.2 scaffold + this PREP §3 `h_fiber` block + S5b §2 ENNReal
  block); 3-lemma pack still ~38 LOC; net S5b ACT delta ~70 LOC.
- §5: three residual risks (`Subtype.coe_mk` simp, `@[simps]` name
  variants, `.left_inv` field projection) with in-doc fallbacks.
- §9: revised S5b ACT 4-step recipe.

### Files updated (S5c)

- `research/problems/prob-method-lovasz-local-oq-01/sessions/2026-05-13-s05c-prep-h-fiber-card-equiv-audit.md`
  — new doc, ~250 LOC.
- `research/problems/prob-method-lovasz-local-oq-01/state.md` — this
  section; iteration 5 → 6.
- `src/data/research/problems/prob-method-lovasz-local-oq-01.json` —
  `currentState.iteration` 5 → 6, `focus` / `nextAction` updated,
  `progressSummary` prepended, `lastUpdate`.

### Build-verification posture

Doc-only PREP; `MoserTardos.lean` unchanged. No build needed.

### Race-safety note (S5c)

- Pre-claim probe (~22:18 UTC): 0 open PRs on the slug;
  most recent merge is S5b PREP (PR #18683) at 08:19 UTC — 14h lead time,
  well outside the morning's 4-merges-in-6h saturation burst.
- Pre-push probe will re-verify before push.

### Next action (S5b ACT — now fully unblocked)

Per the revised recipe in §9 of the new PREP doc + S4b PREP §6/§7 +
S5b PREP §2 + this PREP §3: ship `PMF.marginal_uniformOfFintype_pi`
(~44 LOC) + `resampleAt_apply_inside` (~8 LOC, S4b PREP §6) +
`resampleAt_indep` (~18 LOC, S4b PREP §7). Net delta ~70 LOC.

## S5 ACT (Outside) — researcher-6, 2026-05-13 ~07:10 UTC

**Outcome**: progress — discharged the first of the three S4b PREP §5-§7 marginal-pack lemmas: `resampleAt_apply_outside`. +24 LOC to `proofs/Proofs/MoserTardos.lean` (245 → 269), 0 new sorries, 0 new axioms, 0 new imports.

### What I added

The S4b PREP §5 verbatim discharge of the disjoint-coordinate marginal:

```lean
lemma resampleAt_apply_outside (S : Finset (Fin P.numVars)) (v : P.State)
    (j : Fin P.numVars) (hj : j ∉ S) :
    (P.resampleAt S v).map (fun w => w j) = PMF.pure (v j) := by
  classical
  unfold resampleAt
  rw [PMF.map_comp]
  have h_const :
      (fun a : ∀ k : S, P.alphabet k.val =>
        (fun (b : Fin P.numVars) =>
          if h : b ∈ S then a ⟨b, h⟩ else v b) j)
      = Function.const _ (v j) := by
    funext a
    simp [dif_neg hj]
  rw [h_const, PMF.map_const]
```

11-LOC proof body + docstring + blank line + section context = 24 LOC. Uses only `PMF.map_comp` (Mathlib v4.26.0 `Probability/ProbabilityMassFunction/Constructions.lean:66`) and `PMF.map_const` (same file, line 79), plus `dif_neg`.

### Why ship only `_outside` (not the full §5-§7 pack)

S4b PREP §6 (`_inside`) and §7 (`_indep`) depend on a new helper `PMF.marginal_uniformOfFintype_pi` (~40 LOC, S4b PREP §3) which uses `Equiv.piSplitAt`, `Fintype.card_congr`, `Fintype.card_pi`, `tsum_fintype`, and ENNReal arithmetic. The helper's proof is the single mathematically-substantive step in the pack; shipping it without local Docker build verification (`.lake symlink loop` trap) is risky for ~40-LOC probability-theory code.

This S5 ACT ships only `_outside` (12 LOC, uses only 2 Mathlib lemmas, mechanical `funext + simp [dif_neg]`). The helper + `_inside` + `_indep` are deferred to a subsequent S5b ACT.

### Files updated (S5)

- `proofs/Proofs/MoserTardos.lean` — +24 LOC, one new lemma `resampleAt_apply_outside` inserted between `def resampleAt` and `def step`. File: 245 → 269 LOC.
- `research/problems/prob-method-lovasz-local-oq-01/state.md` — this file. Iteration 3 → 5 (jumping S4 since S4/S4a/S4b were PREP-only).
- `research/problems/prob-method-lovasz-local-oq-01/sessions/2026-05-13-s05-act-outside-marginal.md` — new session note.

### Build-verification posture

Per `feedback_researcher_lake_symlink_loop_and_wipe.md`, the worktree's `proofs/.lake` inherits the main repo's self-referential symlink loop; local Docker build is unreliable. **Lean file committed and pushed first**; PR title carries "build pending" so the doctor agent can verify from a clean worktree.

No new imports (the file already does `import Mathlib`, `open scoped Classical`).

### Race-safety note (S5)

- Pre-claim probe (2026-05-13 ~07:05 UTC): 0 open PRs on the slug; most recent merge is S4b PREP (PR #18580) at 04:50 UTC (~2h15min lead time).
- Pre-push probe will re-verify before push.

### Next action (S5b — helper + `_inside` + `_indep`)

Per S4b PREP §3 + §6 + §7: ship `PMF.marginal_uniformOfFintype_pi` (~40 LOC) and use it to discharge `resampleAt_apply_inside` (~8 LOC) and `resampleAt_indep` (~18 LOC). The helper's proof is the load-bearing step and warrants a fresh session.

## S3 ACT — researcher-1, 2026-05-13 (pre-S5 history, for reference)

S3 ACT (researcher-1, 2026-05-13, this PR): **OQ-01-A.2 `resampleAt`
product-PMF closure** in `Proofs/MoserTardos.lean:131-139` (~9 LOC
replacement of the single deferred `sorry`).

The implementation is the Approach B form recommended by the S3 ANALYSIS
doc (researcher-5, PR #18268, §2.2):

```lean
noncomputable def resampleAt (S : Finset (Fin P.numVars)) (v : P.State) :
    PMF P.State :=
  (PMF.uniformOfFintype (∀ j : S, P.alphabet j.val)).map
    (fun (a : ∀ j : S, P.alphabet j.val) (j : Fin P.numVars) =>
      if h : j ∈ S then a ⟨j, h⟩ else v j)
```

The construction samples the dependent product `∀ j : ↥S, alphabet j.val`
uniformly via `PMF.uniformOfFintype` (a finite nonempty `Fintype` by
`Pi.instFintype` + the namespace-attribute-promoted `alphabetFintype`
and `alphabetNonempty`), then glues the sample with the deterministic
`v j` for `j ∉ S` via a single `PMF.map`. The if-then-else uses
`Finset.decidableMem` to dispatch on `j ∈ S`.

**Net sorry delta**: 1 → 0 in MoserTardos.lean (excluding the two
True-shell theorems `mt_expected_step_bound` / `mt_terminates_as` which
still ship usable algebraic shells with full statements deferred to
OQ-01-B / OQ-01-C).

**Net axiomCount delta**: 0.

## S2 ACT history (previous, for reference)

S2 ACT (researcher-12, 2026-05-12, PR #18213 merged): **OQ-01-A.1
algorithm skeleton — `Proofs/MoserTardos.lean` (NEW FILE, +243 lines)**.

Created a standalone scaffold of the variable-version Moser–Tardos
algorithm and stated the two main theorems whose proofs are deferred to
OQ-01-B (witness-tree construction) and OQ-01-C (Galton–Watson /
generating-function sum). The file is wired into the umbrella
`proofs/Proofs.lean` (alphabetical position between `MorleysTheoremOQ01`
and `MotivicFlagMaps`).

**Public surface introduced (`namespace ProbMethod.MoserTardos`):**

* `structure MTProblem` — packages `numVars`, `numEvents`, per-variable
  `alphabet : Fin numVars → Type` with `Fintype` + `Nonempty` instance
  fields, the variable-collision footprint `vbl : Fin numEvents →
  Finset (Fin numVars)`, the bad-event predicate `isBad` (with field-
  encoded decidability), and a faithfulness clause `vblFaithful`
  certifying that `isBad i v` depends only on `v` at the variables in
  `vbl i`.
* `MTProblem.State := (j : Fin P.numVars) → P.alphabet j` with derived
  `Fintype` and `Nonempty` instances.
* `MTProblem.isViolated : State → Prop` with a `Decidable` instance via
  `Fintype.decidableExistsFintype`.
* `MTProblem.pickBad : State → Option (Fin numEvents)` selecting the
  least-index violated event (a deterministic resampling rule, the
  simplest admissible choice per Moser–Tardos).
* `MTProblem.resampleAt : Finset (Fin numVars) → State → PMF State`
  — **stubbed with `sorry`** for the product-`PMF` construction (the
  natural OQ-01-A.2 follow-on; the full mechanical construction is
  documented as a proof obligation in the file's docstring).
* `MTProblem.step : State → PMF State` — one-step Markov chain via
  `match pickBad v` (pure on the no-bad branch, `resampleAt (vbl i)` on
  the bad branch).
* `MTProblem.run : ℕ → State → PMF State` — iterated `step` via
  `PMF.bind`.
* `MTProblem.LLLAdmissible : (Fin numEvents → ℚ) → Prop` — packages the
  range `0 ≤ x i < 1` and the symbolic LLL inequality
  `prob i ≤ x i * ∏_{k ∈ adj i} (1 - x k)` over auxiliary `prob, adj`
  parameters (the faithful link to a uniform-measure probability is
  deferred to OQ-01-A.2 / OQ-01-B).
* `theorem mt_expected_step_bound` — statement shell; the body proves
  the non-negativity of `Σᵢ x_i/(1-x_i)` (matching the parent
  `moser_tardos_termination`). The actual expected-value bound on
  `run`-resampling counts is deferred to OQ-01-B (witness trees)
  + OQ-01-C (Galton–Watson sum).
* `theorem mt_terminates_as` — statement placeholder (returns `True`);
  full `Tendsto (fun n => (run n v₀).toMeasure {v | isViolated v}) atTop
  (𝓝 0)` statement awaits OQ-01-B `WitnessTree` infrastructure.

**Sorry inventory (this PR):** exactly **one** `sorry`, in
`resampleAt` (the product-`PMF` over `Finset (Fin numVars)`). The two
main theorems are NOT `sorry`-ed at the algebraic-shell level — they
ship usable inequalities, with the full statements documented in
docstrings for OQ-01-B / OQ-01-C.

**Build status:** build pending. Worktree's `proofs/.lake` is a
recursive self-symlink (per
`feedback_researcher_lake_symlink_broken.md`), so a local Docker build
would re-fresh-clone Mathlib (~45 min cold). CI is the ground truth.
The single-file Mathlib API surface invoked is:
`PMF.pure`, `PMF.bind`, `Fintype.decidableExistsFintype`, `Finset.min'`,
`Finset.filter`, `Finset.sum_nonneg`, `div_nonneg`, `linarith`,
`Classical.choice`, plus the auto-derived `Pi.fintype`/`Pi.Nonempty`
chain — all stable across the recent v4.26 API surface.

Next action: **S3 ACT — OQ-01-A.2 product-`PMF`** (close the
`resampleAt` `sorry` via iteration of `PMF.bind` over `Finset.univ`,
using `PMF.uniformOfFintype (P.alphabet j)` for `j ∈ S` and `PMF.pure
(v j)` for `j ∉ S`). Estimated ~60–80 lines.

## S1 history

S1 OBSERVE (researcher-11, 2026-05-12, PR #18100 merged): surveyed the
open question, decomposed into three sub-tasks (OQ-01-A / OQ-01-B /
OQ-01-C), surveyed Mathlib API readiness, and identified the duplication
with `lovasz-local-lemma-oq-03`.

## Active Approach

**Approach 2** — Direct witness-tree proof (Moser–Tardos 2010 §4),
decomposed into:

- **OQ-01-A**: Algorithm + probability space (PMF-based finite model)
- **OQ-01-B**: Witness trees + tree-probability bound
- **OQ-01-C**: Galton-Watson / generating-function sum to `xᵢ/(1-xᵢ)`

Approach 1 (symmetric-only) and Approach 3 (entropy-compression) explicitly
rejected as insufficient for the full OQ — see `problem.md`.

## Attempt Count
- Total attempts: 2 (S1 OBSERVE + S2 ACT)
- Current approach attempts: 1 (S2 OQ-01-A.1 skeleton)
- Approaches considered: 3 (recommended: Approach 2 with A/B/C decomposition)

## Blockers

- **Mathlib gap**: no Galton–Watson branching-process API. Mitigation: use
  direct generating-function calculation in OQ-01-C.
- **Mathlib gap**: no general "rooted labelled tree" type. Mitigation: define
  `inductive WitnessTree` from scratch in OQ-01-B.
- **Sibling duplication**: `lovasz-local-lemma-oq-03` is the same problem.
  Coordinate at S2; do not block S2 on dedup.

## Next Action

**S9 ACT (OQ-01-A.3 paste) — drop the LLLAdmissibleUniform implementation
into Part V of `proofs/Proofs/MoserTardos.lean`, ~130 LOC, post-infra-recovery.**

Per the S7 PREP design (PR #19111) + S8 PREP §3.2 substitute (this PR):

- §4.1 `uniformDrawProb` + `collisionAdj` defs (~10 LOC)
- §4.2 `uniformDrawProb_nonneg` + `uniformDrawProb_le_one` + `card_state_pos` (~30 LOC)
- §3.2 `uniformDrawProb_eq_outerMeasure` faithful-link substitute (~25 LOC, S8 PREP §3.2)
- §4.4 `LLLAdmissibleUniform` structure + `toLLLAdmissible` forward bridge (~30 LOC)
- §4.3a `_eq_toMeasure` corollary (~8-10 LOC, optional — only if downstream needs `toMeasure`)
- §4.5 `_eq_zero_iff` / `_eq_one_iff` boundary lemmas (~20 LOC, optional)

Net target: ~130 LOC, 0 new sorries, 0 new axioms. Build-verify via
`./proofs/scripts/docker-build.sh Proofs.MoserTardos`. ACT-readiness gate
7/8 GREEN substantive + 1/8 RED INFRA (Docker daemon hung + disk 100%
capacity) — wait for infra recovery before claiming S9 ACT.

### Historical (pre-S5) ACT roadmap (preserved for reference)

Per S3 ANALYSIS §4, after OQ-01-A.2 closed (S3 ACT #18400), the following
three sorry-free marginal-pack lemmas were the next addition (all shipped
via S5 ACT #18629 + S5b ACT #18960):

```lean
lemma resampleAt_apply_outside (S : Finset (Fin P.numVars))
    (v : P.State) (j : Fin P.numVars) (hj : j ∉ S) :
    (P.resampleAt S v).map (fun w => w j) = PMF.pure (v j)

lemma resampleAt_apply_inside (S : Finset (Fin P.numVars))
    (v : P.State) (j : Fin P.numVars) (hj : j ∈ S) :
    (P.resampleAt S v).map (fun w => w j) = PMF.uniformOfFintype (P.alphabet j)

lemma resampleAt_indep (S : Finset (Fin P.numVars)) (v : P.State)
    (T : Finset (Fin P.numVars)) (hT : Disjoint T S) :
    (P.resampleAt S v).map (fun w => (fun j : T => w j.val)) =
      PMF.pure (fun j : T => v j.val)
```

The first two are corollaries of `PMF.map_uniformOfFintype_fst/snd` and
the `if h : j ∈ S` dispatch; the third is a `Finset.map` lift. Together
they provide the marginal/independence facts that OQ-01-B (witness
trees) directly invokes.

**Estimated next-PR scope**: ~50-80 LOC. **Build-verify under Docker.**

Then **S4-S5 OQ-01-A.3**: LLLAdmissible faithful link to uniform measure
(~150 LOC). Then **S6+ OQ-01-B**: witness trees.

## Open Sub-Tasks (Roadmap)

| Step | Deliverable | Tractability | Est. LOC |
|------|-------------|--------------|----------|
| S1 OBSERVE (done, #18100) | problem.md / knowledge.md / state.md / JSON | trivial | 1100 markdown |
| S2 ACT OQ-01-A.1 (this PR) | MoserTardos.lean skeleton + 2 stated theorems | medium | +243 LOC |
| S3 ACT OQ-01-A.2 | close `resampleAt` product-PMF + invariance lemma | medium | ~60-80 LOC |
| S4-S5 OQ-01-A.3 | LLLAdmissible faithful link to uniform measure | medium | ~150 LOC |
| S6-S8 OQ-01-B | witness trees + tree-prob bound | hard | ~500 LOC, 2-3 PRs |
| S9-S11 OQ-01-C | Galton–Watson sum bound | hard | ~400 LOC, 2-3 PRs |
| S12 complete | Final integration + close `mt_expected_step_bound` | medium | ~100 LOC |

Total estimated: 6-9 PRs after S1, comparable to a marquee sub-theorem.

## Iteration History

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-12 | researcher-11 | #18100 (merged) | OBSERVE — three-part decomposition + Mathlib survey + sibling dedup analysis |
| S2 | 2026-05-12 | researcher-12 | #18213 (merged) | ACT — OQ-01-A.1 skeleton in `Proofs/MoserTardos.lean` (+243 lines, 1 sorry in `resampleAt`) |
| S3 ANALYSIS | 2026-05-12 | researcher-5 | #18268 (merged) | ANALYSIS — `resampleAt` PMF construction roadmap, Approach A/B/C comparison, three follow-on lemmas (doc-only) |
| S3 ACT | 2026-05-13 | researcher-1 | #18400 (merged) | ACT — OQ-01-A.2 close `resampleAt` sorry via Approach B (PMF.uniformOfFintype + map glue; ~9 LOC replacement) |
| S4 PREP | 2026-05-13 | (researcher) | #18420 (merged) | PREP — OQ-01-B `WitnessTree` skeleton + extraction algorithm + proper-tree predicate (doc-only) |
| S4a PREP | 2026-05-13 | (researcher) | #18477 (merged) | PREP — resampleAt marginal-lemma Mathlib audit (doc-only) |
| S4b PREP | 2026-05-13 | (researcher) | #18580 (merged) | PREP — marginal-lemma discharge via `Equiv.piSplitAt` (doc-only) |
| S5 ACT | 2026-05-13 | researcher-6 | #18629 (merged) | ACT — `resampleAt_apply_outside` marginal (+24 LOC, build pending) |
| S5b PREP | 2026-05-13 | researcher-7 | #18683 (merged) | PREP — close helper bookkeeping sorry via `Fintype.prod_eq_mul_prod_subtype_ne` (doc-only) |
| S5c PREP | 2026-05-13 | researcher-5 | #18930 (merged) | PREP — `h_fiber` bearer audit + sorry-free rewrite (doc-only) |
| S5b ACT | 2026-05-14 | researcher-12 | #18960 (merged) | ACT — `marginal_uniformOfFintype_pi` helper + `_inside` + `_indep` (+113 LOC, build pending) |
| S6 ACT | 2026-05-14 | researcher-8 | #19103 (merged) | ACT — build-verify repair S5/S5b ACT 4-cluster v4.26.0 regression (Docker-verified 7743 jobs; net +20/-20 LOC) |
| S7 PREP | 2026-05-14 | researcher-3 | #19111 (merged) | PREP — `LLLAdmissibleUniform` structure design + ~150-LOC paste-ready skeleton (doc-only) |
| S8 PREP | 2026-05-16 | researcher-8 | #19628 (merged) | PREP — faithful-link bearer-gap resolution + sum-form substitute via `PMF.toOuterMeasure_apply_fintype` + STATE-SYNC catchup (doc-only) |
| (mechanic) | 2026-05-16 | (mechanic) | #19792 (merged) | meta — `leanFiles[1]` `MoserTardos.lean` drift sync post-S6 ACT (243/2/1 → 382/5/0; line/thm/sorry; no Lean edit) |
| S9 STATE-SYNC | 2026-05-17 | researcher-4 | #20041 (merged) | STATE-SYNC — 3 RED INFRA escalation (G7 disk 6.6→2.9 Gi soft-floor cross; G8/G9 unchanged) + Mathlib pin byte-stability re-verify + iteration bump (doc-only) |
| S10 STATE-SYNC | 2026-05-30 | researcher-1 | #21487 (merged) | STATE-SYNC — 13-day-gap absorb + G7+G8 INFRA recovery (62 Gi free + Docker 29.4.1 up) + G9 still-RED + new Docker-mount-overrides-G9 hypothesis flagged for S11 verify + iter 11→12 (doc-only) |
| S11 INFRA-VERIFY | 2026-05-31 | researcher-1 | #21558 (merged) | INFRA-VERIFY — Docker build of origin/main MoserTardos.lean succeeded 7743 jobs at v4.26.0; G9-mount hypothesis EMPIRICALLY CONFIRMED; gate flips to 8/8 GREEN |
| S11.5 STATE-SYNC | 2026-05-31 | researcher-1 | (post-#21558) | STATE-SYNC — JSON catchup absorbing S11 outcome; iteration 12 → 13 (doc-only) |
| S12 ACT | 2026-06-10 | researcher-1 | (this PR) | ACT — OQ-01-A.3 LLLAdmissibleUniform shipped: +135 LOC Part V (uniformDrawProb + collisionAdj defs, basic bounds, outer-measure faithful link, structure + bridge); Docker-verified 7743 jobs at v4.26.0; 0 new sorries, 0 new axioms |
| S13 PREP | 2026-06-12 | researcher-2 | #22938 (merged) | PREP — WitnessTree encoding design: List-children positivity resolution + ranked isProper recursion forms (doc-only) |
| S14 STATE-SYNC | 2026-06-13 | researcher-1 | (merged) | STATE-SYNC — header docstring fix (stale sorry claims, missing Part V) + flag BLOCKED (Docker daemon down) |
| S15 GATE-SYNC | 2026-06-14 | researcher-1 | #24108 (merged) | GATE-SYNC — propagated BLOCKED to JSON + pool gates claim-random reads |
| S16 ACT | 2026-07-24 | researcher-2 | (this PR) | ACT — OQ-01-B WitnessTree skeleton landed as Part VI: inductive WitnessTree + labelOf + inclNbhd + isProper + 3 sanity lemmas (+58 LOC, 522 → 580); Docker-verified 8576 jobs at v4.31.0; 0 new sorries, 0 new axioms; primary recursion form `∀ t ∈ ch, isProper t` elaborates structurally; BLOCKED gates reverted |
| S18-prep ACT | 2026-07-24 | researcher-2 | (this PR) | ACT — Part VII instrumented runner: stepLog/runLog (resample log, most-recent-first ExtractsFrom convention) + conservativity stepLog_map_fst/runLog_map_fst + runLog_length_le + runLog_of_pickBad_none + pickBad_isBad + mem_log_pickBad (+150 LOC, 724 → ~874); Docker-verified 8576 jobs at v4.31.0; 0 new sorries, 0 new axioms; witness_prob_bd (the tree-probability coupling) still open — it will quantify over runLog's support |
