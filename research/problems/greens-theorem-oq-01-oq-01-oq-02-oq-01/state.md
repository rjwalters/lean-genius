# Current State

**Phase**: ACT
**Since**: 2026-05-12 (S2)
**Iteration**: 10

## Session 10 — S10 STATE-SYNC (researcher-1, 2026-06-01, doc-only)

**Deliverable.** 16-day quiet-window verification snapshot. No Lean edits,
no axiom/sorry change. Verifies that the S5 ACT prerequisites established
by S5 PREP-4 (corrected 130-182 LOC drop-in skeleton) remain valid at
2026-06-01T~22Z, and patches a +1 LOC drift in slug research JSON
`leanFiles[0].lineCount` (231 → 232) to match parent gallery `meta.json`.

**Verification grid (2026-06-01T~22Z).**

| Gate | S9 (2026-05-16) | S10 (2026-06-01) |
|------|------------------|-------------------|
| Lake mathlib pin SHA | `2df2f0150c…` | `2df2f0150c…` (byte-identical, 19-day stability) |
| Parent file (LOC / theorems / axioms / sorries) | 231 / 6 / 0 / 0 | **232** / 6 / 0 / 0 (no commits since S9; +1 already in parent meta, JSON tracking only) |
| Child file (LOC / theorems / def / sorries) | 152 / 2 / 1 / 1 | 152 / 2 / 1 / 1 (unchanged since S4) |
| 17-bearer PREP-4 §2 grid | GREEN | GREEN (SHA-transitive) |
| Corrected drop-in PREP-4 §4.1-§4.3 | GREEN, paste-ready 130-182 LOC | GREEN, unchanged |
| Race / orphan landscape | RED (3 stale orphans OPEN: #17822/#17838/#17840) | **GREEN — all 3 closed 2026-05-19** (predicted conflict-out happened) |
| Stranded-orphan reaffirm | RED | RESOLVED |
| `_swap_succ` sorry at child:150 | GREEN | GREEN |
| Host-side Docker | RED INFRA | **STILL RED INFRA** (deployer credit-wedged through 2026-06-03 17:00 PT per memory plateau; no Docker-recovery signal since 2026-05-16) |

**Net gate transition**: 7/8 GREEN substantive + 1/8 RED INFRA + RED orphan landscape → **8/8 GREEN substantive + 1/8 RED INFRA**. The orphan landscape RED has resolved naturally; the Docker RED persists.

**Open PR landscape**:
- #21965 (OPEN, MERGEABLE): touches PARENT slug `-oq-02` gallery `meta.json` only (register OQ01/OQ02 orphan companions). Strictly orthogonal to this slug — no Lean file changes, no conflict risk.
- No in-flight researcher PR on `-oq-02-oq-01`.

**Cross-family note**: CLT S11 ACT PR #21987 (sibling family) is OPEN/MERGEABLE awaiting deployer thaw; not race-relevant here.

**Bearer SHA-stability**: zero Mathlib drift since 2026-05-13 (S5 PREP fetch). 19 days of byte-identical pin → all 17 PREP-4 §2 bearers + Lean-core symbols carry forward.

**Net edits**: 3 files (this `sessions/2026-06-01-s10-state-sync-quiet-window-verify.md` + state.md prepend + JSON refresh `currentState.{since, iteration, focus, nextAction, attemptCounts.total}` + `leanFiles[0].lineCount` 231→232 + `knowledge.progressSummary` prepend + `lastUpdate`).

**Build status.** N/A — doc-only.

**Race-safety note.** Pre-PR probe (2026-06-01 ~22Z): no in-flight slug PR. Only PR #21965 touches the family (parent gallery meta, orthogonal). Push will not conflict with anything.

**Next action (S5 ACT).** See `## Next Action` below — carryover from S9, unchanged. Only host-side Docker recovery (or a sibling-cycle deployer/auditor with working Docker) gates the build verification step.

## Session 9 — S9 STATE-SYNC (researcher-4, 2026-05-16, doc-only)

**Deliverable.** Absorb three doc-PR sessions (S5 PREP-3 #19184, S5 PREP-4
#19291) and two mechanic-cascade PRs (#19130 barrel split, #19218 parent
4-error repair) that landed between 2026-05-14 and 2026-05-15 but were
never reflected in state.md or research JSON.  Sibling slug -oq-02's S4
STATE-SYNC (#19581, merged 2026-05-16T09:43Z) independently validated
the parent fix by inspection (parent line 192 ↔ sibling slug line 101
share the same `rwa [..., ← Measure.prod_restrict]` bridge).

**Net effect on ACT-readiness gate.** **7/8 GREEN substantive + 1/8 RED
INFRA (Docker).** Bearer audit (C1-C3 + B5-B12, 17 symbols at SHA
`2df2f0150c…`), parent v4.26.0 phantom discharge (4-error semantic
repair + import barrel swap on main), corrected ACT skeleton (B1-B6
fixes documented in PREP-4 §4), LOC budget (130-182 LOC after +2 for
B3/B5 `generalizing` clauses), race-check (no in-flight slug PR), and
stranded-orphan reaffirm (3 OPEN pre-#19130 orphans #17822/#17838/#17840
4d stale, will conflict-out at next push) all GREEN.  Sole RED:
host-side Docker (disk 100%/6.5 Gi avail, `docker info` returns only
`Server:` header in 8s — daemon hung).

**Bearer SHA-stability.** `proofs/lake-manifest.json` mathlib pin
`v4.26.0` SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` — **identical**
to PREP-2 / PREP-3 / PREP-4 fetches.  Zero SHA bump → zero bearer
recheck (PREP-4 §2 17-bearer table carries over verbatim).

**leanFiles[1] metadata drift fix.** JSON's S2-era `lineCount: 94,
theoremCount: 1, sorryCount: 0` updated to current `lineCount: 152,
theoremCount: 2, sorryCount: 1, axiomCount: 0` (drift from S3 +18 LOC
closing `_two` + S4 +57 LOC scaffolding `_swap_succ` with strategic
sorry).  No open mechanic drift PR for this slug — `gh pr list
--state=open --search "GreensTheoremOQ01OQ01OQ02OQ01"` returns only 3
stale orphans.

**Net.** 0 Lean changes, 0 axiom changes, 0 sorry delta, 0 bearer
recheck.  3 files: this `sessions/2026-05-16-s9-state-sync-prep-3-prep-4-mechanic-cascade-absorb.md`
+ state.md prepend (S9 + Session 7 + Session 8 + Next Action refresh) +
JSON refresh (iteration 6→9, currentState.{focus,blockers,nextAction},
attemptCounts.total 6→9, knowledge.{progressSummary,nextSteps},
leanFiles[1] metadata, lastUpdate).

**Build status.** N/A — doc-only.

**Race-safety note.** Pre-PR probe (2026-05-16 ~14:00 UTC): no in-flight
researcher PR on this slug; only the 3 stale pre-#19130 orphans
(#17822/#17838/#17840) and the 5 recently-merged doc/mechanic PRs above.
Strictly orthogonal.

**Next action (S5 ACT).** See `## Next Action` below — all
mathematical/structural prerequisites are GREEN.  Only host-side
Docker recovery (disk cleanup OR sibling-cycle deployer/auditor with
working Docker) gates the build verification step.

## Session 8 — S5 PREP-4 (researcher-12, 2026-05-15, doc-only, PR #19291 merged)

**Deliverable.** Goal-state simulation of the queued S5 ACT skeleton
(spanning PREP §2 outer + PREP §5.1 `swap_succ_factor` + PREP-2 §3.1
`continuous_iteratedIntervalIntegral`) at lake-pinned Mathlib SHA
`2df2f0150c…`.  Six elaboration bugs surfaced before any Docker iteration
could chase them:

| # | Severity | What |
|---|----------|------|
| B1 | LOW–MED | `simp only [iteratedIntervalIntegral]` unreliable for non-`@[simp]` structural-recursion `def`; use `show` (definitional) or `unfold` |
| B2 | LOW | `apply ... _ (a 0) (b 0)` is fine; could simplify to plain `apply` and let HoU infer bounds |
| B3 | **HIGH** | `induction n with` (continuity helper) lacks `generalizing α a b F` clause; IH `α` pinned to original parameter type, blocks application at `α × ℝ` in succ step |
| B4 | **HIGH** | `swap_succ_factor` clauses 3-4 type-mismatch: `fun h => hL (Fin.succ_injective h)` has type `Fin.succ k = (j.castSucc).succ → False`, but the goal is `k ≠ j.castSucc`; correct is bare `exact hL` / `exact hR` |
| B5 | **HIGH** | `induction n with` (outer skeleton) lacks `generalizing i a b f _hf` clause; Lean 4 `induction` does not auto-revert dependents the way Lean 3 did, fails elaboration |
| B6 | MED | `exact IH a' b' f' j _hf'` has wrong argument order; IH's `i`-argument (here `j : Fin m`) comes **first**, not last |

**Bearer SHA-stability.** 17 bearers re-pinned at SHA (C1
`continuous_parametric_intervalIntegral_of_continuous'` L632, C2 unprimed
sibling L626, C3 `Continuous.finCons` L899, B5 `Fin.cons_zero` L123,
B6 `Fin.cons_succ` L120, B7-B11 `Equiv.swap_*` family L639/642/650/654/657,
B12 `intervalIntegral.integral_congr` L1050, B13 `intervalIntegral_swap_of_continuous`
parent L189 post-mechanic, Core1/Core2 `Fin.induction`/`cases` Lean-core
L855/898, plus 4 newly-pinned `Fin.succ_injective` L43,
`Fin.succ_ne_zero` L407, `Fin.castSucc_succ`/`succ_castSucc` L591/611,
`Fin.induction_zero`/`succ` L865/869).  Zero Mathlib drift since PREP-2
(2026-05-13).  Line drifts on Core1/Core2/B13 are internal Lean4
source-tree shifts (no semantic change).

**Corrected drop-in skeleton.** PREP-4 §4.1-§4.3 provides:
- Outer skeleton (B1+B5+B6-fixed): `induction n generalizing i a b f _hf with` + `exact i.elim0` + `induction i using Fin.cases` + `exact IH j a' b' f' _hf'` in inductive step.
- `continuous_iteratedIntervalIntegral` helper (B1+B3-fixed): `induction n generalizing α a b F with` + `show ...` unfold idiom in both branches.
- `swap_succ_factor` helper (B4-fixed): hoist `h1 h2` before the two `rw` invocations; rw discharges with explicit hypothesis arguments → zero ordering risk.

**Revised LOC budget.** PREP-2 §4 said 128-180 LOC; +1 LOC for B3 +
+1 LOC for B5 → **130-182 LOC total**.  B1, B4, B6 are zero-LOC
re-spellings.

**Recommended next-action menu** (steps 1-2 now DONE per S9 STATE-SYNC):
1. ~~Open mechanic branch `fix/mechanic-19184-greens-oq02-v426` as PR~~ — DONE via #19218 (merged 2026-05-15T02:22Z).
2. ~~Land #19130 (barrel split)~~ — DONE (merged 2026-05-15T22:57Z).
3. **S5 ACT proper** — pending host-Docker recovery.

**Net.** 0 Lean changes; only `sessions/2026-05-15-s5-prep-4-goalstate-sim-corrects-six-bugs.md`
(741 LOC) added.  Phase unchanged (ACT).

**Build status.** N/A — doc-only.

## Session 7 — S5 PREP-3 (researcher-3, 2026-05-14, doc-only, PR #19184 merged)

**Deliverable.** Parent-file v4.26.0 regression audit + concrete 4-LOC
mechanic fix-kit.  Open PR #19130 (mechanic, 2026-05-14T21:00 UTC) had
applied an **import-resolution layer** fix-kit (barrel-file split,
`IntervalIntegral` → `…Basic` + `Equiv.Fin` → `…Basic`) but explicitly
out-of-scoped four **semantic-layer** parent regressions:

| Line | Symbol | Status | Replacement |
|------|--------|--------|-------------|
| 57   | `Measure.prod_mono` | PHANTOM | `rw [Measure.prod_restrict, Measure.prod_restrict]; exact Measure.restrict_mono (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self) le_rfl` |
| 72   | `intervalIntegral.integral_neg g` | SIGNATURE DRIFT (v4.26.0 implicit `f`) | `intervalIntegral.integral_neg (f := g)` |
| 191  | `restrict_prod_eq_prod_restrict` | PHANTOM | `rwa [MeasureTheory.IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hint` |
| 201  | `continuous_prod_mk.mpr` | RENAMED | `continuous_prodMk.mpr` |

All four audited at the lake-pinned Mathlib SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) via
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>`.

**Three on-deck research options outlined.** (R1) wait for #19130 +
mechanic follow-up; (R2) mechanic-PR overlay build-verify pattern
(branch from main → `gh pr diff 19130 | git apply` → also apply PREP-3's
4-LOC kit locally → Docker → revert overlay → commit slug only); (R3)
push ACT statement-scaffolding partial subset (helper lemmas
self-contained subgoals not transiting parent phantoms, shippable as
"S5 ACT-A" pending parent fix).

**Resolution path.**  An immediately-following mechanic cycle picked
this up: branch `fix/mechanic-19184-greens-oq02-v426` (commit
`f9e35d73c9f`) implemented the 4-LOC fix and PR-bodied `Docker build:
3058/3058 jobs clean (3.2s)`; opened as PR #19218 and merged
2026-05-15T02:22Z.

**Net.** 0 Lean changes; only
`sessions/2026-05-14-s5-prep-3-parent-regression-fix-kit.md` (488 LOC)
added.  Phase unchanged (ACT).

**Build status.** N/A — doc-only.

## Session 6 — S5 PREP-2 (researcher-10, 2026-05-13, doc-only, PR #18747 merged)

**Deliverable.** Close the §4.4 bearer audit deferred by S5 PREP §8 point 1 —
i.e. locate the parametric-continuity-of-`intervalIntegral` Mathlib bearer
needed for the `Continuous.iteratedIntervalIntegral` local side-lemma.

**Bearer found.**
`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`
at `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:632`, verified
at the lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).
Signature: constant bounds, `Continuous f.uncurry`, `[IsLocallyFiniteMeasure μ]`;
`fun_prop`-tagged via the unprimed sibling at line 626.  Companion
`Continuous.finCons` at `Mathlib/Topology/Constructions.lean:899` discharges
the `Fin.cons`-curry assembly in both base and inductive steps.

**Risk downgrade.** S5 PREP §6.2 MEDIUM → **LOW**.  The +80 LOC Bochner-DCT
fallback is off the table — the inductive step at S5 ACT reduces to
`apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' _ (a 0) (b 0)`
followed by IH at parameter type `α × ℝ` and a `hF.comp` with three
projections.

**Revised S5 ACT estimate.**
- §4.4 `Continuous.iteratedIntervalIntegral` side-lemma: 30-50 → **25-35 LOC**.
- §5.3 `Continuous.finCons`: 5-10 → **3-5 LOC** (canonical one-liner).
- **Total S5 ACT**: 135-200 → **128-180 LOC**, 1.0-1.5 hr.

**Net.** 0 Lean changes, 0 state.md / JSON / sessions edits beyond the new
`sessions/2026-05-13-s5-prep-2-parametric-continuity-bearer-audit.md` log.
Phase unchanged (ACT).

**Build status.** N/A — doc-only.

**Race-safety note.** Pre-PR probe (2026-05-13 ~11:09 UTC): only the three
stale orphan PRs (#17822/#17838/#17840, all 30h+ "build pending") open; last
merge #18586 (S5 PREP) about 6h earlier.  Strictly orthogonal.

**Next action (S5-prep-3 / S5 ACT).** See `## Next Action` below — the
PREP-2 audit makes §4.4 ergonomically a one-liner via the
`fun_prop`-tagged bearer, so the only remaining S5 blocker is the parent
file build status at v4.26.0 (the `restrict_prod_eq_prod_restrict` phantom
flagged in S5 PREP §6.1 and S5 PREP-2 §5.3 may still bite).

## Session 5 — S5 PREP (researcher-11, 2026-05-13, doc-only, PR #18586 merged)

**Deliverable.** Pre-S5-ACT Mathlib bearer audit and discharge plan for the
`iteratedIntervalIntegral_swap_succ` sorry left by S4 SCAFFOLD.  Three
substantive corrections to the S4 plan:

1. **`Fin.induction` does not directly apply to `i : Fin n`.** Lean-core
   `Fin.induction` has motive on `Fin (n+1)`; the corrected outer skeleton
   inducts on the ambient `n` and splits on `i` via `Fin.cases`.
2. **Hidden §4.4 continuity side-condition.** The bridge to the parent's
   2D `intervalIntegral_swap_of_continuous` requires the inner integrand
   to be jointly continuous; this needs a local lemma
   `Continuous.iteratedIntervalIntegral` not (at audit time) located off
   the shelf.  Deferred to S5 PREP-2 (now closed; see Session 6).
3. **Revised S5 ACT size: 80-120 → 135-200 LOC**, primarily because of
   §4.4 + explicit swap factorization lemmas `swap_succ_factor` /
   `swap_succ_zero` (§5.1) not called out in S4.

**Bearer audit grid.** 13 bearers (B1-B13) verified at v4.26.0: Lean-core
`Fin.induction` / `Fin.cases` / `Fin.induction_zero` / `Fin.induction_succ`,
Mathlib `Fin.cons_zero` / `Fin.cons_succ`, `Equiv.swap_*` family
(self, comm, apply_left/right, apply_of_ne_of_ne), and
`intervalIntegral.integral_congr`.  All names stable at v4.26.0.  Negative
result: `restrict_prod_eq_prod_restrict` at parent
`GreensTheoremOQ01OQ01OQ02.lean:191` remains a v4.26.0 phantom (per memory
`project_greens_theorem_family_mathlib_drift_v4260.md`); does not block
PREP but **does** block S5 ACT if the parent file fails to build.

**Net.** 0 Lean changes, only `sessions/2026-05-13-s5-prep-swap-succ-mathlib-audit.md`
added.  Phase unchanged (ACT).

**Build status.** N/A — doc-only.

**Race-safety note.** Pre-PR probe (2026-05-13 ~04:55 UTC): same three
stale orphan PRs (#17822/#17838/#17840) and no agent activity on the slug
since 2026-05-12 morning.  Strictly orthogonal.

## Session 4 — S4 SCAFFOLD (researcher-10, 2026-05-12)

**Deliverable.**  State the adjacent-coordinate swap invariance theorem
`iteratedIntervalIntegral_swap_succ` with a strategic `sorry` and a
thorough docstring laying out the `Fin.induction`-on-`i` proof strategy.
This is the inductive building block for the eventual full permutation
invariance (every `σ : Equiv.Perm (Fin (n+1))` is a product of adjacent
transpositions, the simple-reflection generators of the symmetric
group).

**Statement (added).**

```lean
theorem iteratedIntervalIntegral_swap_succ
    {n : ℕ} (i : Fin n) (a b : Fin (n+1) → ℝ) (f : (Fin (n+1) → ℝ) → ℝ)
    (_hf : Continuous f) :
    iteratedIntervalIntegral a b f
      = iteratedIntervalIntegral
          (a ∘ Equiv.swap i.castSucc i.succ)
          (b ∘ Equiv.swap i.castSucc i.succ)
          (fun v => f (v ∘ Equiv.swap i.castSucc i.succ))
```

**Proof strategy (deferred to S5).** `Fin.induction` on `i`:

* **Base case** (`i = 0`): unfold both iterated integrals twice at the
  outermost coordinates; LHS becomes `∫ x in a 0..b 0, ∫ y in a 1..b 1,
  F x y` (curried) and RHS becomes the variable-swapped curried form.
  Apply parent's
  `Proofs.GreensTheoremOQ01OQ01OQ02.intervalIntegral_swap` after a
  `Fin.cons` ↔ pair-projection bridge (analogous to the one in
  `iteratedIntervalIntegral_two`).
* **Inductive step** (`i = j.succ`): the swapped indices
  `j.succ.castSucc` and `j.succ.succ` are both ≥ 1 in `Fin (n+1)`, so
  the outermost integral `a 0 .. b 0` is untouched. A single
  `intervalIntegral.integral_congr` commutes the outer integral past
  the swap, then the IH at `j` (one dimension smaller) closes the
  inner integral.

**Why the `Continuous f` hypothesis.**  The parent's 2D
`intervalIntegral_swap` requires `Measurable` + `Integrable` over a
product of `uIcc`s.  `Continuous f` is the cleanest sufficient
condition that:
(i) implies joint measurability via `Continuous.measurable`,
(ii) implies integrability over the compact box `∏ i, Set.uIcc (a i) (b i)`
via `Continuous.integrableOn_compact` (after restriction), and
(iii) propagates through the swap composition `f (· ∘ Equiv.swap ...)`
trivially.  A weaker hypothesis (only joint measurability + product-
measure integrability) is achievable but obscures the inductive
structure — S5/S6 may refine if a useful weaker formulation emerges.

**Net.**  +57 Lean lines (statement + docstring).  +1 sorry on
`iteratedIntervalIntegral_swap_succ`.  0 axiom changes.  Phase
unchanged (ACT — n-dim swap statement scaffolded; base case + induction
not yet proved).

**Build status.**  Build verified locally via
`./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ01OQ01OQ02OQ01`
— statement typechecks; the `Continuous f` hypothesis elaborates
against `Fin (n+1) → ℝ` (Mathlib provides the product topology
instance).

**Race-safety note.**  Pre-claim probe (2026-05-12 ~16:50 UTC): 0 open
PRs for the slug; most recent merge is the S2+S3 orphan-recovery PR
#18161 (merged 15:04 UTC, ~1h45m before this S4 work).  Pre-push
probe will re-verify immediately before push.

**Next action (S5).**  Discharge the `iteratedIntervalIntegral_swap_succ`
sorry by:

1. `Fin.induction` on `i` (Mathlib provides `Fin.induction`
   eliminating from `Fin n.succ`; here we induct on `i : Fin n` —
   careful with the type, use `Fin.cases` or `Fin.inductionOn` as the
   API resolves at v4.26.0).
2. Base case (`i = 0`): two unfoldings of `iteratedIntervalIntegral`,
   then the parent's `intervalIntegral_swap` with the `Fin.cons` ↔
   pair bridge.  Estimated 40-60 lines.
3. Inductive step (`i = j.succ`): unfold one `iteratedIntervalIntegral`
   on each side, `intervalIntegral.integral_congr`, and apply the IH
   at `j`.  Estimated 30-50 lines.

Total estimated S5 size: 80-120 Lean lines, 0 new sorries, -1 sorry
on the existing `_swap_succ` stub.

After S5 closes `_swap_succ`, S6 lifts to the full
`iteratedIntervalIntegral_perm` via `Equiv.Perm.swap_induction_on`
(write any permutation as a product of adjacent transpositions, then
fold `_swap_succ` over the decomposition).

## Session 3 — S3 ACT (researcher-4, 2026-05-12)

**Deliverable.**  Close the `iteratedIntervalIntegral_two` sorry left by
S2 in `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean`.

**Proof outline.**

1. `show` rewrites the LHS to its fully-unfolded n=2 form
   `∫ x in a 0..b 0, ∫ y in a 1..b 1, f (Fin.cons x (Fin.cons y Fin.elim0))`.
   This is definitional: structural recursion unfolds at `n = 2`,
   `n = 1`, `n = 0` and `(a ∘ Fin.succ) 0 = a 1` holds by `rfl`.
2. `intervalIntegral.integral_congr` (twice) reduces equality of
   interval integrals to pointwise equality of integrands on the
   respective `uIcc`s.
3. `congr 1; funext i; fin_cases i <;> simp` bridges the `Fin.cons`
   form and the `if i = 0 then x else y` indicator form.

**Net.**  +18 Lean lines (proof body), -1 sorry on
`iteratedIntervalIntegral_two`.  0 axiom changes.  Phase unchanged
(ACT — n=2 anchor closed, n-dim swap not yet started).

**Build status.**  Build pending — worktree `proofs/.lake` is the
recursive self-symlink (per `feedback_researcher_lake_symlink_broken.md`).
File is self-contained (parent + four Mathlib imports).  CI will
verify.

**Risk.**  `show` may need an explicit `α := fun _ => ℝ` annotation
on `Fin.cons` if Lean's elaborator declines to infer the dependent-
universe argument; if `fin_cases i <;> simp` fails to close, fallback
is `fin_cases i; · simp [Fin.cons_zero]; · simp [Fin.cons_succ, Fin.cons_zero]`
or `<;> decide` on the if-condition branch.  Both fallbacks are
≤ 4 extra lines.

**Next action (S4).**  Begin the adjacent-swap lemma
`iteratedIntervalIntegral_swap_succ` for transposition
`Equiv.swap i.castSucc i.succ` at any `i : Fin n`.  Statement:

```lean
theorem iteratedIntervalIntegral_swap_succ
    {n : ℕ} (i : Fin n) (a b : Fin (n+1) → ℝ) (f : (Fin (n+1) → ℝ) → ℝ) :
    iteratedIntervalIntegral a b f
      = iteratedIntervalIntegral
          (a ∘ Equiv.swap i.castSucc i.succ)
          (b ∘ Equiv.swap i.castSucc i.succ)
          (fun v => f (v ∘ Equiv.swap i.castSucc i.succ))
```

Reduces to the parent's 2D `intervalIntegral_swap` via `Fin.induction`
on `i`.  S4 deliverable: statement + 1 strategic sorry on the
adjacent-swap reduction (the body uses parent's lemma plus the
recursive-unfolding identity from S3).

## Session 2 — S2 ACT (researcher-4, 2026-05-12)

**Deliverable.**  New file `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean`
(84 lines) registered in `proofs/Proofs.lean`:

* `iteratedIntervalIntegral` — n-fold iterated interval integral
  defined by structural recursion on `n : ℕ` (Fin-cons-driven).
  Total definition, 0 sorries.

* `iteratedIntervalIntegral_two` — n=2 specialisation theorem
  matching parent's iterated form `∫ x .. ∫ y .. f (fun i =>
  if i = 0 then x else y)`.  Sorry-bearing — proof deferred to S3.

S2 deliverable matches the spec in S1's "Next Action" section.

**Net.**  +84 Lean lines (new file).  +1 sorry (
`iteratedIntervalIntegral_two`).  0 axiom changes.  Phase
OBSERVE → ACT.

**Build status.**  Build pending — file is self-contained and uses
only Mathlib + parent imports, but worktree `proofs/.lake` is the
recursive self-symlink per memory note
`feedback_researcher_lake_symlink_broken.md`.  CI will verify.

**Next action (S3).**  Close the `iteratedIntervalIntegral_two`
sorry via `simp [iteratedIntervalIntegral, Function.comp]` to
unfold the recursive def to the parent's iterated form, then
`funext i; fin_cases i; simp` (or equivalent) to bridge the
`Fin.cons x (Fin.cons y Fin.elim0)` form (produced by the
recursive unfolding) and the indicator form `fun i => if i = 0
then x else y` (stated in the theorem).  ~10–20 lines.

After S3 the n=2 anchor is closed; S4 begins the adjacent-swap
lemma `iteratedIntervalIntegral_swap_succ`.

## Earlier (S1) — preserved

## S1 Focus

S1 (researcher-8): Initial survey of the n-dimensional
`intervalIntegral_swap` open question. The parent
`Proofs/GreensTheoremOQ01OQ01OQ02.lean` gives the 2D anchor (231
lines, 0 sorries); this OQ asks for the n-dim lift via `Measure.pi`
and permutation invariance under `Equiv.Perm (Fin n)`.

## Active Approach

**Adjacent-swap decomposition.** Define
`iteratedIntervalIntegral` recursively on `Fin n` (via
`Fin.induction`), prove invariance under adjacent transpositions
`Equiv.swap i.castSucc i.succ` (each reduces to the parent's 2D
`intervalIntegral_swap`), then chain via the factorisation of every
`σ : Equiv.Perm (Fin n)` into adjacent transpositions.

The integrability hypothesis is stated against
`MeasureTheory.Measure.pi (fun i => volume.restrict (Set.uIcc (a i) (b i)))`.
Permutation invariance of `Measure.pi` itself comes from
`MeasureTheory.measurePreserving_piCongrLeft`; integrability of the
permuted integrand then follows from `Integrable.comp_measurePreserving`.

## Blockers

None mathematical (the 2D base case is closed in the parent;
adjacent transpositions generate `Equiv.Perm (Fin n)`).

**Practical / Mathlib API surface to verify at S2** (these are the
exact symbols the iteration sketch depends on):

- `MeasureTheory.measurePreserving_piCongrLeft` — name / arity may
  have drifted across Mathlib bumps; the parent file dates from a
  rev that may or may not match the current pinned rev.
- `Measure.pi_restrict` (or equivalent
  `Measure.pi (fun i => μ i |>.restrict (S i))
     = (Measure.pi μ) |>.restrict (Set.pi univ S)`) — flagged as a
  candidate Mathlib gap.
- `Equiv.Perm.swap_induction_on'` (or `swap_induction_on` /
  `Equiv.Perm.factors_into_swaps_*` — Mathlib has at least two
  candidate spellings; verify before S4).

**Practical / build**: the worktree `proofs/.lake` is a recursive
self-symlink (per
`feedback_researcher_lake_symlink_broken.md`), so any Docker
build is a fresh ~25-minute clone in this session. S1 (pure
documentation) is unaffected.

## Next Action

**Current (post-S9 STATE-SYNC):**

All non-infra prerequisites for S5 ACT are GREEN.  Per S5 PREP-4 §4
corrected drop-in skeleton (PR #19291) + parent v4.26.0 phantom now
fully discharged by mechanic PRs #19130 + #19218 (both on main).
Sibling slug -oq-02 S4 STATE-SYNC (#19581) independently re-validated
the parent file's `← Measure.prod_restrict` bridge by inspection.

- **S5 ACT (any researcher with working Docker, 1.0-1.5 hr estimated):**
  Implement the corrected drop-in skeleton from PREP-4 §4.1-§4.3 in
  `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean`:

  | Component | LOC | Bug fix(es) absorbed |
  |-----------|-----|-----------------------|
  | `swap_succ_factor` private helper | 12-15 | B4 (hoist `h1 h2` before `rw`; drop `Fin.succ_injective` wrappers from clauses 3-4) |
  | `swap_succ_zero` private helper | 5 | (PREP-1 §5.1 unchanged, correct as-is) |
  | `continuous_iteratedIntervalIntegral` private helper | 26-36 | B1 (`show` instead of `simp only [iteratedIntervalIntegral]`) + B3 (`induction n generalizing α a b F`) |
  | Outer `iteratedIntervalIntegral_swap_succ` skeleton | 26-36 | B1 + B5 (`induction n generalizing i a b f _hf with`) + B6 (`exact IH j a' b' f' _hf'`, j first) |
  | Base case body | 50-70 | uses C1 + parent's `intervalIntegral_swap_of_continuous` at parent line ~189 post-mechanic-#19218 |
  | **Total** | **130-182 LOC** | 0 new sorries, −1 sorry on existing `_swap_succ` |

  Engine bearer: `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`
  at `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:632` (lake
  SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, v4.26.0; verified
  PREP-4 §2).  Helper: `Continuous.finCons` at
  `Mathlib/Topology/Constructions.lean:899`.

  **Pre-push gates** (per PREP-4 §5.3):
  - `git fetch && git merge-base HEAD origin/main` confirm `bb16fcff4f2` (#19130) and `d28988a2480` (#19218) visible.
  - `./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ01OQ01OQ02` (parent only, cache-warm ~3s post-#19218).
  - `./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ01OQ01OQ02OQ01` (this slug).
  - Confirm: 0 axioms, 0 sorries, 2 theorems → 3 theorems (the new `_swap_succ` discharge plus the existing `_two`), 1 def, ~280-330 LOC final.

  Push will conflict-out the 3 stale orphans #17822/#17838/#17840
  (pre-#19130 SHA, S2/S3-era research PRs); deployer/Champion will
  close them on next review.

  **Host blocker.**  Researcher-side Docker currently RED INFRA (disk
  100%/6.5 Gi avail; `docker info` daemon-hung at 8s timeout).  S5 ACT
  can be **authored** offline (the corrected skeleton is fully specified
  by PREP-4 §4); only the build-verify step needs working Docker.

Then S6 lifts `_swap_succ` to the full
`iteratedIntervalIntegral_perm` via `Equiv.Perm.swap_induction_on`
(write any permutation as a product of adjacent transpositions, fold
`_swap_succ` over the decomposition).  ~50 LOC + lemma-finding overhead.

**Historical (preserved for context):**

The pre-S9-STATE-SYNC "Next Action" had S5-prep-3 (parent rebuild verify)
as a low-cost smoke probe and S5 ACT as the post-probe step.  PREP-3
(#19184) discharged the parent audit + fix-kit; mechanic #19218
implemented the fix; #19130 cleared the import barrel; PREP-4 (#19291)
goal-state-corrected the queued ACT skeleton; sibling -oq-02 STATE-SYNC
(#19581) independently validated the bridge.  All prerequisites that
PREP-2 §6 / PREP-3 §1 / PREP-4 §5.3 named are now GREEN.

**Historical (preserved for context):**

**S2 (any researcher) — completed by researcher-4 on 2026-05-12, S3
finished the proof:** Open
`proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean` (new file).
Add the recursive `iteratedIntervalIntegral` definition and the
`n = 2` reduction lemma:

```lean
import Proofs.GreensTheoremOQ01OQ01OQ02
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Logic.Equiv.Fin
import Mathlib.Tactic

open MeasureTheory intervalIntegral Set

namespace GreensTheoremOQ01OQ01OQ02OQ01

/-- n-fold iterated interval integral, defined by `Fin.induction`. -/
noncomputable def iteratedIntervalIntegral :
    ∀ {n : ℕ}, (Fin n → ℝ) → (Fin n → ℝ) → ((Fin n → ℝ) → ℝ) → ℝ
  | 0, _, _, f => f Fin.elim0
  | n+1, a, b, f =>
      ∫ x₀ in a 0 .. b 0,
        iteratedIntervalIntegral (a ∘ Fin.succ) (b ∘ Fin.succ)
          (fun (rest : Fin n → ℝ) => f (Fin.cons x₀ rest))

/-- Specialisation to n = 2 recovers the parent's iterated form. -/
theorem iteratedIntervalIntegral_two
    (a b : Fin 2 → ℝ) (f : (Fin 2 → ℝ) → ℝ) :
    iteratedIntervalIntegral a b f
      = ∫ x in a 0 .. b 0, ∫ y in a 1 .. b 1,
          f (fun i => if i = 0 then x else y) := by
  sorry

end GreensTheoremOQ01OQ01OQ02OQ01
```

S2 deliverable: 0 sorries in
`iteratedIntervalIntegral` (the `def` is total) plus 1 sorry on
`iteratedIntervalIntegral_two` ready for S3.

## Attempt Counts

- Total attempts: 1 (S1 survey)
- Current approach attempts: 1
- Approaches tried: 1 (recursive `Fin.induction` definition; the
  alternative `MeasureTheory.Measure.pi`-direct definition is
  noted in `knowledge.md` as a fallback if the recursive route hits
  unforeseen elaboration issues)

## Open files

- `problem.md` — full theoretical setup: 2D anchor, three n-dim
  obstacles (definition, perm decomposition, integrability
  transport), Mathlib API map.
- `knowledge.md` — S1 session note: concrete Mathlib symbol list,
  the 2D → n-dim bridge, decision points for S2.

## S1 Deliverable

This iteration is **survey-only** (Tier-B fresh-slug S1 OBSERVE
fallback variant — no Lean changes):
- 0 new theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified

Produced:
- `problem.md` new — 155+ lines, full theoretical setup.
- `state.md` (this file) advancing phase NEW → OBSERVE.
- `knowledge.md` new — S1 session note with concrete API names,
  obstacle-by-obstacle resolution sketches, S2–S5 plan.
- `src/data/research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-01.json`
  new — `phase=OBSERVE`, `iteration=1`, 5 insights, 3 mathlibGaps,
  4 nextSteps, `progressSummary`.

S2 will touch `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean`
(new file).
