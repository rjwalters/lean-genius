# GOAL: Complete Epic #37508 — Lean v4.26.0 → v4.31.0 toolchain + Mathlib migration

**Standing objective** (set by operator 2026-07-13): drive epic #37508 to full completion.
The lean-genius agent fleet is intentionally OFF while this goal is active; work is driven
by orchestrator sessions dispatching workers directly.

## Completion criteria (epic closes when all true)

- [ ] #38065 closed — residual failure ledger burned down (safe subset green at v4.31)
- [ ] #38066 closed — pins flipped on `main` (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`,
      `Dockerfile` ×2 lines, `docker-build.sh` IMAGE), volumes refreshed, CI image retagged;
      0 lingering v4.26.0 refs in build config
- [ ] #38067 closed — `mathlib_version` swept across ~3,508 `src/data/proofs/*/meta.json` + pnpm build green
- [ ] #37508 closed — epic dashboard updated, unlocks #37507 (CDC port)

## Operator decisions

- **Aristotle gate (b) of #38066 is RE-SCOPED, not blocking**: do NOT wait for the Aristotle
  backend to support v4.31. Translate to/from Aristotle's pinned Lean version (currently v4.28)
  at the submission/integration boundary as needed — they will eventually update. Post-flip,
  Aristotle outputs get drift-repaired on integration (rename map in
  `research/toolchain-v4.31-rename-map.md` is the starting point).
- Disk headroom must be re-verified immediately before the #38066 volume refresh (~10GB cold refill;
  host has B2/ENOSPC history).
- **Wrapper volume hazard (found during increment-4 salvage)**: `proofs/scripts/docker-build.sh`
  hardcodes the shared v4.26 volumes (`lean-mathlib-cache`/`lean-mathlib-packages`). Running it on
  the v4.31 branch cross-contaminates the fleet-wide v4.26 cache. Migration verification MUST use
  the containerized recipe in `proofs/batch2/STATUS.md` (dedicated `lean-mathlib-{packages,cache}-v431`
  volumes, runner4.sh, --memory 11g). The wrapper needs v431-volume awareness as part of the
  #38066 infra flip.

## State at goal creation (2026-07-13)

- Branch: `feature/issue-37508` (long-lived migration branch; keep rebased/merged vs `main`)
- Ledger: `proofs/batch2/verify-results.tsv` — 724 GREEN / 1,911 RESIDUAL / 24 PRE-EXISTING
  after increment 4 (PR #38596, merged 2026-07-13; ledger hygiene + DR14 salvage, +5 GREEN)
  (of 2,659-fail baseline in `proofs/spike-logs-full/results-full.tsv`)
- Increments so far: #38384 (+190→484), #38396 (+167→651), #38559 (+68→719), #38596 (+5→724),
  #38599 inc-5B proof-drift (+81→805), #38600 inc-5A type-mismatch (+189+addl reverify → 1048).
  #38602 inc-6 instance-synth (+44, cyclotomic root cause = demote DivisionRing.toRatAlgebra),
  #38601 inc-7 type-mismatch+proof-drift remainder (+122). As of 07-13 ~12:05 PT:
  **1206 GREEN / 1429 RESIDUAL / 24 PRE-EXISTING** (55% of the 2,635 fixable baseline done).
  Continued 07-13 PM: #38603 inc-8 unknown-const (+24→1230), #38604 inc-9 rewrite-drift
  (+34→1264). As of ~13:35 PT: **1264 GREEN / 1371 RESIDUAL** (48% of fixable remaining;
  unknown-const bucket found to be ~230/323 MIXED rows really belonging to tm/pd passes).
  NOTE: hitting monthly-spend-limit deaths now (not just session limits) — a /login clears
  session limits but NOT a monthly spend cap (raise at claude.ai/settings/usage). The
  14-agent internal fan-out dies on spend-limit; central-fixing fallback is reliable.
  #38605 inc-10 tm/pd+mixed (+27→1291). As of ~14:10 PT: **1291 GREEN / 1344 RESIDUAL**
  (49% of fixable remaining). Residual: unknown-const 320 (~mixed), instance-synth 224,
  type-mismatch 223, proof-drift 222, rewrite-drift 101, parse-error 79, signature-drift 44,
  elab-drift 44, dot-notation 30, decide-maxrecdepth 13, unclassified 10, noncomputable 9,
  duplicate-decl 8. Deep-rework tail known: Ballot ncard_biUnion, partenat/ℕ∞, 3 cyclotomic
  compositum-tower rows.
- Continued 07-13 PM round 2: #38606 inc-12 parse/sig/elab/dot (+26→1317), #38608 inc-11
  instance-synth (+46→1363). As of ~15:05 PT: **1363 GREEN / 1272 RESIDUAL** (52% done, 48%
  of fixable remaining). instance-synth now 178 (deeper cascades). Meta-finding across all
  increments: a zero-edit re-verify flips ~0 (dep-backfill already ran); every GREEN needs
  real per-file fixes now. Hook friction fully resolved (#38597/#38598/#38607) — force ops,
  docker lifecycle, and /Volumes rm all prompt-free on working branches.
  Parallel pattern works: 2 agents on disjoint failure classes, cpus 0-5 vs 6-11, separate
  build-cache volumes (lean-mathlib-cache-v431 / -v431-b), shared packages volume (no lock
  contention). Ledger conflicts on concurrent branches resolve by 3-way row-union keeping both
  sides' GREEN flips (rows are disjoint → 0 contradictions).
- Residual class breakdown (07-13 12:05): unknown-const 347 (long tail, mostly singletons),
  proof-drift 246, instance-synth 224, type-mismatch 223, rewrite-drift 135, parse-error 79,
  signature-drift 44, elab-drift 44, dot-notation 30, decide-maxrecdepth 13, unclassified 10,
  noncomputable 9, duplicate-decl 8.
- **Operator decision (07-13): FIX mathematically false statements when found.** Correct the
  statement to the intended-true form (add the missing hypothesis / fix the edge case — e.g.
  exclude n=0, add nontriviality), never weaken to vacuous truth and never `sorry`/axiomatize.
  Note each statement repair in the commit message and STATUS.md so the gallery meta can be
  re-checked. Applies to the 4 flagged files: Erdos820Aristotle (`gcd_ge_two_of_ne_one`),
  Erdos469Problem (`not_pseudoperfect_0`), Erdos1155OQ01 (`f_small_values_bound` conjunct 2),
  Erdos1156Problem (`isKColorable_zero_iff` mpr) — and any future finds.
- Doctor increments continue from a fresh `feature/issue-38065` branch reset onto
  `origin/feature/issue-37508`, family-clusters-first per `proofs/batch2/STATUS.md`.

## MECHANICAL PHASE COMPLETE (2026-07-14 ~17:50 PT)

Base `feature/issue-37508`: **1904 GREEN / 731 RESIDUAL / 24 never-compiled (exempt)**.
Started 07-13 at 719 GREEN → +1185 over ~2 days across 49 Doctor increments.
**Both partition seams (A–M, N–Z) DECLARED DRY** by increments 47/48/49: <5–10% of remaining
residuals are mechanical/catalog-fixable; each further green now requires real proof surgery,
not a rename. Rename catalog: research/toolchain-v4.31-rename-map.md (~45 families, §7a–§7ae).

Remaining 731 residual composition: deep-rework (#38612: Ballot/condCount, Sylow clusters,
cyclotomic towers, partenat/ℕ∞, GeneralizeProofs), OOM files (Wolstenholme, TestApi203),
100+-error rewrites (TriangleAngleSumOQ02, PoincareConjecture, PNPBarriersLegacy),
dependency-blocked files, and **files whose ORIGINAL statements are unsound** (only compiled by
luck pre-4.31: Erdos1123/1112/1125/724, TestApi241, BertrandsPostulate exponent ineq) — logged
to #38611. ~40+ genuine statement repairs made during the burn-down (real math errors the
stricter toolchain exposed).

**DECISION MADE (operator, 2026-07-14): OPTION (b) — keep grinding the tail.**
Continue processing the full residual tail to green even though it's slow; do NOT flip the
#38066 infra pins yet. The loop should NOT keep re-asking the flip question — the decision is
settled. Deep-rework phase: dispatch Doctor increments at coherent clusters (partenat/ℕ∞,
GeneralizeProofs, Sylow-API, SchroederBernstein concrete-category) + statement-repair files
(fix unsound originals to intended-true, log #38611). Infra flip (#38066) remains gated on a
SEPARATE explicit operator go-ahead, to be raised only once the tail is genuinely exhausted
(residual ≈ just OOM + never-compiled exempt), not before.

(Superseded option a, for reference: narrow safe-subset excluding #38612, flip #38066 pins on
main, unblock #38067/#37507 — deferred by operator choice.)

**FRAMING CORRECTION (operator, 2026-07-14):** a file green on the OLD pin means the theorem
is true and a proof existed — v4.31 changed how the proof is SPELLED, not whether it's
provable. So "deep-rework"/"stuck" was wrong; the honest word is EXPENSIVE (many surface-drift
sites per file), not impossible. Every one of the ~700 residual that were green before is
PORTABLE with enough per-file effort — the tail is finishable, just throughput-bound (slow
under the ~25-min session throttle). Agents must NOT skip a file as "impossible" just because
it has 10+ errors — treat it as budget-permitting, keep going. THREE genuine exceptions where
"we proved it before" does NOT hold: (1) unsound-original files whose old green exploited a bug
(Erdos1196 Dvd.dvd.symm, Erdos1123 fake trivial, TestApi241 false Sidon) — NOT valid proofs;
v4.31 correctly rejects them; fix statement+proof to genuinely-true (the #38611 work, mostly
done). (2) native_decide/noncomputable-SetLike cases (SylowTheoremOQ04) — theorem provable but
the cheap "compute it" proof is gone; needs a real argument. (3) the 24 never-compiled rows —
never proven even on v4.26; exempt.

## SESSION HANDOFF (2026-07-14, updated ~21:30 PT) — deep-rework in progress

**State:** base `feature/issue-37508` = **1992 GREEN / 643 RESIDUAL / 24 never-compiled exempt**
after inc-56 (PR #38659, +30, A), inc-57 (PR #38660, +18, B), inc-58 (PR #38661, +9, A),
inc-59 (PR #38662, +5, B) all merged. +62 this session. inc-58/59 died on Fable-5 usage
credits mid-run but push-after-every-file saved all flips (PRs opened early at +3, undercounted;
merging the branch pulled every pushed commit). Ledger row-unions all auto-merged clean
(A vs B partitions disjoint — no hand-merge of tsv). Switched to Opus 4.8 to escape the Fable
credit pool. Statement repairs logged to #38611: Erdos428 (inc-58) added to prior Erdos490Ari/
Erdos323/Erdos296/Erdos1157(×2)/Erdos623.

**Continued on Opus 4.8:** inc-60 (PR #38664, +4, A) merged → base **1996 GREEN / 639 RESIDUAL**.
inc-60 KEY FINDING: partition A cheap single-blocker rows are HARVESTED — the `unknown-const:X`
ledger class is only the FIRST error; every remaining file has 5–33 real errors, ~0 free flips
left. Deep-rework is now the norm; ~+4/increment is a good rate. New seams: FDeriv-API family
(`HasFDerivAt.prod`→`.prodMk`, `.comp_hasDerivAt` now 3-arg, `hasFDerivAt_const (v) (pt)`),
`Set.Finite.of_not_infinite`→`Set.not_infinite`, `gcongr with <name>`.

**07-15 continued (Opus):** inc-61 (PR #38663, +8, B → crossed 2000 GREEN), inc-62 (PR #38665,
+5, A) merged → base **2009 GREEN / 626 RESIDUAL**. inc-61/62 ledger conflicts resolved by
STATUS.md marker-strip (keep both records) + tsv auto-merge (A/B disjoint). Both partitions
now confirmed 0 free-flips (deep-rework everywhere). Statement repairs to #38611 now: Erdos428,
Erdos129(×2), plus candidates Erdos807/823/133 flagged. New seams cataloged §7ah (∀ᶠ binder
pin, Nat.find atom, abbrev-for-Membership, congrArg(·i) for EuclideanSpace, List.Sorted→Pairwise,
Classical-instance-for-Nat.find, rpow root delisting, greedy-by, theorem-Prop→def).

**07-15 mid-session tally (Opus, two-lane pipeline steady state):** incs 63 (+6,B), 64 (+6,A),
65 (+6,B) all merged → base **2027 GREEN / 608 RESIDUAL**. +97 this session (1930→2027, incs
56–65). Statement repairs to #38611 now 11 total (Erdos428/129×2/823/850/133 + earlier
490Ari/323/296/1157×2/623/1059); GALLERY FLAG logged to #38611: CevasTheoremOQ01.routhRatio
denominator is math-wrong (routh_theorem_std genuinely FALSE, dependents only pass at symmetric
point) — separate follow-up task, NOT a mechanical migration fix, agents told to skip it. More
seams §7ai (λ reserved keyword; Finset.product↛mem_product simp; decide can't pierce opaque
Prop-field; open-scoped-Classical shadows computable Decidable; auto-bound vars drop variable
instance-binders; ℝ≥0∞ scoped notation; inv_ne_zero implication; PiLp._apply for EuclideanSpace).
~+12/round two-lane; long grind, self-sustaining, push-after-every-file caps death cost at a partial wave.

**CLEAN RESUME POINT (07-15, ~account-throttle wall):** base `feature/issue-37508` =
**2028 GREEN / 607 RESIDUAL / 24 exempt** (+98 this session over incs 56–66). inc-66 salvaged
(+1 Erdos598Problem — universe pin + Cardinal.lift; PR #38669 merged). inc-67 died in setup with
0 pushed (no branch, nothing lost). BOTH worktrees clean, no containers, no in-flight agents.
BLOCKER: account session limit hit (resets 1:50am PT) — subagents die during setup reads, ~0
inference headroom. To resume the two-lane grind: `/login` rotates to a fresh account (13
available) OR wait for the reset, then re-dispatch inc-67 (partition B, .loom/worktrees/issue-38065,
cpus 0-5) + inc-68 (partition A, /Volumes/Stripe/lean-genius/doctor-b, cpus 6-11), both fresh off
origin/feature/issue-37508. Deferred warm leads for the next wave: partition B = PartitionTheoremOQ01
(3000-line, subsetsWithSum dup-decl), Erdos1067/910 (Cardinal toPartENat/continuum), Sylow-API /
SchroederBernstein / ThreeSubgroupsLemma-lowerCentralSeries / partenat-ℕ∞ clusters; partition A =
Erdos560/461/153/483, ErdosKoRado-family, Amgm…OQ03, Bezout…Transitive, CantorDiag…Incomplete01.
Merge protocol: STATUS.md marker-strip (keep both increment records) + tsv row-union auto-merges
(A/B partitions disjoint). NEVER hand-merge an auto-merged tsv.

**07-15 post-rotation (account /login cleared the wall):** incs 67 (+9,B), 68 (+4,A) merged →
base **2041 GREEN / 594 RESIDUAL**. +111 this session (1930→2041, incs 56–68). Cleared 3 orphaned
containers (dr58/dr59 up 10h from the Fable deaths) before relaunch. Statement repairs to #38611
now 12 (added FeuerbachsTheoremOQ05 sign error N−F=+(R/r)(I−F) not −). Seams through §7aj
(interval_cases can't bound from x∣N; open-scoped-Classical shadows decide; decide refuses
have-bound free vars→lift to def; Finset.mul_sum orientation flip; convert-HasDerivAt junk goals;
dot-notation exact-namespace _root_ fix; lost-import→Function-expected; ring_nf reindexes sums;
tendsto_arctan→nhdsWithin; λ reserved keyword). In flight: inc-69 (B, cpus 0-5) + inc-70 (A,
cpus 6-11). NOTE for next wave: BezoutIdentityOQ01OQ02OQ02Transitive may be a never-green (its own
docstring says never machine-checked) — candidate to reclass RESIDUAL→PRE-EXISTING, not force green.

## 4-LANE SCALE-UP (2026-07-15, operator: "run more agents in parallel")

Scaled the proven two-lane grind to **FOUR parallel Doctor lanes** on the 28-CPU/96GB host.
Infra: seeded 2 new 21GB cache volumes (`lean-mathlib-cache-v431-c/-d`) from the warm v431 via
`docker run --rm -v v431:/from -v v431-c:/to alpine cp -a /from/. /to/`; 4 worktrees, disjoint
CPU sets, shared packages volume. Partition rule (disjoint, sum=RESIDUAL): L1 Erdos<500 (cpus 0-5,
cache v431, wt .loom/worktrees/issue-38065) · L2 Erdos≥500 (6-11, v431-b, doctor-b) · L3 non-Erdos
A–K (12-17, v431-c, doctor-c) · L4 non-Erdos L–Z (18-23, v431-d, doctor-d). Merge protocol per wave:
git auto-merges verify-results.tsv (disjoint rows); STATUS.md conflicts resolve by STRIPPING the 3
conflict markers (keep both increment records). Merge each PR via
`~/GitHub/loom/defaults/scripts/merge-pr.sh <PR>` (gh pr merge is hook-blocked; script false-negs
post-merge verify → confirm with `gh pr view --json state`).

**Wave 1 (incs 73–76, all merged): +13 → base 2075 GREEN / 558 RESIDUAL / 25 PRE-EXISTING.**
PRs #38677(+4 Erdos367/411/281/471) #38676(+3 Erdos1006/1018Ari/552) #38679(+3 ArithmeticSeries…/
Hierholzer/FourColorOQ01) #38678(+3 LawsOfLargeNumbersOQ03/+Ari/PartitionThmOQ03). Statement repairs
to #38611: Erdos552 cycleGraph (missing i≠j, self-loop at n=1), FourColorOQ01 min_counterexample
(missing minDeg≤avgDeg hyp). Confirmed CevasTheoremOQ01.routhRatio is a real parent-def bug
(signedArea 1/10 vs routhRatio 25/252 at (1/2,1/3,1/4)) — skip, #38611 follow-up.
**Wave 2 (incs 77–80) IN FLIGHT.** Big seams found wave 1: PreErgodic/Ergodic field reshape,
`Nat.factorization_prime`→`Nat.Prime.factorization`, Euler-partition Archive→mainline,
`PowerSeries.coeff` ring-arg implicit, forward-reference reordering, `open scoped Classical` for
Finset.filter decidability, root-decl-vs-`_root_` collision→namespace-wrap, minimal-import
`⌈⌉` lex failure→`import Mathlib.Data.Real.Archimedean`. KEY: many "1-error" rows are
GREEN-parent-olean-missing cascades — build the parent's olean first to unmask real child drift.

## PAUSE POINT (2026-07-15, operator asked to pause) — superseded by 4-lane scale-up above

**State:** base `feature/issue-37508` = **2063 GREEN / 571 RESIDUAL / 25 PRE-EXISTING (exempt)**.
+133 this session (1930→2063 over incs 56–72, 17 increments). No containers running, BOTH doctor
worktrees clean (/Volumes/Stripe/lean-genius/doctor-b + .loom/worktrees/issue-38065), no in-flight
agents, no open increment PRs — everything merged.

**Erdos608Problem reclassified RESIDUAL→PRE-EXISTING** (inc-71): invalid `O(1)` statement syntax +
`sorry` body, FAIL on v4.26 baseline — never compiled on any toolchain. That's why PRE-EXISTING
went 24→25. BezoutIdentity…Transitive still pending the same never-green check.

**Statement/reference repairs to #38611 now 13+**: Erdos428/129×2/823/850/133/FeuerbachOQ05 +
WilsonOQ02ExtOQ02 dangling-ref (miller_prod) + earlier 490Ari/323/296/1157×2/623/1059. Plus the
CevasTheoremOQ01.routhRatio GALLERY bug (separate #38611 follow-up, agents told to skip).

**To resume the two-lane grind:** re-dispatch inc-73 (partition B = N–Z + Erdos≥600,
.loom/worktrees/issue-38065, cpus 0-5, cache lean-mathlib-cache-v431) + inc-74 (partition A = A–M +
Erdos<600, /Volumes/Stripe/lean-genius/doctor-b, cpus 6-11, cache -v431-b), both fresh off
origin/feature/issue-37508. Deferred warm leads:
  - Partition B: Erdos1131 (26-err long grind), SylowTheoremOQ04 (native_decide×noncomputable — use
    upstream-axiom-if-defeq trick like inc-70 Erdos483, else defer), Erdos1067/910 (Cardinal
    toPartENat/continuum + universe .{0}), PartitionTheoremOQ01 (3000-line subsetsWithSum dup-decl),
    SchroederBernstein / ThreeSubgroupsLemma-lowerCentralSeries(39) / partenat-ℕ∞ clusters.
  - Partition A: Erdos367 (14, forward-refs + factorization_prime), Erdos411 (8, forward-refs + 2
    maxHeartbeats bumps), Erdos358(14)/Erdos201(29), Erdos560/153, ErdosKoRado-family, DeMoivreOQ02OQ02
    (implicit-R refactor), LagrangeFourSquaresOQ01OQ03 (native_decide catch-22), CantorDiag…Incomplete01
    (genuine universe-design mismatch), BezoutIdentity…Transitive (never-green check).
Seam catalog now through §7al. Merge protocol unchanged: STATUS.md marker-strip (keep both records) +
tsv row-union auto-merges (A/B disjoint); NEVER hand-merge an auto-merged tsv. Partition rule is now Erdos-number-aware
(Erdos<600 → A, ≥600 → B) since most residuals are Erdos files. Phase: DEEP-REWORK
(mechanical seam dry). Decision: OPTION (b) grind the tail, NO infra flip, don't re-ask
(see above + memory epic-37508-tail-decision). Inc-56 logged 3 statement repairs to #38611
(Erdos490ProblemAristotle missing 0<a₂ hyp; Erdos323 ℚ-rpow respell; Erdos296 witness repair)
and new seams (forward-reference harvest, Basis→Module.Basis, List.Chain'→IsChain,
diff→sdiff family, omega structure-field blindness) — details in STATUS.md inc-56 record.

**To resume next session:** re-run the /loop with the deep-rework prompt. Dispatch pattern that
works: 2 parallel Doctor agents on disjoint partitions (A–M/Erdos<600 on cpus 6-11 via
/Volumes/Stripe/lean-genius/doctor-b; N–Z/Erdos≥600 on cpus 0-5 via .loom/worktrees/issue-38065),
UNIQUE branch name per increment (feature/issue-38065-inc<N>), per-file work, PR-early (~+4-8 or
~20 min — sessions throttle to ~25-30 min), push after every file. Merge via GitHub layer only
(never git-op a live worktree). Ledger conflicts: scratchpad/merge-ledger.py (skips tsv when
git auto-merged — do NOT hand-merge an auto-merged tsv, that corrupted it once on 07-13).

**Yielding sub-seams (deep-rework, ~+7-13/increment):** local-`def`-shadows-Mathlib rename;
Archive→mainline lemma relocation (`condCount`→`uniformOn`, `Theorems100.*`→mainline);
Type-valued-`theorem`→`def`; `deriving DecidableEq`→`noncomputable instance Classical.decEq`;
`termination_by`/`Nat.log_lt_self`; missing project-namespace import; free-greens as deps clear;
partenat/emultiplicity where the PARENT is already green; statement repairs (fix unsound
originals to intended-true, log #38611). Full rename catalog: research/toolchain-v4.31-rename-map.md
(§7a–§7af). Per-increment recipes: proofs/batch2/STATUS.md.

**Genuine exceptions (NOT plain renames):** unsound-original files (old green exploited a bug —
fix statement+proof to genuinely-true); native_decide/noncomputable-SetLike/orderOf (theorem
provable but the compute-proof is gone, needs a real argument); 24 never-compiled (exempt, never
proved even on v4.26). Everything else that was green before IS provable/portable, just expensive.

**Account throttle reality:** we exhausted one account's weekly budget in ~1 day of 2-agent
operation; sessions now throttle to ~25 min. `/login` rotates to a fresh account (13 available).
Push-after-every-file means a limit-death costs at most a partial wave. On death: salvage the
branch delta via a follow-up PR (branch is safe on origin because of unique names).

## Follow-on issues (filed 2026-07-13)

- **#38611** — post-migration gallery-metadata re-audit for the ~30 statement-repaired
  entries (genuine math errors v4.31 caught: wrong arithmetic on display, the Erdos1196
  `Dvd.dvd.symm` soundness hole, missing-hypothesis/degenerate fixes). NOT covered by
  #38067 (which is only the `mathlib_version` field). Sequenced after #38065.
- **#38612** — deep-rework residual clusters deferred by increments (Ballot ncard_biUnion,
  partenat/ℕ∞, ThreeSubgroupsLemma 39-site lowerCentralSeries, GeneralizeProofs reimpls,
  3 cyclotomic compositum-tower rows, 24 never-compiled PRE-EXISTING). Long tail of #38065.

## Working loop

1. Salvage/land any in-flight increment (worktree above → PR to `feature/issue-37508`).
2. Dispatch Doctor increments against the RESIDUAL ledger (family-clusters-first per
   `proofs/batch2/STATUS.md` routing), verify GREEN claims in Docker
   (`./proofs/scripts/docker-build.sh`, NEVER bare `lake build`), merge increments.
3. Repeat until RESIDUAL ≈ 0 (24 PRE-EXISTING never-compiled files are exempt).
4. Execute #38066 infra flip (disk check first; Aristotle gate re-scoped per above).
5. Execute #38067 metadata sweep; verify `pnpm build`.
6. Update + close #37508; note #37507 unblocked.

Progress notes for cross-session continuity go in issue comments on #38065/#37508.
