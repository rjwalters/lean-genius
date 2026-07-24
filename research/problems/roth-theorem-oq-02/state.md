# Current State — roth-theorem-oq-02

> **S9 JOINT ACT: S6-a + S6-d SHIPPED — PREP CACHE DRAINED (researcher-1,
> 2026-07-24).** Docker recovered, so the 2026-06-13 BLACKOUT blocker is
> cleared and both queued paste-ready ACTs landed in one session (per S6
> PREP §17's joint-ACT recommendation). `RothTheoremOQ02.lean` 351 → 574
> LOC (+223): **S6-a** `analytic_envelope_bloom_sisask` (def) +
> `bloom_sisask_analytic_envelope_conditional` (B–S dominates Behrend
> under `blasiConst ≤ 2e − 1`; verbatim from S6 PREP §10/§11, only the
> predicted `lt_of_lt_of_lt` → `.trans` micro-fix needed — the v4.26 PREP
> survived the v4.31 migration intact); **S6-d**
> `kelley_meka_envelope_le_bloom_sisask_envelope_conditional` (K–M
> envelope ≤ B–S envelope given `0 < C₁ ≤ kelleyMekaConst`,
> `blasiConst ≤ C₂`, and threshold `(log N)^{1/12} ≥ ((1+C₂)/C₁)·log log N`
> — S6c PREP §4's sorry discharged) + corollary
> `min_blasi_kelley_meka_eq_kelley_meka_eventually` (the joint min
> envelope collapses to its K–M term past the threshold). Counts: 12 thm /
> 4 def / **2 axioms (unchanged)** / **0 sorries (unchanged)**. Host
> `lake env lean` exit 0; `#print axioms` = foundational + the 2 declared
> axioms only; Docker `Built Proofs.RothTheoremOQ02` (2495 jobs) exit 0.
> **All paste-ready work is now exhausted** — remaining next steps are
> multi-quarter only (S4-b BohrSet scaffold / LeanAPAP reuse). v4.31
> gotchas recorded in
> `sessions/2026-07-24-s6a-s6d-act-envelopes.md`: `field_simp` closes the
> `C₁`-cancel goal fully (drop the trailing `ring`), and
> `rw [Real.rpow_def_of_pos]` grabs the *LHS* `(log N)^{1/12}` occurrence
> first — prove the RHS bridge as a standalone `have` instead.

> **S8 STATE-SYNC + BLOCKED (researcher-1, 2026-06-13).** Populated the **empty**
> research-JSON `leanFiles` with the actual file `RothTheoremOQ02.lean` at
> canonical origin/main counts (351 LOC / 9 thm / 3 def / 0 sorry / 2 axioms).
> Set `status: blocked`: the next step S6-a ACT (paste the verbatim Bloom–Sisask
> `bloom_sisask_analytic_envelope_conditional` discharge, ~50–60 LOC, paste-ready
> per S6 PREP #18685 §3) is build-dependent and unbuildable under the 2026-06-13
> verification blackout (Docker hung + Aristotle 404). Flagged to stop depth-first
> re-claim churn on this RICH (score 34) slug until Docker recovers; the recipe is
> queued, not abandoned. S5-a just shipped (#22769, Docker clean). No Lean touched.

**Phase**: ACT (S9 joint S6-a + S6-d shipped 2026-07-24 — PREP cache drained; only multi-quarter S4-b remains)
**Since**: 2026-05-13T01:10:00.000Z (S4-a ACT, researcher-4)
**Iteration**: 11 (S1 + S2 + S3-B + S4-a + S5 + S5b + S6 + S6c + S7 + S5-a + S8 + this S9 joint ACT)
**Researcher**: researcher-1 (S8 + this S9 joint ACT); researcher-6 (S5b + S7 STATE-SYNC + S5-a ACT); researcher-5 (S5); researcher-11 (S1 + S6); researcher-12 (S2 + S6c); researcher-3 (S3); researcher-4 (S4-a)
**Mode**: S9 joint ACT (Docker-verified paste-in of S6 PREP B–S envelope + discharge of S6c PREP head-to-head skeleton)

## Current Focus (S5-a ACT 2026-06-10)

**Author:** researcher-6, claim `researcher-23844`.
**Mode:** ACT — paste-in + Docker verification.

### What this PR ships

`proofs/Proofs/RothTheoremOQ02.lean`: 236 → 350 LOC (+114).

- **+2 imports**: `Mathlib.Analysis.SpecialFunctions.Pow.Real` (for `Real.rpow_*`, `Real.sqrt_eq_rpow`) and `Mathlib.Analysis.Complex.ExponentialBounds` (for `Real.exp_one_lt_d9`).
- **+1 def**: `analytic_envelope_kelley_meka (N : ℕ) : Prop` records the bare envelope inequality `N * exp(-4 * √(log N)) ≤ N * exp(-kelleyMekaConst * (log N)^(1/12))` as a `Prop`-valued function. Unprovable unconditionally (`Exists.choose` of unbounded existential).
- **+1 theorem**: `analytic_envelope_conditional (N : ℕ) (hN : 3 ≤ N) (hKM_bound : kelleyMekaConst ≤ 4 * (Real.log 3)^(5/12))` proves the negated-exponent inequality `-(4) * √(log N) ≤ -kelleyMekaConst * (log N)^(1/12)`. Verbatim composition of 11 Mathlib lemmas closed by `linarith`. ~50 LOC body.
- **+1 section docstring** at L262-284 explaining why the conditional analytic envelope is *strictly stronger* than the existing transitive `kelley_meka_consistent_with_Behrend`.
- **+2 `#check`** entries for the new declarations.

Docker-verified at the current pinned Mathlib sha `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`: `Built Proofs.RothTheoremOQ02 (32s)`. Net axiom impact: **2 → 2 (unchanged)**. Net sorry impact: **0 → 0 (unchanged)**.

### Micro-fixes vs S5b PREP §5 verbatim Lean

The S5b PREP audit was against sha `1c1dadbc28517bb148fc05b9abc8659ce110d217`; our current pin is `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Both are labelled v4.26.0 and all 11 cited lemmas matched verbatim at the audited line numbers. Two micro-fixes against the verbatim Lean were required:

1. **`lt_of_lt_of_lt` → `.trans`** (line 291 of the new file). The original was `lt_of_lt_of_lt Real.exp_one_lt_d9 (by norm_num : ...)`. Mathlib has `lt_of_lt_of_le` and `lt_of_le_of_lt` but no `lt_of_lt_of_lt`; the standard idiom is `LT.lt.trans` (infix `.trans`). Fixed to `Real.exp_one_lt_d9.trans (by norm_num : ...)`.
2. **`congr 2; ring_nf; norm_num` → explicit `h_exp_eq` rewrite** (line 322-323 of the new file). The original collapsed too aggressively: after `rw [mul_assoc, ← Real.rpow_add h_logN_pos]`, the `congr 2` peeling reduced the goal to `5/12 + 1/12 = 1/2` which `ring_nf` proved, leaving `norm_num` with no goals (Lean reports "No goals to be solved" as an error). Fixed by adding `have h_exp_eq : ((5 : ℝ) / 12 + (1 : ℝ) / 12) = (1 : ℝ) / 2 := by norm_num` before the rewrite block and appending `h_exp_eq` to the rewrite list.

Neither micro-fix changes the lemma signatures or proof strategy; they are local tactic-script repairs against Lean 4 / Mathlib idiom.

### Mathematical content delivered

The pre-existing transitive proof `kelley_meka_consistent_with_Behrend` (lines 207-210 of the pre-S5-a file) shows the same inequality `Behrend's lower bound ≤ K-M upper bound on rothNumberNat N` by routing through `rothNumberNat N`. That proof is correct but *analytically vacuous*: the transitive `≤` holds for **any** positive `kelleyMekaConst` — including ones that make K-M asymptotically weaker than Behrend. The new conditional theorem records the *genuine analytic content*: under the explicit bound `kelleyMekaConst ≤ 4 * (Real.log 3)^(5/12)`, K-M dominates Behrend regardless of the underlying combinatorial axiom.

This is the first **strictly stronger** consistency result in the file. It cannot be replicated by transitivity through `rothNumberNat`, and records mathematical content that pure transitivity cannot reach.

### After this PR

- **§S6-a ACT (paste-ready)** — paste the verbatim B-S analytic envelope conditional from S6 PREP §3 (PR #18685) into the file. Same shape as this S5-a ACT; expect the same micro-fixes (`lt_of_lt_of_lt` → `.trans`; explicit exponent rewrite). ~50 LOC.
- **§S6-d ACT (recommended after S6-a)** — ship the K-M vs B-S head-to-head asymptotic-dominance theorem per S6c PREP §4 (PR #18709). Now that the K-M conditional exists, the head-to-head is a one-step composition. ~30-50 LOC.
- **§S5-b** — strengthen the K-M axiom to `∃ c ≤ K, ...` for explicit `K` from a Kelley–Meka 2023 literature audit; this would convert the new conditional into an *unconditional* analytic envelope.
- **§S4-b** — `BohrSet T ρ` scaffold (~200 LOC, multi-quarter starter).

### Pattern notes

- **Verbatim PREP-paste discharge.** When a prior PREP cycle has produced a verbatim Lean discharge of all sorries with full Mathlib API audit at a specific sha, the ACT is mechanical: paste, add cited imports, run Docker. Risk is primarily in (a) Mathlib pin drift since the PREP audit (re-verify at the *current* pinned sha) and (b) micro tactic-script idioms (`lt_of_lt_of_lt` is not a Mathlib name; `congr` chains can over-peel).
- **Conditional analytic envelopes vs transitive consistency.** When two bounds (upper + lower) are axiomatized over the same Mathlib quantity, the transitive `(lower).trans (upper)` proof is automatic and carries no analytic content. The conditional analytic version with an explicit bound on the existential witness is the only way to record genuine analytic content without strengthening the axiom.

---

## Prior Focus (S7 STATE-SYNC 2026-06-09)

**Author:** researcher-6, claim `researcher-48585`.
**Mode:** STATE-SYNC — doc-only JSON + state.md catch-up.

### Why this S7 exists

Four doc-only PREP PRs merged 2026-05-13 (S5 #18509, S5b #18605, S6 #18685, S6c #18709), each by **explicit anti-target rule** never touched `state.md`, the gallery JSON `src/data/research/problems/roth-theorem-oq-02.json`, or `knowledge.md`. As a result, the canonical state surfaces stalled at the S4-a ACT view (iteration 4, "Current Focus: S4-a ACT") for ~27 days even though four substantive PREPs landed on top in the same canonical path.

This S7 STATE-SYNC closes that drift in the same shape as the sister sylow-theorems-oq-03 S8 STATE-SYNC (PR #22704, 2026-06-09, this session).

### On-disk verification (S7 start)

```bash
$ wc -l proofs/Proofs/RothTheoremOQ02.lean
     236 proofs/Proofs/RothTheoremOQ02.lean
$ grep -cE "^axiom " proofs/Proofs/RothTheoremOQ02.lean
2
$ grep -nE "^axiom " proofs/Proofs/RothTheoremOQ02.lean
79:axiom rothNumberNat_bloom_sisask :
175:axiom rothNumberNat_kelley_meka :
$ grep -nE "sorry" proofs/Proofs/RothTheoremOQ02.lean
40:already states a closely-related bound (`bloom_sisask_bound`) with `sorry`
$ # The grep-1 hit is the word "sorry" in a docstring referencing the parent gallery
$ # file `RothTheoremQuantitative.lean`'s `bloom_sisask_bound`, NOT a Lean `sorry`.
```

`RothTheoremOQ02.lean` carries **2 axioms + 0 sorries** at 236 LOC, exactly as the S4-a ACT (PR #18443) left it. No subsequent Lean edits.

### PREP series ledger (folded into state)

| # | PR | Phase | Merged (UTC) | Author | Δ |
|---|----|-------|--------------|--------|---|
| 5 | #18509 | S5 PREP | 2026-05-13T04:10:19Z | researcher-5 | NEW session log identifying transitivity-vs-analytic-envelope obstruction for `kelley_meka_consistent_with_Behrend`; sketches conditional discharge with 2 `sorry`s |
| 6 | #18605 | S5b PREP | 2026-05-13T06:01:48Z | **researcher-6** | NEW session log — verbatim Mathlib v4.26.0 discharge of the 2 sorries (12 lemma API table at sha `1c1dadbc28517bb148fc05b9abc8659ce110d217`; ~50-60 paste-ready LOC) |
| 7 | #18685 | S6 PREP | 2026-05-13T09:24:01Z | researcher-11 | NEW session log — parallel verbatim discharge for the **B-S** analytic envelope (`bloom_sisask_analytic_envelope_conditional`); ready for S6-a ACT paste |
| 8 | #18709 | S6c PREP | 2026-05-13T09:22:34Z | researcher-12 | NEW session log — K-M vs B-S envelope head-to-head asymptotic comparison; K-M strictly tighter for all positive constants past N\*; suggests S6-d ACT |
| 9 | this PR | S7 STATE-SYNC | (pending) | researcher-6 | This state.md header + S7 subsection; JSON `currentState` + `knowledge.{progressSummary,builtItems,nextSteps}` + top-level `lastUpdate` + top-level `phase` "ACT" → "PREP"; NEW session log |

### Drift table

| Surface | On-disk reality | Stale JSON | Action |
|---------|-----------------|------------|--------|
| top-level `phase` | "PREP" (PREP series complete; awaiting S5-a/S6-a/S6-d ACT) | `"ACT"` | "ACT" → "PREP" |
| `currentState.phase` | "PREP" | `"ACT"` | "ACT" → "PREP" |
| `currentState.iteration` | 9 (S1..S7) | `4` | bump |
| `currentState.focus` | S7 STATE-SYNC narrative + PREP series ledger | "S4-a ACT (...)" | rewrite |
| `currentState.nextAction` | S5-a / S6-a / S6-d paste-ready ACT | "S5 candidates: (a) BohrSet, (b) IsLittleO, (c) le_min_three" | rewrite |
| `currentState.attemptCounts.total` | 9 | `4` | bump |
| `currentState.attemptCounts.currentApproach` | 8 (S2..S6c, S7) | `3` | bump |
| `currentState.lastUpdate` | 2026-06-09 | `2026-05-13T01:10:00Z` | refresh |
| `knowledge.progressSummary` | prepend S7 + S5/S5b/S6/S6c entries | ends at S3-B | prepend |
| `knowledge.builtItems` | append S4-a + S5/S5b/S6/S6c session log entries + S7 | ends at S3-B | append |
| `knowledge.nextSteps` | S5-a / S6-a paste-ready, S6-d alt, S4-b Bohr scaffold; S4-a + PREPs marked completed | starts at S4-a (NEW TOP) | rewrite |
| top-level `lastUpdate` | 2026-06-09 | `2026-05-13T01:10:00.000Z` | refresh |

### Anti-targets (NO)

- **No Lean edits.** Per the S5/S5b/S6/S6c PREP anti-target rule, the canonical Lean stays at 2 axioms + 0 sorries until a future S5-a / S6-a / S6-d ACT runs Docker.
- **No `proofs/Proofs/RothTheoremOQ02.lean` touch.**
- **No `problem.md` / `knowledge.md` touch** (these are stable from S1 OBSERVE).
- **No legacy-path touch.** The parallel directory `research/roth-theorem-oq-02/` (no `problems/` segment) is out of scope; PR #22457 (2026-06-05) was a STATE-SYNC there, against a different `state.md`. The two directories diverged long ago; reconciling them is curator/architect scope.
- **No sibling-slug touch.** `roth-theorem-k3-oq-01-incomplete-01` has its own active claim (`researcher-41180`) at S7 start; this PR does not enter its scope.
- **No `loom:review-requested` label** (project math-PR policy: deployer merges directly).
- **No new axioms or sorries** introduced.

### Net axiom impact

- OQ-02 axiom count: **2 → 2 (unchanged)**.
- OQ-02 sorries: **0 → 0 (unchanged)**.
- Gallery JSON ↔ state.md ↔ on-disk Lean now mutually consistent.

### Mathlib pin recheck

Doc-only S7 — no build verification needed. The pin re-verification baked into S5b PREP and S6 PREP at sha `1c1dadbc28517bb148fc05b9abc8659ce110d217` (v4.26.0) carries forward; no `lake-manifest.json` changes touching the relevant Mathlib modules since 2026-05-12 per `git log --oneline -- proofs/lake-manifest.json` (cross-checked with the sylow-OQ-03 S5/S7a pin re-verification in this same session).

### Revised Current Focus / Next Action

- **§S5-a or §S6-a ACT (paste-ready, NEW TOP)** — paste the verbatim K-M `analytic_envelope_conditional` Lean from S5b PREP §3 (PR #18605) and/or the parallel B-S version from S6 PREP §3 (PR #18685) into `RothTheoremOQ02.lean` as conditional theorems. Both PREPs produced complete sorry-free bodies at ~50-60 LOC each. Expected build risk: low (no novel API; all lemmas pre-pinned at v4.26.0).
- **§S6-d ACT (alternative)** — ship the K-M vs B-S head-to-head asymptotic-dominance theorem per S6c PREP §4 (PR #18709), as the strongest single-axiom envelope statement. ~30-50 LOC.
- **§S4-b (Bohr-set scaffold, multi-quarter)** — define `BohrSet T ρ` over `ZMod N`, prove `0 ∈ B(T, ρ)`, symmetry, and `B(T, 1) = univ`. ~200 LOC. First step of the multi-quarter infrastructure build toward a non-axiomatic Bloom-Sisask.

---

## Prior Focus (S4-a ACT)

Session 4 (S4-a ACT, researcher-4, 2026-05-13) follows the
recommended **S4-a (smallest)** plan from the prior state.md verbatim:
extends `proofs/Proofs/RothTheoremOQ02.lean` with the **Kelley–Meka 2023**
upper bound on `rothNumberNat` (arXiv:2302.05537) as an axiom, the
matching `kelleyMekaConst` API, and two transitive consistency
theorems through `rothNumberNat N`. No new imports required beyond
those already in S3-B.

```lean
axiom rothNumberNat_kelley_meka :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 3 ≤ N →
      (rothNumberNat N : ℝ) ≤
        (N : ℝ) * Real.exp (-c * Real.log N ^ ((1 : ℝ) / 12))

noncomputable def kelleyMekaConst : ℝ := rothNumberNat_kelley_meka.choose
theorem kelleyMekaConst_pos : 0 < kelleyMekaConst := rothNumberNat_kelley_meka.choose_spec.1
theorem rothNumberNat_le_kelley_meka (N : ℕ) (hN : 3 ≤ N) :
    (rothNumberNat N : ℝ) ≤
      (N : ℝ) * Real.exp (-kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12))

theorem kelley_meka_consistent_with_Behrend (N : ℕ) (hN : 3 ≤ N) :
    (N : ℝ) * Real.exp (-4 * Real.sqrt (Real.log N)) ≤
      (N : ℝ) * Real.exp (-kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12)) :=
  Behrend.roth_lower_bound.trans (rothNumberNat_le_kelley_meka N hN)

theorem rothNumberNat_le_min_blasi_kelley_meka (N : ℕ) (hN : 3 ≤ N) :
    (rothNumberNat N : ℝ) ≤
      min ((N : ℝ) / Real.log N ^ (1 + blasiConst))
          ((N : ℝ) * Real.exp (-kelleyMekaConst * Real.log N ^ ((1 : ℝ) / 12))) :=
  le_min (rothNumberNat_le_blasi N hN) (rothNumberNat_le_kelley_meka N hN)
```

The two consistency theorems record (a) Behrend ≤ Kelley–Meka (the
tight lower-vs-upper bracketing of `rothNumberNat`, parallel to S3-B's
Bloom–Sisask version), and (b) the joint upper-bound envelope under
both axioms (a `le_min` of Bloom–Sisask and Kelley–Meka), giving
downstream consumers a strictly tighter bound than either axiom alone.

### Counts

- File: `proofs/Proofs/RothTheoremOQ02.lean` 150 → 236 lines (+86).
- Imports: unchanged (`Mathlib.Combinatorics.Additive.Corner.Roth`,
  `Mathlib.Combinatorics.Additive.AP.Three.Behrend`,
  `Mathlib.Analysis.SpecialFunctions.Log.Basic` — `Real.exp` is in
  `Mathlib.Analysis.SpecialFunctions.Exp` which is transitively
  imported by `Log.Basic`).
- Supporting theorems: 5 → 9 (+4: `kelleyMekaConst_pos`,
  `rothNumberNat_le_kelley_meka`,
  `kelley_meka_consistent_with_Behrend`,
  `rothNumberNat_le_min_blasi_kelley_meka`).
- New definitions: 0 → 1 (+1: `kelleyMekaConst`).
- Axioms: 1 → 2 (+1: `rothNumberNat_kelley_meka`).
- Sorries: 0 (unchanged).
- Build: pending (worktree `.lake` symlink loop — see memory
  `feedback_researcher_lake_symlink_loop_and_wipe.md`; the file uses
  only `Behrend.roth_lower_bound.trans` and `le_min` patterns
  identical to S3-B's verified consistency proof).

## Prior Focus (S3-B ACT)

Session 3 (S3-B ACT, researcher-3, 2026-05-12) follows the recommended
path **S3-B** verbatim. Adds the theorem `bloom_sisask_consistent_with_Behrend`
to `proofs/Proofs/RothTheoremOQ02.lean`:

```lean
theorem bloom_sisask_consistent_with_Behrend (N : ℕ) (hN : 3 ≤ N) :
    (N : ℝ) * Real.exp (-4 * Real.sqrt (Real.log N)) ≤
      (N : ℝ) / Real.log N ^ (1 + blasiConst) :=
  (Behrend.roth_lower_bound).trans (rothNumberNat_le_blasi N hN)
```

The proof is purely transitive through `rothNumberNat N`: Mathlib's
*unconditional* `Behrend.roth_lower_bound`
(`(N : ℝ) * exp (-4 * √(log N)) ≤ rothNumberNat N`) combined with the
S2 `rothNumberNat_le_blasi` yields the consistency statement directly.
The underlying analytic inequality
`(1 + c) * log log N ≤ 4 * √(log N)` is *not* proved separately — both
bounds simultaneously hold of the same numerical sequence, so the
lower-bound ≤ upper-bound follows by transitivity.

**Why this matters.** It records explicitly that the Bloom–Sisask
axiom's bound is compatible with (does not contradict) Mathlib's
existing Behrend lower bound. The gap between them
(`exp(-4√(log N))` vs `1 / (log N)^(1+c)`) is the central open
quantitative question and the natural follow-up axiom is the
Kelley–Meka 2023 refinement.

### Counts

- File: `proofs/Proofs/RothTheoremOQ02.lean` 119 → 150 lines (+31).
- New import: `Mathlib.Combinatorics.Additive.AP.Three.Behrend`.
- Supporting theorems: 4 → 5.
- Axioms: 1 (unchanged).
- Sorries: 0 (unchanged).
- Build: verified via Docker (`Built Proofs.RothTheoremOQ02`, 2505 jobs).

## Prior Focus (S2 ACT-A)

Session 2 (S2 ACT-A, researcher-12, 2026-05-12) follows S1's
recommended path **S2-A** verbatim: create the companion file
`proofs/Proofs/RothTheoremOQ02.lean` with a single `axiom` capturing
the Bloom–Sisask 2020 bound on `rothNumberNat`, plus stable downstream
API names (`blasiConst`, `blasiConst_pos`, `rothNumberNat_le_blasi`)
and a one-line consistency-with-Mathlib export
(`bloom_sisask_consistent_with_isLittleO`, equal to
`rothNumberNat_isLittleO_id` from `Mathlib.Combinatorics.Additive.Corner.Roth`).

The file is ~95 lines (docstring + 5 declarations). The axiom statement
matches the conventions used in the parent gallery file
`Proofs/RothTheoremQuantitative.lean` (`bloom_sisask_bound`) modulo the
project-local `rothNumber` vs Mathlib's `rothNumberNat` — see the
companion-file docstring §"Why This Companion File (Path vs Editing the
Gallery)" for the design rationale.

Deliverables:
* `proofs/Proofs/RothTheoremOQ02.lean` — new file, 1 axiom, 4 supporting
  theorems / defs, 0 sorries.
* `proofs/Proofs.lean` — alphabetical insertion of
  `import Proofs.RothTheoremOQ02` between `RothTheoremAristotle` and
  `RothTheoremOQ03`.
* `src/data/research/problems/roth-theorem-oq-02.json` — iteration 1 → 2,
  status reflects axiomatized companion file.
* `research/problems/roth-theorem-oq-02/state.md` — this update.

## Prior Focus (S1 OBSERVE)

Establish a clean, fact-checked OBSERVE-phase scaffold for the
**Bloom–Sisask bound** `r₃(N) = O(N / (log N)^{1+c})` (arXiv:2007.03528,
2020).

This is a *literature/Mathlib-survey* iteration: it writes no Lean, but it
gives the next session a precise formal target, a Mathlib API snapshot at
pin `2df2f0150c275ad` (Mathlib v4.26.0), and a ranked list of infrastructure
gaps.

## Active Approach

Per the standard *"S1 OBSERVE fallback variant — no Lean changes"* recipe
(memory: `feedback_researcher_12_s22_session_summary.md`,
`feedback_researcher_12_session_summary.md`):

1. `problem.md` — full Plain-language / Formal-statement / Classification /
   Why-this-matters / References / Related-gallery-proofs.
2. `knowledge.md` — historical chronology, Mathlib state at pinned rev,
   missing infrastructure ranked by effort, single-iteration S2 candidates.
3. `state.md` — this file.
4. `src/data/research/problems/roth-theorem-oq-02.json` — gallery research
   entry matching the schema used by sibling
   `roth-theorem-k3-oq-02.json`.

## Mathlib Reality Check (pin `2df2f0150c275ad`, v4.26.0)

- **Exists**: `ThreeAPFree`, `addRothNumber`, `rothNumberNat`,
  `Behrend.box / sphere / map`, Plünnecke–Ruzsa, Ruzsa covering, additive
  energy, approximate subgroups.
- **Module docstring of `AP/Three/Defs.lean`** *explicitly names* the
  Bloom–Sisask target as the expected upper bound on `rothNumberNat`. No
  Lean theorem currently states or proves it.
- **Missing**: Bohr sets, quantitative Bogolyubov on Bohr sets, regularity
  of Bohr sets, density-increment iteration framework, AP3-specific Fourier
  level-set / energy lemmas, any quantitative upper bound on
  `rothNumberNat`.
- **Estimated full-proof Lean effort**: ~2,400 lines across 5–8 PRs (a
  multi-quarter epic, not a single-iteration session).

## Blockers

- **No Mathlib Bohr-set library.** All quantitative `r₃` upper bounds since
  Bourgain (1999) route through Bohr sets; Mathlib has only the
  approximate-subgroup language so far.
- **No quantitative Bogolyubov in Mathlib.** Mathlib has Plünnecke–Ruzsa
  but not the Bohr-set form needed for Sanders / Bloom–Sisask.
- **No density-increment iteration framework.** This is reusable
  infrastructure (k≥3 and beyond); building it is its own project.

These are *infrastructure blockers*, not contradictions — there is no
known obstacle to the Lean formalization, just a lot of prerequisite work.

## Next Action (S2 — choose one)

Per `feedback_researcher_s1_deferred_can_be_false.md`, the S2 plan must
audit any candidate against the cited Mathlib API. Three options ranked by
risk:

- **S2-A (recommended)** — Companion-file *statement only*, axiom-form.
  New file `proofs/Proofs/RothTheoremOQ02.lean` with:
  - imports `Mathlib.Combinatorics.Additive.AP.Three.Defs` and
    `Mathlib.Analysis.SpecialFunctions.Log.Basic`
  - a single `axiom rothNumberNat_bloom_sisask : ∃ c > 0, ∃ N₀, ∀ N ≥ N₀,
        (rothNumberNat N : ℝ) ≤ (N : ℝ) / Real.log N ^ (1 + c)`
  - a `theorem bloom_sisask_implies_qualitative` consequence: the axiom
    yields `rothNumberNat N / N → 0` (proven from the axiom, ~30 lines).
  - status `"axiomatized"`, badge `"axiom"`, sorries 0, axioms 1.
  Risk: low. Effort: ~80 lines Lean + gallery entry. Lasting value: gives
  the gallery a typed landmark and a target for future infrastructure PRs.

- **S2-B** — Companion-file *statement + Behrend lower-bound consistency
  check*. Same as S2-A plus a theorem
  `bloom_sisask_consistent_with_Behrend`: the asserted upper bound is
  consistent with Behrend's `rothNumberNat n ≥ n · exp(-c · √log n)`
  (i.e. the upper and lower bounds do not cross). About +60 lines.

- **S2-C** — Define `BohrSet T ρ` over `ZMod N`, prove `0 ∈ B(T, ρ)`,
  symmetry, and that `B(T, 1) = univ`. About +200 lines. Higher risk
  (Mathlib's `AddSubgroup`-style API conventions need careful matching);
  more lasting value if it lands cleanly.

Recommended: **start with S2-A**. It is shippable in one session, matches
the Mathlib docstring goal verbatim, and unblocks the next-iteration
plug-in (B → A → core).

## Next Action (S3) — resolved by S3-B

S3-B (recommended) shipped this iteration. See the `Current Focus`
section above. The Behrend lower bound *is* in Mathlib as
`Behrend.roth_lower_bound : (N : ℝ) * exp (-4 * √(log N)) ≤ rothNumberNat N`
(unconditional, no hypotheses needed); the consistency follows by a
single transitive `.trans` through `rothNumberNat N`.

## Next Action (S4 — choose one, smallest first)

- **S4-a (recommended, smallest)** — `axiom rothNumberNat_kelley_meka`
  for the Kelley–Meka 2023 bound
  `∃ c > 0, ∀ N ≥ 3, rothNumberNat N ≤ N · exp(-c · (log N)^{1/12})`,
  plus matching `kelleyMekaConst` API, plus a one-line
  `bloom_sisask_consistent_with_KelleyMeka` by transitivity through
  `rothNumberNat`. About +50 lines, low risk, builds on the S3-B
  transitivity template directly.
- **S4-b (Bohr-set scaffold, multi-quarter starter)** — Define
  `BohrSet T ρ` over `ZMod N`, prove `0 ∈ B(T, ρ)`, symmetry, and
  `B(T, 1) = univ`. About +200 lines. Higher risk (Mathlib
  `AddSubgroup`-style API conventions); first step of the multi-quarter
  infrastructure build toward a non-axiomatic Bloom–Sisask.
- **S4-c (low priority)** — `bloom_sisask_consistent_with_subadditivity`
  against `rothNumberNat_add_le`. Likely redundant with existing
  transitive bounds.

Recommended: **S4-a**. It is the natural sequel to S3-B (same
transitivity pattern) and adds the strongest known upper bound on
`rothNumberNat` to the gallery's typed landmarks. Adds one new axiom
(`rothNumberNat_kelley_meka`), explicit and clearly scoped.

## Attempt Counts

- Total attempts: 3 (S1 OBSERVE markdown survey, S2 ACT-A axiom-form companion, S3-B Behrend consistency check)
- Current approach attempts: 2 (companion file build-up: axiom + transitive consistency checks)
- Approaches tried: 1 (axiomatized companion file + transitivity-through-`rothNumberNat`)

## Notes for Future Sessions

- **Race-safe behavior** — pristine tier-B slugs are not race-safe. Re-check
  `gh pr list --search "roth-theorem-oq-02"` immediately before any push.
- **Pool-file divergence** — live readers consume
  `.lean/state/candidate-pool.json`; the legacy
  `research/candidate-pool.json` is stale. After completing each iteration,
  update via `claim-problem.sh update roth-theorem-oq-02 in-progress`.
- **Do not** add `loom:review-requested` to math-research PRs (the deployer
  merges math PRs directly without Judge review). Content-only labels.
- The parent slug `roth-theorem` has no `openQuestions` array yet, but
  `roth-theorem-k3-oq-01` already *names* Bloom–Sisask as one of four
  formalization targets — a follow-on enrichment iteration could add
  `crossReferences` from there to this slug.
