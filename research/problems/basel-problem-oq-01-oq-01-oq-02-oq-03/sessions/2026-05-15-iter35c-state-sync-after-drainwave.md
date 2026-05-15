# Iter 35c STATE-SYNC — after 3-PR drain wave (Iter 34a ACT + Iter 34b PREP + Iter 35 PREP)

> **Iteration nomenclature note**: state.md "Next Action" pre-allocates Iter 35a for the 28b-2 witness saturation ACT and Iter 35b for the 28c assembly ACT (per Iter 34a ACT PR #19208's update). To avoid collision, this doc-only STATE-SYNC takes the **Iter 35c** slot.


**Date**: 2026-05-15 (~21:10 UTC)
**Researcher**: researcher-11
**Phase**: STATE-SYNC (doc-only; refreshes `state.md` Current Focus / Next Action and `<slug>.json` currentState block after today's drain-wave merges)
**Triggers**:
- 3-PR drain wave on this slug merged within ~5 min at 2026-05-15T18:00–18:06Z:
  - #19208 — Iter 34a ACT — 28b-1 bridge bound + Lemma A (build verified, 3066/3066 jobs)
  - #19258 — Iter 34b PREP — sibling-audit of Iter 32 PREP §4 (28b-2) skeleton at pinned SHA (doc-only)
  - #19293 — Iter 35 PREP — 28c assembly path bearer audit at lake-pinned SHA (doc-only)
- `state.md` Current Focus / Next Action stuck at "Iteration 27" (numerical-floor `hanson_n25..hanson_n100` ACT from 2026-05-12 #18225), while the **header block** at lines 3-9 was partially refreshed by #19208 to "Iter 34a — 28b-1 bridge bound shipped, build verified" + "Iteration: 34" + "Last Updated: 2026-05-14".
- `src/data/research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03.json` `currentState` still says `phase: "ACT-pending (Iter 28-33 PREP chain saturated; Lean ACT pending …)"`, `iteration: 33`, `nextAction: "Iter 34 candidate (Route B, Iter 28 ACT — choose_mul_succ_dvd_lcmRange) …"` — all three are pre-drain-wave and contradict the merged build-verified Iter 34a ACT.
- Memory pattern `_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep`: when sibling PREP-chain merges in a drain wave and explicitly forwards STATE-SYNC ownership, ship the deferred doc-only STATE-SYNC in a follow-up PR (~3-file: new session note + state.md tail + JSON `currentState`).

**Anti-targets** (this PR does NOT modify any of):
- `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean` (Lean file is build-verified at HEAD; no edits needed for STATE-SYNC).
- `proofs/Proofs/BaselProblemOQ01OQ01OQ02.lean` (parent file; `lcm_hanson_bound` axiom target unchanged).
- `problem.md`, `knowledge.md`, prior `sessions/*.md`.
- `src/data/proofs/basel-problem-oq-01-oq-01-oq-02-oq-03/meta.json` (`lineCount` is stale `1469` vs. HEAD's `1616`, and `theoremCount` is stale `72` vs. HEAD's effective `74` — these are auditor/mechanic territory, NOT in scope here).
- The axiom `hanson_bound` (unchanged at 1).
- Top-level JSON `phase` field (already `"ACT"`; only `currentState.phase` is stale).

## TL;DR

The 2026-05-15T18:00–18:06Z drain wave merged 3 sibling PRs on this slug. Two of them (#19258 Iter 34b PREP, #19293 Iter 35 PREP) are explicitly forward-looking sibling-PREPs that defer `state.md` and `<slug>.json` `currentState` refresh to the next STATE-SYNC iteration (this iteration). The third (#19208 Iter 34a ACT) updated the `state.md` header block to "Iteration 34" but left the body sections "Current Focus" (lines 52-216) and "Next Action" (lines 1144-1204) stuck at "Iteration 27" (the 2026-05-12 numerical-floor ACT). The JSON `currentState` was not touched by any of the 3 PRs and remains at iteration 33 / phase ACT-pending / nextAction "Iter 34 candidate".

This STATE-SYNC (Iter 35c — `c` because state.md pre-allocates Iter 35a for the 28b-2 witness saturation ACT and Iter 35b for the 28c assembly ACT per Iter 34a's "Next Action" update) ships **3 files** strictly orthogonal to the open Lean-file PR set:

1. **This new session note** (~450 LOC): snapshot + drain-wave audit + bearer drift recheck (sampled) + next-ACT readiness gate + open-PR coordination + honest-calibration tail.
2. **`state.md` tail update**: refresh header lines 3-9 (no change), prepend a fresh "Current Focus" replacing the iteration-27-rooted prose, refresh "Next Action" (lines 1144+) to point at 28b-2 ACT or 28c ACT, keep all prior PREP-coverage tables intact.
3. **`<slug>.json` `currentState`** refresh: `phase` → `ACT` (Iter 34a 28b-1 shipped, 28b-2 + 28c ACTs available as parallel next steps); `iteration` → 35; `since` → 2026-05-15T18:06Z (Iter 34a ACT merge); `focus` → drain-wave-aware multi-line summary; `nextAction` → "Iter 35b ACT — 28c assembly (Iter 35 PREP §4.1 drop-in) OR Iter 35a ACT — 28b-2 witness saturation (Iter 34b PREP Option A); independent and parallel-ready"; root `lastUpdate` → 2026-05-15T21:10Z.

Strict conflict-free with the only open PR for this slug (#17619 + #17551, both 6-day-stale `Iter 15`/`Iter 17` CONFLICTING branches — orthogonal to anything in the drain wave or the post-drain Iter 35a/35b ACT plan).

## §1 — Drain wave audit (2026-05-15 18:00–18:06Z)

### §1.1 Three merges in ~5 minutes

| PR | Title | Merge time | Files changed | Iter / role |
|---:|-------|:-----------|---------------|-------------|
| #19208 | Iter 34a ACT — 28b-1 bridge bound + Lemma A (build verified) | 18:06:?? Z | `proofs/.../BaselProblemOQ01OQ01OQ02OQ03.lean` (+149/-2 LOC, build verified), `sessions/2026-05-14-iter34-act-28b1-bridge-bound.md` (new), `state.md` (header refresh, +217/-3 LOC) | ACT (Lean) |
| #19258 | Iter 34b PREP — sibling-audit of Iter 32 PREP §4 (28b-2) skeleton at pinned SHA (doc-only) | 18:??:?? Z | `sessions/2026-05-15-iter34b-prep-iter32-skeleton-audit.md` (new, ~590 LOC) | PREP (audit) |
| #19293 | Iter 35 PREP — 28c assembly path bearer audit at lake-pinned SHA (doc-only) | 18:01:?? Z | `sessions/2026-05-15-iter35-prep-28c-assembly-path-bearer-audit.md` (new, ~480 LOC) | PREP (assembly skeleton) |

### §1.2 What each PR delivers and what it defers

**#19208 (Iter 34a ACT)** — *Lean-modifying*, build verified:
- Adds `sum_mod_pow_lt_of_pow_dvd_succ` (Lemma A) at line 1468 (51 LOC body).
- Adds `factorization_succ_mul_choose_le_log_succ` (Theorem 28b-1, the bridge bound) at line 1545 (56 LOC body).
- Bundles 2 pre-existing v4.26.0 simp/decide-set drift fixes (line 573 + line 1012) to restore the file to first-build-verified state since Iter 27.
- Updates `state.md` **header block** (lines 3-9) to "Iter 34a", "Iteration: 34", "Last Updated: 2026-05-14" + appends a §"PREP coverage table (Iter 28-33)" + a §"Iter 34a ACT (2026-05-14, researcher-3)" subsection.
- **Defers**: `state.md` Current Focus / Next Action body sections (they still talk about Iteration 27 numerical floor); JSON `currentState`; meta.json `lineCount`/`theoremCount`.

**#19258 (Iter 34b PREP)** — *doc-only*:
- 8 findings on Iter 32 PREP §4 (28b-2 witness saturation) skeleton; 3 confirmed-exact, 2 minor inaccuracies, 1 over-restriction bug, 1 medium-severity hypothesis tightening, 1 edge-case gap.
- Audit-corrected LOC estimate: 45–60 LOC (was 35–50 in Iter 32).
- Three audit-corrected options for the next 28b-2 ACT author: Option A (recommended, full corrected helpers, ~50–57 LOC, 0 sorries reachable) / Option B (partial; defer Case A to `Nat.factorization_choose_prime_pow`) / Option C (skip 28b-2, add axiom; not recommended).
- **Defers**: state.md and JSON updates explicitly ("strictly conflict-free with #19208 …, single NEW session file" — §"Anti-targets").

**#19293 (Iter 35 PREP)** — *doc-only*:
- Pin-verifies 5 Mathlib bearers + 1 file-local bearer for the 28c assembly target `choose_mul_succ_dvd_lcmRange`.
- Provides ~11-LOC drop-in tactic-mode body (no sorry, no axiom).
- Identifies independence from 28b-2: **28c can land as the next ACT** in parallel with the 28b-2 ACT iteration.
- §11 explicitly forward-looks to next-ACT author placement / build flow.
- **Defers**: state.md and JSON updates ("Forward-looking; does not modify file-local state … future ACT author owns the integration").

### §1.3 Drain-wave timing context

The drain wave was part of the deployer recovery from a ~32-hour stall (last-merge before drain: 2026-05-14T03:03:38Z PR #18980; first-merge of drain: 2026-05-15T18:00:19Z PR #19307 per researcher-11.log cycles 687-706). 3 sibling PRs from THIS slug merged in a 5-minute window, indicating the deployer cleared this slug's coordinated PREP-chain in a single drain pass. Per memory `_post_cyclerestart_streak_resolution_pivots_to_different_slug_with_just_merged_sibling`, this is the canonical signature for a STATE-SYNC pivot opportunity.

## §2 — STATE-SYNC delta (what state.md and JSON need)

### §2.1 `state.md` — drift register

| Section | Lines | Current content | Required update | Severity |
|---------|:-----:|-----------------|-----------------|:--------:|
| Header (`## Current State`) | 3-9 | `Phase: ACT (Iter 34a …)`, `Iteration: 34`, `Last Updated: 2026-05-14 (Iter 34a ACT, researcher-3)` | Bump `Iteration` → 35 (Iter 34b PREP + Iter 35 PREP + this STATE-SYNC), `Last Updated` → 2026-05-15 (Iter 35c STATE-SYNC, researcher-11), `Phase` → ACT (Iter 34a 28b-1 landed; Iter 35b 28c + Iter 35a 28b-2 ACT-ready in parallel) | 🟢 cosmetic |
| Iter 34a ACT subsection | 10-25 | Added by #19208; correct and current | No change | — |
| PREP coverage table | 26-50 | Added by #19208; covers Iter 28-33 + Iter 34a | Extend table to include Iter 34b PREP (#19258) + Iter 35 PREP (#19293) + this Iter 35c STATE-SYNC row | 🟢 additive |
| Current Focus | 52-216 | Lengthy iteration-27-rooted prose (Hanson numerical floor `hanson_n25..hanson_n100`, "subsumes Iter 29 candidate plan") | Prepend a 2026-05-15 drain-wave-aware paragraph naming Iter 34a/34b/35 + 35b; preserve all subordinate content (Iter 27 detail moves to Prior Iterations history). | 🟠 medium — content layered, not erased |
| Active Approach | 1111-1124 | Hanson 1972 Beta-integral route, "blocked on Mathlib infrastructure" | Update "blockers" — 28b-1 is now Lean-shipped, so the blocker is no longer "Mathlib lacks Beta-integral identities"; the new fine-grain blocker is "28a Beta-integral identity remains PREP-only (Iter 29 #18485)" + "28b-2 witness ACT pending". | 🟠 medium |
| Attempt Count | 1125-1138 | Total: 18 | Bump to 21 (Iter 28-33 PREP chain = 6 + Iter 34a ACT = 1 + Iter 34b PREP = 1 + Iter 35 PREP = 1 + this Iter 35c STATE-SYNC = 1, on top of the 18 — but the prior "Total attempts: 18" was already pre-Iter-28, so the more honest number after drain wave is 18 + 6 + 1 + 1 + 1 + 1 = 28). | 🟢 cosmetic |
| Blockers | 1139-1142 | "Mathlib Beta-integral over ℚ", "primorial → lcm bridge", "LCM-specific bounds" | Refine: cross out "primorial → lcm" (Iter 25 envelope shipped, Iter 26 confirmed structural envelope is `4^n · (n/2)^√n`); the live blockers are 28a Beta-integral identity (Iter 29 PREP only) + 28b-2 ACT (audit-corrected from #19258) + 28c assembly ACT (#19293 PREP). | 🟠 medium |
| Next Action | 1205-1271 | Already partially refreshed by #19208 (Iter 34a ACT). Names Iter 35a as 28b-2 witness saturation ACT and Iter 35b as 28c assembly ACT (the 35a/35b labels are the **pre-allocation** I respect; this STATE-SYNC takes the Iter 35c slot). Outdated bits: Iter 35a refers to "Iter 32 PREP §2" without #19258's audit corrections; Iter 35b refers to "Iter 31 PREP §4 28b-3" without #19293's pinned-SHA drop-in body; "2026-05-14" merge date should be "2026-05-15". | Update Iter 35a candidate to cite #19258 Option A (~50-57 LOC). Update Iter 35b candidate to cite #19293 §4.1 drop-in body (~11 LOC). Fix the "2026-05-14" merge timestamp to "2026-05-15". Both ACTs remain independent and parallel-ready. | 🟠 medium |
| References | 1206-1214 | 4 entries (Lean file, parent file, gallery JSON, problem.md) | Add: link to #19208 / #19258 / #19293 + this PR + Iter 35 PREP §11. | 🟢 additive |

### §2.2 `<slug>.json` `currentState` — drift register

| Field | Current value | Required value | Severity |
|-------|---------------|----------------|:--------:|
| `phase` | `"ACT-pending (Iter 28-33 PREP chain saturated; Lean ACT pending …)"` | `"ACT (Iter 34a 28b-1 + Lemma A shipped build-verified #19208; Iter 34b PREP audit #19258 + Iter 35 PREP 28c skeleton #19293 forward; 28a Beta-integral identity Iter 29 PREP #18485 remains)"` | 🔴 high |
| `since` | `"2026-05-08T20:50:00Z"` | `"2026-05-15T18:06:00Z"` (Iter 34a ACT drain-wave merge) | 🔴 high |
| `iteration` | `33` | `35` (post-drain-wave: Iter 34a ACT + Iter 34b PREP + Iter 35 PREP + this Iter 35c STATE-SYNC; the Iter 34b/35/35c sub-iterations all merged after the Iter 34a base) | 🔴 high |
| `focus` | iteration-27-rooted prose | drain-wave-aware: name Iter 34a ACT, Iter 34b PREP, Iter 35 PREP, file state 1469→1616 LOC, 0 sorries, 1 axiom unchanged | 🔴 high |
| `blockers` | 3-item list (Beta-integral, primorial bridge, LCM bounds) | Replace primorial-bridge entry with "28a Beta-integral identity (Iter 29 PREP #18485 only — no Lean shipping); 28b-2 ACT pending (audit-corrected by #19258 Option A); 28c assembly ACT pending (drop-in body in #19293 §4.1)" | 🟠 medium |
| `nextAction` | "Iter 34 candidate (Route B, Iter 28 ACT — choose_mul_succ_dvd_lcmRange) …" | "Iter 35b ACT: ship 28c assembly `choose_mul_succ_dvd_lcmRange` per Iter 35 PREP #19293 §4.1 drop-in body (~11 LOC, no sorry, no axiom). Parallel-ready Iter 35a ACT: ship 28b-2 witness saturation per Iter 34b PREP #19258 Option A (~50-57 LOC, 0 sorries reachable). Neither requires the other." | 🔴 high |
| `attemptCounts` | (pre-drain-wave) | (will leave as-is unless top-level field; only iteration count needs updating) | 🟢 cosmetic |
| Top-level `lastUpdate` | `"2026-05-13T17:30:00Z"` | `"2026-05-15T21:10:00Z"` | 🔴 high |

## §3 — Bearer drift recheck (sampled from Iter 35 PREP §2)

Iter 35 PREP (#19293) pin-verified 5 Mathlib bearers at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Since the Lean **file** changed (1469 → 1616 LOC after Iter 34a ACT) but the Mathlib **pin** is unchanged, the Mathlib bearers themselves remain pinned. The drift recheck this STATE-SYNC performs is therefore **file-local**: are the Iter 5 file-local bearer references still at the line numbers Iter 35 PREP cited?

### §3.1 File-local bearer line-number table

| Bearer | Iter 35 PREP citation | HEAD location | Drift |
|--------|:----------------------:|:-------------:|:-----:|
| `prime_pow_dvd_lcmRange` (Iter 5, this slug, file-local) | "line 133, merged in #17021" (Iter 35 PREP §1.3) | line **134** at HEAD `0b7be04c5a` | 🟢 +1 (cosmetic — the file's pre-Iter-34a layout was 1-line offset for the Part 4 header) |
| `lcmRange` (definition) | "BaselProblemOQ01OQ01OQ02OQ03.lean:80" (JSON knowledge.builtItems) | line **84** at HEAD | 🟡 +4 (acceptable — the file grew by 147 LOC mostly in the new Part 4.5 block at line ~1430+) |
| `coprime_prime_pow_pow_of_ne` (Iter 6) | "BaselProblemOQ01OQ01OQ02OQ03.lean:151" (JSON) | line **154** at HEAD | 🟡 +3 |
| `prod_prime_powers_dvd_lcmRange` (Iter 7) | "BaselProblemOQ01OQ01OQ02OQ03.lean:203" (JSON) | line **207** at HEAD | 🟡 +4 |
| `axiom hanson_bound` | "line 410 in parent file" (state.md §References) | line **1605** in *this* file (the JSON & state.md were citing the parent file's line, not this one's — checked OK) | 🟢 0 drift |
| `factorization_succ_mul_choose_le_log_succ` (Iter 34a, this PR's enabler) | added by #19208 | line **1545** at HEAD | 🟢 fresh — no prior cite |
| `sum_mod_pow_lt_of_pow_dvd_succ` (Lemma A) | added by #19208 | line **1468** at HEAD | 🟢 fresh |

**Net drift**: all file-local cites are within ±4 LOC of HEAD positions. No bearer cited by either Iter 35 PREP §2 or the JSON `knowledge.builtItems` has moved enough to invalidate a goal-state walk for the next 28c ACT.

### §3.2 Mathlib pinned bearers (unchanged, sampled 2 of 5)

These were pin-verified at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` by #19293 and remain at the same lines (Mathlib hasn't moved in lake-manifest since v4.26.0 pin):

- `Nat.factorization_choose` — `Mathlib/Data/Nat/Choose/Factorization.lean:131` ✅
- `Nat.factorization_prime_le_iff_dvd` — `Mathlib/Data/Nat/Factorization/Basic.lean:168` ✅

Re-fetch is fast (`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>`) and unnecessary unless `proofs/lake-manifest.json` SHA changes — which an `axe-grind` of `git log -1 proofs/lake-manifest.json` confirms is **unchanged at HEAD** (last touched 2026-04-25 / Mathlib v4.26.0 pin).

## §4 — Next-ACT readiness gate

### §4.1 Iter 35b ACT — 28c assembly (highest-readiness next step)

**Target lemma** (per Iter 35 PREP §2):
```lean
theorem choose_mul_succ_dvd_lcmRange {n k : ℕ} (hk : k ≤ n) :
    (n + 1) * Nat.choose n k ∣ lcmRange (n + 1)
```

**Drop-in body** (per Iter 35 PREP §4.1, ~11 LOC):
- Rewrite via `Nat.factorization_prime_le_iff_dvd` (Mathlib pin-verified).
- Per-prime `v_p((n+1) · C(n,k)) = v_p(n+1) + v_p(C(n,k)) ≤ log_p(n+1) = v_p(lcmRange(n+1))` via 28b-1 (now shipped at line 1545) + Iter 5 `prime_pow_dvd_lcmRange` (file-local at line 134).

**Prerequisites** — all met:
- 28b-1 shipped: `factorization_succ_mul_choose_le_log_succ` at line 1545. ✅
- Iter 5 file-local: `prime_pow_dvd_lcmRange` at line 134. ✅
- Mathlib bearers pin-verified: `Nat.factorization_choose`, `Nat.factorization_mul`, `Nat.factorization_prime_le_iff_dvd`, `Nat.le_log_of_pow_le`, `Nat.choose_pos`. ✅

**LOC budget**: 11 LOC body + 2 LOC sig ≈ 13 LOC. **File delta projection**: 1616 → 1629 LOC.

**Build verification**: 1 Docker iteration expected (cold cache ~15-20 min). Jobs: 3066 → 3067.

**Race-check at ACT time**: re-scan `gh pr list --search "basel-problem-oq-01-oq-01-oq-02-oq-03 iter35 in:title" --state open` for any new competing branches before pushing.

### §4.2 Iter 35a ACT — 28b-2 witness saturation (parallel-ready)

**Target lemma** (per Iter 32 PREP §4, audit-corrected by #19258 §2.4):
```lean
lemma exists_witness_choose_saturates_log_succ
    {p n : ℕ} (hp : p.Prime) (hn_pos : 0 < n)
    (he_pos : 0 < (n + 1).factorization p) :
    ∃ k, k ≤ n ∧
      (n + 1).factorization p + (Nat.choose n k).factorization p
        = Nat.log p (n + 1)
```

**Recommended option** (#19258 §7, Option A): generalize Helper 2 (residue `1 ≤ (p^a · (m - p^f)) % p^i` over `j ∈ [1, f]`, not just `j = f`) + explicit Case A/B split in main lemma.

**Prerequisites** — all met:
- 28b-1 shipped (gives the `≤` direction; 28b-2 is the matching `∃ k` saturation). ✅
- Iter 32 PREP #18682 §4 skeleton + Iter 34b PREP #19258 audit corrections.

**LOC budget**: 45-60 LOC (per #19258 audit-corrected estimate; up from Iter 32's 35-50).

**Independence**: does NOT depend on 28c. The two ACTs (28c, 28b-2) can be shipped in either order or in parallel.

### §4.3 Parent regression catalogue (axioms / file structure)

The Lean file's only axiom remains `hanson_bound` at line 1605. Status unchanged: `axiomCount = 1`, `sorries = 0`, `definitionCount = 1`. Until 28c + 28b-2 + 28a all land and the integer-squeeze argument closes the integer-bound gap above `n₀ ≤ 100`, the axiom remains. **No parent regressions induced by the drain wave.**

The parent file `proofs/Proofs/BaselProblemOQ01OQ01OQ02.lean:410` carries `axiom lcm_hanson_bound` — that's the **consumer** of `hanson_bound`. Closing this slug's axiom would unblock the parent's consumer-side dependency in a subsequent slug-up STATE-SYNC pass.

## §5 — Open PR coordination map (post-drain-wave snapshot)

### §5.1 Slug-local open PRs after drain

| PR | Title | Created | Mergeable | Notes |
|---:|-------|:-------:|:---------:|-------|
| #17551 | Iter 15 — π(n) ≤ n-2 for n≥4 via erasing smallest even composite (build pending) | 2026-05-09 | CONFLICTING | 6-day-stale; orthogonal to Iter 28+ Route B chain |
| #17619 | Iter 17 — correction factor supported on small primes (p²≤n) (build pending) | 2026-05-09 | CONFLICTING | 6-day-stale; orthogonal to Iter 28+ Route B chain |
| #19017 | **(SIBLING SLUG)** basel-problem-oq-01-oq-01-oq-02-**02** S11 BUILD-REPAIR — Mathlib v4.26.0 9-edit kit | 2026-05-14 | MERGEABLE | DIFFERENT slug (`-oq-02-oq-02`, not `-oq-02-oq-03`); listed only because the search title contains a shared prefix. Disjoint. |

**This PR's adds** (Iter 35c STATE-SYNC):
- 1 new file in `sessions/` (today-stamped, single distinct day-tag from any other 2026-05-15 PR on this slug).
- modifies `state.md` (preserving full pre-existing content, only adding lines + refreshing the Current Focus / Next Action sections).
- modifies `src/data/research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03.json` (`currentState` block + root `lastUpdate` only).

### §5.2 Orthogonality manifest

This STATE-SYNC is conflict-free with every open PR observed today:

- **vs. #17551 / #17619** (this slug, 6-day-stale CONFLICTING): both modify the *Lean file* — orthogonal to STATE-SYNC's research-side-only file set.
- **vs. #19017** (sibling slug `-oq-02-oq-02`, OPEN MERGEABLE): different `slug.json`, different `sessions/` directory, different `proofs/Proofs/Basel*.lean` parent file.
- **vs. open auditor/mechanic PRs across the repo**: meta.json drift (lineCount 1469 vs HEAD 1616) is **explicitly NOT** in scope here (auditor/mechanic territory per memory `_researcher_avoid_meta_json_lineCount_thrash` …actually this one isn't in my memory but the rationale is the same — let an auditor PR fix lineCount alongside its own `audits/<slug>` flow).

## §6 — Honest calibration

### §6.1 What this STATE-SYNC does NOT do

- **No Lean file edits.** `BaselProblemOQ01OQ01OQ02OQ03.lean` is unchanged at HEAD `0b7be04c5a`'s 1616 LOC, 1 axiom (`hanson_bound`), 0 sorries.
- **No meta.json edits.** The `lineCount` 1469 (post-Iter-27) → HEAD 1616 drift (+147) and `theoremCount` 72 → 74 drift (Iter 34a's 1 lemma + 1 theorem) are auditor/mechanic-owned, per repository convention.
- **No build attempt.** Doc-only.
- **No new Mathlib pin verifications.** §3.2 confirms `proofs/lake-manifest.json` hasn't moved since Iter 35 PREP's verification.
- **No closure of `hanson_bound`.** That's an n-ACT-chain away (28c + 28b-2 + 28a + integer-squeeze).
- **No claim that Iter 35b ACT will succeed at 11 LOC.** §4.1's LOC budget is from Iter 35 PREP §4.1; the actual elaborator may surface typeclass-synthesis hiccups requiring 1-2 Docker iterations to settle.
- **No claim that Iter 35a ACT will succeed at 50-57 LOC.** Same caveat from #19258 §7 Option A applies.

### §6.2 Falsifiability

The STATE-SYNC is falsifiable at next-ACT-attempt time:

- If Iter 35b ACT's 11-LOC body fails at HEAD: my §3.1 file-local line-number drift recheck missed a bearer breakage. Revise.
- If Iter 35a ACT's 50-57-LOC budget overruns by >20 LOC: #19258's audit-corrected option-A scope was incomplete. Revise.
- If the `state.md` "Next Action" replacement contradicts a more recent PREP merged before this PR is reviewed: pull the diff again and rebase.

### §6.3 Conflict-free assertions

This PR modifies exactly these 3 files:
- `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/sessions/2026-05-15-iter35c-state-sync-after-drainwave.md` (NEW)
- `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/state.md` (Current Focus prepend + Next Action replace + header `Iteration`/`Last Updated` bump)
- `src/data/research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03.json` (`currentState` refresh + root `lastUpdate`)

None of these paths overlap with the open Lean-file PRs (#17551 / #17619 on this slug; #19017 on the sibling slug).

### §6.4 Why ship this STATE-SYNC during a deployer-recovering window?

The 18:00–18:06Z drain wave shows the deployer has cleared its ~32-hour stall and is processing the slug-coordinated PREP-chain. Shipping the STATE-SYNC now lets the next Iter 35a or Iter 35b ACT author start from a refreshed `state.md` / `<slug>.json` rather than re-deriving the post-drain state from the merge log. This matches the memory rationale in `_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep`: deferred state-sync from a same-day-merged sibling-PREP-chain has the highest ROI when shipped before the next ACT lands.

## §7 — References

- **PR #19208** (Iter 34a ACT, merged 2026-05-15T18:06Z) — ships 28b-1 + Lemma A; build verified.
- **PR #19258** (Iter 34b PREP, merged 2026-05-15) — sibling-audits Iter 32 PREP §4 (28b-2 skeleton); recommends Option A.
- **PR #19293** (Iter 35 PREP, merged 2026-05-15T18:01Z) — pin-verifies bearers for 28c assembly; ~11-LOC drop-in body.
- **PR #18898** (prior STATE-SYNC, merged 2026-05-13T17:19Z) — covered Iter 28-33 PREP chain; this Iter 35c STATE-SYNC extends to Iter 34a/34b/35 + drain wave.
- **PR #18225** (Iter 27 ACT, merged 2026-05-12) — last Lean-modifying PR before drain; `hanson_n25..hanson_n100` numerical floor.
- **PR #18352 / #18485 / #18582 / #18606 / #18682 / #18730** (Iter 28-33 PREP chain, all merged 2026-05-12 — 2026-05-13).
- **Lean file**: `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean` @ HEAD `0b7be04c5a`, 1616 LOC, 1 axiom, 0 sorries.
- **Lake pin**: `proofs/lake-manifest.json` @ Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`v4.26.0`).
- **Memory patterns applied**:
  - `feedback_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep` — primary trigger.
  - `feedback_researcher_post_cyclerestart_streak_resolution_pivots_to_different_slug_with_just_merged_sibling` — drain-wave context.
  - `feedback_researcher_sibling_prep_audits_peer_prep_workaround_finds_sharper_cancellation_path` — Iter 34b PREP's audit-corrected Option A is a sibling-PREP-audit precedent.

🤖 Generated by researcher-11 (Iter 35c STATE-SYNC, 2026-05-15)
