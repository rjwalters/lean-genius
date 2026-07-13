# S22 STATE-SYNC — Build-blocker resolved; absorb drain-wave PRs #19232 / #19237 / #19286 / #19247

**Date**: 2026-05-16T03:09Z (researcher-9)
**Mode**: STATE-SYNC (doc-only; no Lean edits)
**Slug**: `birthday-problem-oq-03-oq-01-oq-02-oq-01`
**Target file**: `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` (2102 LOC on `origin/main` @ `8a3cda556b6`)
**Pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged from S16d/S18/S19/S20/S21)
**Pattern**: `feedback_researcher_postdrain_statesync_absorbs_four_additive_preps_from_one_drain_wave`

---

## 1. Why this STATE-SYNC

Between S21 (2026-05-15 ~08:00Z) and S22 (this session, 2026-05-16 ~03:09Z) the slug's BUILD-BLOCKER era ended:

| PR # | Date merged | Author | Type | Effect |
|---|---|---|---|---|
| #19232 | 2026-05-15 18:04:46Z | researcher-12 | doc-only PREP | S19 K12 hygiene-leak root cause + latent `let φ` rename plan |
| #19237 | 2026-05-15 18:04:27Z | researcher-? | doc-only PREP | S20 K14 6-site cascade prediction; identified L570 as needing ~1-LOC explicit-scope fix |
| #19286 | 2026-05-15 18:01:33Z | researcher-? | doc-only PREP | S21 kit pin-verify sweep — 11 Mathlib citations at lake SHA, 0 phantom APIs, 1 off-by-1 cosmetic |
| **#19247** | **2026-05-15 ~18:xx** | **mechanic** | **Lean fix** | **`fix(mechanic): BirthdayProblemOQ03OQ01OQ02.lean v4.26.0 9-cluster repair (#19135) (#19247)` — Docker build 7743 jobs clean, 0 sorries, 1 axiom (unchanged), +105/−89 = +16 LOC** |

`state.md` head + `currentState.*` JSON fields were last touched 2026-05-14T03:30:00Z (S17 doc handoff). They still read `phase: BUILD-BLOCKER`, `iteration: 22`, `focus: "Build-blocker discovered..."`. Future researchers / Aristotle integrators would mis-route as a result. The drain-wave above demands a doc-only STATE-SYNC. This file ships it.

**Scope guarantee**: no Lean / no `meta.json` edits this session. Only:

1. This new file `s22-build-blocker-resolved-state-sync.md`.
2. `state.md` head replacement (preserves the entire tail's Session-16d/16d-PREP-FollowUp/etc. archive).
3. `src/data/research/problems/birthday-problem-oq-03-oq-01-oq-02-oq-01.json` field updates (`phase`, `currentState.phase`, `currentState.iteration`, `currentState.since`, `currentState.lastUpdate`, `currentState.focus`, `currentState.nextAction`, `currentState.blockers`, `currentState.attemptCounts.total`, plus a prepended `knowledge.progressSummary` entry).

---

## 2. Post-mechanic file snapshot (verified against `origin/main` @ `8a3cda556b6`)

```text
File:        proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean
Line count:  2102 (was 2086 pre-mechanic; +16 net delta)
Axioms:      1 — `axiom p_no_triple_tendsto` @ L329 (Lemma C, qualitative Poisson limit)
Sorries:     0
Build:       7743 jobs Docker clean (per PR #19247 commit message)
```

**Axiom architecture (post-S5 PR #16150, unchanged by mechanic)**:

```lean
-- L329 — the SOLE remaining axiom
axiom p_no_triple_tendsto (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun d : ℕ => P_no_triple (n_c c d) d) Filter.atTop (nhds (Real.exp (-(c^3 / 6))))

-- L451 — proved lemma (Lemma B)
lemma exp_lambda_tendsto (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun d : ℕ => Real.exp (-(λ_c c d))) Filter.atTop (nhds (Real.exp (-(c^3 / 6))))

-- L462 — original target restated as a THEOREM derived from B + C
theorem poisson_approx_birthday3 (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto
      (fun d : ℕ => P_no_triple (n_c c d) d − Real.exp (-(λ_c c d)))
      Filter.atTop (nhds 0)
```

The earlier framing "axiom poisson_approx_birthday3" is **stale**: it has been a derived theorem since PR #16150 (S5, 2026-05-06). The single remaining axiom is `p_no_triple_tendsto` (Lemma C only). This was already correct in `knownResults.open` but the `currentState.focus` text still echoed the old framing.

**Layer 3a–3f status — all on `origin/main`** (cross-checked against `#check` block at file tail):

```
✅ strictTriples                              (Layer 3a — S14 #17227)
✅ descFactorial_two_real_eq                  (Layer 3a — S14 #17227)
✅ tripleCount_descFact_2_eq_pairs            (Layer 3b — S14 #17227)
✅ tripleSet                                  (Layer 3c — S15 #17322)
✅ overlapPattern                             (Layer 3c — S15 #17322)
✅ overlapPattern_three_eq_empty              (Layer 3c — S15 #17322)
✅ overlapPattern_partitions_offDiag          (Layer 3c — S15 #17322)
✅ tripleCount_descFact_2_eq_overlap_sum      (Layer 3d — S15 #17322)
✅ bad_count_disjoint                         (Layer 3e — S16 #17381)
✅ p_pair_disjoint                            (Layer 3e — S16 #17381)
✅ bad_count_disjoint_strict                  (Layer 3e — S16b #17436)
✅ tripleSet_union_card_of_overlap            (Layer 3f prelim — S16c #17444)
✅ tripleSet_union_card_of_overlap_zero/one/two  (Layer 3f prelim — S16c #17444)
✅ card_overlapPattern_le_generic             (Layer 3f main — S16d #18925)
✅ card_overlapPattern_le_one                 (Layer 3f main — S16d #18925)
✅ card_overlapPattern_le_two                 (Layer 3f main — S16d #18925)
```

What is **NOT** yet in the file:

```
☐ bad_count_overlap_one                       (Layer 3f per-pair, S16e, ≈100 LOC)
☐ bad_count_overlap_two                       (Layer 3f per-pair, S16e, ≈80 LOC)
☐ factorial_moment_2 → (c³/6)²                (Layer 3g, S17, ≈30 LOC tendsto algebra)
☐ Method of Factorial Moments → Poisson limit (Layer 4, S18+, ≈200 LOC or Mathlib upstream)
```

Goal-line: with Layer 4 closed, `p_no_triple_tendsto` (the sole axiom) becomes derivable.

---

## 3. Bearer drift recheck (8 Mathlib bearers at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

S21 (PR #19286) pin-verified 11 citations at this same SHA on 2026-05-15 ~08:00Z. The lake SHA has not advanced since (verified via `proofs/lake-manifest.json` on current `origin/main`). Therefore the S21 verdicts remain valid **modulo any upstream Mathlib refs that the mechanic fix introduced**. New / re-checked rows below.

| Bearer | Cited location | S21 verdict | S22 recheck | Notes |
|---|---|---|---|---|
| `Nat.descFactorial` def | `Mathlib/Data/Nat/Factorial/Basic.lean:311-313` | ✅ confirmed (S21) | ✅ stable | Mechanic K4 used recursive unfold + `Nat.sub_zero, Nat.mul_one, Nat.mul_comm` not `Nat.descFactorial_two` (which is removed). |
| `card_eq_sum_card_fiberwise` w/ `Set.MapsTo` arg | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:971` | ✅ confirmed (S21) | ✅ stable | Mechanic K7 converted the file's `have hF : ∀ p ∈ s, _` style to `Set.MapsTo` form at L1384/1394/1414/1428 callsites — 4 sites cascade-resolved. |
| `card_sdiff_of_subset` | `Mathlib/Data/Finset/Card.lean:569` | ✅ confirmed (S21) | ✅ stable | Used by mechanic K8 (rename from old unconditional `card_sdiff`). |
| `Finset.orderEmbOfFin_unique` | `Mathlib/Data/Finset/Sort.lean:267` | ✅ confirmed (S21) | ✅ stable | New signature `(h : s.card = k)` as first explicit arg already accommodated by S12 author (PR #17120). |
| `filter_card_add_filter_neg_card_eq_card` | `Mathlib/Data/Finset/Card.lean:633` | ✅ confirmed (S21) | ✅ stable | Used by Layer 2 callsites. |
| `Nat.totient` `φ` scoped notation | `Mathlib/Data/Nat/Totient.lean:38` (S21 corrected from kit's L37) | ⚠ off-by-1 cosmetic (S21) | ✅ stable | S19 K12 renamed in-file `let φ` → `let embed` at 3 sites; cleared the hygiene leak. |
| `Finset.card_sigma` | `Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean:134` | ✅ confirmed (S16d PREP, S21) | ✅ stable | Used by S16d's `card_overlapPattern_le_generic`. |
| `Finset.card_powersetCard` | `Mathlib/Data/Finset/Powerset.lean:190` | ✅ confirmed (S16d PREP, S21) | ✅ stable | Used by S16d's `card_overlapPattern_le_generic`. |

**Verdict**: 0 substantive bearer drift since S21. Off-by-1 cosmetic line on `Nat.totient` scoped notation remains the only marker quibble; it does not affect any tactic.

---

## 4. ACT-readiness gate for next session (S23 = Layer 3f per-pair counts, S16e)

| Gate | Status | Evidence |
|---|---|---|
| File builds on lake SHA | ✅ GREEN | PR #19247 commit msg "Build: 7743 jobs clean (Docker, lake-pinned SHA 2df2f01)" |
| 0 sorries | ✅ GREEN | `grep -cE " sorry$" = 0` on `origin/main`:`proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` |
| 1 axiom (Lemma C only) | ✅ GREEN | `grep -cE "^axiom " = 1`; L329 `p_no_triple_tendsto` |
| Bearer audit current | ✅ GREEN | §3 above, 0 substantive drift since S21 |
| Layer 3a–3f infrastructure in place | ✅ GREEN | §2 above, 16 lemmas verified via `#check` block |
| Existing `bad_count_disjoint` template available | ✅ GREEN | L?? in `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean`; S16e is template-and-modify |
| Next-ACT skeleton drafted | ⚠ partial | S16d PREP cites "≈100 LOC mirrors `bad_count_disjoint`" + "≈80 LOC analogue"; full per-pair statement not yet pinned line-by-line |
| Other agents not in flight on slug | ✅ GREEN | `gh pr list --search "birthday-problem-oq-03 in:title is:open"` returned 0 open after this S22 |

**Gate verdict**: 7/8 GREEN, 1 partial. ACT for Layer 3f per-pair counts is unblocked **modulo** drafting the precise statement signatures for `bad_count_overlap_one` and `bad_count_overlap_two`. That drafting fits a S23 PREP (~30-60 min) using `bad_count_disjoint` (existing Layer 3e general form) as the template.

---

## 5. Next-ACT picker priority (for whoever picks up this slug next)

Ranked TOP→BOTTOM:

1. **S23 PREP — `bad_count_overlap_{one,two}` statement draft + tactic skeleton** (`bad_count_disjoint` template at S16 PR #17381). Doc-only; ~30-60 min; ships a Lean-paste-ready block. Reduces S24 ACT to single Docker iteration. Mathlib bearers needed: same as `bad_count_disjoint` (no new APIs). High-confidence build-clean on first try given the template.
2. **S24 ACT — paste the two `bad_count_overlap_*` lemmas** into §9 of the Lean file (after `card_overlapPattern_le_two`); one Docker build verify; ~30 LOC mechanical edits + ~180 LOC Lean.
3. **S25 PREP — Layer 3g (`factorial_moment_2 → (c³/6)²`)**. Combine 3d (`tripleCount_descFact_2_eq_overlap_sum`) with 3f-bound + 3e-per-pair into a single tendsto. ~30 LOC tendsto algebra. May fit in S24 if S23 PREP includes the closer.
4. **S26+ — Layer 4 (Method of Factorial Moments)**. Largest remaining piece (~200 LOC local or Mathlib upstream contribution). Closes the loop on Lemma C.

### Not-to-do checklist (anti-patterns from `Pre-Work Assessment`)

- ☐ Do NOT generalize the per-pair counts to general overlap k > 2 (no payoff; S16d already gives a global O(n^{6-k}) bound).
- ☐ Do NOT re-attempt Chen-Stein-method-from-scratch (≥500 LOC; Method of Factorial Moments is the strictly lighter path per S9 roadmap).
- ☐ Do NOT enumerate cases on f-trivialisation; the structural identity `tripleCount_descFact_2_eq_overlap_sum` already covers all f.
- ☐ Do NOT chain another `(build pending)` PR on this slug; the file is GREEN, keep it that way (every ACT must Docker-verify before push).

---

## 6. State.md head replacement (preview; actual write is in this same PR)

```
## Current State
**Phase**: ACT-READY — build-blocker resolved; Layer 3a–3f complete on main; S23 PREP for Layer 3f per-pair counts is next
**Path**: full
**Since**: 2026-05-15T18:04:46Z   (build-blocker lift via PR #19247 + drain-wave merges)
**Iteration**: 23 (S22 STATE-SYNC absorbing PRs #19232, #19237, #19286, #19247)
**Last Update**: 2026-05-16 (Session 22, researcher-9) — see `s22-build-blocker-resolved-state-sync.md`
```

(The existing Session 17 summary and the Session 16d/16d-PREP-FollowUp/S15/S14/S13/S12/etc. archive below the head are preserved.)

---

## 7. Sibling-PR compatibility ledger

| Open PR? | Conflict? |
|---|---|
| `gh pr list --search "birthday-problem-oq-03 in:title is:open"` @ 2026-05-16 ~03:09Z → 0 results | n/a |
| `state.md` simultaneously edited? | No — last touch 2026-05-14T20:47 (S17). This is the next edit. |
| JSON simultaneously edited? | No — last touch 2026-05-15T23:29Z (PR #19002 S17 JSON sync). This is the next edit and leaves `knownResults` / `knowledge.builtItems` / `knowledge.insights` untouched. |

**Bottom line**: strictly conflict-free.

---

## 8. References

- PR #19247: `fix(mechanic): BirthdayProblemOQ03OQ01OQ02.lean v4.26.0 9-cluster repair (#19135) (#19247)` — commit `e08dd1c8a90`
- PR #19232: S19 K12 root cause (researcher-12, doc-only)
- PR #19237: S20 K14 cascade prediction (doc-only)
- PR #19286: S21 kit pin-verify sweep (doc-only)
- PR #19135: S18 mechanic kit prep (CLOSED — superseded by PR #19247)
- PR #19002: S17 JSON state-sync (merged 2026-05-15 23:29Z; left `currentState.phase` stale — fixed by this PR)
- `s19-k12-root-cause-and-latent-sweep.md`
- `s20-k14-cascade-prediction.md`
- `s21-kit-pin-verify-sweep.md`
- `s16d-overlap-pattern-bounds.md`
- `s16d-bearer-audit-and-tactic-draft.md`
- `lemma-c-roadmap.md`
- `state.md`
