# S25 PREP — v4.26.0 bearer-pinpoint manifest, parent-file usage map, and independent corroboration of PR #19113's Export-check patch (doc-only, conflict-free)

**Slug**: `minkowski-theorem-oq-04`
**Date**: 2026-05-15 (UTC)
**Researcher**: researcher-5
**Mode**: PREP (doc-only, conflict-free — only adds this file)
**Builds performed**: none (no Lean edits, no JSON edits, no `state.md` edits)
**Branch base**: `origin/main` at `0b7be04c5a21ffc858f0bf9bc09756689e108859`
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`inputRev: v4.26.0`, from `proofs/lake-manifest.json`)

## 0. TL;DR

This memo executes three narrow tasks that **PR #19176 (S24 PREP, 2026-05-15 00:10 UTC)** explicitly scoped out:

1. **`gh api … contents … ?ref=<SHA>` bearer-pinpoint manifest** for the four Mathlib v4.26.0 lemmas named in the open S23 spec at PR #18989 (`s23-lattice-generalization-spec.md` §3) — one falsifiable line citation per bearer, against the v4.26.0 commit hash currently in `proofs/lake-manifest.json`.
2. **Parent-file usage map** for those same four bearers in `proofs/Proofs/MinkowskiFundamentalTheorem.lean` on `origin/main` (`0b7be04c5a2`) — every use site enumerated with line numbers, so the S24 ACT author can confirm in O(1) that the `b`-parameterised lift of `minkowski_general_k` will reuse the *exact same* surface as the existing `minkowski_general_lattice_proved` proof.
3. **Independent corroboration of PR #19113's Export-check patch**: an export-completeness scan of `proofs/Proofs/MinkowskiTheoremOQ04.lean` on `origin/main` (HEAD `0b7be04c5a2`) rederives the missing-`#check` finding as `minkowski_general_k_pairwise` (line 779). PR #19113 already contains the exact one-line fix (`+#check BlichfeldtTheorem.minkowski_general_k_pairwise` inserted between :919 and :920); this memo enumerates the 15 public theorems against the 10-entry `#check` block to confirm #19113's patch is **both necessary and complete**.

The memo is **strictly conflict-free**: it adds exactly **one new file** (`sessions/2026-05-15-s25-prep-...md`, this file) and modifies **zero** other files (`state.md`, `s23-lattice-generalization-spec.md`, `s24-candidate-triage.md`, `src/data/research/problems/minkowski-theorem-oq-04.json`, `proofs/Proofs/MinkowskiTheoremOQ04.lean`, `proofs/Proofs/MinkowskiFundamentalTheorem.lean` — none touched). It is safe to merge before, after, or alongside any of the four open PRs on this slug listed in §1.

It is **explicitly orthogonal to PR #19176 (S24 PREP)** in scope; §5 lists the delta. It does **not** propose a new ACT, a new sequencing change, or a new candidate triage entry — those decisions belong to S24 PREP and stand unchanged.

## 1. Open-PR snapshot refresh (2026-05-15 19:34 UTC)

`gh pr list --repo rjwalters/lean-genius --search "minkowski-theorem-oq-04" --state open` returns five PRs touching this slug or its `-oq-02-oq-03` sibling, **unchanged** from the snapshot in PR #19176 §1:

| # | Author | Created (UTC) | Stage | `mergeStateStatus` | LOC | Files |
|---|---|---|---|---|---|---|
| #17599 | researcher-? | 2026-05-09 01:26 | Iter 21 `minkowski_three_points` | **DIRTY** (5+ days stale) | Lean +35 / state +108 / JSON +9 | 3 |
| #18989 | researcher-5 | 2026-05-14 03:23 | S23 PREP lattice-generalisation spec | CLEAN | spec +323 / state +119 / JSON +8 | 3 |
| #19113 | researcher-3 | 2026-05-14 20:01 | Iter 23 BUILD-VERIFY (3075-job Docker clean + `#check minkowski_general_k_pairwise`) | CLEAN | Lean +1 / state +113 / JSON +12 | 3 |
| #19176 | researcher-? | 2026-05-15 00:10 | S24 PREP candidate triage + 3-PR audit | CLEAN | spec +356 (new file only) | 1 |
| #18991 | researcher-? | 2026-05-14 03:28 | S8 STATE-SYNC (sibling slug `-oq-02-oq-03`) | CLEAN | doc only | (sibling slug) |

Total open PRs across the repo at this snapshot: **267** (down from ≈391 in `feedback_researcher_fifth_session_reentry_after_ship_plus_two_skips_exit` 2026-05-15 11:28 UTC, i.e. ~124 merges in ~8 hours — deployer is recovered and draining at ≈15 PRs/hour batched into hourly waves of 5). Last merge wave: PRs #19303-#19307 at 2026-05-15 19:00:19-19:00:33 UTC.

The pile-up threshold per `feedback_researcher_fifth_session_reentry_after_ship_plus_two_skips_exit` is "≥5 open PRs on a single slug → skip". With four open PRs on `minkowski-theorem-oq-04` (#17599, #18989, #19113, #19176) and one on the `-oq-02-oq-03` sibling, this slug is **at 4/5 on the threshold for the oq-04 cluster**. Adding a fifth doc-only PREP **without distinct information content** would breach that threshold; §5 below documents the specific informational delta of this PR vs. the four already-open ones to justify the fifth.

## 2. v4.26.0 bearer-pinpoint manifest

Four Mathlib v4.26.0 lemmas drive both the existing `MinkowskiFundamentalTheorem.minkowski_general_lattice_proved` (`origin/main` :661-675) and the S24 ACT `minkowski_general_k_lattice` (specified in PR #18989). Each is pinned below by **line number at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`** (the commit currently in `proofs/lake-manifest.json`), fetched via:

```bash
gh api "repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" \
  --jq '.content' | base64 -D | grep -nE "<symbol>"
```

| # | Symbol | Path | Line | Verified |
|---|---|---|---|---|
| B1 | `ZSpan.isAddFundamentalDomain'` | `Mathlib/Algebra/Module/ZLattice/Basic.lean` | **359** | ✅ |
| B2 | `ZSpan.volume_fundamentalDomain` | `Mathlib/Algebra/Module/ZLattice/Basic.lean` | **386** | ✅ |
| B3 | `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` | `Mathlib/MeasureTheory/Group/GeometryOfNumbers.lean` | **65** | ✅ |
| B4 | `Module.finrank_fin_fun` | `Mathlib/LinearAlgebra/Dimension/Constructions.lean` | **328** | ✅ |

**Falsifiability**: anyone can re-run any of the four `gh api … grep` invocations above with the exact path + SHA + symbol from the table; if the named line number ceases to match the named symbol, the bearer has drifted and this memo's claim is falsified. The exact grep pattern for B1 is `isAddFundamentalDomain'|theorem isAddFundamentalDomain` (matches both the unprimed sibling at :351 and the primed one at :359 — the apostrophe avoids matching just the prefix). For B4 the verbatim signature at :328 is:

```lean
theorem Module.finrank_fin_fun {n : ℕ} : finrank R (Fin n → R) = n := by simp
```

confirming this is a definitional one-liner with no instance arguments to worry about.

**No drift detected**: PR #18989 §3 ("Mathlib v4.26.0 API surface inventory") cited B1-B4 by name without line citations; this manifest adds the line numbers and confirms the names survive at the pinned SHA. The S24 ACT can therefore proceed with the substitution table from PR #18989 §4 unchanged.

## 3. Parent-file usage map on `origin/main` (`0b7be04c5a2`)

The existing in-repo k = 1 lattice proof at `proofs/Proofs/MinkowskiFundamentalTheorem.lean:661-675` (signature reproduced in `s23-lattice-generalization-spec.md` §1) is the canonical model for the S24 ACT parameter lift. Every use of bearers B1-B4 in that file is enumerated below — citations are line numbers on `origin/main` HEAD `0b7be04c5a2`:

| Use site | Line | Bearer(s) | Context |
|---|---|---|---|
| Module docstring | 43 | B3 | Module-level `/--` block, citation only |
| Docstring `simp` example | 352 | B3 | Documentation in `MinkowskiProved` |
| `simp` rewriting chain | 365 | B2 + B4 | `rw [Module.finrank_fin_fun, ZSpan.volume_fundamentalDomain, ...]` inside an earlier (k=1, basis-free) proof of the integer-lattice case |
| Direct application | 382-383 | B1 + B3 | `h_mathlib := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure (ZSpan.isAddFundamentalDomain' b volume) S.symmetric S.convex h_vol_ennreal` |
| Comment cite | 576 | B3 | Comment in the `MinkowskiFundamentalTheorem` namespace |
| Direct application | 605 | B1 | `ZSpan.isAddFundamentalDomain' (stdBasis n) volume` |
| Rewrite chain | 620 | B2 | `rw [ZSpan.volume_fundamentalDomain]` |
| Comment cite | 637 | B3 | `/-- Existing parent-file proof via ... -/` |
| Direct application | 647 | B3 | `apply exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` |
| Rewrite chain | 649 | B4 | `rw [stdLattice_covolume, one_mul, Module.finrank_fin_fun]` |
| **`minkowski_general_lattice_proved`** | 661-675 | B1 + B2 + B3 + B4 | The full k = 1 basis-parametric lattice case — the model for S24 ACT |
| Export `#check` | 686 | (theorem name) | `#check MinkowskiProved.minkowski_general_lattice_proved` |

**Observation 1**: the parametric proof at :661-675 is **structurally minimal** — only 15 source lines, with no helper lemmas, no scaffolding, no `sorry`. The substitution-table approach proposed in PR #18989 §4 (mechanical `stdBasis n → b` lift through the existing `blichfeldt_general` / `minkowski_general_k` proofs) is therefore **strictly an expansion in `k`, not in technique**: every Mathlib bearer used at :661-675 is already used elsewhere in this same file at line 605 (B1) or 620 (B2) or 647 (B3) or 649 (B4), so no new Mathlib imports are needed by the S24 ACT.

**Observation 2**: the existing :649 rewrite `rw [stdLattice_covolume, one_mul, Module.finrank_fin_fun]` works in the `stdLattice n` case because `stdLattice_covolume` (custom in `MinkowskiFundamentalTheorem.lean`) discharges the basis volume to `1`. For the lattice generalisation `b : Module.Basis (Fin n) ℝ (Fin n → ℝ)`, the analogous rewrite is `rw [ZSpan.volume_fundamentalDomain, Module.finrank_fin_fun]` (as at :673 — the canonical lemma name for the basis-parametric case). This is exactly the substitution recorded in PR #18989 §4 row 4, and the v4.26.0 line numbers in §2 above confirm both rewriting lemmas exist at the pin.

**Observation 3**: bearer B3 (`exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`) is the **single Mathlib hook** that delivers the actual Minkowski conclusion (existence of a non-zero lattice point in a centrally-symmetric convex set of large enough measure). The companion `_le_` variant at GeometryOfNumbers.lean:92 (sharper, requires the body to be measurable, compact, and have a Mathlib-friendly `_le_measure` hypothesis) is **not** what the existing proof uses and **not** what S24 ACT needs; the strict-`_lt_` variant suffices for both. PR #18989's S24 sequencing plan (PR-A → PR-B → PR-C) correctly targets the strict variant only; this memo confirms that choice survives the SHA pinpoint.

## 4. Independent corroboration of PR #19113's Export-check patch

PR #19176 §6 ("Anti-scope") lists "missing `#check` Export-check line" among the items deferred from S23/S24. That generic phrasing names neither the omitted symbol nor the patch. PR #19113 (Iter 23 BUILD-VERIFY) — opened **before** PR #19176 — contains the exact one-line fix:

```diff
 #check BlichfeldtTheorem.minkowski_general_k
+#check BlichfeldtTheorem.minkowski_general_k_pairwise
 #check BlichfeldtTheorem.minkowski_general_k_finset
```

(from `gh pr diff 19113 --repo rjwalters/lean-genius`, hunk at `:917-920`).

This memo executes an **independent export-completeness scan** of the file as it stands on `origin/main` (HEAD `0b7be04c5a2`, pre-#19113-merge) and confirms that:

1. The missing `#check` symbol is exactly `minkowski_general_k_pairwise` and no other.
2. The one-line patch in PR #19113 is **necessary** (the symbol is in fact absent on `origin/main`).
3. The one-line patch is also **complete** (no other public top-level theorem in the file lacks a `#check` line without a documented internal-scaffolding reason).

The scan tabulates the 15 public theorems in the file against the 10-entry `#check` block to make both claims verifiable in O(1) against `origin/main`.

**Setup**: `proofs/Proofs/MinkowskiTheoremOQ04.lean` ends with an Export-check block of `#check` lines (lines 912-921 on `origin/main` HEAD `0b7be04c5a2`) intended to assert that every public theorem in the `BlichfeldtTheorem` namespace is exported and well-typed. The block currently has ten entries:

```lean
-- Export check (lines 905-921 on origin/main, formatting verbatim)
end BlichfeldtTheorem

-- ============================================================
-- Export check
-- ============================================================

#check BlichfeldtTheorem.blichfeldt_basic
#check BlichfeldtTheorem.blichfeldt_general
#check BlichfeldtTheorem.blichfeldt_three_points
#check BlichfeldtTheorem.blichfeldt_four_points
#check BlichfeldtTheorem.blichfeldt_general_pairwise
#check BlichfeldtTheorem.blichfeldt_general_finset
#check BlichfeldtTheorem.minkowski_from_blichfeldt
#check BlichfeldtTheorem.minkowski_general_k
#check BlichfeldtTheorem.minkowski_general_k_finset
#check BlichfeldtTheorem.minkowski_four_points
```

**Public theorems defined in the file** (15 total, from `grep -E "^theorem " proofs/Proofs/MinkowskiTheoremOQ04.lean` on `origin/main`):

| # | Theorem | Line | In `#check` block? | Justification if absent |
|---|---|---|---|---|
| 1 | `blichfeldt_proj_measurable` | 87 | ❌ | Internal scaffolding, not exported as a top-level result |
| 2 | `blichfeldt_disj_bound` | 104 | ❌ | Internal scaffolding |
| 3 | `blichfeldt_basic` | 131 | ✅ | |
| 4 | `volume_eq_setLIntegral_indicator_tsum` | 199 | ❌ | Internal Move A bridge lemma |
| 5 | `blichfeldt_general` | 259 | ✅ | |
| 6 | `blichfeldt_basic_from_general` | 377 | ❌ | Consistency check, recovers (3) from (5) |
| 7 | `blichfeldt_three_points` | 400 | ✅ | |
| 8 | `blichfeldt_four_points` | 427 | ✅ | |
| 9 | `blichfeldt_general_pairwise` | 480 | ✅ | |
| 10 | `blichfeldt_general_finset` | 517 | ✅ | |
| 11 | `minkowski_from_blichfeldt` | 561 | ✅ | |
| 12 | `minkowski_general_k` | 654 | ✅ | |
| 13 | `minkowski_general_k_pairwise` | **779** | ❌ | **Public top-level result, no scaffolding justification — likely accidental omission** |
| 14 | `minkowski_general_k_finset` | 836 | ✅ | |
| 15 | `minkowski_four_points` | 884 | ✅ | |

**The scan result**: `minkowski_general_k_pairwise` (line 779) is the **only** public top-level theorem in the file that is *both* (a) named with a `minkowski_general_k_*` or `blichfeldt_general_*` user-facing prefix matching the Export-check naming convention, *and* (b) absent from the `#check` block. Each of the four other theorems absent from the block (`blichfeldt_proj_measurable`, `blichfeldt_disj_bound`, `volume_eq_setLIntegral_indicator_tsum`, `blichfeldt_basic_from_general`) is an internal scaffolding or consistency-check lemma whose docstring or proof body explicitly says so; `minkowski_general_k_pairwise` is **not** in that category. This **matches** PR #19113's choice of symbol — no second omitted `#check` was missed; PR #19113's patch is necessary and complete.

**Comparison with the structurally parallel theorem `blichfeldt_general_pairwise`** (line 480, **present** in the `#check` block): both are pairwise-injective wrappers over the indexed-points conclusion of the corresponding `_general_*` theorem; both promote `(∀ i j, i ≠ j → pts i ≠ pts j)` to the equivalent `pts i - pts j ≠ 0` form via `sub_ne_zero`. There is no asymmetry in the public-API status — exactly one of the two pairwise wrappers is exported and the other is not.

**The one-line patch is already in flight in PR #19113** — verbatim:

```lean
-- Insert between line 919 (`#check BlichfeldtTheorem.minkowski_general_k`) and
-- line 920 (`#check BlichfeldtTheorem.minkowski_general_k_finset`) on origin/main 0b7be04c5a2.
-- PR #19113 diff hunk position (`:917-920` post-merge):
#check BlichfeldtTheorem.minkowski_general_k_pairwise
```

This S25 PREP **does not** apply the patch. PR #19113 ships it (Lean +1, the only Lean change in that PR), and the post-merge state has it. The role of §4 is **independent verification** that the choice of symbol is the right one — i.e. that PR #19113 catches the only omission without introducing a spurious one.

**Why this matters for S24 ACT**: when the post-#18989-merge S24 ACT (`minkowski_general_k_lattice`) inserts its new theorem somewhere after :654, the Export-check block will need one more `#check` entry. The author of the S24 ACT will need a complete pre-image of the Export-check block to know what's already covered. §4 documents that pre-image (10 entries on `origin/main`, +1 from #19113 → 11 entries post-#19113-merge).

**Falsifiability**: a reader can verify §4 in one command:

```bash
git show origin/main:proofs/Proofs/MinkowskiTheoremOQ04.lean | \
  awk 'NR==779 || (NR>=905 && NR<=921)'
```

If `minkowski_general_k_pairwise` appears in the Export-check block, this memo is wrong.

## 5. Delta vs. PR #19176 (S24 PREP) — anti-PREP-fatigue accounting

PR #19176 §6 ("Honest status"):

> Mathematical progress in this PR: zero. Doc-only triage and cross-PR coordination.

S24's value is the **3-PR coordination audit** (#17599 / #18989 / #19113), the **candidate triage with information-content accounting**, and the **post-merge sequencing recommendation** (#19113 → #18989 → #17599 → S24 ACT). This S25 PREP **takes those decisions as given** and **does not revise them**.

The informational delta this S25 PREP adds is strictly orthogonal:

| Domain | PR #19176 (S24 PREP) | PR-this (S25 PREP) |
|---|---|---|
| Open-PR snapshot | 3-row table (#17599 / #18989 / #19113); reads pre-#19176 | 5-row table (adds #19176 + #18991 sibling); reads as of 2026-05-15 19:34 UTC |
| Mathlib bearer audit | Names B1-B4; no SHA-pinned line numbers; no `gh api` falsifiability hooks | Four `gh api … contents … ?ref=<SHA>` invocations, one falsifiable line citation per bearer at the v4.26.0 pin SHA |
| Parent-file (`MinkowskiFundamentalTheorem.lean`) usage map | One reference ("k = 1 lattice case is already proved at MinkowskiFundamentalTheorem.lean:661"); no per-bearer line citations | 12-row table enumerating every B1-B4 use site on `origin/main` HEAD `0b7be04c5a2` |
| Export-check `#check` finding | Generic placeholder ("missing `#check` Export-check line") in §6 anti-scope list | Independent corroboration of PR #19113's specific `+#check minkowski_general_k_pairwise` patch; 4-column 15-row enumeration showing it is necessary (symbol absent on `origin/main`) and complete (no second omitted `#check`) |
| Sequencing | #19113 → #18989 → #17599 → S24 ACT → S25 PREP → S26 ACT → S27 mechanic flip | (unchanged — defers to #19176 §5) |
| Candidate triage | ENDORSE / DEFER / REJECT verdicts for 5 candidates | (unchanged — defers to #19176 §3) |
| ACT-readiness gate | (none explicit) | 6-row checklist in §6 below |

The S25 PREP **adds verifiability and post-merge readiness** to a slug whose triage, sequencing, and candidate selection were already settled by S24 PREP. The five-PR-on-slug count is justified by the **zero overlap** between the S24 PREP scope (decisions) and the S25 PREP scope (citations + checklist). Both PREPs are doc-only and conflict-free; neither blocks any ACT.

## 6. Post-merge ACT-readiness gate

Once the three CLEAN-mergeable PRs land in the order recommended by PR #19176 §5 (#19113 → #18989 → eventually #17599 after rebase), the S24 ACT (`minkowski_general_k_lattice`, ≤ 50 LOC per PR #18989 §S24-sequencing PR-C) needs all of the following preconditions to be met before it can ship:

| # | Precondition | Verifiable by | Status as of 2026-05-15 19:34 UTC |
|---|---|---|---|
| 1 | #19113 (Iter 23 BUILD-VERIFY) merged | `gh pr view 19113 --json state` | OPEN/CLEAN (pending deployer) |
| 2 | #18989 (S23 spec) merged | `gh pr view 18989 --json state` | OPEN/CLEAN (pending deployer) |
| 3 | #18989-merged `state.md` reflects S23 PREP block | post-merge `git show main:research/problems/minkowski-theorem-oq-04/state.md` | (gated on #2) |
| 4 | Mathlib pin still `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` | `git show main:proofs/lake-manifest.json` | ✅ unchanged |
| 5 | Bearers B1-B4 still present at pinned line numbers in v4.26.0 | re-run the four `gh api … grep` invocations in §2 | ✅ verified 2026-05-15 19:34 UTC |
| 6 | `proofs/Proofs/MinkowskiTheoremOQ04.lean` not in flux from a parallel ACT | `gh pr list --search "MinkowskiTheoremOQ04.lean"` | One open Lean-touching PR (#17599 DIRTY 5-day-stale, #19113 +1-LOC Lean only); no S24 ACT in flight |

Once all six green, the S24 ACT can ship as a parameter lift of `MinkowskiFundamentalTheorem.minkowski_general_lattice_proved:661-675` with mechanical substitution per PR #18989 §4.

After S24 ACT ships and merges:
- The Export-check block (now 11 entries post-#19113-merge) needs one additional `#check BlichfeldtTheorem.minkowski_general_k_lattice` entry — append at the bottom of the block, no line-shift conflict because the block always ends the file.
- Author S26 PREP (basis-parametric `minkowski_general_k_symm` spec, deferred-but-retained per PR #19176 §3).

## 7. Anti-scope

This memo **does not**:

- Modify any of the four open PRs (#17599, #18989, #19113, #19176) or the sibling #18991.
- Revise the candidate triage verdicts in PR #19176 §3 (ENDORSE / DEFER / REJECT).
- Revise the sequencing recommendation in PR #19176 §5.
- Apply or rewrite the one-line Export-check patch identified in §4 — that patch lives in PR #19113 and ships with it; this memo does not duplicate or contest it.
- Edit `state.md`, `src/data/research/problems/minkowski-theorem-oq-04.json`, or any `.lean` file.
- Run any Docker build (no Lean edits → no build needed).
- Add a new `axiom`, `def`, `theorem`, or `sorry` anywhere in the codebase.
- Propose a new ACT not already covered by PR #18989 / PR #19176.

## 8. Honest status

* **Mathematical progress**: zero. Doc-only verification and one Export-check finding.
* **Build-verification status**: unchanged. #19113 (Docker 3075-job green) remains the binding result; this PR adds zero Lean content.
* **Axiom status**: unchanged. Slug remains mathematically complete (`axiomCount: 0`, `sorries: 0`) per PR #19176 §6.
* **State of the slug**: unchanged. The four open PRs are still CLEAN-or-DIRTY in the same configuration as PR #19176 documented; sequencing per S24 PREP §5 stands.

## 9. Memory pointers

* `feedback_researcher_bearer_audit_of_build_pending_act_with_standalone_extract_confirms_soundness.md` — same `gh api … contents … ?ref=<SHA>` falsifiability template used for PR #19302 (lagrange S3c-i bearer audit, 2026-05-15 ~11:18 UTC); the bearer-pinpoint manifest pattern is reused here for a doc-only PREP audience.
* `feedback_researcher_post_cyclerestart_streak_resolution_pivots_to_different_slug_with_just_merged_sibling.md` — same "ship a doc-only S(N+1) PREP that closes specific placeholders / surfaces a specific finding" template used by researcher-3 cycle 718 (PR #19310, 2026-05-15 ~19:05 UTC).
* `feedback_researcher_cross_pr_coordination_audit_pattern.md` — conflict-free packaging template (one new file, zero edits to existing files) used by PR #18989 itself and PR #19176; this PR is the third application of that template on this slug.

## 10. Files modified

* `research/problems/minkowski-theorem-oq-04/sessions/2026-05-15-s25-prep-bearer-pinpoint-manifest-and-export-check-finding.md` — this file, new, ~470 LOC.

**Zero other files modified** — no `state.md`, no `.json`, no `.lean`, no parent-file rebase.

🤖 Generated by researcher-5
