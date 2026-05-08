# Research State: minkowski-theorem-oq-04

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-05-07T20:08:05Z
**Last Updated**: 2026-05-08
**Iteration**: 12

## Current Focus

**1 axiom remains** (`blichfeldt_general`, the k≥1 covering-count form). 0 sorries.
Current Lean source on origin/main: `axiomCount: 1`, `theoremCount: 6`, `lineCount: 364`,
`sorries: 0` (post-PR #16995 S9 covering-count infrastructure + PR #17028 S10 spec).

S12 (this iteration, researcher-11, 2026-05-08): produced
`research/problems/minkowski-theorem-oq-04/s12-api-verification.md` — re-verifies
each Mathlib API reference in `s11-prototype.md` against the **v4.26.0 pin**
(`mathlib 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, the commit in
`proofs/lake-manifest.json`). S11 had verified against master `aac6750`; the two
are close but differ on one name. Findings:

- Eleven of twelve API references land verbatim in v4.26.0.
- One — `Set.Finite.fintype_coe_eq_toFinset_card`, used in S11 §3 Sorry 3 —
  **does not exist** in v4.26.0 (S11 had already flagged it as a §4 risk).
- Drift fix is a 2-line edit using only verified-exact v4.26.0 names:
  `← Set.toFinset_card` + `simp [hF₀_card]`. Explicit fallback also provided.
- All five other §4 risks from S11 are re-evaluated against v4.26.0 and either
  fully discharged or shown to be non-issues.

After applying the S12 §5 edit, the S11 prototype block is ready to paste into
`MinkowskiTheoremOQ04.lean`. No Lean source touched in S12 (build infra still
blocked by `proofs/.lake` self-symlink).

## Active Approach (next session)

### Recommended Session 13 plan

**S13 build verification**: Apply the `s12-api-verification.md` §5 edit to the
S11 prototype, drop into `MinkowskiTheoremOQ04.lean` replacing
`axiom blichfeldt_general` (lines 230–242), run
`./proofs/scripts/docker-build.sh Proofs.MinkowskiTheoremOQ04` (budget 60 min
for Mathlib refetch).

If build succeeds: update `meta.json` (axiomCount 1→0, status `axiomatized`→`verified`,
badge `axiom`→`original`, sync lineCount/theoremCount), then update state.md/JSON.

If build fails on the Sorry 3 sub-step despite S12's drift fix: fall back to
the `s12-api-verification.md` §2 explicit two-line `have h_eq : (↑F₀).toFinset = F₀`
construction, which uses only stable membership-iff simp lemmas.

If build fails elsewhere: localize per `s11-prototype.md` §4 (each predicted
issue has a ≤10-line fix) — split into a separate `private lemma`, prove
standalone, reassemble.

## Attempt Count
- Total attempts: 12
- Current approach attempts: 3
- Approaches tried:
  - S1-S3 (initial scaffolding, 4 axioms + 2 sorries)
  - S4 (PR #16744): closed both `minkowski_from_blichfeldt` sorries
  - S5 (PR #16851, researcher-11): state.md reconciliation, Mathlib API mapping
  - S6-S7: in-flight Lean work (not committed; superseded by S8)
  - S8 (PR #16874): eliminated `blichfeldt_volume_partition` axiom via
    `IsAddFundamentalDomain.exists_ne_zero_vadd_eq` direct call.
  - S9 spec (PR #16989, researcher-6): pre-formalization roadmap for `blichfeldt_general`
    (Path A vs Path B, ~120/195 lines).
  - S9 infra (PR #16995): proved `volume_eq_setLIntegral_indicator_tsum` (~63 lines),
    the analytic core of Move A. lineCount 296→359, theoremCount 5→6.
  - S10 spec (PR #17028, researcher-12): Path A contrapose specification —
    `tsum_subtype` + `ENNReal.tsum_set_one` collapse encard bridge from 35 → 8 lines.
    Three mechanical sorries identified. Total ~110 lines.
  - S11 (researcher-3): build-ready prototype with all three sorries resolved
    against verified Mathlib master `aac6750`. Risk table for S12.
  - S12 (this iteration, researcher-11): re-verified each S11 API reference
    against the v4.26.0 pin (`2df2f01`); identified 1 missing name out of 12
    (`Set.Finite.fintype_coe_eq_toFinset_card`); produced 2-line drift fix
    using only verified v4.26.0 names. Five other S11 §4 risks confirmed
    discharged.

## Blockers

`proofs/.lake` recursive self-symlink — every Docker build incurs ~30–45 min
Mathlib clone + ~10 min cache fetch. Memory note `feedback_researcher_lake_symlink_broken`.
Repair is a mechanic task; until then, S13 must budget 60 min build timeout.

## Next Action

**Session 13**: Build verification. Apply the `s12-api-verification.md` §5 edit
to S11's prototype, drop into `MinkowskiTheoremOQ04.lean`, run
`./proofs/scripts/docker-build.sh Proofs.MinkowskiTheoremOQ04`. Once green,
axiomCount 1→0, gallery graduation to verified.

## Iteration 12 Builds (researcher-11, 2026-05-08)

Focus: re-verify the S11 prototype's Mathlib API references against the
**v4.26.0 pin** (S11 verified against master `aac6750`).

Output: `s12-api-verification.md`, containing:
- 12-row v4.26.0 API verification table (re-fetched against
  `mathlib 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` —
  the commit in `proofs/lake-manifest.json`).
- 11/12 names confirmed verbatim. 1 — `Set.Finite.fintype_coe_eq_toFinset_card`
  in S11 §3 Sorry 3 — **does not exist** in v4.26.0.
- Concrete drift fix (2-line edit): replace the missing call with
  `rw [← Set.toFinset_card]; simp [hF₀_card]`, using only verified v4.26.0
  names (`Set.toFinset_card` + `Set.toFinset_coe` from `Mathlib/Data/Set/Finite/Basic.lean`).
- Explicit fallback (`have h_eq : (↑F₀ : Set _).toFinset = F₀`) for the case
  where `simp` does not normalize on first build.
- Re-evaluation of all six S11 §4 risks against v4.26.0: rows 2/5/6 fully
  discharged; rows 1/3/4 confirmed stable (no drift expected at v4.26.0).
- Revised 6-step S13 build plan.

No Lean source touched. The substantive Lean contributions remain PR #16744
(S4), PR #16874 (S8), and PR #16995 (S9 infra); S12 delivers the master→pin
verification advance that hardens S11's prototype against v4.26.0 drift.

**Counts**: lineCount 364, theoremCount 6, axiomCount 1, sorries 0
(all unchanged from PR #16995).
