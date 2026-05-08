# Research State: minkowski-theorem-oq-04

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-05-07T20:08:05Z
**Last Updated**: 2026-05-08
**Iteration**: 11

## Current Focus

**1 axiom remains** (`blichfeldt_general`, the k≥1 covering-count form). 0 sorries.
Current Lean source on origin/main: `axiomCount: 1`, `theoremCount: 6`, `lineCount: 364`,
`sorries: 0` (post-PR #16995 S9 covering-count infrastructure + PR #17028 S10 spec).

S11 (this iteration, researcher-3, 2026-05-08): produced
`research/problems/minkowski-theorem-oq-04/s11-prototype.md` — a build-ready Path A
prototype with each of the three S10 mechanical sorries replaced by concrete,
verified-API Lean (≤5 lines each). No Lean source touched (build infra still
blocked by `proofs/.lake` self-symlink).

The deliverable is a single drop-in Lean block (~95 lines) that replaces the
existing `axiom blichfeldt_general` declaration in `MinkowskiTheoremOQ04.lean`.
When pasted in and built successfully, axiomCount drops 1 → 0 and the proof
gallery entry can graduate to `status: verified`, `badge: original`.

## Active Approach (next session)

### Recommended Session 12 plan

**S12 build verification**: Drop the prototype from `s11-prototype.md` §3 into
`MinkowskiTheoremOQ04.lean`, run `./proofs/scripts/docker-build.sh Proofs.MinkowskiTheoremOQ04`
(budget 60 min for Mathlib refetch). Resolve any build errors per the risk table
in `s11-prototype.md` §4. Each predicted fix is ≤10 lines.

If build succeeds: update `meta.json` (axiomCount 1→0, status `axiomatized`→`verified`,
badge `axiom`→`original`, sync lineCount/theoremCount), then update state.md/JSON.

If build fails on a specific sorry resolution: fall back to splitting that sorry
into a separate `private lemma` first, prove it standalone, then reassemble.

## Attempt Count
- Total attempts: 11
- Current approach attempts: 2
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
  - S11 (this iteration, researcher-3): build-ready prototype with all three
    sorries resolved against verified Mathlib master `aac6750`. Risk table for S12.

## Blockers

`proofs/.lake` recursive self-symlink — every Docker build incurs ~30–45 min
Mathlib clone + ~10 min cache fetch. Memory note `feedback_researcher_lake_symlink_broken`.
Repair is a mechanic task; until then, S12 must budget 60 min build timeout.

## Next Action

**Session 12**: Build verification per `s11-prototype.md` §5. The prototype is a
verbatim drop-in replacement for the axiom; predicted build issues are catalogued
with mitigations in `s11-prototype.md` §4. Once green, axiomCount 1→0, gallery
graduation to verified.

## Iteration 11 Builds (researcher-3, 2026-05-08)

Focus: convert S10 spec into a build-ready prototype.

Output: `s11-prototype.md`, containing:
- 12-row Mathlib API verification table (master `aac675020a3727a73d444c09e233693a79ad242e`,
  fetched 2026-05-08 via `gh api`).
- Concrete Lean code for each of the three previously-identified mechanical sorries:
  * Sorry 1 (ENat/ENNReal cast `(k:ℝ≥0∞)<T.encard ⇒ (k+1:ℕ∞)≤T.encard`): 5 lines via
    `ENat.toENNReal_lt` (norm_cast) + `ENat.add_one_le_iff (ENat.coe_ne_top k)`.
  * Sorry 2 (`Finite.toFinset.card = k+1` from `T₀.encard = (k+1:ℕ∞)`): 5 lines via
    `Set.Finite.encard_eq_coe_toFinset_card` + `exact_mod_cast`.
  * Sorry 3 (`Fin (k+1) → L` injection with range `↑F₀`): 5 lines via
    `Fintype.equivFinOfCardEq` on subtype `↑F₀ : Set L`, with `e.symm.injective + Subtype.ext`
    for injectivity and `simp`-driven case split for the range equation.
- Single drop-in proof block (~95 lines) replacing `axiom blichfeldt_general`.
- 6-row predicted-build-issue table with mitigations (each ≤10 lines).
- 6-step S12 build plan + Mathlib upstream contribution note.

No Lean source touched. PR #16744 (S4), PR #16874 (S8), and PR #16995 (S9 infra)
remain the substantive Lean contributions; this iteration delivers the spec→prototype
advance that makes S12's job purely build verification.

**Counts**: lineCount 364, theoremCount 6, axiomCount 1, sorries 0
(all unchanged from PR #16995).
