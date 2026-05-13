# Research State: nth-root-irrational-oq-03

## Current State

**Phase**: PREP (S4c complete — Mathlib API for S5 ACT verified at pinned rev)
**Path**: full
**Since**: 2026-05-12T13:07:57-07:00 (slug creation by seeker)
**Last Updated**: 2026-05-13T12:30:00Z (Iteration 2, researcher-11)
**Iteration**: 2

## Iteration 1 (researcher-10, 2026-05-12) — S1 OBSERVE

**Outcome**: doc-only — duplicate-detection survey identifying that this slug substantially overlaps existing Hermite-Lindemann / Lindemann-Weierstrass infrastructure.

### What I did

- Inventoried all existing project Lean files related to transcendence of $e$, $\pi$, and the Hermite-Lindemann statement: 6 files totalling 2,623 lines.
- Confirmed `HermiteLindemann.lean:147` axiomatizes the main statement (`axiom hermite_lindemann`); 1 axiom on this file.
- Confirmed sibling `ETranscendentalOQ03.lean` has 2 tractable axioms (`irrational_liouvilleWith_two`, `e_not_liouvilleWith_gt_two`) on the $\mu(e) = 2$ irrationality-measure result.
- Noted the slug's placement under `nth-root-irrational` parent is misleading: parent is *algebraic-irrationality*, this OQ is *transcendence*. The technical content effectively duplicates `e-transcendental-oq-{01,02,03}` plus `HermiteLindemann.lean`.
- Drafted a 4-iteration roadmap focused on **bridge work** (axiom reduction in `ETranscendentalOQ03.lean`) rather than re-formalising Lindemann-Weierstrass from scratch (an 800-1500 line task).
- Generated 0 new mathematical content (no Lean changes); deliverable is documentation only.

### Files Modified

- `research/problems/nth-root-irrational-oq-03/problem.md` (new — refined problem statement, parent mismatch documented)
- `research/problems/nth-root-irrational-oq-03/knowledge.md` (new — literature survey, axiom inventory, three tier-A/B/C target lists)
- `research/problems/nth-root-irrational-oq-03/state.md` (new — this file)
- `src/data/research/problems/nth-root-irrational-oq-03.json` (new — gallery entry with cross-references)

### Knowledge Added

- **Insights**: 4
  1. The "open question" is mostly already infrastructure (axiomatized in HermiteLindemann.lean)
  2. Two tractable adjacent axioms in OQ03 sibling
  3. The full HL axiom is ~900 lines of work — wait for Mathlib upstream PR
  4. Project status is "axiomatized", not "verified"

- **Built items**: 0 (S1 OBSERVE is doc-only)
- **Next steps**: 4 planned iterations (S2-S4 plus optional S5)

## Current Focus

S1 OBSERVE complete. Next session should advance to S2 ACT.

## Active Approach

**S2 plan**: Discharge `axiom irrational_liouvilleWith_two` in `proofs/Proofs/ETranscendentalOQ03.lean` using Mathlib Dirichlet-approximation API. This is the highest-value tractable next step: axiom count 2 → 1 on the relevant file, and the proof is canonical (~30-60 lines).

If Mathlib v4.26.0 API has the needed lemmas, attempt the proof. If not, **document the upstream API gap** as a contribution boundary (memo: file in `research/problems/nth-root-irrational-oq-03/literature/` or as a follow-up Mathlib PR target).

## Attempt Count

- Total attempts: 1 (this S1)
- Current approach attempts: 0 (S2 not yet attempted)
- Approaches tried: 0

## Blockers

None for S1 (doc-only). For S2:

- Mathlib v4.26.0 API compatibility with `LiouvilleWith 2` (low risk).
- Whether `Mathlib.NumberTheory.DiophantineApproximation.exists_q_lt_inv` (or equivalent) exists at the pin.

## Next Action

**Session 2 (S2 ACT)**: Open `proofs/Proofs/ETranscendentalOQ03.lean`. Locate `axiom irrational_liouvilleWith_two` on line 114. Replace with `theorem … := by …`. Prove using Mathlib's Dirichlet approximation API:

```lean
theorem irrational_liouvilleWith_two (x : ℝ) (hx : Irrational x) : LiouvilleWith 2 x := by
  -- LiouvilleWith p x ↔ ∃ C > 0, ∀ᶠ q in atTop, ∃ p, |x - p/q| < C/q^p
  -- Dirichlet: ∀ N ≥ 1, ∃ (p,q) with 1 ≤ q ≤ N, |x - p/q| < 1/(qN) ≤ 1/q^2
  -- Take C := 1, lift Dirichlet pairs to LiouvilleWith infinite family
  sorry
```

Run `./proofs/scripts/docker-build.sh Proofs.ETranscendentalOQ03` to verify. Update axiom count in `src/data/proofs/e-transcendental-oq-03/meta.json` (if such gallery entry exists) from 2 → 1.

**Race-readiness**: Before pushing S2, re-run:
```bash
gh pr list -R rjwalters/lean-genius --search "nth-root-irrational-oq-03" --state all
gh pr list -R rjwalters/lean-genius --search "e-transcendental-oq-03" --state all
git branch -r | grep -E "nth-root-irrational-oq-03|liouvilleWith"
```
to detect parallel work.

## Race Notes (S1)

S1 deliverable scope kept small (4 doc files, no Lean) to ship fast given Wiedijk-100 race-prone slug risk. Pre-write check: 0 open research PRs for this slug; only PR #18263 (seeker batch init) creates the same 3 markdown files — minor expected conflict if #18263 merges first (mine includes substantive content, theirs is a stub).

## Iteration 2 (researcher-11, 2026-05-13) — S4c PREP

**Outcome**: doc-only — verify S4b §4.3's deferred Mathlib API at pinned rev + correct a `rw` direction error in S4b §4.3's `log_transcendental_real` skeleton. Retires 2 of S4b §6 risks; reduces S5 ACT's API-layer blockers to "PR #28013 merge only".

### What I did

- Fetched `Mathlib/Analysis/SpecialFunctions/Complex/Log.lean` at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Confirmed `Complex.ofReal_log` at line 62 with signature `{x : ℝ} (hx : 0 ≤ x) : (x.log : ℂ) = log x`.
- Fetched `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` at the same rev. Confirmed `Real.log_ne_zero_of_pos_of_ne_one` at line 254 with signature `{x : ℝ} (hx_pos : 0 < x) (hx : x ≠ 1) : log x ≠ 0`.
- Verified absence of `LindemannWeierstrass.transcendental_log` at v4.26.0: `gh api .../trees/2df2f0150c...?recursive=1` shows the Lindemann directory contains only `AnalyticalPart.lean` (no `Basic.lean`).
- Fetched PR #28013 head (`3bafffe279084269f91f91b0ea8bafc4ac666bbe`); confirmed `transcendental_log` signature at `Basic.lean:255` matches S4b §4.3's cited form verbatim. PR head SHA + `updated_at` (`2026-05-12T09:28:36Z`) unchanged from S4 PREP — > 28h stale.
- Caught direction error in S4b §4.3: both `rw [Complex.ofReal_log hu_pos.le]` calls need a `←` arrow (the lemma orients `Real.log → Complex.log` but the rewrite is needed `Complex.log → Real.log`). Provided corrected 7-LOC skeleton.
- Flagged S4b §4.1's `rw [Complex.ofReal_exp]` orientation question for S5 ACT verification (local file uses same pattern in compiling code, so direction is some-orientation-correct; not fetched in this PREP to keep scope tight).

### Files Modified

- `research/problems/nth-root-irrational-oq-03/sessions/2026-05-13-s4c-prep-mathlib-api-verify-at-pinned-rev.md` (new — this iteration's report)
- `research/problems/nth-root-irrational-oq-03/state.md` (this entry)

### Knowledge Added

- **Insights**: 3
  1. Both deferred §4.3 lemmas (`Complex.ofReal_log`, `Real.log_ne_zero_of_pos_of_ne_one`) are present at v4.26.0 — no upstream Mathlib gap.
  2. S4b §4.3 has a 2-arrow `rw` direction error that would have caused S5 ACT to fail at `lake build` time; corrected in §3.2.
  3. PR #28013 has been completely dormant since 2026-05-12 09:28 UTC (≥ 28h stale at S4c write-time) — S6 (local re-prove) becomes more likely if no movement in another 1–2 weeks.

- **Built items**: 0 (S4c PREP is doc-only)
- **Risks retired**: 2 of S4b §6 (`Complex.ofReal_log` existence; `Complex.ofRealHom.toAlgHom` instance for `ℤ`-algebra)
- **Next steps**: S5 ACT remains gated on PR #28013 merge; no further PREP work needed at the Mathlib-API layer.

## Current Focus (updated S4c)

S5 ACT remains gated on PR #28013 merge. At the Mathlib-API layer, all bridge dependencies are verified at the pinned rev (`Complex.ofReal_log`, `Real.log_ne_zero_of_pos_of_ne_one`, `IsAlgebraic.algHom`, `Complex.ofRealHom.toAlgHom`, `IsFractionRing.isAlgebraic_iff`). Only `LindemannWeierstrass.{transcendental_exp, transcendental_e, transcendental_pi, transcendental_log}` are PR-#28013-gated.

**Watch-loop cadence**: re-check PR #28013 head SHA + `updated_at` once per 24h. If unchanged for ≥ 1 week (i.e. > 7×24h from `2026-05-12T09:28:36Z`), promote S6 (local re-prove ~700–900 LOC) from "deferred" to "consider scoping". Current count: ~28h stale.

## Active Approach (updated S4c)

**S5 plan (post-merge)**: apply S4 PREP §3.4's 5-LOC bridge for `hermite_lindemann`. Optionally apply S4b §3.2/§3.3 refactors and add `log_transcendental_real` using **S4c §3.2's corrected skeleton** (with `← Complex.ofReal_log` in both rewrite sites).

If PR #28013 stalls past 2026-05-19 (1 week from current `updated_at`), pivot to S6 (Scenario C local re-prove).

## Attempt Count

- Total iterations: 2 (S1 OBSERVE + S4c PREP); intervening S2/S2c/S2d/S3/S3a/S4/S4b are listed in iteration-1 dependents but track separately as merged PRs not state-update iterations
- Current approach attempts: 0 (S5 ACT not yet attempted; gated externally)
- Approaches tried: 0 (no Lean refactor yet)
