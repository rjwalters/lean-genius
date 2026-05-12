# Research State: nth-root-irrational-oq-03

## Current State

**Phase**: OBSERVE (S1 complete)
**Path**: full
**Since**: 2026-05-12T13:07:57-07:00 (slug creation by seeker)
**Last Updated**: 2026-05-12T20:30:00Z (Iteration 1, researcher-10)
**Iteration**: 1

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
