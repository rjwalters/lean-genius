# Research State: elementary-quadratic-reciprocity-oq-01-oq-01-oq-01-oq-02

## Current State
**Phase**: COMPLETED — verified, sorry-free, axiom-free
**Path**: single-session ACT (S1 OBSERVE+ACT combined; researcher author + sources merged 2026-05-07)
**Since**: 2026-05-07
**Last Updated**: 2026-05-16T14:40:00Z (S2 RETRO-BOOTSTRAP, researcher-4)
**Iteration**: 2

## Status Summary

| Field | Value |
|---|---|
| Phase | COMPLETED |
| Primary Lean file | `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ01OQ01OQ02.lean` |
| File size | 252 LOC (actual; JSON leanFiles[i] says 254 — minor +2 mechanic-drift) |
| Theorems / Sorries / Axioms / Defs | 11 / 0 / 0 / 1 |
| Build status | verified (PR #16443 docker-built post-merge per `knowledge.md` Session 1 notes) |
| Gallery entry | `src/data/proofs/elementary-quadratic-reciprocity-oq-01-oq-01-oq-01-oq-02/` (per `knowledge.md` Files Modified) |
| Tier / Significance / Tractability | B / 6 / 6 |
| Tags | `seeker-selected` |

## Outcome (S1, 2026-05-07)

**Answer**: **YES** — the full Gauss sum proof of quadratic reciprocity
(all four classical steps) assembles into a single Lean 4 proof with 0
sorries and 0 axioms.

The slug's gallery entry was submitted in PR #16443 (initial ACT) and
enriched in PR #16579 (enricher-2, merged 2026-05-07T16:58Z). An audit
PR (#16457, merged 2026-05-07T00:47Z) marked the slug clean.

### What S1 delivered

(Summarized from `knowledge.md` Session 2026-05-07 — that file remains
the authoritative substantive doc for the assembly; this state.md is
the orientation index.)

1. **`legendreCharQ`** — the Legendre character as a `MulChar (ZMod p)
   (ZMod q)` built via `ringHomComp Int.castRingHom`. The bridge
   between the abstract character identity and the concrete `legendreSym`
   formula.
2. **`legendreCharQ_neg_one`** — `χ(−1) = (−1)^(p/2)` via
   `legendreSym.at_neg_one` + `chi4_eq_neg_one_pow` (first supplement).
3. **`legendreCharQ_eval_q`** — `χ(q) = legendreSym p q` via
   `legendreSym` unfold + `norm_cast`.
4. **`gauss_sum_char_identity`** (Step 4) — uses
   `FrobeniusStepQR.qr_gauss_sums_identity` and the assembled character
   identity `(χ(−1)·p)^{(q−1)/2} = χ(q)` from `OQ01OQ01OQ02.lean`.
5. **ZMod-q assembly** — `(−1)^(p/2 · q/2) · legendreSym q p =
   legendreSym p q` (in `ZMod q`) via Euler's criterion
   (`legendreSym.eq_pow`).
6. **Main theorem** —
   `legendreSym p q * legendreSym q p = (−1)^(p/2 · q/2)`
   (the classical QR statement in integer-Legendre form).

### Pre-existing parent-file API drift fixed during S1

* `OQ01OQ01OQ02`: `exact_mod_cast fun h => hpq h.symm` →
  `exact_mod_cast hpq.symm` (Lean type-inference change in newer
  versions).
* `OQ01OQ01OQ02`: removed erroneous `.symm` in
  `gauss_qr_pathway_complete`.
* Added private `Fact` instances for concrete examples in both
  `OQ01OQ01OQ01.lean` and `OQ01OQ01OQ02.lean`.

## S2 RETRO-BOOTSTRAP (researcher-4, 2026-05-16)

S1 was a single-session FRESH ACT documented in `knowledge.md` only
(no `state.md`, no `problem.md`, no `sessions/` directory). S2 is a
doc-only retro-bootstrap that adds the missing scaffolding so the slug
matches the rest of the gallery's convention. Scope:

1. NEW `state.md` (this file).
2. NEW `problem.md` — formal restatement of the question + the slug's
   main theorem Lean signature + non-claims.
3. NEW `sessions/2026-05-16-s2-retro-bootstrap.md` — this session's
   memo with verification commands + leanFiles drift note.
4. JSON `currentState.iteration` 1 → 2 + `currentState.focus` refresh
   + `lastUpdate` refresh.

S2 does **not** touch:

* `knowledge.md` — substantive content is preserved as-is (the
  Session 2026-05-07 entry is the canonical record of S1 work).
* `leanFiles[i]` for this slug — JSON has `lineCount=254` vs actual
  `252` (minor +2 drift, likely from S1 author counting pre-final
  whitespace). Mechanic territory; informational handoff in S2 memo §3.
* `proofs/Proofs/` — slug is verified and on origin/main since
  2026-05-07; zero proof delta.
* `src/data/proofs/<slug>/` (gallery dir) — out of S2 scope.
* `lake-manifest.json`, `lakefile.toml`, `proofs/Proofs.lean` — out of
  S2 scope.

### Files modified (S2 narrow)

- `research/problems/elementary-quadratic-reciprocity-oq-01-oq-01-oq-01-oq-02/state.md` — NEW.
- `research/problems/elementary-quadratic-reciprocity-oq-01-oq-01-oq-01-oq-02/problem.md` — NEW.
- `research/problems/elementary-quadratic-reciprocity-oq-01-oq-01-oq-01-oq-02/sessions/2026-05-16-s2-retro-bootstrap.md` — NEW.
- `src/data/research/problems/elementary-quadratic-reciprocity-oq-01-oq-01-oq-01-oq-02.json` — 3 field updates (currentState.iteration, currentState.focus, lastUpdate).

No `.lean` files touched. No Docker build (zero proof delta).

### Pool side-effect (out-of-PR)

`scripts/research/claim-problem.sh update elementary-quadratic-reciprocity-oq-01-oq-01-oq-01-oq-02 completed`
ran out-of-band; `.lean/state/candidate-pool.json` is gitignored.

## Session History

* **Session 1** (researcher author + sources merged 2026-05-07): full
  four-step Gauss sum QR assembly proved in
  `ElementaryQuadraticReciprocityOQ01OQ01OQ01OQ02.lean` (NEW, ~252
  lines, 11 theorems, 1 def, 0 sorries, 0 axioms). PR #16443 (ACT) +
  PR #16579 (enricher-2 follow-on). Pre-existing parent-file API
  drift fixed simultaneously. Substantive notes in `knowledge.md`.
* **Session 2** (researcher-4, 2026-05-16): RETRO-BOOTSTRAP — added
  `state.md`, `problem.md`, `sessions/`; refreshed JSON
  `currentState.iteration` 1→2 + `lastUpdate`. Doc-only; preserved
  `knowledge.md` and Lean source verbatim.

## Active Approach

**None** — slug is COMPLETED. The Gauss-sum four-step assembly is
proved sorry-free and axiom-free; the question is answered YES.

## Next Action

**None** — slug is COMPLETED.

Optional follow-ups (low-priority, none load-bearing):

1. Mechanic refresh of `leanFiles[i]` `lineCount` for
   `ElementaryQuadraticReciprocityOQ01OQ01OQ01OQ02.lean` (`254 → 252`).
   See S2 memo §3.

## References

* `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ01OQ01OQ02.lean`
  — 252 LOC, 11 theorems, 1 def, 0 sorries, 0 axioms; slug's primary
  Lean file. The main theorem
  `legendreSym p q * legendreSym q p = (−1)^(p/2 · q/2)` lives here.
* `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ01OQ01.lean`
  — proves τ² = χ(−1)·p (step 2 of the four-step proof); 0/0/0.
* `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ01OQ02.lean`
  — proves Frobenius step + assembled character identity (step 3); 0/0/0.
* `research/problems/elementary-quadratic-reciprocity-oq-01-oq-01-oq-01-oq-02/knowledge.md`
  — authoritative substantive record of S1 work (Session 2026-05-07).
* PR #16443 (S1 ACT) — initial assembly proof.
* PR #16457 (audit, merged 2026-05-07T00:47Z) — marked clean.
* PR #16579 (enricher-2, merged 2026-05-07T16:58Z) — enrichment.
* Mathlib `legendreSym.quadratic_reciprocity` — final integer lift.
* Mathlib `legendreSym.eq_pow` — Euler's criterion.
* Mathlib `legendreSym.at_neg_one` — first supplement.
