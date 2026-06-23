# Research State: inverse-galois-oq-06-oq-01

## Current State

**Phase**: OBSERVE (S2 substantive — state.md ↔ JSON sync + sibling overlap audit; retargeting recommendation pending)
**Path**: full
**Since**: 2026-06-06T08:10:00Z (S2 OBSERVE state-sync iteration)
**Iteration**: 2

## Iteration 2 (researcher-1, 2026-06-06) — S2 OBSERVE substantive: state.md ↔ JSON sync + sibling overlap audit (doc-only)

**Outcome**: OBSERVE complete. state.md replaced template stub from iter 1 (2026-04-04, T+63d) with substantive content matching JSON's prior feasibility survey. Sibling slug `inverse-galois-a5-oq-01` (iter 7, S4h PREP) identified as duplicative on the same axiom-elimination target; retargeting recommendation made.

Full memo at `sessions/2026-06-06-s2-observe-state-sync-sibling-map.md`.

### Local Lean file audit

`Proofs/InverseGaloisOQ06OQ01.lean` exists (255 LOC, 13 thm, **0 sorries, 0 `axiom` declarations** at git HEAD). Six sections cover root counts in ℂ/ℝ, complex conjugation, `gal_card_ne_5`, mod-7 factorization, and a §6 "summary" that **re-uses** the parent `axiom three_dvd_gal_card` rather than eliminating it. So the headline 0-axiom count is *misleading*: the bridge from "mod-7 has irreducible cubic factor" to "3 ∣ |Gal|" still relies on the parent axiom via `theorem three_dvd_gal_card_proved := InverseGaloisA5.three_dvd_gal_card` (line 252).

### Sibling overlap

`inverse-galois-a5-oq-01` works on the **same target axiom** (`three_dvd_gal_card` in `InverseGaloisA5.lean`) via Frobenius at p=7. Iter 7 (S4h PREP, 2026-06-02): paste-ready 32-LOC sub-step (a) typeclass plumbing, 16-bearer set 7× attested at pin SHA `2df2f0150c…` across a 17-day window, zero drift. This slug at iter 1 was racing the sibling without coordination — state-sync this iteration prevents further wasted effort.

### Three options recommended (deployer/champion picks)

| Option | Action | Pro | Con |
|---|---|---|---|
| **A** Subsume | mark this slug `subsumed`; redirect to sibling | avoids race | strands 255 LOC of local infra |
| **B** Retarget (recommended) | reframe as **general Dedekind upstream** track, A5 evidence as unit test | aligns with problem.md; high upstream value | 300-500 LOC, multi-month, very high risk |
| **C** Status quo | keep slug as A5-specific mod-7/cubic infra | no churn | semantics drift (title says general, scope is A5) |

**Preferred**: Option B with explicit retarget amendment. Anti-recommendation: do NOT spawn a parallel Frobenius track on this slug — sibling already owns it.

### Next Action

**Preferred** (S2-bis, doc-only): write a problem.md / JSON retargeting amendment framing the slug as the general Dedekind theorem upstream track, with a `subsumes` / `subsumedBy` link to the sibling slug. Defer pool-status reconciliation to deployer/champion.

**Alternative** (S3 ORIENT): pivot to Option C (status quo); extend the local Lean file to cover `gal_card_ne_20` (~40 lines, A₅ simple → no order-20 subgroup per JSON `insights[3]`). Bounded scope, immediate ACT-shippable.

**Conservative**: pause this slug at S2 OBSERVE-substantive (this iteration) until a human / deployer / champion picks Option A/B/C. State.md sync is the value delivered this iteration.

### Anti-scope (S2 OBSERVE)

- No Lean diff. Local `InverseGaloisOQ06OQ01.lean` untouched.
- No `meta.json` edit on parent `inverse-galois-oq-06` gallery entry.
- No bearer audit (sibling has 7× attestations at the same pin).
- No retargeting commitment — Options A/B/C presented; pick deferred to deployer/champion.
- No coordination edit on sibling slug.

### Files modified (S2 doc-only)

- `research/problems/inverse-galois-oq-06-oq-01/sessions/2026-06-06-s2-observe-state-sync-sibling-map.md` (new, ~140 LOC, 9 sections).
- `research/problems/inverse-galois-oq-06-oq-01/state.md` — this file, replaced template stub with iter-2 substantive head.
- `src/data/research/problems/inverse-galois-oq-06-oq-01.json` — `currentState.{phase, since, iteration 1→2, focus, nextAction}` + `lastUpdate`.

### Counts (no Lean file authored or modified this iteration)

- Local Lean file `InverseGaloisOQ06OQ01.lean`: 255 LOC, 13 thm, 0 sorries, **transitively 1 axiom** (via re-use of `InverseGaloisA5.three_dvd_gal_card` at line 252) — honest count, not the literal "0 axioms in this file" cached in JSON `leanFiles[].axiomCount`.

---

## (Historic) Iteration 1 (2026-04-04 — auto-created from template, no substantive work)

**Phase**: OBSERVE
**Path**: fast
**Since**: 2026-04-04T02:41:25-07:00
**Iteration**: 1

Template-stub state from slug creation. Focus: "Initial problem understanding. Read problem.md and gather context." Next action: "Fast path: Quick Mathlib search, then directly to ACT if obvious approach found."

The JSON `currentState.focus` already captured a substantive feasibility survey ("|Gal| ∈ {5,10,60}; eliminate 5 and 20; D₅ hard via Dedekind") at slug creation time (2026-04-04T09:42:47Z), but this state.md was never updated to match. T+63d gap until iter 2 reconciliation.
