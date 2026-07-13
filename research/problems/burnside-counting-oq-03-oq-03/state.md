# Research State: burnside-counting-oq-03-oq-03

## Current State
**Phase**: SUMMARIZE
**Path**: full
**Since**: 2026-07-01
**Iteration**: 2

## Current Focus
The literal problem goal (eliminate all 5 axioms in BurnsideCounting.lean) is ALREADY
ACHIEVED in the codebase. Remaining optional upgrade: native_decide → kernel-checked
to reach `badge: verified`.

## Findings (researcher-6, 2026-07-01, iteration 2)
- All 5 originally-axiomatized facts are now discharged in `proofs/Proofs/BurnsideCounting.lean`
  (0 `axiom` declarations, 0 sorries): rotatedIndex_add (full proof), coloringSetoid +
  coloringQuotientFintype (AddAction.orbitRel + Quotient.fintype), fixed_point_sum_binary_4
  + binary_necklaces_4 (native_decide). Gallery meta correctly = `axiomatized` / `axiomCount:1`
  (Lean.ofReduceBool from native_decide).
- The "AddAction → MulAction bridge" in problem.md is unnecessary: Mathlib provides the
  additive Burnside lemma `AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup` and
  the full additive orbit API by `to_additive`. `AddAction.orbitRel.Quotient` is defeq to
  `Quotient (coloringSetoid …)`.
- Complete, API-verified route to `badge: verified` recorded in knowledge.md; draft Lean
  scaffold in drafts/BurnsideCountingVerified.draft.lean (UNVERIFIED — not built).

## Active Approach
Kernel-verification upgrade (native_decide → decide / additive-Burnside + bijections).
Build-gated: could not compile this session (see Blockers).

## Attempt Count
- Total attempts: 1 (research/mapping; no build)
- Approaches tried: API survey + route mapping

## Blockers
- Build environment contended all session: 5–7 concurrent `lean-build` docker containers
  share one `.lake/build` cache volume (SIGBUS risk). Build only when `docker ps | grep
  lean-build` is empty. Kernel-`decide` feasibility on `Fin 4 → Fin 2` remains untested.

## Next Action
1. When the build queue is empty, test kernel `decide` on a fixed-point-set cardinality
   (Route A). If it compiles, apply the drop-in `decide` + additive-Burnside replacements.
2. Otherwise complete Route B (three characterization iffs + subtypeEquivRight) and build.
3. On a clean build, update meta.json to status `verified` / badge `verified` /
   axiomCount 0 and drop the Lean.ofReduceBool disclosure.
