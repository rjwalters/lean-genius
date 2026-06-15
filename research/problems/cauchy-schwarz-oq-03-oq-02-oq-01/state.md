# Research State: cauchy-schwarz-oq-03-oq-02-oq-01

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-14
**Iteration**: 1

## Current Focus
Reverse Minkowski inequality for `0 < p < 1`:
`(∑(a_i+b_i)^p)^(1/p) ≥ (∑a_i^p)^(1/p) + (∑b_i^p)^(1/p)` (nonneg a,b). Statement,
equality locus (proportional), and proof route pinned and numerically certified.

## Active Approach
**Route 1 — reverse Hölder** (mirrors the parent's "Minkowski from Hölder"):
prove `reverse_holder` (negative conjugate `q=p/(p-1)<0`, `v>0`) from forward
`NNReal.inner_le_Lp_mul_Lq` by exponent substitution, then derive
`reverse_minkowski` via the two-Hölder split + division by `(∑(a+b)^p)^{1/q}`.
~150–250 LOC, Docker-gated. Route 2 (quasi-norm concavity) is the fallback.

## Attempt Count
- Total attempts: 0 (survey only; no Lean built)
- Current approach attempts: 0
- Approaches tried: 1 (reverse-Hölder route — viable, numerically validated)

## Blockers
- **Verification blackout (2026-06-14)**: Docker daemon down (`docker info` 15s
  timeout) and Aristotle MCP `prove` → "Resource not found" (probed). No Lean
  build possible, so the ~150–250 LOC formalisation is build-gated. The ORIENT
  (statement, Mathlib survey at pin v4.26.0, numerical cert, ACT plan) is
  build-free and complete.
- **Mathlib gap (genuine, not wiring)**: no reverse Hölder / reverse Minkowski /
  `0<p<1` quasi-norm concavity in Mathlib; every Hölder lemma is gated on
  `HolderConjugate` (⇒ p,q>1). The reverse direction must be built.

## Next Action (when Docker recovers)
1. Implement Route 1 in `Proofs/CauchySchwarzOQ03OQ02OQ01.lean`
   (namespace `ReverseMinkowski`): `reverse_holder` → `reverse_minkowski`,
   `p=1/2` instance, signed-real corollary. Confirm at build: negative-exponent
   casts (`v_i^{p/(p-1)}`, keep `v_i>0`) and the `1/q<0` division flip.
2. Build: `./proofs/scripts/docker-build.sh Proofs.CauchySchwarzOQ03OQ02OQ01`.
3. Add gallery entry `src/data/proofs/cauchy-schwarz-oq-03-oq-02-oq-01/`.
4. Re-run `verify_reverse_minkowski.py` to re-confirm artifacts.

## Dead Ends
- `rpow_add_le_add_rpow` ((a+b)^p≤a^p+b^p, 0≤p≤1) does **not** prove reverse
  Minkowski — it gives the outer **upper** bound `LHS ≤ (X+Y)^(1/p)`, wrong
  direction (see knowledge.md (C4)).
- Instantiating `NNReal.Lp_add_le` with `p<1` is impossible (`hp : 1 ≤ p`).
