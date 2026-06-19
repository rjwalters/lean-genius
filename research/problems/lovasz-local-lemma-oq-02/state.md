# Research State: lovasz-local-lemma-oq-02

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-19 (S2, researcher-3)
**Iteration**: 2

## Current Focus
Closing the sole sorry in `proofs/Proofs/LovaszLocalLemmaOQ02.lean`:
`lllThreshold_strict_maximum` — strict maximum / uniqueness of the maximizer
`x·(1-x)^d < T(d)` for `x ∈ [0,1]`, `x ≠ 1/(d+1)`.

## Active Approach
**Strict weighted AM-GM equality case.** Primary tool:
`geom_mean_lt_arith_mean_weighted_iff_of_pos` (Mathlib/Analysis/MeanInequalities.lean:254).
The AM-GM equality case `z₀ = z₁` reduces exactly to `xr = 1/(dr+1)`, so `x ≠ 1/(d+1)`
gives strict AM-GM, which propagates through the same rpow chain the (already-proved)
non-strict `lllThreshold_is_maximum` uses. Forward `<` route preferred; backward
equality-contradiction route (`geom_mean_eq_arith_mean_weighted_iff'`) is the fallback.

Full skeleton + API map:
`sessions/2026-06-19-s2-orient-strict-maximum-amgm.md`.
The in-file `sorry` comment now carries the actionable proof outline.

## Attempt Count
- Total attempts: 0 (ORIENT only; no ACT build yet)
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None mathematical. ACT must build **solo** (7.65 GB Docker VM OOM-kills concurrent
mathlib builds) — wait for an empty `lean-build-*` container slot before verifying.

## Next Action
ACT: replace the sorry following the preferred forward route in the session memo;
build solo via `./proofs/scripts/docker-build.sh Proofs.LovaszLocalLemmaOQ02`; on green
+ clean `#print axioms`, flip gallery meta to verified/original and `leanFile.sorries 1→0`.

## Notes / corrections to prior knowledge
The `knowledge.md` "dead end" (full LLL tightness needs measure-theoretic
`ProbabilityTheory`) does **not** apply to this lemma: `lllThreshold_strict_maximum` is
the purely algebraic uniqueness of the maximizer of `x·(1-x)^d` and is fully formalizable
with existing real-analysis API. Scope is already correctly reduced in the Lean file.
