# Current State

**Phase**: ACT (S1 OBSERVE/ACT scaffold delivered)
**Since**: 2026-05-12 (S1 iteration, researcher-1)
**Iteration**: 1

## Current Focus

S1 scaffold landed: `proofs/Proofs/MinpolyCharpolyOQ03OQ01.lean` (187 lines,
3 definitions, 3 theorems, 1 instance, 3 sorries). Gallery entry added at
`src/data/proofs/minpoly-charpoly-oq-03-oq-01/`.

Deliverables fixed in API:

* `xModule M = Module.AEval' M.mulVecLin` (the F[X]-module synonym)
* `xModule.instFinite : Module.Finite F[X] (xModule M)` — **unconditional**,
  via `Module.AEval.instFinitePolynomial`. No sorry.
* `xModule_isTorsionBy_charpoly` — Cayley-Hamilton on AEval'. Sorry-guarded.
* `xModule_isTorsion` — the deliverable consumed by OQ-03-OQ-02. Sorry-guarded.
* `xModule_has_invariantFactorChain` — bridge to parent's main theorem.
  Sorry-guarded.

## Active Approach

Mathlib's existing `Module.AEval'` synonym + `M.mulVecLin` gives the F[X]-module
structure for free; the instance pipeline gives Module.Finite for free; only
the IsTorsion proof requires manual work (Cayley-Hamilton transported across
the standard-basis algebra equivalence).

## Blockers

None at the strategy level. The S2+ task is mechanical:

1. Discharge `xModule_isTorsionBy_charpoly` (~30-50 lines): combine
   `Matrix.aeval_self_charpoly` with the algebra equivalence
   `Matrix.toLinAlgEquiv (Pi.basisFun F n) : Matrix n n F ≃ₐ[F] (n→F →ₗ[F] n→F)`.
   Key fact: aeval commutes with algebra homomorphisms.
2. Discharge `xModule_isTorsion` from (1) + `charpoly_monic` (~10-15 lines).
3. Discharge `xModule_has_invariantFactorChain` from (2) +
   `Module.equiv_directSum_of_isTorsion` (this is actually OQ-03-OQ-02
   territory; we keep the statement here only to fix the API surface).

## Next Action

Next iteration should pick:

1. **S2 ACT** — discharge `xModule_isTorsionBy_charpoly` by:
   a. Lift `Matrix.aeval_self_charpoly` across `Matrix.toLin'`'s
      algebra-hom property to get `aeval M.mulVecLin M.charpoly = 0`
      as a LinearMap.
   b. Unfold `Module.AEval'`'s smul to relate it to the LinearMap action.
   c. Conclude `M.charpoly • x = 0` for any `x : xModule M`.

   Estimate: ~30-50 lines. Self-contained; no Mathlib gap.

2. **S3 ACT** — discharge `xModule_isTorsion` from S2's result +
   `Matrix.charpoly_monic`. The conversion `Monic ⇒ nonZeroDivisor` in
   an integral domain F[X] is standard Mathlib API. Estimate: ~10-15 lines.

3. **OQ-03-OQ-02 SCAFFOLD** — start the next sub-OQ:
   `MinpolyCharpolyOQ03OQ02.lean` (~300 lines) applies
   `Module.equiv_directSum_of_isTorsion` to extract the invariant-factor
   decomposition. Can begin in parallel with S2/S3 (statements are fixed).

## Attempt Counts

- Total attempts: 1 (S1 scaffold, this session)
- Current approach attempts: 1
- Approaches tried: 1 (Module.AEval' + auto Module.Finite + sorry-guarded IsTorsion)

## Session Log

* **S1 (researcher-1, 2026-05-12)** — created scaffold:
  `MinpolyCharpolyOQ03OQ01.lean` (187 lines, 3 def / 3 thm / 1 instance /
  3 sorries) + gallery entry (`meta.json` with 5 sections, `annotations.json`
  empty, `index.ts`) + manifest import. **Module.Finite F[X] (xModule M)
  is proved unconditionally** (no sorry). IsTorsion + bridging statements
  are sorry-guarded with proof routes documented in detail in the file's
  top docstring and in this state.md's Blockers section.
