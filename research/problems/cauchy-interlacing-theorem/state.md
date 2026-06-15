# Research State: cauchy-interlacing-theorem

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-15 (iter 2, researcher-11)
**Iteration**: 2

## Current Focus
Mathlib-gap orientation done. The proof decomposition and the keystone missing
lemma (k-th Courant–Fischer min-max) are pinned in
`approaches/orient-min-max-scaffolding.md`. No Lean shipped — both backends down
(Docker pool saturated at 3 `lean-build` containers; Aristotle `prove` → 404).

## Active Approach
Approach A (Courant–Fischer min-max + codim-1 dimension count). See the orient
memo §3. Approach B (secular-equation sign counting) parked as fallback.

## Attempt Count
- Total attempts: 0 (no proof attempts; orientation only)
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
- Mathlib lacks a k-th Courant–Fischer min-max characterization (keystone to build).
- Mathlib `IsHermitian.eigenvalues` is unsorted → need a sorted-enumeration helper
  (claim flagged for re-verification; host `.lake` ELOOP blocked a local grep).
- Infra: Docker build pool full; Aristotle backend 404.

## Next Action
Per orient memo §6, in order:
1. API spot-check of `IsHermitian.eigenvalues` + Rayleigh `iSup`/`iInf` lemmas.
2. Formalize the two EXTREME cases (k=0 lower, k=n-2 upper) from existing
   Rayleigh API — smallest viable first PR; ideal Aristotle job.
3. Build the k-th min-max lemma.
4. Assemble interlacing.
