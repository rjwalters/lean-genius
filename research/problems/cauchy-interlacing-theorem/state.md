# Research State: cauchy-interlacing-theorem

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-15 (iter 5, researcher-11)
**Iteration**: 5

## Current Focus
First Lean shipped: `lean/CauchyInterlacingMinMax.lean` states the operator-level
keystone (`eigenvalue_eq_iSup_iInf_rayleigh`) and its two closed leaf lemmas —
Sublemma B (`inf_exists_ne_zero_of_finrank_add_gt`, proof attempted) and Sublemma
A (`rayleigh_mem_Icc_of_mem_eigenspan`, `sorry`). These are the `prove_file` leaf
targets from design §5. File is **build-pending** (Aristotle 404; Docker 3/3
containers — no slot). Complements the parallel matrix statement of record on
branch `research/cauchy-interlacing-statement` (#24800), whose keystone is only a
`True` stub.

## Active Approach
Approach A (Courant–Fischer min-max + codim-1 dimension count). See the orient
memo §3. Approach B (secular-equation sign counting) parked as fallback.

## Attempt Count
- Total attempts: 1 (Sublemma B proof attempted in Lean; unverified — no backend)
- Current approach attempts: 1
- Approaches tried: 1 (Approach A, leaf lemmas)

## Blockers
- Mathlib lacks a k-th Courant–Fischer min-max characterization (keystone to build) — CONFIRMED absent on master.
- Infra: Docker build pool full; Aristotle backend 404.
- (Resolved: the "unsorted eigenvalues" blocker — `eigenvalues₀` is sorted/antitone.)

## Next Action
1. ~~API spot-check~~ DONE (iter 3). ~~State keystone + leaf lemmas in Lean~~ DONE
   (iter 5, `lean/CauchyInterlacingMinMax.lean`).
2. When ANY backend returns: submit `CauchyInterlacingMinMax.lean` to Aristotle
   `prove_file` (Sublemma A + B are closed leaf targets), OR `docker-build.sh`
   when ≤2 containers. Reconfirm lemma names (`finrank_bot`, `eigenvalues`,
   `eigenvectorBasis`, `finrank_sup_add_finrank_inf_eq`) against v4.26.0 pin.
3. Prove the keystone max–min identity (design §2) from the leaf lemmas.
4. Bridge to the matrix `sortedEigs` (#24800) via the spectral theorem; assemble
   one-step interlacing (scaffolding §3).
