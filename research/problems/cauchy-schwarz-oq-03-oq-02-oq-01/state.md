# Research State: cauchy-schwarz-oq-03-oq-02-oq-01

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-06-14 (ORIENT) → 2026-06-19 (ACT, completed)
**Iteration**: 2

## Current Focus
Reverse Minkowski inequality for `0 < p < 1`:
`(∑(a_i+b_i)^p)^(1/p) ≥ (∑a_i^p)^(1/p) + (∑b_i^p)^(1/p)` (nonneg a,b).
FORMALIZED and verified (0 sorry / 0 axiom).

## Result (Session 2, 2026-06-19, researcher-2)
New file `Proofs/CauchySchwarzOQ03OQ02OQ01.lean` (namespace `ReverseMinkowski`,
199 LOC, 0 sorries, 0 axioms — only propext/Choice/Quot.sound):

1. `reverse_holder` — reverse Hölder for `0<p<1`, `v>0`:
   `(∑u^p)^(1/p)·(∑v^(p/(p-1)))^(1/(p/(p-1))) ≤ ∑ u·v`.
   Proved from forward `NNReal.inner_le_Lp_mul_Lq` via the substitution
   `P=1/p`, `P'=1/(1-p)` (HolderConjugate, `Real.HolderConjugate.inv_one_sub_inv`)
   on `f=(uv)^p`, `g=v^(-p)`. The negative conjugate `q=p/(p-1)` appears only in
   the conclusion. Final inequality discharged by `NNReal.rpow_le_rpow_iff` (raise
   to power p) + `rpow_add`.
2. `reverse_minkowski` — reverse (super-additive) Minkowski for `0<p<1`,
   `a_i+b_i>0`. Riesz split + two reverse-Hölder applications with weight
   `w=(a+b)^(p-1)` (so `w^q=(a+b)^p`), divide by `(∑(a+b)^p)^(1/q)` using
   `1/p+1/q=1`.
3. `reverse_minkowski_half` — p=1/2 instance `(∑√a)²+(∑√b)² ≤ (∑√(a+b))²`.

Registered in `proofs/Proofs.lean`. Gallery entry
`src/data/proofs/cauchy-schwarz-oq-03-oq-02-oq-01/meta.json` added.
Numerical cert `verify_reverse_minkowski.py` re-run: ALL CHECKS PASSED.

## Attempt Count
- Total attempts: 1 (Route 1 — reverse Hölder; succeeded)
- Approaches tried: 1

## Blockers
- None remaining. (The 2026-06-14 Docker/Aristotle blackout that gated the build
  is resolved: file compiled via `lake env lean` against the pinned Mathlib oleans.)

## Notes / Mathlib gap confirmed
Mathlib (pin v4.26.0) has NO `0<p<1` Hölder / Minkowski / quasi-norm concavity —
every Hölder lemma is gated on `HolderConjugate` (⇒ p,q>1). This file supplies the
reverse direction by substitution. `rpow_add_le_add_rpow` gives only the wrong
(outer upper) bound (caveat C4 in knowledge.md).

## Dead Ends
- `rpow_add_le_add_rpow` ((a+b)^p≤a^p+b^p) → outer UPPER bound, wrong direction.
- Instantiating `NNReal.Lp_add_le` with `p<1` impossible (`hp : 1 ≤ p`).
