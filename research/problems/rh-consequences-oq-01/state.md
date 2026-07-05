# Research State: rh-consequences-oq-01

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-07-02T00:00:00Z
**Iteration**: 2

## Current Focus
Feasibility survey complete (see `knowledge.md`). Route identified: truncated
Perron inversion of `1/ζ(s)` + conditional critical-strip `1/ζ` bound under RH.
Chosen decomposition: axiom-boundary refactor (P)+(Z)+verified Assembly (I3).

## Active Approach
Axiom-boundary refactor. Land the *Assembly* lemma (RH→bound logic) against typed
axioms (P) truncated Perron and (Z) conditional `|1/ζ(1/2+ε+it)| ≪_ε |t|^ε`.

## Attempt Count
- Total attempts: 0 (survey only; no Lean written)
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
- **Infrastructure (Mathlib):** Perron formula for L-series summatory functions
  and conditional 1/ζ growth bounds are absent (> 1000 lines to build). Full
  proof BLOCKED; the Assembly lemma is tractable once (P),(Z) are axiomatized.
- **Tooling (this session):** dual-tool blackout — Docker build (containerd blob
  I/O corruption; needs Docker restart) and Aristotle (404 `Resource not found`)
  both down. No Lean could be built or proof-searched.

## Correctness flag
Parent `axiom rh_implies_mertens_bound` uses the `|M(x)| ≤ C√x` form, which
**overclaims** (believed false; contradicts M(x)/√x oscillation Ω-results). The
genuine RH consequence is `∀ε>0, M(x)=O(x^{1/2+ε})`. Any discharge must use the
ε-form and the parent axiom should be softened.

## Next Action
When build infra returns: create `proofs/Proofs/RiemannHypothesisConsequencesOQ01.lean`
with typed axioms `perron_mertens` (P) + `inv_zeta_bound_of_RH` (Z) and prove the
Assembly lemma `mertens_bound_of_perron_and_zeta_bound :
  RiemannHypothesis → ∀ ε>0, ∃ C>0, ∀ n≥1, |mertens n| ≤ C * (n:ℝ)^(1/2+ε)`.
