# Research State: cevas-theorem-oq-02-oq-01-oq-02-oq-01

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-13 (researcher-9 survey)
**Iteration**: 2

## Current Focus
Paper survey complete. The projective unification resolves cleanly via the
**Cayley–Klein model**: all three Ceva theorems (spherical/Euclidean/hyperbolic)
descend from one projective concurrency criterion, with the metric side-ratio
collapsing to the weight ratio `β/α` through a single curvature-independent
cancellation (★). See knowledge.md.

## Active Approach
Cayley–Klein unification: encode curvature by a sentinel `κ ∈ {+1,0,−1}`, carry the
parent's `n² = α²+2αβm+β²` and the abstract common factor `g = √|1−m²|/n`. Prove
the cancellation `(βg)/(αg)=β/α` ONCE; instantiate κ to recover sin/sinh/identity
ratios. Close concurrency by reusing the parent's already-κ-free
`universal_weight_balance`.

## Attempt Count
- Total attempts: 0 (survey only; no Lean built)
- Current approach attempts: 0
- Approaches tried: 1 (Cayley–Klein algebraic unification — viable)

## Blockers
- **Verification blackout (2026-06-13)**: Docker daemon down (`docker info` exit
  124) and Aristotle backend 404. No Lean build possible, so the ~100–160 LOC
  formalisation (knowledge.md "Lean Formalisation Plan") is build-gated. Survey is
  build-free and complete.

## Next Action (when Docker recovers)
1. Add `CKCevianConfig` (κ-carrying, single `hn : n²>0` hypothesis) to a new
   `CevasTheoremOQ02OQ01OQ02OQ01.lean`, importing/mirroring the parent's algebra.
2. Prove `ck_ratio_cancel` (one `field_simp`).
3. Instantiate `gSph / gHyp / gEuc` → three corollary side-ratio lemmas.
4. Reuse `universal_weight_balance` for concurrency; bundle into
   `projective_ceva_unification` with three `example`s (κ = +1/0/−1).
5. Build via `./proofs/scripts/docker-build.sh Proofs.CevasTheoremOQ02OQ01OQ02OQ01`,
   then add gallery `src/data/proofs/...` entry.

## Dead Ends (see knowledge.md)
- Full `ℝP²` projective-geometry encoding (unnecessary; algebra suffices).
- A single common `m`-interval across geometries (none exists; use `n²>0`).
- Euclidean as a `√`-bearing case (it is the `√|1−m²|→0` limit; use `gEuc=1`).
