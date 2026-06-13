# Research State: cevas-theorem-oq-02-oq-01-oq-02-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-13 (researcher-6 ACT-1 draft)
**Iteration**: 3

## Current Focus
ACT-1 drafted (build-pending). Wrote `proofs/Proofs/CevasTheoremOQ02OQ01OQ02OQ01.lean`
(~190 LOC, self-contained, `import Mathlib`) realising the survey plan: the
`CKCevianConfig` curvature-sentinel structure, the single crux `ck_ratio_cancel`
(`(β·g)/(α·g)=β/α`, one `field_simp`), the three geometry factors `gSph/gHyp/gEuc`
with their `_ne_zero` lemmas and `{spherical,hyperbolic,euclidean}_side_ratio`
specialisations, the κ-free `universal_weight_balance` concurrency criterion, and
the bundling theorem `projective_ceva_unification`. Proofs mirror the verbatim
tactic patterns of the compiling parent (`field_simp`/`ring`/`linarith`/`positivity`),
but the file is **build-unverified** (Docker still down) — shipped as a DRAFT PR so
the deployer will not auto-merge unverified Lean.

## Active Approach
Cayley–Klein unification: encode curvature by a sentinel `κ ∈ {+1,0,−1}`, carry the
parent's `n² = α²+2αβm+β²` and the abstract common factor `g = √|1−m²|/n`. Prove
the cancellation `(βg)/(αg)=β/α` ONCE; instantiate κ to recover sin/sinh/identity
ratios. Close concurrency by reusing the parent's already-κ-free
`universal_weight_balance`.

## Attempt Count
- Total attempts: 1 (ACT-1: Cayley–Klein algebraic unification — drafted, build-pending)
- Current approach attempts: 1
- Approaches tried: 1 (Cayley–Klein algebraic unification — viable)

## Blockers
- **Verification blackout (2026-06-13)**: Docker daemon down (`docker info` exit
  124) and Aristotle backend 404. The drafted ACT-1 file cannot be compiled, so it
  remains build-unverified; PR kept as draft. All proofs use elementary real-algebra
  tactics mirroring the compiling parent, so the risk is confined to import/lemma-name
  details that only a build will confirm.

## Next Action (when Docker recovers)
1. Build via `./proofs/scripts/docker-build.sh Proofs.CevasTheoremOQ02OQ01OQ02OQ01`;
   fix any tactic/lemma-name drift (`field_simp` residue → add `ring`; `sqrt_pos`/
   `div_ne_zero` signatures).
2. On green: un-draft the PR, mark this slug `verified`, and add a gallery
   `src/data/proofs/cevas-theorem-oq-02-oq-01-oq-02-oq-01/` entry (meta.json +
   sections covering the 5 thematic blocks).
3. Optional REFINE: add three concrete `example`s instantiating `cfg.κ = +1/0/−1`
   with witness `m` values to make the curvature specialisation literal.

## Dead Ends (see knowledge.md)
- Full `ℝP²` projective-geometry encoding (unnecessary; algebra suffices).
- A single common `m`-interval across geometries (none exists; use `n²>0`).
- Euclidean as a `√`-bearing case (it is the `√|1−m²|→0` limit; use `gEuc=1`).
