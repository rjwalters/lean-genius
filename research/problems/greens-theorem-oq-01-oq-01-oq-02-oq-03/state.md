# Current State

**Phase**: OBSERVE
**Since**: 2026-05-11 (S1)
**Iteration**: 1
**Owner**: researcher-1

## Current Focus

S1 (researcher-1): Audit the parent
`Proofs/GreensTheoremOQ01OQ01OQ02.lean` against Mathlib's Bochner
integration API to determine whether the three real-valued
`intervalIntegral_swap` theorems generalize verbatim to a Banach
codomain `E`. Documentation-only iteration; **no Lean
changes.**

## Active Approach

**Mathlib API audit, no Lean changes (S1 OBSERVE fallback variant
per memory).**

The parent file is `verified` (0 sorries, 0 axioms) so the
question reduces to a codomain-genericity audit of each Mathlib
lemma the parent invokes. The audit (see `knowledge.md` § "Mathlib
API audit") finds:

- Every Mathlib lemma the parent uses is already stated for
  Bochner-valued integrands (`E : NormedAddCommGroup`,
  `NormedSpace ℝ E`, `CompleteSpace E`).
- The only ℝ-specific element of the parent's proof is four
  `linarith` invocations in the general-case sign analysis,
  which `abel` replaces directly (the underlying identity is
  additive-abelian-group, not order-theoretic).

**Conclusion**: The Bochner generalization is "free" — port the
parent's three theorems with `f : ℝ → ℝ → E`, replace
`linarith → abel`, ship.

## Blockers

None mathematical.

Practical (build): the `proofs/.lake` symlink in the researcher
worktree points to itself (memory note
[feedback_researcher_lake_symlink_broken.md]), so any Docker
build will be a fresh ~25-minute clone. Strict text-only
iterations (this S1) are unaffected; S2+ should plan
≥45 min Docker timeouts.

## Next Action

**S2 SCAFFOLD** (next iteration): Create
`proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ03.lean` containing:

1. `variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]` block (Bochner setup).
2. `theorem intervalIntegral_swap_of_le` for `f : ℝ → ℝ → E` —
   **fully proved** (smallest buildable instance demonstrating
   the codomain genericity), since the parent's ordered-case
   script is already codomain-agnostic.
3. `theorem intervalIntegral_swap` for `f : ℝ → ℝ → E` —
   `:= by sorry` (defer the 4-case sign analysis to S3, where
   `linarith → abel` substitution is exercised).
4. `theorem intervalIntegral_swap_of_continuous` for
   `f : ℝ → ℝ → E` — `:= by sorry` (depends on the general case).
5. Companion file
   `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ03Aristotle.lean`
   for routine helpers (`flip_bounds_E`, `neg_outside_E`) so
   Aristotle can attempt them in parallel.

Include sibling-style header docstring summarizing the
generalization claim and the `linarith → abel` rationale.

**S3** (after S2 build-verifies): port the general 4-case proof
using `abel`. **S4**: continuous case + gallery entry +
`src/data/proofs/<slug>/{meta.json, index.ts, annotations.json}`.

## Session log

- **S1** (researcher-1, 2026-05-11): OBSERVE — Mathlib API
  audit, codomain-genericity classification, `linarith → abel`
  identification. Documentation-only; no Lean changes.
  Deliverables: `problem.md`, `knowledge.md`, `state.md`,
  `src/data/research/problems/<slug>.json`.
