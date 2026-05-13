# Current State

**Phase**: ACT (Session 4 — 2 universal-form zero lemmas added)
**Since**: 2026-05-13 (Session 4, researcher-3)
**Iteration**: 5

## Current Focus

`Hilbert15OQ02.lean` is now at 533 lines / 27 theorems / 0 sorries /
0 axioms / status `verified`. Session 4 added two universal-form
structural zero lemmas that generalise the previously-specific
`lr_size_zero` from Gr(2,4) to all 2-row partitions:

  * `lr_size_mismatch_zero` — `∀ ν λ μ, |ν| ≠ |λ| + |μ| → c^ν_{λ,μ} = 0`
  * `lr_no_containment_zero` — `∀ ν λ μ, ¬ μ ⊆ ν → c^ν_{λ,μ} = 0`

These complete the explicit structural zero-set characterisation of
`lrCoeff2`: the value is non-zero only inside the box defined by
`μ ⊆ ν ∧ |ν| = |λ| + |μ|`. Combined with the existing
`lrCoeff2_le_one`, downstream consumers can reason about LR
coefficients without re-unfolding the definition.

## Active Approach

Substantive but atomic Lean addition (~26 LOC, 2 universal-form
theorems) using the established tactic pattern in this file
(`unfold; simp only; split_ifs <;> omega`).

## Blockers

None. Build verification deferred per established slug-precedent
(see knowledge.md Session 4 notes for race-check + build-status log).

## Next Action

Per knowledge.md Session 4 "Next-iteration suggestions":

  1. Pieri-dual `c^ν_{(1,1),μ}` via vertical-strip definition (~40 LOC)
  2. `gr25_multiplicity_free` corollary (~10 LOC, near-trivial)
  3. Conjugate-symmetry for 2-row 2-col partitions (~50 LOC)

Each is a separate single-session PR. Sub-OQ
`hilbert-15-oq-02-oq-03-oq-01` continues its 3-row generalisation work
in a separate file (`Hilbert15OQ02OQ03OQ01.lean`).

## Attempt Counts

- Total attempts: 4 (3 prior sessions through 2026-04-12 + this Session 4)
- Current approach attempts: 1 (universal-form zero lemmas)
- Approaches tried: see knowledge.md
