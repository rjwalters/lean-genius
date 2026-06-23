# Can the JPSZ axioms in `Erdos29Problem.lean` be removed using Mathlib?

## Source

- **Proof**: Erdős Problem #29: Explicit Economical Additive Basis (`erdos-29`)
- **Type**: open-question
- **Category**: extension
- **Tractability**: challenging (full removal: person-year scope; sub-goal A: tractable)

## Problem Statement (original)

The JPSZ axioms (`JPSZ_set`, `JPSZ_is_basis`, `JPSZ_is_economical`) fail to load in Aristotle due to `harmonicSorry` axioms. Can the JPSZ construction be formalized in Lean WITHOUT axioms, using Mathlib's existing library for hash functions, pseudorandomness, or derandomization?

## Refined target (S1 OBSERVE 2026-05-13)

The parent file `proofs/Proofs/Erdos29Problem.lean` has **5 independent axioms** (`axiomCount: 5`):

| # | Name (line) | Type |
|---|---|---|
| 1 | `JPSZ_set` (L158) | `Set ℕ` |
| 2 | `JPSZ_is_basis` (L164) | `IsAdditiveBasis JPSZ_set` |
| 3 | `JPSZ_representation_bound` (L281) | `∃ C > 0, ∀ n ≥ 2, r_A(n) ≤ exp(C·√log n)` |
| 4 | `JPSZ_explicit` (L419) | `ExplicitSet JPSZ_set` (decidable membership) |
| 5 | `JPSZ_size_optimal` (L489) | `∃ C > 0, ∀ N ≥ 1, |A ∩ [1,N]| ≤ C·√N·√log N` |

Note: `JPSZ_is_economical` is **already a theorem** at L170 (proved from #3 via squeeze). The OQ's original statement is slightly stale.

The OQ refines to: **can any of axioms #1–#5 be replaced with sorry-free Lean proofs, using Mathlib's existing additive-combinatorics infrastructure?**

## Related Gallery Proofs

- `erdos-29`: Parent proof. Status: `axiomatized` (5 axioms, 0 sorries, 523 lines).
- `erdos-29-oq-02`: Sibling OQ.
- Mathlib analogue: `Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean` (explicit 3-AP-free construction, dual to JPSZ).

## Sub-goal decomposition (see `state.md` for full details)

- **Sub-goal A** (tractable, ~50–100 LOC): General `|A ∩ [1,N]| ≤ C·√N·polylog N` for any economical basis, without depending on JPSZ_set being concrete.
- **Sub-goal B** (medium-risk, ~150–250 LOC): Define concrete `JPSZSet : Set ℕ` via Behrend-like sphere construction; removes axioms #1 and #4 immediately.
- **Sub-goal C** (research-level, person-months): Prove representation-count bound (axiom #3) for the candidate. Requires JPSZ-paper sieve estimates.

## Mathlib bearer audit summary

At lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

- ✅ Behrend construction (`Behrend.sphere`, `Behrend.map`): structurally closest analogue.
- ✅ Additive energy, Plünnecke–Ruzsa, dissociation, randomisation.
- ❌ No Sidon / B_h set predicate.
- ❌ No `IsAdditiveBasis` on `Set ℕ`.
- ❌ No `representationCount` (`r_A(n)`) for general sets.
- ❌ No JPSZ-style algebraic-geometric primitives in `(ℤ/p)²`.

## Suggested First Steps

1. Read parent `proofs/Proofs/Erdos29Problem.lean` to understand the 5 axioms and their dependents.
2. Read `Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean` to understand the closest existing Mathlib construction.
3. Pick a sub-goal:
   - For a single-session win: sub-goal A (50–100 LOC, low risk).
   - For a multi-session project: sub-goal B + C.
4. Draft a companion file `Erdos29OQ01.lean` containing the theorem(s) being attempted, so the work is incremental and doesn't destabilize the parent proof.

## Honesty note

Full axiom removal (all 5) is **research-level mathematics from a 2024 paper resolving a 90-year-old problem**. It is realistic only as a multi-month, multi-PR project. Single-session contributions are limited to:
- Doc-only PREPs and sub-goal decomposition (this S1 OBSERVE).
- Sub-goal A (general size bound).
- Possibly opening sub-goal B (Behrend-like candidate definition without proving it's a basis).
