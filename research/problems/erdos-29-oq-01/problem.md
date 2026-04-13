# The JPSZ axioms (`JPSZ_set`, `JPSZ_is_basis`, `JPSZ_is_economical`) fail to l...

## Source

- **Proof**: Erdős Problem #29: Explicit Economical Additive Basis (`erdos-29`)
- **Type**: open-question
- **Category**: extension
- **Tractability**: challenging

## Problem Statement

The JPSZ axioms (`JPSZ_set`, `JPSZ_is_basis`, `JPSZ_is_economical`) fail to load in Aristotle due to `harmonicSorry` axioms. Can the JPSZ construction be formalized in Lean WITHOUT axioms, using Mathlib's existing library for hash functions, pseudorandomness, or derandomization?

## Related Gallery Proofs

- `erdos-29`: Parent proof

## Suggested First Steps

1. Read the source proof in `proofs/Proofs/` and `src/data/proofs/erdos-29/meta.json`
2. Check Mathlib for relevant definitions and lemmas
3. Assess feasibility of the approach
