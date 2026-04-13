# Knowledge: partition-theorem-oq-01-oq-01

## Overview

Sub-question of PartitionTheoremOQ01. Computationally verifies the Rogers-Ramanujan
first and second identities for n = 0, 1, ..., 8 using `native_decide`.

## Session 2026-04-13 — PROVED

**Mode**: FRESH
**Outcome**: All theorems verified (0 sorries)

### What I Did

Created new Lean file `PartitionTheoremOQ01OQ01.lean` with:
1. Individual `rr1_n0` through `rr1_n8` theorems via `native_decide`
2. Individual `rr2_n0` through `rr2_n8` theorems via `native_decide`
3. Combined theorem `rr_both_verified_through_8` using `interval_cases`

### Key Techniques

- `native_decide`: Lean kernel-level computation for decidable propositions
- `interval_cases n`: Splits `n ≤ 8` into 9 concrete cases automatically
- The definitions `rr1GapPartitions`, `rr2GapPartitions`, `rr1Mod5Partitions`, `rr2Mod5Partitions`
  are all computable (use `Finset.filter` on `Nat.partition.antidiagonals`), making `native_decide` applicable

### Mathematical Context

- Rogers-Ramanujan First Identity (RR1): #{partitions of n with gap ≥ 2} = #{partitions of n with parts ≡ 1,4 mod 5}
- Rogers-Ramanujan Second Identity (RR2): #{partitions of n with gap ≥ 2 and min part ≥ 2} = #{partitions of n with parts ≡ 2,3 mod 5}
- General proof requires q-series (Rogers 1894, Ramanujan 1913, Andrews-Garvan bijection)
- Computational verification for small n confirms definitions are correct

### Files Created

- `proofs/Proofs/PartitionTheoremOQ01OQ01.lean` (71 lines, 0 sorries)
- `src/data/proofs/partition-theorem-oq-01-oq-01/meta.json`
- `src/data/research/problems/partition-theorem-oq-01-oq-01.json`

## Key References

- Parent: `src/data/proofs/partition-theorem-oq-01/`
- Gallery: Rogers-Ramanujan identities
