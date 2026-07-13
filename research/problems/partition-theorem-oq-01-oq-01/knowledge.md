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

## Session 2026-06-13 (Session 2) — STATE-SYNC

**Mode**: REVISIT
**Outcome**: status sync (no Lean change)

### What I Did

- Found this slug's research JSON stale: `status: available`, `slug/phase/knowledge` all null,
  and a misleading broad title ("Can RR be proved via q-series…") despite the deliverable
  being **done** since 2026-04-13 (gallery `meta.json` status=verified, 0 sorries, 0 axioms).
- Flipped research JSON to `completed`/`COMPLETED`, corrected the title to match the real
  scope (n≤8 computational verification), and populated the knowledge block.

### Scope Clarification (important)

This sub-question is the **computational verification** of RR1/RR2 for n ≤ 8 — and that is
complete. The **general** Rogers-Ramanujan identities remain **axiomatized** in the parent
`PartitionTheoremOQ01.lean` (`rogers_ramanujan_first`/`second`). The parent's axiom-elimination
roadmap is at step 8/9: mod-side generating functions are fully connected
(`partGF_coeff_eq_card`, `rr1Mod_card_eq_gf_coeff`, …, steps 1–7f ✅), but the **gap-side**
generating function (step 8) and the composition (step 9) are unbuilt. The gap-side is the
deep RR core (Bailey chain / Jacobi triple product / RR continued fraction), none of which
is in Mathlib — a >1000-line foundational build. General proof should be pursued in the
parent slug, not here.

### Files Modified

- `src/data/research/problems/partition-theorem-oq-01-oq-01.json` (status/title/knowledge sync)

## Key References

- Parent: `src/data/proofs/partition-theorem-oq-01/`
- Gallery: Rogers-Ramanujan identities
