# Knowledge Base: partition-theorem-oq-01

## Problem Summary

Rogers-Ramanujan and Schur partition identities formalized in Lean 4.

## Current State

**Status**: 0 sorries, 3 axioms, ~2160 lines (sorry-free!)
**File**: `proofs/Proofs/PartitionTheoremOQ01.lean`

## Key Results (All Proved)

- Partition infrastructure: multiset-based partitions, part constraints
- Counting machinery for restricted partition types
- Equivalence framework between partition classes
- Schur's theorem structure
- **Bridge theorems**: decidable ↔ noncomputable equivalence for all partition sets
- **GF infrastructure**: distinctPartGF, subsetsWithSum, insert recursion
- **Computational verification**: all three identities verified to n=15

## Three Remaining Axioms

1. `rogers_ramanujan_first` — First Rogers-Ramanujan identity
2. `rogers_ramanujan_second` — Second Rogers-Ramanujan identity
3. `schur_partition_identity_corrected` — Schur's partition theorem (corrected gap)

### Why They're Hard

- All three are deep combinatorial identities requiring either:
  - Generating function proofs (formal power series in Lean)
  - Bijective constructions (complex combinatorial bijections)
- Definitions use `noncomputable section` (due to `Multiset.toList`), preventing `native_decide`
  - **Mitigated**: decidable versions with native_decide verification to n=15
- Mathlib has PowerSeries but needs coefficient extraction chain for partition GFs

### Assessment

GF infrastructure is complete through step 6. The path to axiom elimination is:
1. ✅ Define distinctPartGF = ∏_{k ∈ S} (1 + X^k)
2. ✅ Define subsetsWithSum S n (subsets summing to n)
3. ✅ Prove subset sum recursion (insert splitting)
4. ✅ Prove GF coefficient = |subsetsWithSum S n| (distinctPartGF_coeff)
5. ✅ Build partition-subset correspondence (partitionOfSubset, schurMod_to_subset)
6. ✅ Specialize for Schur mod-side: |schurMod n| = coeff n (schurModGF n)
   - Built schurModSet, bijection via Finset.card_bij, GF link
   - **Note**: RR1/RR2 mod sides allow repetition → need ∏ 1/(1-X^k) (not yet built)
7. 🔲 Build gap-side generating function characterization (**hard step**)
   - For Schur: gap condition → recurrence/functional equation for GF
   - Standard approach: Schur's original iterative construction
8. 🔲 Compose to prove identities

## Session Log

### Session 2026-03-15 (researcher-6) - Assessment

**Mode**: REVISIT
**Outcome**: surveyed — assessed axiom elimination approaches

**Findings**: All three axioms encode deep partition identities. The noncomputable
definitions prevent computational verification. Proving any of these requires either
generating function infrastructure or bijective proof constructions not available
in Mathlib. No tractable single-session path.

### Session 2026-03-15 (researcher-3) - BUILD

**Mode**: REVISIT
**Outcome**: progress — built GF coefficient infrastructure, extended verification

**Built**:
- Subset sum insert recursion (splitting lemma, cardinality recursion)
- GF coefficient theorem statement and base case
- partitionOfSubset: Finset → Nat.Partition constructor
- Extended native_decide verification from n=12 to n=15 for all identities

**3 new sorries**: subsetsWithSum_insert_mem_image, distinctPartGF_coeff, schurMod_to_subset
**Docker build**: PASSED (all 3061 jobs)

### Session 2026-03-15 (researcher-7) - DEEP DIVE

**Mode**: REVISIT
**Outcome**: completed — eliminated ALL remaining sorries

**Proved**:
- `subsetsWithSum_insert_mem_image`: key bijection T ↦ insert k T for k-containing subsets
- `subsetsWithSum_insert_card`: cardinality recurrence via disjoint union decomposition
- `distinctPartGF_coeff`: **GF Coefficient Theorem** — coeff n (∏(1+X^k)) = |subsetsWithSum S n|
  - By Finset.induction with `revert n` (critical: IH needs to work for all indices)
  - k≤n case: `coeff_X_pow_mul` shifts index
  - n<k case: `X_pow_dvd_iff` + `dvd_mul_right` gives 0
- `schurMod_to_subset`: SchurMod partition → subset via `Multiset.toFinset`
- `partitionOfSubset` fixed for current Mathlib API
- Fixed `PowerSeries.coeff` API (R now implicit: use `coeff (R := ℤ) n`)

**Sorry count**: 3 → 0 (file is now sorry-free)
**Docker build**: PASSED (all 3061 jobs)

### Session 2026-03-15 (researcher-1) - DEEP DIVE

**Mode**: REVISIT
**Outcome**: progress — completed step 6: Schur mod-side specialization

**Proved**:
- `schurModSet`: {k ∈ [1..n] | k ≡ 1,2 mod 3} definition
- `schurModSet_pos`: elements are positive
- `schurModSet_eq_gf_set`: equivalence with schurModGF filter
- `schurMod_card_eq_subsetsWithSum`: **Bijection theorem** — |schurMod n| = |subsetsWithSum S n|
  - Via `Finset.card_bij` with forward map p ↦ p.parts.toFinset
  - Injectivity: nodup parts ⇒ toFinset determines partition
  - Surjectivity: partitionOfSubset gives inverse
- `schurMod_card_eq_gf_coeff`: **GF Link** — |schurMod n| = coeff n (schurModGF n)
  - Chains bijection + distinctPartGF_coeff + GF definition

**Key insight**: RR1/RR2 mod sides allow repetition (no Nodup condition), so
distinctPartGF (∏(1+X^k)) doesn't directly apply. Schur mod side IS distinct,
so the bijection works. RR would need ∏ 1/(1-X^k) infrastructure.

**Docker build**: PASSED (all 3061 jobs)
**Lines added**: ~80 (Part XXXIV-B + XXXIV-C)

### Session 2026-03-17 (researcher-3) - BUILD

**Mode**: REVISIT
**Outcome**: progress — built partGF infrastructure for RR identities

**Built**:
- `geomPow k`: geometric series 1 + X^k + X^{2k} + ... (= 1/(1-X^k))
- `one_sub_X_pow_mul_geomPow`: fundamental identity (1-X^k) * geomPow k = 1
- `partGF S = ∏ geomPow k`: partition GF with repetition (for RR mod sides)
- `partitionsFrom S n`: partitions of n with all parts from S
- `rr1Mod5_eq_partitionsFrom`, `rr2Mod5_eq_partitionsFrom`: connections
- `geomPow_isUnit`, `partGF_isUnit`: unit proofs
- Basic structural lemmas: empty, insert, singleton, union, constantCoeff

**Key insight**: RR1/RR2 mod sides allow repeated parts, requiring ∏ 1/(1-X^k)
(not ∏(1+X^k) which is only for distinct parts / Schur). The `partGF`
infrastructure fills this gap.

**Docker build**: PASSED (all 3061 jobs)
**Lines added**: ~230 (Parts XXXVII through XXXVII-C)
**Sorry count**: 0 (unchanged)
**Axiom count**: 3 (unchanged)
