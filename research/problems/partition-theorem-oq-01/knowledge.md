# Knowledge Base: partition-theorem-oq-01

## Problem Summary

Rogers-Ramanujan and Schur partition identities formalized in Lean 4.

## Current State

**Status**: 3 sorries (recurrence bridge), 3 axioms, ~2300 lines
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
### Session 2026-03-15 (researcher-2) - BUILD

**Mode**: REVISIT
**Outcome**: progress — mod-side specialization (step 6) completed

**Built**:
- `schurModSet`: definition of modular set {k ≤ n | k ≡ 1,2 mod 3}
- `schurModSet_pos`, `schurModSet_eq_gf_filter`: basic properties
- `part_le_of_mem`: utility lemma (a ∈ p.parts → a ≤ n)
- `schurMod_card_eq_subsetsWithSum`: |schurMod n| = |subsetsWithSum (schurModSet n) n|
  via explicit bijection (toFinset forward, partitionOfSubset backward)
- `schurMod_card_eq_gf_coeff`: |schurMod n| = coeff n (schurModGF n)

**Key insight**: Bijection only works for Schur (distinct parts). RR1/RR2 mod sides
allow repeated parts, needing ∏ 1/(1-X^k) framework instead of ∏ (1+X^k).

**File state**: 0 sorries, 3 axioms, ~2160 lines
**Docker build**: PASSED (3061 jobs)

**Roadmap update**: Steps 1-6 complete. Remaining:
- Step 7: Gap-side generating function characterization (hard)
- Step 8: Compose mod + gap to prove Schur identity axiom

### Session 2026-03-15 (researcher-2) - BUILD (second iteration)

**Mode**: REVISIT
**Outcome**: progress — fixed flawed bijection, added counting recurrences

**Critical finding**: The subtractTriangular bijection approach (from a previous
session) is **mathematically INCORRECT** for Schur's identity:
1. Doesn't preserve partition sums: [6,1] (sum 7) → [3,1] (sum 4)
2. `subtractTriangular_mod3` was FALSE: [6,1] → [3,1], but 3%3=0
3. Gap partitions include parts ≡ 0 mod 3 (e.g., [6,1] is valid Schur gap-full),
   and subtracting a multiple of 3 preserves the residue class

**Removed**: subtractTriangular/addTriangular infrastructure (also failed to
compile — `List.enum` doesn't exist in current Lean/Mathlib v4.26.0)

**Removed**: Duplicate ModSideSpecialization section (Part XXXVII was identical
to existing Part XXXIV-B/C definitions)

**Added**: Counting recurrence approach (Part XXXIX):
- `schurGapCount n m`: recursive count of gap partitions of n with parts ≤ m
- `schurModCount n m`: recursive count of mod partitions of n with parts ≤ m
- Both verified computationally through n=20 (beyond the n=15 Finset limit!)
- Three sorry'd bridge theorems: `schurGapCount_eq_card`, `schurModCount_eq_card`,
  `schurGapCount_eq_schurModCount`

**Key insight**: The recurrence approach enables verification beyond n=15 (where
Finset/native_decide exhausts memory). Extends to n=20+ via efficient recursion.

**File state**: 3 sorries (recurrence bridge), 3 axioms, ~2300 lines
**Docker build**: PASSED (3061 jobs)

**Roadmap update**: Steps 1-6 complete, step 7a-7b complete. Remaining:
- Step 7c: Prove schurGapCount_eq_card (recurrence = Finset for gap side)
- Step 7d: Prove schurModCount_eq_card (recurrence = Finset for mod side)
- Step 7e: Prove schurGapCount_eq_schurModCount (the deep step)
- Step 8: Compose to eliminate axiom