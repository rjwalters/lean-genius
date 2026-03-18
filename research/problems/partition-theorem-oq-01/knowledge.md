# Knowledge Base: partition-theorem-oq-01

## Problem Summary

Rogers-Ramanujan and Schur partition identities formalized in Lean 4.

## Session 2026-03-18 (researcher-4) - Fix Build Errors

**Mode**: REVISIT (RICH knowledge score 62)
**Outcome**: progress — fixed 2 build-breaking issues + added RR1/RR2 GF bridge

### What I Did

1. **Fixed duplicate `partGF_constantCoeff`**: Two definitions with same name (different signatures). Deleted the redundant second one.
2. **Fixed `partGF_insert'` geomSeries mismatch**: Added `geomPow_eq_geomSeries` bridge lemma.
3. **Added Part XLVII: RR1/RR2 Mod-Side GF Bridge**: `rr1Mod_card_eq_gf_coeff` and `rr2Mod_card_eq_gf_coeff` connecting partition counts to GF coefficients.
4. **Updated stale roadmap**: Marked steps 7d-7f as complete.

### Files Modified

- `proofs/Proofs/PartitionTheoremOQ01.lean` — 2 fixes + Part XLVII (+65 lines)

---

## Current State

**Status**: 0 sorries, 3 axioms, ~3485 lines (sorry-free!)
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

### Session 2026-03-16 (researcher-1) - BUILD

**Mode**: REVISIT
**Outcome**: progress — built gap-side bounded partition infrastructure (step 7a)

**Built** (Part XXXVII + XXXVIII):
- `schurGapBounded(m, n)`: gap-side partitions with largest part ≤ m
- `schurModBounded(m, n)`: mod-side partitions with largest part ≤ m
- `schurGapBounded_ge/schurModBounded_ge`: m ≥ n reduces to full set
- `schurGapBounded_zero`: no partition of n > 0 with bound 0
- `schurGapBounded_mono/schurModBounded_mono`: monotonicity in m
- `schurGapBounded_split`: union decomposition by m-membership
- `schurModBounded_div3`: m ≡ 0 mod 3 ⟹ bound m = bound (m-1)
- `schurGapRec/schurModRec`: pure recursive counting functions
- Computational verifications: recurrences match Finset definitions

**KEY FINDING**: `schurGapBounded(m,n) ≠ schurModBounded(m,n)` for m < n.
The gap-side and mod-side have DIFFERENT (m,n)-recurrences:
- Gap: G(m,n) = G(m-1,n) + G(m-gap(m), n-m) where gap(m) = 3 or 4
- Mod: M(m,n) = M(m-1,n) + [m≢0 mod 3] · M(m-1, n-m)
These recurrences use different second arguments (m-gap vs m-1), so the
identity cannot be proved by matching recurrences on (m,n).

**Implication**: Need global proof strategy — direct bijection, GF identity,
or clever variable substitution.

**Docker build**: PASSED (all 3061 jobs)
**Lines added**: ~260 (Parts XXXVII + XXXVIII)

### Session 2026-03-17 (researcher-4) - BUILD

**Mode**: REVISIT
**Outcome**: progress — built Schur identity reduction and exchange framework

**Built** (Parts XLIII-XLVI):
- `schur_axiom_from_gap_gf`: formal reduction — axiom ⟺ gap count = GF coeff
- `gap_gf_from_schur_axiom`: reverse direction of the reduction
- `splitHi`/`splitLo`: canonical split for parts ≡ 0 mod 3 (11 properties proved)
- `schurGapOnly`/`schurModOnly`/`schurBoth`: partition classification into 4 classes
- `schurGapFull_eq_both_union_gapOnly`: disjoint union decomposition (gap side)
- `schurMod_eq_both_union_modOnly`: disjoint union decomposition (mod side)
- `schur_identity_iff_exchange`: **KEY** — Schur identity ⟺ |GapOnly| = |ModOnly|
- Computational verification of exchange for n = 0, 3, 6, 9, 12

**KEY FINDING**: The Schur identity reduces to an exchange bijection between
"gap-only" partitions (gap-valid, has ≡0 mod 3 parts) and "mod-only" partitions
(mod-valid, gap-invalid). The canonical split has gap ≤ 2, automatically creating
gap violations. However, collisions can occur (e.g., split(9)=(5,4) collides with
existing part 4 in {9,4,1}), requiring context-dependent splitting.

**Docker build**: PASSED (all 3061 jobs)
**Lines added**: ~306 (Parts XLIII-XLVI)

### Session 2026-03-17 (researcher-1) - BUILD

**Mode**: REVISIT
**Outcome**: progress — proved partGF bridge theorem (step 7e)

**Built** (Parts XLV-XLVI):
- `partRemoveOne`: remove one copy of k from partition parts → partition of n-k
- `partitionsFrom_insert_rec`: **Key recursion** — |P(S∪{k}, n)| = |P(S, n)| + [k≤n]·|P(S∪{k}, n-k)|
  - Bijection via remove/add one copy of k (Finset.card_bij)
  - Split: partitions using 0 copies of k vs ≥1 copy
- `partGF_coeff_eq_partitionsFrom`: **Bridge Theorem** — coeff n (partGF S) = |partitionsFrom S n|
  - By double induction: Finset.induction on S, Nat.strongRecOn on n
  - Matches GF recursion (geomSeries_mul_coeff_rec) with partition recursion term-by-term

**Step 7e**: ✅ COMPLETE
**Docker build**: 0 new errors (15 pre-existing Mathlib API breakages in Parts XXXIX-XLIII)
**Lines added**: ~130 (Parts XLV-XLVI)
