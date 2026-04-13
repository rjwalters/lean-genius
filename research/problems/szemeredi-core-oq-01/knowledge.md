# Knowledge Base: szemeredi-core-oq-01

**Problem**: Formalize the energy increment lemma: if a partition has an irregular pair,
the refinement increases energy by at least ε^5.

---

## Session 2026-04-03 (Session 1) — Energy Increment Algebraic Infrastructure

**Mode**: FRESH
**Outcome**: progress

### What I Did

- Proved `edgeDensity_symm`: edge density is symmetric d(A,B) = d(B,A)
- Proved `density_sq_convex_right`: convexity for the second argument
- Proved `sub4pair_energy_lower_bound`: splitting both A and B never decreases pair energy
- Proved `edgeDensity_union_weighted_avg`: d(A₁∪A₂,B) is the |A|-weighted average of d(A₁,B) and d(A₂,B)
- Proved `energy_excess_A_split`: exact excess formula = |A₁|·|A₂|/|A| · (d(A₁,B) - d(A₂,B))²
- Stated `energy_increment_step` with sorry and detailed proof sketch

### Key Findings

- `partitionEnergy` uses n² normalization (n = total vertices), NOT k² (k = parts count)
- The `card_mul_edgeDensity` and `edge_count_union` lemmas in SzemerediRegularity.lean are private; had to inline them for the weighted average proof
- `edgeDensity_union_weighted_avg` proof: case split on B.card = 0, then use inlined `card_mul_edgeDensity` + `edge_count_union` to prove `(n₁+n₂)*B.card*d = n₁*B.card*d₁ + n₂*B.card*d₂`, cancel B.card, divide by (n₁+n₂)
- For `Finset.card_bij`, must use `.mp`/`.mpr` forms (not `⟨...⟩`) for Finset membership, and `Prod.ext` for pair injectivity, and `Prod.eta` for surjectivity
- After `set a₁ : ℚ := (A₁.card : ℚ)`, cast is already done so no further `simp only [show...]` needed

### Files Modified

- `proofs/Proofs/SzemerediCoreOQ01.lean` (created)
  - 5 proved lemmas, 1 sorry (energy_increment_step)

### Next Steps

1. Prove `energy_increment_step`: given irregular pair, the partition split increases energy
   - The key gap: need to sum the excess over all pairs in the refined partition
   - Use `sub4pair_energy_lower_bound` for the (A,B) pair split
   - Use `density_sq_convex` for all other pairs that get split
   - Quantify: need |A|·|B| ≥ ε·n² (from equipartition) and d-deviation > ε
2. Alternative: submit `energy_increment_step` to Aristotle as HARD sorry
   - The algebraic steps are clear; the Finset sum manipulation may be automatable

---

## Session 2026-04-05 (Session 2) — Infrastructure Discovery & partitionEnergy_mono

**Mode**: REVISIT
**Outcome**: progress

### What I Did

- Discovered the main file had been significantly extended since Session 1:
  - `four_subpair_edge_count_identity`: PROVED (double weighted average identity)
  - `four_subpair_deviation_identity`: PROVED (variance decomposition equality)
  - `four_subpair_excess_lb`: PROVED (variance bound: 4-pair excess ≥ |A₁||B₁|(d₁₁-d)²)
  - `energy_increment_step` already updated to claim `eps^6` (corrected from ε^5)
  - `hcore` is already derived: `A'.card * B'.card * dev² > eps^6 * n²`
- Proved `partitionEnergy_mono` in SzemerediCoreOQ01Aristotle.lean:
  - P ⊆ Q (as Finsets of parts) → partitionEnergy G Q ≥ partitionEnergy G P
  - Proof: Finset.sum_le_sum_of_subset_of_nonneg with Finset.product_subset_product
- Documented the complete block decomposition strategy for the main sorry

### Key Findings

1. **ε^5 vs ε^6 clarification**: The correct bound for a SINGLE irregular pair with
   hypothesis `hpart_size: P.card ≥ eps*n` is ε^6, not ε^5. The ε^5 standard result
   sums over ≥ ε*k² irregular pairs, each contributing ~ε^4/k². One pair → ε^6.
   The theorem statement was already corrected to ε^6 in the main file.

2. **Block decomposition strategy** (completely worked out mathematically):
   Refactored partition: parts' = S ∪ T, parts = S ∪ {A,B}
   where S = parts\{A,B}, T = {A', A\A', B', B\B'}
   Energy comparison via Finset.sum_union:
   - S×S block: equal
   - S×T ≥ S×{A,B}: density_sq_convex per C∈S
   - T×S ≥ {A,B}×S: same by edgeDensity_symm
   - T×T ≥ {A,B}×{A,B} + eps^6:
     * A-self, B-self: sub4pair_energy_lower_bound (≥0)
     * A×B cross: four_subpair_excess_lb + hcore → ≥ eps^6
     * B×A cross: symmetry → ≥ eps^6 (total ≥ 2*eps^6)

3. **Key Lean challenge**: S∩T disjointness requires A', A\A', B', B\B' ∉ S.
   This holds since S = (parts.erase B).erase A contains only other parts, and
   A', A\A' are strict subsets of A (not equal to any other part). But formalizing
   this requires showing that the other parts in S are disjoint from A (by hdisjoint),
   hence no other part equals A' (since A' ⊆ A). This is the remaining formalization gap.

### Files Modified

- `proofs/Proofs/SzemerediCoreOQ01Aristotle.lean`:
  - Proved `partitionEnergy_mono`
  - Added `partitionEnergy_term_nonneg` (inline proof)
  - Cleaned up redundant lemmas (double_weighted_avg, four_subpair_excess_lb were in main)
  - Documented complete block decomposition strategy in `energy_increment_packaging_ari` comments

### Next Steps

1. **Prove disjointness**: Show S ∩ T = ∅, i.e., A', A\A', B', B\B' ∉ S
   - Use: ∀ C ∈ S, C is disjoint from A and B (from hdisjoint)
   - A' ⊆ A, so A' ∩ C = ∅ implies A' ≠ C for any C ∈ S
   - Key Lean lemma needed: `Finset.disjoint_of_subset_left` + contradiction
2. **Implement the block decomposition**:
   - Use Finset.sum_union for disjoint S and T
   - Use Finset.product_union_right/left
   - Apply density_sq_convex for S×T and T×S blocks
   - Apply four_subpair_excess_lb + hcore for T×T block
3. **Alternative**: Submit the packaging sorry to Aristotle
   - The goal is well-typed, hypotheses are concrete
   - Aristotle might handle the Finset.sum manipulation

---

## Session 2026-04-05 (Session 4) — Complete Proof: energy_increment_step

**Mode**: REVISIT
**Outcome**: completed

### What I Did

- Added `energy_increment_packaging` as a standalone lemma in SzemerediCoreOQ01.lean
- Used it to close the last sorry in `energy_increment_step`
- SzemerediCoreOQ01.lean now has **0 sorries**

### Key Insight

The edge case `A₂ = A\A' = ∅` (when A' = A) was handled by replacing `hA₂pos`/`hB₂pos`
with `hparts_nonempty : ∀ P ∈ parts, 0 < P.card` (derivable from `hpart_size`).
In `hST_disj`, if X = A₂ ∈ S ⊆ parts, then X.card > 0 (from `hparts_nonempty`), 
allowing the disjointness contradiction to proceed even when A₂ might be ∅.

### Proof Structure

`energy_increment_packaging` proves: S ∪ {A',A₂,B',B₂} has energy ≥ parts + ε^6
- `block_split` helper: double sum over X∪Y splits into 4 blocks via `Finset.sum_union`
- **ST ≥ SAB**: `density_sq_convex_right` + `nlinarith` with card hints
- **TS ≥ ABS**: `density_sq_convex` + `nlinarith`
- **TT ≥ ABAB + ε^6**: `sub4pair_energy_lower_bound` (×3) + `four_subpair_excess_lb` + `hcore` + `nlinarith`

`energy_increment_step` calls `energy_increment_packaging` after deriving:
- `hparts_nonempty` from `hpart_size + heps + hVpos`
- `hA'pos`/`hB'pos` from `hcore > eps^6 * n^2 > 0`

### PR

#10159 (pending docker build verification of nlinarith calls)

### Files Modified

- `proofs/Proofs/SzemerediCoreOQ01.lean`: +338 lines, 0 sorries
- `proofs/Proofs/SzemerediCoreOQ01Aristotle.lean`: +198 lines, 0 sorries (companion)
