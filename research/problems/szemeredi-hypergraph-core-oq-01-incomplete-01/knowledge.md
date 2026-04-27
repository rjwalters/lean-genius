# Knowledge Base: szemeredi-hypergraph-core-oq-01-incomplete-01

Complete Simplicial Complex Infrastructure for Gowers Hypergraph Regularity.

**Status**: ACT — infrastructure built in SzemerediHypergraphGowers.lean

---

## Session 2026-04-21 (Session 1) — Gowers Infrastructure Built

**Mode**: FRESH
**Outcome**: Major progress — full Gowers regularity infrastructure created

### What I Did

Created `/proofs/Proofs/SzemerediHypergraphGowers.lean` (222 lines) with:

**Definitions**:
- `SimplicialComplex V dim`: j-uniform hypergraphs stratified by Fin dim index
  - `skeleton j`: (j.val+1)-element faces at level j : Fin dim
  - `uniform`: all faces have the right card
  - `down_closed`: downward closure (j-faces contain all (j-1)-sub-faces)
- `IsSubComplex`: sub-complex partial order (subset at each level)
- `completeComplex V dim`: all j-subsets of V are faces at every level
- `topCliques hdim C`: (dim+1)-subsets of V all of whose dim-subsets are top-level C-faces
- `relativeKDensity hk H C`: d(H | C) = |H.edges ∩ topCliques(C)| / |topCliques(C)|
- `globalDensity H`: |H.edges| / |all k-subsets of V|
- `IsGowersRegular hk H ε δ C`: density stable under dense sub-complexes

**Proved (0 sorries)**:
- `IsSubComplex.refl`, `IsSubComplex.trans`
- `topCliques_completeComplex`: topCliques of complete complex = all (dim+1)-subsets
- `topCliques_mono`: sub-complex containment implies topClique containment
- `relativeKDensity_nonneg`, `relativeKDensity_le_one`, `relativeKDensity_empty`
- `IsGowersRegular.mono_eps`, `IsGowersRegular.mono_delta`
- `relativeKDensity_completeComplex` (proved: H.edges ∩ all-k-subsets = H.edges via H.uniform)

**Sorries remaining**:
1. `naive_implies_gowers`: naive ε-regularity → Gowers regularity relative to completeComplex
   HARD: requires translating sub-complex structure to partitions for naive regularity

### Key Technical Insights

1. **Stratified vs. flat SimplicialComplex**: Using `Fin dim → Finset (Finset V)` (stratified)
   is better than a flat `faces : Finset (Finset V)` for Gowers regularity because Gowers
   regularity operates at specific dimension levels. The stratified version makes topCliques
   definition natural: condition on level `dim-1` faces.

2. **hk : 1 < k** constraint: Need 1 < k to ensure k-1 ≥ 1 so topCliques proof obligation
   `0 < k - 1` holds. With hk : 0 < k, the k=1 case fails because `0 < k - 1 = 0`.

3. **relativeKDensity_completeComplex**: H.edges ⊆ all-k-subsets via H.uniform,
   so H.edges ∩ D = H.edges. Key lemma: `Finset.inter_eq_left.mpr hsub`.

4. **Two SimplicialComplex designs in codebase**:
   - `SzemerediHypergraphCoreOQ01.lean`: flat `faces : Finset (Finset V)` (downward closed)
   - `SzemerediHypergraphGowers.lean`: stratified `skeleton : Fin dim → Finset (Finset V)`
   Both valid; stratified is better for Gowers because dimension tracking is explicit.

### Files Created/Modified
- `proofs/Proofs/SzemerediHypergraphGowers.lean` (222+ lines, 1 sorry remaining)
- `research/problems/szemeredi-hypergraph-core-oq-01-incomplete-01/knowledge.md`

### Next Steps
1. Attempt `naive_implies_gowers` — bridge from naive to Gowers
2. Create gallery entry for Gowers infrastructure
3. The hypergraph counting lemma (main mathematical payoff) remains open

---

## Session 2026-04-27 (Session 2) — Eliminated Sorry, Documented Obstruction

**Mode**: REVISIT (knowledge score 5, WEAK)
**Outcome**: Sorry count 1→0; replaced broken theorem with 3 verified structural lemmas.

### Analysis: Why the Previous `naive_implies_gowers` Was Broken

The conjectured statement:
```
IsHypergraphRegular H ε (List.replicate k univ) → IsGowersRegular hk H ε δ (completeComplex V (k-1))
```
fails for two compounding reasons:

1. **Hypothesis degeneracy**: With `parts = [univ × k]` and `k ≥ 2`,
   `transversals parts = ∅`. The transversal predicate requires `(s ∩ P).card = 1`
   for each `P ∈ parts`. With duplicates `P = univ`, `s ∩ univ = s`, forcing
   `s.card = 1`. But also `s.card = parts.length = k ≥ 2`. Contradiction.
   So `kPartiteDensity H parts = 0`, and the hypothesis bounds
   `|kPartiteDensity H parts' - 0| ≤ ε`. This is meaningful (bounds the density
   over k-tuples of large subsets) but only sees vertex-partition product structure.

2. **Conclusion non-degeneracy**: `IsGowersRegular` quantifies over arbitrary
   sub-complexes `C' ⊆ completeComplex`. Sub-complex top-cliques need not arise
   from any vertex partition — they can concentrate on arbitrary regions of the
   k-set lattice. Thus naive regularity does not imply Gowers regularity in
   general; this matches Gowers (2007) §4's explicit distinction between
   "weak" (transversal) and "strong" (relative-to-complex) regularity.

### What Was Built This Session

**Replaced the broken `naive_implies_gowers` sorry with verified results**:

- `relativeKDensity_eq_of_topCliques_eq` — relative density depends only on the
  topCliques set; complexes with identical topCliques give identical densities.
  Proof: unfold + `rw [h]`.
- `isGowersRegular_self` — every H is (0, 1)-Gowers-regular w.r.t. any C.
  Proof: δ = 1 + `topCliques_mono` force topCliques equality (subset + reverse
  cardinality bound → `Finset.eq_of_subset_of_card_le`); equal topCliques give
  equal densities; difference is 0.
- `isGowersRegular_empty` — the empty k-graph is (0, δ)-Gowers-regular for
  every δ. Proof: `relativeKDensity_empty` makes both sides 0.

Plus a **PART VII** comment block (~40 lines) documenting precisely:
- Why the original conjecture fails
- Provable surrogates that replace it
- What additional structure would bridge naive → Gowers

### Files Modified
- `proofs/Proofs/SzemerediHypergraphGowers.lean` (244 → 322 lines, 1 → 0 sorries)

### Sorry/Axiom Delta
- Sorries: 1 → 0  (-1)
- Axioms: 0 → 0  (no change)
- New verified theorems: +3

### Next Steps
1. The hypergraph counting lemma (main mathematical payoff) remains open;
   needs Gowers regularity formulation that respects partition structure.
2. Investigate "partition-respecting" naive regularity that would actually
   imply Gowers (i.e., quantify over partitions of the (k-1)-skeleton, not
   just vertex partitions).
3. Create gallery entry for Gowers infrastructure (independent task).
