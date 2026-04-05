# Knowledge Base: szemeredi-core-oq-01

**Problem**: Formalize the energy increment lemma: if a partition has an irregular pair,
the refinement increases energy by at least ε^6 (single pair; ε^5 requires all pairs).

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

## Session 2026-04-05 (Session 2) — δ-Decomposition and Corrected Bound

**Mode**: REVISIT
**Outcome**: progress

### What I Did

- Proved `four_subpair_edge_count_identity`: 2D edge count additivity
  - `Σᵢⱼ|Aᵢ||Bⱼ|d(Aᵢ,Bⱼ) = |A₁∪A₂||B₁∪B₂|d(A₁∪A₂,B₁∪B₂)`
  - Proved by inlining edge count union additivity twice (for B-split then A-split)
- Proved `four_subpair_deviation_identity`: δ-decomposition
  - `Σᵢⱼ|Aᵢ||Bⱼ|dᵢⱼ² - |A||B|d² = Σᵢⱼ|Aᵢ||Bⱼ|(dᵢⱼ-d)²`
  - Key: expand (dᵢⱼ-d)², use weighted average to cancel cross-terms
- Proved `four_subpair_excess_lb`: excess ≥ |A₁||B₁|(d₁₁-d)²
  - Drop non-negative terms from the deviation identity
- Corrected `energy_increment_step` bound: eps^5 → eps^6
  - ε^5 requires summing over ALL ε·k² irregular pairs
  - Single irregular pair gives only ε^6: |A'||B'|·dev² ≥ ε²n·ε²n·ε² = ε^6·n²
- Proved complete `hcore`: |A'||B'|(d(A',B')-d(A,B))² > ε^6·n²
  - Using hA'n: |A'| ≥ ε²n, hB'n: |B'| ≥ ε²n, hdev: dev² > ε²
- Proved `hVpos`: V non-empty (by contradiction with hd > eps > 0)

### Key Findings

- **ε^5 vs ε^6**: For a SINGLE irregular pair, the energy gain is ε^6 (not ε^5).
  The ε^5 bound in Komlós-Simonovits comes from summing ε^4/k² over all ≥ ε·k² pairs.
- **δ-decomposition technique**: expand (dᵢⱼ-d)² algebraically; the cross-term
  -2d·Σ|Aᵢ||Bⱼ|dᵢⱼ becomes -2d·|A||B|·d = -2|A||B|d² using the weighted average identity
- **hdev proof**: `rw [← sq_abs]; exact pow_lt_pow_left hd (le_of_lt heps) (by norm_num)`
- **hVpos proof**: contradiction — if V=∅, all edgeDensity = 0, then |d(A',B')-d(A,B)| = 0 < eps

### Files Modified

- `proofs/Proofs/SzemerediCoreOQ01.lean`
  - Added 3 proved lemmas: four_subpair_edge_count_identity, four_subpair_deviation_identity, four_subpair_excess_lb
  - Corrected energy_increment_step: eps^5 → eps^6, proved hcore and hVpos
  - 1 sorry remains: Finset.sum packaging for T×T block

### Next Steps

1. Submit remaining sorry in `energy_increment_step` to Aristotle (HARD: Finset.sum decomposition)
2. The algebraic core is complete; only the Finset.sum_union packaging remains
3. If Aristotle solves it, sorryCount drops to 0 → advance to COMPLETED
