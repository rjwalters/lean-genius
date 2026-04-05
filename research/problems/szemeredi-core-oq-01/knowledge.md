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
