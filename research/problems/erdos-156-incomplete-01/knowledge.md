# Knowledge Base: erdos-156-incomplete-01

**Erdős #156: Minimum Size of Maximal Sidon Sets — Greedy Lower Bound**

The greedy construction greedySidon(N) produces a maximal Sidon set of size Ω(N^{1/3}), proved by shadow counting.

---

## Session 2026-04-24 (Session 1) — All 3 Sorries Proved

**Mode**: FRESH
**Outcome**: COMPLETE — all 3 sorries eliminated, PR #12393

### What I Did

1. Analyzed `proofs/Proofs/Erdos156Problem.lean` (652 lines)
2. Read the full proof infrastructure: `IsSidonSet`, `greedySidon`, `sumset`, `diffShadow`, `midShadow`
3. Identified the 3 remaining sorries and their proof strategies
4. Proved all 3 via shadow cardinality argument

### Proof of `diffShadow_ncard_le`

**Goal**: `(diffShadow A).ncard ≤ A.ncard * (A.ncard * (A.ncard + 1) / 2)`

**Strategy**: Embed `diffShadow A` into the image of `(fun p : ℕ × ℕ => p.2 - p.1) '' (A ×ˢ sumset A)`.

For `x ∈ diffShadow A`: ∃ a, b, c ∈ A with `a + x = b + c`. Then `(a, b+c) ∈ A ×ˢ sumset A` and `(b+c) - a = x` by omega. So `|diffShadow A| ≤ |A × sumset A| = n × n(n+1)/2`.

### Proof of `midShadow_ncard_le`

**Goal**: `(midShadow A).ncard ≤ A.ncard * (A.ncard + 1) / 2`

**Strategy**: Map `midShadow A` into upper-triangular pairs via `(b,c) ↦ (b+c)/2`. WLOG b≤c, so the upper-triangular set has size n(n+1)/2 by `card_upper_tri`.

### Proof of `greedySidon_cube_lower_bound`

**Goal**: `N ≤ n + n * (n * (n + 1) / 2) + n * (n + 1) / 2`

**Strategy**: Interval N ⊆ A ∪ diffShadow A ∪ midShadow A (by `greedySidon_complement_in_shadow`), then apply shadow size bounds and `Set.ncard_union_le`.

### Key Insights

- `diffShadow A ⊆ image(A×sumset(A))`: elegant embedding, avoids triple counting
- `size` (custom def) equals `Set.ncard` for finite sets via `Set.Finite.ncard_eq_toFinset_card`
- `greedySidon_complement_in_shadow` was already proved, making the lower bound clean
- `Set.ncard_union_le` works without disjointness for upper bounds

### Files Modified

- `proofs/Proofs/Erdos156Problem.lean` (3 sorries → 0 sorries)
- `src/data/research/problems/erdos-156-incomplete-01.json` (status: completed)
- `research/problems/erdos-156-incomplete-01/knowledge.md`
