# Knowledge: Erdős #871 — Partitioning Additive Bases of Order 2

## Current Status

3 axioms in `Erdos871Problem.lean`:
1. `erdos_nathanson_1989` — Fixed-threshold counterexample (Acta Arithmetica LII, 1989)
2. `erdos_nathanson_positive` — Partition possible under log-growth condition
3. `larsen_construction_blocking` — Blocking property of Larsen 2026 construction

## Key Insight

Larsen (2026) disproved Erdős's conjecture by constructing a basis A with r_A(n) → ∞
but A cannot be partitioned into two additive bases. The proof uses a "blocking property":
the construction is dense enough to be a basis but not decomposable.

## Reduction Targets (Priority Order)

### 1. `larsen_construction_blocking` (PRIMARY)
- Constructive argument: A = ∪_{k} B_k where each block B_k blocks all potential partitions
- May be formalizable via explicit density/greedy construction
- Mathlib target: `Mathlib.Combinatorics.Additive` — check for sumset/density infrastructure

### 2. `erdos_nathanson_positive` (SECONDARY)
- log-growth condition: if r_A(n) > c·log n for c > (log 4/3)⁻¹ ≈ 3.48, partition IS possible
- May use Mathlib entropy/counting lemmas

## Mathlib Resources to Survey

- `Mathlib.Combinatorics.Additive.Salem` — Salem-Spencer structure
- `Mathlib.Combinatorics.Additive.Behrend` — density constructions
- `Mathlib.Data.Set.Card` — cardinality infrastructure
- Sumset API: `Finset.sumset`, `Set.IsSumFree`
