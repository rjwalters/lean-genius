# Selection Report: szemeredi-regularity-oq-02

**Date**: 2026-04-23
**Mode**: SELECT (default)
**Pool Status**: 33 available, 9 active claims

## Selected Problem

- **ID**: szemeredi-regularity-oq-02
- **Name**: Szemerédi Regularity: Frieze-Kannan Weak Regularity Comparison
- **Tier**: A
- **Significance**: 8/10
- **Tractability**: 6/10
- **Knowledge Score**: 0 (EMPTY)
- **Composite Score**: 68
- **Status**: available

## Selection Rationale

1. **Highest viable composite after quality gate (68)**: Higher-scoring problems (`triangle-angle-sum-oq-03` at 76, `minkowski-fundamental-theorem-oq-04` at 77, `cauchy-schwarz-integral-oq-01-oq-03-oq-01` at 76) were either recently selected (< 3h ago), currently claimed, or rejected on quality grounds (degenerate angle-function behavior = shallow implementation question).
2. **A-tier significance**: Frieze-Kannan weak regularity is a foundational result in extremal combinatorics. Its tight exponential bound (vs Szemerédi's tower-type) is mathematically significant and under-represented in formal verification.
3. **Graph theory / combinatorics domain**: Distinct from both cauchy-schwarz (analysis) and minkowski (discrete geometry). The Szemerédi regularity parent proof already provides `Finpartition`, `IsEpsilonRegular`, and energy infrastructure in the gallery — strong foundation for the extension.
4. **Concrete formalization target**: The Frieze-Kannan weak regularity lemma has a short proof via a greedy algorithm on cut-norm improvements. The main gap is `cutNorm` definition (not in Mathlib), but building it on `Finpartition` is bounded and achievable.
5. **EMPTY knowledge tier**: No prior research attempts on this exact question — full exploration value.

## Rejection Summary

- **Candidates considered**: 33 available after pool sync
- **minkowski-fundamental-theorem-oq-04** (77): selected 14:06 today, <3h ago — avoid re-selection
- **triangle-angle-sum-oq-03** (76): rejected on quality gate — degenerate angle-function cases is a shallow implementation question, not meaningful mathematics
- **cauchy-schwarz-integral-oq-01-oq-03-oq-01** (76): selected 15:31 today, <3h ago
- **triangle-angle-sum-oq-02** (68): Gauss-Bonnet formalization requires `ConvexPolyhedron` type with `EulerCharacteristic` — significant infrastructure risk; comparable score to this candidate
- **sperner-ndim-oq-04** (68): currently claimed by active researcher
- **lebesgue-measure-oq-06** (68 raw): RICH knowledge tier (score=27) → deprioritized
- **shapley-folkman-oq-03** (67 raw): MODERATE knowledge tier (score=12) → deprioritized
- **Open conjectures** (twin-primes, Goldbach, Sophie Germain): tractability ≤ 2, no viable Lean path
- **Confidence**: high (clear formalization path via Finpartition + cut-norm; parent proof infrastructure available)

## Related Gallery Proofs

- `szemeredi-regularity`: Parent proof — provides Finpartition, IsEpsilonRegular, energy increment API
- `szemeredi-counting`: Szemerédi regularity for counting lemma — closely related formalization
- `szemeredi-full`: Full Szemerédi theorem — downstream context

## Suggested First Steps

1. **OBSERVE**: Check `Mathlib.Combinatorics.SimpleGraph.Regularity.*` for cut-norm content. Survey whether `cutNorm` or bipartite density approximation exists in Mathlib.
2. **ORIENT**: Read the Frieze-Kannan 1999 proof: start with the tensor product / step function representation. Map `IsEpsilonRegular` (Szemerédi) → `IsWeaklyRegular` (Frieze-Kannan) conceptually.
3. **DECIDE**: Define `cutNorm : (V → V → ℝ) → ℝ` as `⊔_{S,T ⊆ V} |∑_{i∈S,j∈T} f(i,j)|`, formalize the weak regularity predicate, then prove the greedy construction gives an exponential-size partition.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 33 |
| In Progress | 1309 |
| Completed | 644 |
| Graduated | 15 |
| Blocked | 3 |

## Candidate Pool Health

- Pool depth: **adequate** (33 available >> 15 threshold)
- Pool refreshed during this session: 25 → 33 available (DB sync brought in 8 new candidates)
- Domain coverage: combinatorics, analysis, geometry, number theory, graph theory all represented
- Recommendation: Pool healthy; standard 30-minute interval sufficient
- Next refresh recommended: 30 minutes
