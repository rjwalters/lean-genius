# Problem Selection Report

**Date**: 2026-04-05
**Mode**: SELECT
**Pool Status**: 12 available, 406 in-progress, 1222 completed

## Selected Problem

- **ID**: erdos-1008
- **Name**: Erdős Problem #1008: C₄-Free Subgraphs
- **Tier**: B
- **Significance**: 6/10
- **Tractability**: 6/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Concrete sorry target**: `exponent_optimal` at line 594 has a single sorry — "Real arithmetic: 2n² < (n³)^{2/3+ε} for n^{3ε} > 3" — that is pure rpow arithmetic, not a deep mathematical result. This is the most tractable single-step improvement available.
2. **Single deep axiom**: `erdos_1008` (Conlon-Fox-Sudakov main theorem) is the only remaining `axiom` declaration. All other components are proved: Kővári-Sós-Turán via cherry counting, K₂₂↔C₄ equivalence, structural lemmas, Folkman ratio, bipartite KST.
3. **All EMPTY knowledge tier**: All 12 available candidates score 0 knowledge items. Tiebreaker is composite score: tractability × 10 + significance. erdos-1008 scores 66 (tract 6, sig 6), tied with erdos-1026 and erdos-1027 but with a more concrete next step.
4. **Domain diversity**: Graph theory / extremal combinatorics (C₄-free subgraphs, Zarankiewicz problem) — different domain from the immediately preceding selections (erdos-1069: Szemerédi-Trotter geometry, dissection-of-cubes: geometry).
5. **No active claim or branch**: No `.lock` file and no `research/erdos-1008*` branch found.

## Rejection Summary

- **Candidates considered**: 12 available (from candidate pool)
- **Skipped — recently selected**: `erdos-1069` (b7b931e7ec, this session), `dissection-of-cubes` (0e0793f23a, this session)
- **Skipped — recently selected**: `binary-gcd-oq-01-oq-04-oq-01` (bdba7fbe78), `hilbert-10-oq-03` (e17ecb8422)
- **Rejected — active research branch**: `erdos-1131` (branches: erdos-1131-oq-01, erdos-1131-oq-01-axiom-reduction, erdos-1131-oq-01-session3)
- **Rejected — lower composite**: `borsuk-ulam-oq-02-oq-01-oq-03` (56), `erdos-1131` (56), `borsuk-ulam` (48), `erdos-1085` (48)
- **Rejected — tied but weaker target**: `erdos-1026` (66, 2 axioms both deep), `erdos-1027` (66, 1 axiom, no sorry to close)
- **Confidence**: medium (three-way tie at composite 66; erdos-1008 wins on concrete sorry availability)

## Related Gallery Proofs

- **erdos-1069** (just completed): Szemerédi-Trotter k-rich lines — shares extremal combinatorics context
- **erdos-157**: C₄-free and bipartite subgraph results — related Zarankiewicz machinery
- **szemeredi-core**: Regularity lemma infrastructure — potentially useful for probabilistic method arguments

## Suggested First Steps

1. **OBSERVE**: Read `proofs/Proofs/Erdos1008Problem.lean` in full. Locate `exponent_optimal` at line 560. Understand the chain: `|E(H)| < 2n²` (from `bip_edge_bound`) → `2n² < n^{2+3ε}` (from `n^{3ε} > 3`) → `n^{2+3ε} ≤ (n³)^{2/3+ε}` (rpow associativity) → `(n³)^{2/3+ε} ≤ |E(G)|^{2/3+ε}` (monotone rpow).
2. **ORIENT**: Identify which rpow lemmas are needed. Key Mathlib lemmas: `Real.rpow_natCast`, `Real.mul_rpow`, `Real.rpow_add`, `Real.rpow_le_rpow`. The step "2n² < n^{2+3ε}" requires `n^{3ε} > 3` which is established via `hn` from Archimedean.
3. **DECIDE**: Try `norm_num`, `nlinarith`, or `field_simp` + `rpow` lemmas to close the sorry. If those fail, establish the bound via `calc` chain with explicit intermediate steps.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 12 |
| In Progress | 406 |
| Completed | 1222 |
| **Total** | **1640** |

## Candidate Pool Health

- **Pool depth**: adequate (12 available, well above the 5-problem threshold)
- **Recommendation**: Pool healthy. No replenishment needed this cycle.
- **Next refresh recommended**: when available count drops below 5
