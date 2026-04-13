# Problem: Erdős #1069 — Szemerédi-Trotter on k-Rich Lines (Axiom Reduction)

**Slug**: erdos-1069
**Created**: 2026-04-05T08:11:58-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

**Gallery status**: `axiomatized` with 2 axioms:
1. `szemeredi_trotter` — The main incidence bound: I(P,L) ≤ C·(n^{2/3}·m^{2/3} + n + m)
2. `kRich_bound` — The k-rich lines bound: numKRichLines(P,L,k) ≤ C·n²/k³ when k² ≤ n

**Research goal**: Prove `kRich_bound` as a theorem from `szemeredi_trotter`, reducing axiom count from 2 → 1.

$$
\text{If } k^2 \leq |P|, \text{ then } |\{l \in L : |P \cap l| \geq k\}| \leq C \cdot \frac{|P|^2}{k^3}
$$

### Plain Language

Given n points in the plane, how many lines can each pass through at least k of those points? The answer is O(n²/k³) — the Szemerédi-Trotter theorem proves this via an elegant counting argument:

If m lines are each k-rich, then the total incidence count satisfies mk ≤ I(P,L). The Szemerédi-Trotter bound then gives mk ≤ C(n^{2/3}·m^{2/3} + n + m). Solving algebraically yields m ≤ O(n²/k³).

The `kRich_bound` axiom is therefore *logically derivable* from `szemeredi_trotter`. The current Lean formalization axiomatizes both independently. We can reduce to 1 axiom.

### Why This Matters

- Szemerédi-Trotter is a cornerstone of incidence geometry; its applications include the Erdős distinct distances problem and sum-product estimates
- Formalizing the derivation would strengthen the gallery's incidence geometry chain
- The counting argument is elementary — good candidate for Lean mechanization

## Known Results

### What's Already Proven

- **In the gallery (axiomatized)**: both `szemeredi_trotter` and `kRich_bound` are stated as axioms
- `erdos_1069` and `erdos_1069_summary` are theorems that trivially follow from the axioms
- `kRich_incidences_lower`: mentioned in section summaries as "Verified" — if this says mk ≤ totalIncidences, that's the key lemma
- The actual Lean file has only the 2 axioms; other "axioms" in section descriptions are from the gallery UI metadata, not from the Lean source

### The Derivation (on paper)

Let P be n points, L be a finite set of lines, m = numKRichLines(P, L, k).

1. **Lower bound on incidences**: Each k-rich line contributes ≥ k incidences, so:
   m·k ≤ totalIncidences(P, kRichLines(P, L, k)) ≤ totalIncidences(P, L)

2. **Szemerédi-Trotter upper bound**:
   totalIncidences(P, L) ≤ C·(n^{2/3}·|L|^{2/3} + n + |L|)

3. **Combined**: mk ≤ C·(n^{2/3}·m^{2/3} + n + m)

4. **Algebraic solve for m** (assuming mk > Cm, i.e., k > C):
   - If mk ≤ 2Cn^{2/3}·m^{2/3}: then mk/2C ≤ n^{2/3}·m^{2/3}, so (m/k)^{1/3} ≤ (2C·n^{2/3}/k)... → m ≤ (2C)³·n²/k³
   - If mk ≤ 2Cn: then m ≤ 2Cn/k ≤ 2Cn²/k³ (when k² ≤ n)

### What's Still Open

- Proving `szemeredi_trotter` from scratch (very hard — requires crossing number inequality)
- Tight constants
- Generalization to curves

### Our Goal

**Specific goal**: Prove `kRich_bound` as a `theorem` from `szemeredi_trotter` by formalizing the counting + algebraic argument. Remove the `kRich_bound` axiom.

Secondary: Check if any of the "dyadic" or "lower bound" axioms from gallery sections actually appear in the Lean source (they don't — only 2 axioms exist).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `erdos-1085` (Unit Distance) | Same incidence geometry family | Incidence bounds |
| `erdos-89` (Distinct Distances) | Uses Szemerédi-Trotter as key tool | Polynomial method |
| `erdos-52` (Sum-Product) | Elekes argument uses Szemerédi-Trotter | Incidence counting |
| `erdos-211` (Beck's Theorem) | Closely related incidence result | Crossing number |

## Initial Thoughts

### Potential Approaches

1. **Direct counting derivation**:
   - Prove `incidences_lower`: numKRichLines(P,L,k) * k ≤ totalIncidences(P,L)
   - Apply `szemeredi_trotter` to get upper bound
   - Do algebra: mkk ≤ C(n^{2/3}m^{2/3} + n + m) → m ≤ C'·n²/k³
   - Risk: Real-number algebra in Lean can be painful; nnreal or ℕ casting issues

2. **Existential C approach** (matching the axiom signature):
   - The axiom gives: ∃ C > 0, numKRichLines ≤ C · n²/k³
   - We can extract the C from `szemeredi_trotter` and construct the right C for kRich_bound
   - May need to case-split on whether mk ≤ 2Cn^{2/3}m^{2/3} or mk ≤ 2Cn

3. **Aristotle-first** (if steps 1-2 prove difficult):
   - Turn `kRich_incidences_lower` (mk ≤ I(P,L)) into a theorem/sorry
   - Let Aristotle handle the mechanical parts
   - Focus human effort on the algebraic inequality solve

### Key Difficulties

- The `totalIncidences` function sums `incidenceCount` over all lines; relating this to `numKRichLines` requires Finset.sum inequalities
- `pointsOnLine` uses `decide` with `Real.decEq` — may have universe issues or be non-computable
- The algebraic step (mk ≤ C(n^{2/3}m^{2/3} + n + m) → m ≤ C'n²/k³) requires careful real arithmetic
- `k^2 ≤ n` hypothesis is needed to convert the n/k term to n²/k³

### What Would a Proof Need?

- **Key lemma 1** (incidences_lower): `numKRichLines(P, L, k) * k ≤ totalIncidences(P, L)`
  - Proof: `Finset.sum_le_sum` over k-rich lines, each contributing ≥ k
- **Key lemma 2** (algebraic): From mk ≤ C(n^{2/3}m^{2/3} + n + m) and k² ≤ n, derive m ≤ C'n²/k³
  - Lean-side: `nlinarith` or `positivity` with manual case splits
- **Technical**: Coercion from ℕ to ℝ for all cardinality terms

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematical argument is elementary (a 3-step counting + algebra derivation)
- Lean4 real arithmetic with `nlinarith`/`linarith` can handle polynomial inequalities
- `Finset.sum_le_sum` and `Finset.card_filter_le` are available in Mathlib
- Main risk: casting between ℕ and ℝ for `Finset.card` and `Finset.sum`; also the `decide` approach to `pointsOnLine` may need `Classical.decProp` to work

**Estimated Effort**:
- Exploration: 1 iteration (OBSERVE/ORIENT)
- If tractable: 2-3 iterations (DECIDE/ACT with algebra)
- If hard: may need intermediate lemmata or Aristotle for sub-goals

## References

### Papers
- Szemerédi & Trotter, "Extremal problems in discrete geometry", Combinatorica 1983
- Székely, "Crossing numbers and hard Erdős problems", CPC 1997 — elegant re-proof
- Elekes, "On the number of sums and products", Acta Arith 1997 — sum-product application

### Online Resources
- https://erdosproblems.com/1069 — problem statement and history

### Mathlib
- `Mathlib.Algebra.BigOperators.Group.Finset` — `Finset.sum_le_sum`, summation bounds
- `Mathlib.Data.Finset.Card` — `Finset.card_filter_le`, `Finset.card_le_card`
- `Mathlib.Analysis.SpecialFunctions.Pow.Real` — real-number powers (n^(2/3))

## Metadata

```yaml
tags:
  - incidence-geometry
  - combinatorial-geometry
  - erdos
  - szemeredi-trotter
  - axiom-reduction
related_proofs:
  - erdos-1085
  - erdos-89
  - erdos-52
difficulty: medium
source: gallery-gap
created: 2026-04-05T08:11:58-07:00
```
