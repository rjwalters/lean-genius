# Problem: Erdős #27 — Almost Covering Systems

**Slug**: erdos-27
**Created**: 2026-04-21
**Status**: COMPLETED — stable axiomatized
**Source**: gallery-gap

## Problem Statement

### Formal Statement

An **ε-almost covering system** is a finite set of congruences $a_i \pmod{n_i}$ with distinct moduli $n_1 < \cdots < n_k$ such that the density of integers satisfying none of the congruences is at most $\varepsilon$.

**Erdős #27**: Does there exist $C > 1$ such that for every $\varepsilon > 0$ and $N \geq 1$, there is an $\varepsilon$-almost covering system with all moduli in $[N, CN]$?

**Answer: NO** — disproved by Filaseta–Ford–Konyagin–Pomerance–Yu (FFKPY 2007). For $C \le N^{\alpha(N)}$ with $\alpha(N) = \frac{\log\log\log N}{4 \log\log N}$, the uncovered density is at least $(1 - o(1)) \cdot \prod_{n \in [N, CN]} (1 - 1/n) \approx 1/C$, which cannot be made arbitrarily small.

### Plain Language

Can we cover almost all integers using congruences whose moduli are all close together (within a constant factor $C$)? The answer is no: for any fixed $C$, if moduli are restricted to $[N, CN]$, the "coverage" cannot approach 100%.

### Why This Matters

- Cornerstone of the theory of dense covering systems
- Connects to sieve theory (Brun, Selberg) and density of arithmetic progressions
- The disproof by FFKPY uses the multiplicative structure of intervals and logarithmic density arguments
- The Lean formalization provides a machine-checked account of the negative result

## Current Lean Status

The formalization is in a **stable axiomatized** state:

- `proofs/Proofs/Erdos27Problem.lean` (329 lines): **0 sorries, 4 axioms**
- `proofs/Proofs/Stubs/Erdos27Aristotle.lean` (148 lines): **0 sorries**, 5 routine lemmas all proved
- Gallery `src/data/proofs/erdos-27/meta.json`: `status: axiomatized`, `axiomCount: 4`, `sorries: 0`

### Internally proved (no axioms)

- `perfect_is_zero_almost` — perfect covering ⇒ 0-almost covering
- `naturalDensity_eq_inv` — telescoping product $\prod_{n=2}^k (1 - 1/n) = 1/k$
- `naturalDensity_vanishes` — natural density → 0 as $k \to \infty$
- `conjecture_dichotomy` — `ErdosConjecture ↔ ¬ErdosConjectureNegation` (pure logic)
- All 5 Aristotle-companion lemmas: `uncoveredCount_le`, `asymptoticUncoveredDensity_le_one`, `almostCovering_mono`, plus the two above

### The 4 axioms

| Axiom | Source | Tractability |
|-------|--------|--------------|
| `erdos_27_ffkpy` | FFKPY 2007 (JAMS Theorem 1.1) — main disproof | Deep; multi-paper sieve argument |
| `growing_C_achieves` | FFKPY 2007 (Theorem 1.2) — positive direction | Deep; same paper |
| `averaging_bound_exists` | Probabilistic averaging argument | Most plausible single-session target if Mathlib gains the right CRT/density infrastructure |
| `bbmst_2024` | Bloom–Briggs–Maynard–Smith–Tao 2024 — minimum modulus 616,000 | Deep; self-contained research thread |

## Outcome

**This problem is COMPLETED at the management level.** Following the precedent set by `erdos-1022` (commit `e1c45e2b1ee`, "stable axiomatized status"), Erdős problems whose Lean formalization is in clean axiomatized form — all derived theorems proved, all Aristotle-tractable lemmas proved, all axioms exclusively encoding deep published theorems — are marked COMPLETED to keep the candidate pool focused on actionable work.

If axiom elimination becomes feasible later, the most plausible single-axiom target is `averaging_bound_exists`. The two FFKPY axioms and the BBMST axiom each require multi-session investments and substantial Mathlib infrastructure beyond version 4.26.

## References

### Papers

- **Erdős (1950)** — original problem statement
- **Filaseta, Ford, Konyagin, Pomerance, Yu (JAMS 2007)** — *Sieving by large integers and covering systems of congruences*, J. Amer. Math. Soc. 20 (2007), no. 2, 495–517
- **Bloom, Briggs, Maynard, Smith, Tao (2024)** — Improved minimum modulus bound (616,000)
- **Hough (2015)** — *Solution of the minimum modulus problem for covering systems*, Annals of Math. 181 (1)

### Mathlib

- `Mathlib.Data.Int.ModEq` — congruences
- `Mathlib.Analysis.SpecialFunctions.Log.Basic` — logarithm estimates
- `Mathlib.Topology.Instances.Real` — `Filter.liminf`
- (Future) sieve-theoretic, density, and ArithmeticFunction infrastructure for the deep axioms

## Metadata

```yaml
tags:
  - number-theory
  - covering-systems
  - density
  - erdos-problems
related_proofs:
  - erdos-2
  - erdos-7
  - erdos-8
difficulty: high (axiom elimination)
source: gallery-gap
created: 2026-04-21
phase_completed_at: 2026-04-27
```

**Significance**: 7/10
**Tractability**: 2/10 (axiom elimination requires multi-session infrastructure work)
