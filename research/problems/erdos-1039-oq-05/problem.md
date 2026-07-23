# Problem: Relating ρ(f) to transfinite diameter and logarithmic capacity

**Slug**: erdos-1039-oq-05
**Created**: 2026-07-09T15:40:19-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\rho(f) = \sup\{r > 0 : \exists c \in \mathbb{C},\ B(c,r) \subseteq \{z : |f(z)| < 1\}\}, \qquad f(z) = \prod_{i=1}^{n}(z - z_i),\ |z_i| \le 1.
$$

Let $d(Z)$ be the transfinite diameter of the root multiset $Z = \{z_1,\dots,z_n\}$ and let $\operatorname{cap}(E)$ denote the logarithmic capacity of the lemniscate complement $E = \{z : |f(z)| \ge 1\}$. The task is to determine explicit quantitative relations of the form $\rho(f) \gtrsim g\big(d(Z), \operatorname{cap}(E)\big)$ and to decide whether either potential-theoretic quantity governs the conjectured lower bound $\rho(f) \gg 1/n$.

### Plain Language

For a monic polynomial whose roots all lie in the closed unit disc, the region where $|f(z)| < 1$ (a "lemniscate interior", a union of at most $n$ petals) contains a largest inscribed disc of radius $\rho(f)$. Two classical potential-theoretic numbers are attached to the same polynomial: the transfinite diameter of the set of roots (roughly, how spread out the roots are), and the logarithmic capacity of the complementary set where $|f| \ge 1$. We want to know, precisely, how the size of the biggest inscribed disc is controlled by these two capacity-type quantities.

### Why This Matters

The lemniscate $\{|f(z)| = 1\}$ is the level-1 set of the Green's function of the complement of $\{|f| < 1\}$, so $\rho(f)$ is a genuinely potential-theoretic quantity in disguise. Pinning down its relationship with transfinite diameter and logarithmic capacity would recast the open Erdős–Herzog–Piranian conjecture $\rho(f) \gg 1/n$ as a capacity inequality, connecting Problem 1039 directly to Problem 1040 (transfinite diameter) and Problem 1038 (sublevel-set measure). Because logarithmic capacity is exactly the tool Pommerenke (1961) used for the first lower bound $\rho(f) \ge 1/(2en^2)$ and underlies the KLR (2025) area method, a clean capacity characterization could be the route to eliminating the residual $\sqrt{\log n}$ gap.

## Known Results

### What's Already Proven

- Pommerenke (1961): $\rho(f) \ge 1/(2en^2)$ for every unit-disc polynomial, via Green's-function and Koebe-distortion estimates — capacity is already the engine — captured as the `pommerenke_lower` axiom in `Proofs/Erdos1039Problem.lean`.
- Krishnapur–Lundberg–Ramachandran (2025): area$(\{|f|<1\}) \ge \pi/(n^2\log n)$ hence $\rho(f) \ge c/(n\sqrt{\log n})$ — the `klr_area_bound` and `klr_lower` axioms.
- Fekete–Szegő theory: for a compact set $E$, transfinite diameter $d(E)$, logarithmic capacity $\operatorname{cap}(E)$, and Chebyshev constant coincide; the lemniscate $\{|f| \le 1\}$ has $\operatorname{cap} = 1$ for monic $f$ of degree $n$ (a classical normalization).
- Benchmark $\rho(z^n-1) \le \pi/(2n)$ — the `benchmark_upper` axiom — fixes the target rate $\Theta(1/n)$.

### What's Still Open

- Whether $\rho(f)$ admits a two-sided bound purely in terms of $d(Z)$ and $\operatorname{cap}(\{|f| \ge 1\})$, uniformly in $n$.
- Whether the transfinite diameter of the root set alone (independent of their fine spacing) can force $\rho(f) \ge c/n$, or whether spacing information beyond capacity is essential.
- The main Erdős–Herzog–Piranian conjecture $\rho(f) \gg 1/n$ itself, and in particular removal of the $\sqrt{\log n}$ factor.

### Our Goal

Formalize the definitions of transfinite diameter of the root multiset and logarithmic capacity of the lemniscate complement in the existing `Erdos1039` framework, and state (as theorems where provable, axioms where they cite the literature) the quantitative links $\rho(f) \gtrsim g(d(Z), \operatorname{cap})$. We do not attempt to resolve the $1/n$ conjecture; we scope to making the capacity/transfinite-diameter relationship precise and machine-checkable, mirroring the `pommerenke_lower`/`klr_area_bound` axiom pattern.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1039 | Parent problem: defines ρ(f), sublevel set, and the bound hierarchy this OQ extends | Lemniscate geometry, inscribed disc radius, area bounds, axiomatized capacity results |
| erdos-1040 | Directly about transfinite diameter and sublevel-set measure — the other half of this relationship | Transfinite diameter, Green's functions, potential theory |
| erdos-1038 | Sublevel-set measure feeds the KLR area bound linking capacity to ρ(f) | Lebesgue measure of {\|f\|<1}, capacity estimates |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Capacity-to-radius via Green's function**: Express $\rho(f)$ through the Green's function $g_E$ of the lemniscate complement, use $\operatorname{cap}(E)=1$ normalization, and derive $\rho(f) \gtrsim h(\operatorname{cap})$ from Harnack/Koebe distortion of $g_E$ near the level-1 curve.
   - Why it might work: this is precisely Pommerenke's toolkit, already implicitly axiomatized, so the scaffolding exists.
   - Risk: making the Green's-function machinery explicit in Lean/Mathlib may require infrastructure (subharmonic functions, capacity) that Mathlib currently lacks.

2. **Approach B — Fekete points and transfinite diameter of $Z$**: Bound $\rho(f)$ below using the transfinite diameter $d(Z)$ of the root multiset via the arithmetic–geometric spread of $|f|$ on a candidate disc.
   - Why it might work: $d(Z)$ controls the minimal product $\prod|z-z_i|$ and hence where $|f|<1$ holds; roots-of-unity minimize spread and give the worst case.
   - Risk: $d(Z)$ alone may not distinguish clustered from spread configurations finely enough to reach $1/n$; capacity of the complement may be the sharper invariant.

### Key Difficulties

- Mathlib has essentially no logarithmic-capacity / transfinite-diameter API, so definitions must be built from scratch or axiomatized.
- Separating what is genuinely provable from what must cite Pommerenke/KLR (to respect the axiom-integrity policy: any literature-dependent inequality becomes an `axiom`, counted in `axiomCount`).

### What Would a Proof Need?

- Key lemma 1: a formal definition of transfinite diameter $d(Z) = \lim_k \big(\max \prod_{i<j}|w_i-w_j|\big)^{2/(k(k-1))}$ specialized to the finite root multiset (or its finite-$n$ discrete version $\prod_{i<j}|z_i-z_j|^{2/(n(n-1))}$).
- Key lemma 2: a formal definition of logarithmic capacity of the compact complement piece $\{|f|\ge 1\}\cap\overline{B(0,R)}$ and the normalization $\operatorname{cap}=1$.
- Technical requirements: Green's-function estimates or an equivalent isoperimetric/area bridge connecting capacity to the inscribed disc radius, plus the existing `sublevelArea`/`area_implies_disc_bound` lemmas.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The underlying mathematics is open research (the $1/n$ conjecture is unresolved), so a full characterization is a moonshot; a *stated, axiom-backed* relationship is high-but-feasible.
- Similar problems solved: the parent `erdos-1039` successfully axiomatized Pommerenke and KLR while proving the elementary geometry lemmas — the same pattern applies here.
- Techniques available in Mathlib: `MeasureTheory.volume`, `Complex.abs`, `Polynomial.eval₂`, `Real.log` exist; capacity/transfinite-diameter do not, so those pieces must be defined or axiomatized.

**Estimated Effort**:
- Exploration: 2–4 days
- If tractable: 2–3 weeks (definitions + stated relations with a few proved special cases)
- If hard: unknown (a genuine capacity characterization implying $1/n$ would resolve the open conjecture)

## References

### Papers
- Erdős, Herzog, Piranian, "Metric properties of polynomials", J. Analyse Math. 6 (1958) — origin of $\rho(f)$ and the lemniscate geometry questions.
- Pommerenke, "On metric properties of complex polynomials", Michigan Math. J. 8 (1961) — capacity/Green's-function lower bound $\rho \ge 1/(2en^2)$.
- Krishnapur, Lundberg, Ramachandran, "Inscribed discs in polynomial lemniscates" (2025) — area/capacity method giving $\rho \ge c/(n\sqrt{\log n})$.

### Online Resources
- https://erdosproblems.com/1039 — canonical statement, status, and bound history for Problem 1039.
- https://erdosproblems.com/1040 — companion transfinite-diameter problem referenced by this open question.

### Mathlib
- Mathlib.MeasureTheory.Measure.MeasureSpace — Lebesgue measure for area bounds bridging capacity to $\rho(f)$.
- Mathlib.Analysis.SpecialFunctions.Complex.Circle — `Complex.abs` for the sublevel set and lemniscate.
- Mathlib.Analysis.SpecialFunctions.Log.Basic — `Real.log` for capacity/Green's-function-style logarithmic quantities.

## Metadata

```yaml
tags:
  - complex-analysis
  - polynomials
  - potential-theory
  - lemniscates
  - open-problem
related_proofs:
  - erdos-1039
  - erdos-1040
  - erdos-1038
difficulty: high
source: proof-suggestion
created: 2026-07-09T15:40:19-07:00
```

## Adversarial Checklist (claim: transfinite diameter of the closed unit disc = 1, dₙ = n^{1/(n-1)} exactly)

Recorded 2026-07-23 for the SOLVED claim of the scoped transfinite-diameter program
(`Erdos1039TransfiniteDiameter.lean`, theorems `transfiniteDiameterN_eq_rpow`,
`transfiniteDiameter_eq_one`). How THIS claim could be wrong:

- **Wrong set**: confirm `discreteDiameter`/`transfiniteDiameterN` quantify over ALL
  `z : Fin n → ℂ` with `∀ i, ‖z i‖ ≤ 1` (closed unit disc), not merely roots of unity or
  the boundary circle. The upper bound must hold for every configuration — check
  `transfiniteDiameterN_le_rpow` takes an arbitrary `hz : ∀ i, ‖z i‖ ≤ 1`.
- **Sup vs max**: `transfiniteDiameterN n` is a `csSup` over the set of discrete diameters;
  the upper bound must go through `csSup_le` with the nonemptiness witness
  (`unitDiscDiameters_nonempty`) — an empty-set `csSup = 0` degenerate would make the
  "equality" vacuous. Requires `n ≥ 2` (the `m + 2` indexing).
- **Exponent off-by-one**: `dₙ = (spreadProduct)^{2/(n(n-1))}`, so the Hadamard bound
  `spreadProduct ≤ n^{n/2}` must convert to exponent `(n/2)·(2/(n(n-1))) = 1/(n-1)` —
  check the `field_simp` rpow algebra in `discreteDiameter_le_rpow`, not `1/n` or `2/n`.
- **Hadamard row/column form**: `norm_det_le_prod_norm_row` bounds by ROW norms; the
  Vandermonde rows must be the power sequences `(1, zᵢ, …, zᵢⁿ⁻¹)` (each of ℓ²-norm ≤ √n),
  not the columns (whose norms are NOT uniformly √n-bounded in the same way). Check
  `Matrix.vandermonde_apply` orientation: `vandermonde z i j = z i ^ (j : ℕ)` — rows indexed
  by points. ✓ matches.
- **Circularity**: the limit `d = 1` combines `transfiniteDiameter_le m` (monotone/inf
  structure) with the root-of-unity LOWER bound already on main; neither imports any
  axiom — `#print axioms transfiniteDiameter_eq_one` should show only
  propext/Classical.choice/Quot.sound. File has 0 `axiom` declarations.
- **Not the parent**: this claim is about `d` of the DISC (= cap = 1 normalization), NOT
  the Erdős–Herzog–Piranian `ρ(f) ≫ 1/n`, which remains OPEN; the ρ-capacity bridge
  (Green's function machinery) remains deep-blocked and is NOT claimed.
