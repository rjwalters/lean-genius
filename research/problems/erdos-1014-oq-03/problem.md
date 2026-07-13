# Problem: Asymptotic formula for the consecutive off-diagonal Ramsey difference R(k,l+1) − R(k,l)

**Slug**: erdos-1014-oq-03
**Created**: 2026-07-09T15:40:17-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{Fix } k \ge 3. \text{ Determine whether } \Delta_l(k) := R(k,l+1) - R(k,l) \text{ admits an asymptotic formula } \Delta_l(k) \sim g_k(l) \ (l \to \infty).
$$

### Plain Language

The Ramsey number $R(k,l)$ is the smallest $n$ so that every red/blue edge-coloring of the complete graph $K_n$ contains a red $K_k$ or a blue $K_l$. For a fixed first argument $k$, we look at how much this number jumps when we bump the second argument by one: the increment $R(k,l+1) - R(k,l)$. This open question asks whether that increment settles into a clean, predictable growth rate — some explicit function $g_k(l)$ that it is asymptotically equal to — rather than fluctuating erratically as $l$ grows.

### Why This Matters

A meaningful asymptotic for the increment is strictly stronger than the ratio-convergence statement of Erdős Problem #1014 ($R(k,l+1)/R(k,l) \to 1$): knowing $\Delta_l(k) \sim g_k(l)$ pins down the local growth *rate* of the Ramsey function, not just that it grows smoothly. It would sharply constrain any conjectured closed form for $R(k,l)$ (for $k=3$ the expectation is $\Delta_l(3) \sim c\, l/\log l$, matching $R(3,l) \sim c\, l^2/\log l$), connect Ramsey growth to finite-difference/discrete-derivative techniques, and provide a concrete quantitative target that is often easier to attack than a full closed-form asymptotic.

## Known Results

### What's Already Proven

- Erdős–Szekeres upper bound $R(k,l) \le \binom{k+l-2}{k-1}$, giving polynomial growth $R(k,l) = O(l^{k-1})$ for fixed $k$ — Erdős–Szekeres (1935); `diagonal_ramsey_upper` in `Proofs/Erdos1014Problem.lean`
- Recurrence $R(k,l+1) \le R(k,l) + R(k-1,l+1)$, hence the increment bound $\Delta_l(k) \le R(k-1,l+1)$; for $k=3$ this specializes to $\Delta_l(3) \le l+1$ — `increment_bound_general`, `increment_bound_k3`
- Tight order of magnitude $R(3,l) = \Theta(l^2/\log l)$: AKS upper bound (1980) and Kim/Shearer lower bound (1995/1983) — `R3_asymptotic_bounds`, `R3_ratio_convergence`
- Monotonicity $R(k,l) \le R(k,l+1)$, so $\Delta_l(k) \ge 0$ — `ramsey_monotone_left`

### What's Still Open

- Whether $\Delta_l(3) := R(3,l+1) - R(3,l)$ has an asymptotic formula (conjecturally $\sim c\, l/\log l$), which is open because the implied constants in the $\Theta(l^2/\log l)$ bounds for $R(3,l)$ differ
- Whether any explicit $g_k(l)$ describes $\Delta_l(k)$ for fixed $k \ge 4$, where even the order of magnitude of $R(k,l)$ is unknown
- Whether the increment is even monotone or eventually smooth in $l$, as opposed to oscillating

### Our Goal

We do not attempt to resolve the open asymptotic. The tractable target is to formalize the *structural* consequences: prove in Lean that a power-law asymptotic $R(k,l) \sim c_k\, l^{k-1}/(\log l)^{k-2}$ would force $\Delta_l(k) \sim (k-1)\, c_k\, l^{k-2}/(\log l)^{k-2}$, and to relate this increment asymptotic to the already-formalized ratio and difference reformulations of #1014, giving a clean conditional bridge from asymptotics to increment behavior.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1014 | Parent problem: ratio convergence $R(k,l+1)/R(k,l)\to1$; supplies the increment bounds and $R(3,l)$ asymptotics this question builds on | Axiomatized Ramsey number, recurrence, real-analysis growth-ratio lemmas, ε–δ convergence |
| erdos-544 | Studies $R(3,l)$ growth, the best-understood case for the $k=3$ increment | Triangle-free process, probabilistic lower bounds |
| erdos-1030 | Diagonal Ramsey asymptotics $R(k,k)^{1/k}$; parallel regularity question along the diagonal | Stirling estimates, exponential growth bounds |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Conditional derivation from power-law asymptotics.
   - Why it might work: If $R(k,l) \sim c_k\, l^{k-1}/(\log l)^{k-2}$, then $\Delta_l(k) = R(k,l)\big((l+1)/l\big)^{k-1}(1+o(1)) - R(k,l)$ expands via the mean-value/binomial estimate to $\sim (k-1)R(k,l)/l$. This reuses the `GrowthRatioHelpers` lemmas already in the parent file.
   - Risk: It only yields a *conditional* increment asymptotic; it does not settle the unconditional open question and depends on an unproven hypothesis.

2. **Approach B**: Sandwich the $k=3$ increment between analytic bounds.
   - Why it might work: The upper increment bound $\Delta_l(3) \le l+1$ together with a lower bound derived from $R(3,l) = \Theta(l^2/\log l)$ could pin $\Delta_l(3)$ to order $l/\log l$ if the constants could be matched.
   - Risk: The constants in the AKS and Kim bounds genuinely differ; without matching them no true asymptotic (only an order-of-magnitude window) can be obtained — this is precisely why the problem is open.

### Key Difficulties

- The gap between the implied constants in $R(3,l) = \Theta(l^2/\log l)$ prevents comparing consecutive values sharply enough to isolate a leading term for the difference.
- For $k \ge 4$ the increment $R(k-1,l+1)$ is itself superlinear and of order comparable to $R(k,l)$, so no clean separation of scales exists.
- No Mathlib infrastructure computes or bounds Ramsey numbers beyond tiny explicit cases, so all growth facts must be axiomatized.

### What Would a Proof Need?

- Key lemma 1: A finite-difference expansion showing $g \sim c\, l^{a}/(\log l)^{b} \implies g(l+1)-g(l) \sim a\, c\, l^{a-1}/(\log l)^{b}$ over the reals.
- Key lemma 2: A transfer lemma converting the increment asymptotic into the ratio/difference statements already in `Erdos1014Problem.lean`.
- Technical requirements: `Filter.Tendsto`, `Asymptotics.IsEquivalent`, and the existing `GrowthRatioHelpers` real-analysis lemmas; an axiomatized $R(k,l)$ with recurrence and monotonicity.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The unconditional question is genuinely open (open even for $k=3$), so only conditional/structural formalization is realistically attainable.
- Similar conditional reductions were successfully formalized in the parent `erdos-1014` (e.g. `ratio_from_asymptotics`, `ratio_equiv_difference`), giving a proven template.
- Mathlib provides the analytic scaffolding (`Filter.Tendsto`, `Asymptotics.IsEquivalent`) but nothing Ramsey-specific, so the combinatorial content must remain axiomatic.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable: 1–2 weeks for the conditional increment-asymptotic formalization
- If hard: unknown (the unconditional asymptotic is a genuine open problem)

## References

### Papers
- Erdős, P., "On some extremal problems on r-graphs", Discrete Mathematics 1(1) (1971), 1–6 — poses Problem #1014 on Ramsey ratio growth, the parent of this increment question.
- Ajtai, M., Komlós, J., Szemerédi, E., "A note on Ramsey numbers", J. Combin. Theory Ser. A 29(3) (1980), 354–360 — upper bound $R(3,l) \le c\, l^2/\log l$.
- Kim, J.H., "The Ramsey number R(3,t) has order of magnitude t²/log t", Random Structures & Algorithms 7(3) (1995), 173–207 — matching lower bound via the triangle-free process.
- Mattheus, S., Verstraëte, J., "The asymptotics of r(4,t)", Annals of Mathematics 199(2) (2024), 919–941 — improved off-diagonal lower-bound constants via finite-field constructions.

### Online Resources
- https://erdosproblems.com/1014 — Erdős Problems database entry for the parent ratio-convergence problem.

### Mathlib
- `Mathlib.Analysis.Asymptotics.AsymptoticEquivalent` — provides `IsEquivalent` for stating $\Delta_l(k) \sim g_k(l)$.
- `Mathlib.Order.Filter.Basic` / `Mathlib.Topology.Algebra.Order.Tendsto` — `Filter.Tendsto` machinery for the limit reductions reused from the parent file.

## Metadata

```yaml
tags:
  - erdos
  - graph-theory
  - ramsey-theory
  - combinatorics
  - asymptotics
  - open
related_proofs:
  - erdos-1014
  - erdos-544
  - erdos-1030
difficulty: high
source: proof-suggestion
created: 2026-07-09T15:40:17-07:00
```
