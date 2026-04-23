# Problem: Optimal Constant in Diameter Lower Bound (Erdős #100)

**Slug**: erdos-100-oq-03
**Created**: 2026-04-23T11:58:34+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{Find the optimal constant } c > 0 \text{ such that for any } n\text{-point set }
P \subset \mathbb{R}^2 \text{ with at most } n \text{ distinct pairwise distances,}
\quad \text{diam}(P) \geq c \cdot n.
$$

Equivalently: what is $\displaystyle c^* = \liminf_{n \to \infty} \frac{\text{diam}(P_n)}{n}$
over all valid $n$-point configurations?

### Plain Language

Erdős #100 (Point Sets with Restricted Distances) asks about $n$-point sets in the plane
where the number of distinct pairwise distances is at most $n$. The gallery entry
`erdos-100` has formalized that the diameter of such a set grows at least linearly ($\geq c \cdot n$
for some $c > 0$).

The open question is: **what is the best possible constant $c$?** The current lower bound
proven in the gallery may not be tight. Piepmeyer (1996) constructed a 9-point example
achieving a specific diameter-to-$n$ ratio; extending this to large $n$ would give an
upper bound on $c^*$.

### Why This Matters

Pinning down $c^*$ is a step toward resolving the full Erdős #100 conjecture. It requires
understanding extremal configurations — either:
1. Proving the known lower bound is tight (by exhibiting matching configurations), or
2. Improving the lower bound constant using analytic/combinatorial methods.

This is a genuine open problem in combinatorial geometry. Even formalizing the **question**
precisely in Lean (what the right definition of $c^*$ is) has value.

## Known Results

### What's Already Proven

- `erdos-100` gallery: For any $n$-point set with $\leq n$ distinct distances, $\text{diam}(P) \geq cn$
  for some absolute constant $c > 0$ (formalized with axioms/sorries for the construction)
- Piepmeyer (1996): 9-point construction showing $c^* \leq \text{diam}(P_9)/9$
- Guth-Katz (2015): $n$-point sets have $\Omega(n/\log n)$ distinct distances in general,
  not directly about restricted-distance sets

### What's Still Open

- The exact value of $c^*$
- Whether Piepmeyer's 9-point construction generalizes to an infinite family
- Whether $\text{diam}(P) \geq n-1$ for large $n$ (the strong conjecture)

### Our Goal

At the formalization level:
1. Precisely define $c^*$ in Lean as a `liminf`
2. Compute the lower bound $c$ from the existing `erdos-100` proof
3. Compute the Piepmeyer upper bound from the 9-point construction (by `decide`/`norm_num`)
4. State the gap as a formal open problem

A full resolution of $c^*$ is likely out of reach; formalizing the question and bounding the gap is the goal.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `erdos-100` | Parent proof, linear diameter lower bound | Distance combinatorics, point set geometry |
| `erdos-100-oq-01` | Is diam ≥ n-1 strong conjecture | Extremal configurations |
| `erdos-100-oq-02` | Piepmeyer extension question | Construction methods |

## Initial Thoughts

### Potential Approaches

1. **Compute Piepmeyer's ratio**: For the known 9-point construction, use `native_decide` to
   compute $\text{diam}(P_9)/9$ and establish $c^* \leq \text{that ratio}$.
   - Why it might work: Finite computation on a fixed point set.
   - Risk: Need to coordinate with how `erdos-100` defines "valid" configurations.

2. **Formalize $c^*$ as liminf**: Use Mathlib's `Filter.liminf` to define
   $c^* = \liminf_{n\to\infty} \inf_{P : \text{valid}(n)} \text{diam}(P)/n$.
   - Why it might work: Mathlib has liminf infrastructure.
   - Risk: The infimum over all valid $P$ may be hard to state without a clean definition.

3. **Survey approach**: Read the `erdos-100` Lean source, extract the current constant $c$,
   compare to Piepmeyer's construction, and document the gap formally in `problem.md` / `knowledge.md`.
   This is a **research/orientation** task even if no new Lean theorem results.
   - Why it might work: Clarifies what remains to be done.

### Key Difficulties

- The `erdos-100` proof may use existential $c$ without a computable value
- Defining "at most $n$ distinct distances" in Lean requires a clean finite set definition
- The Piepmeyer configuration (9 points) needs to be encoded as a `Finset (ℝ × ℝ)`

### What Would a Proof Need?

- Read `erdos-100` Lean source to extract the current $c$
- Encode Piepmeyer's 9 points explicitly
- `Finset.card (Finset.image (dist · ·) (Finset.product P P))` for distance counting

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematical content is genuinely open (exact $c^*$ unknown)
- The formalization goal is modest: state the gap, bound it from both sides
- Piepmeyer computation is finite and doable; the lower bound extraction requires reading code

**Estimated Effort**:
- Exploration: 2-4 hours (read erdos-100 source, understand current $c$)
- If tractable: 3-7 days (encode Piepmeyer, prove bounds, formalize gap statement)
- If hard: 2+ weeks (if the lower bound $c$ is buried in non-computable arguments)

## References

### Papers
- Erdős (1946) — Original "Point Sets with Restricted Distances" problem
- Piepmeyer (1996) — 9-point extremal construction
- Guth-Katz (2015) — Distinct distances in the plane (related, not identical)

### Mathlib
- `Mathlib.Topology.MetricSpace.Basic` — `dist` API
- `Mathlib.Order.Filter.Basic` — `Filter.liminf` for the constant definition
- `Mathlib.Data.Finset.Basic` — finite point set computations

## Metadata

```yaml
tags:
  - combinatorics
  - geometry
  - erdos
  - extremal-combinatorics
  - distance-geometry
related_proofs:
  - erdos-100
  - erdos-100-oq-01
  - erdos-100-oq-02
difficulty: medium
source: gallery-gap
created: 2026-04-23T11:58:34+02:00
```
