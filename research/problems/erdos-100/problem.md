# Problem: Erdős #100: Point Sets with Restricted Distances

## Statement

### Plain Language

Let $A$ be a set of $n$ points in $\mathbb{R}^2$ such that all pairwise
distances are at least $1$ and any two distinct distances differ by at
least $1$. Equivalently (after rescaling), $A$ is a finite
*integer-distance set*: every pairwise distance is a positive integer.
Erdős asked whether such a set must have diameter that grows linearly
in $n$.

### Formal Statement

$$
\exists\, c > 0,\quad \forall^\infty n \in \mathbb{N},\quad
\inf_{\substack{A \subset \mathbb{R}^2 \\ |A| = n,\ A \text{ integer-distance}}}
\mathrm{diam}(A) \;\geq\; c \cdot n.
$$

In Lean (`Erdos100Conjecture` in `Erdos100Problem.lean`):

```lean
def Erdos100Conjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop,
    c * n ≤ minDiameterRestrictedSets n
```

The strong form (`Erdos100StrongConjecture`) replaces $c \cdot n$ with
$n - 1$.

## Classification

```yaml
tier: A
significance: 7
tractability: 5
tags:
  - erdos
  - discrete-geometry
  - distinct-distances
  - combinatorial-geometry
  - integer-distance-sets
  - open
```

**Significance**: 7/10
**Tractability**: 5/10

## Why This Matters

1. **Central open problem in discrete geometry.** The integer-distance
   restriction is one of the cleanest forcings of "rigidity" on point
   sets in the plane, and the gap between what is known
   ($\Omega(n/\log n)$, Guth–Katz 2015) and what is conjectured
   ($\Omega(n)$) is exactly one logarithmic factor — the same factor
   that obstructs many polynomial-method arguments.

2. **Direct link to Erdős's distinct-distances conjecture (#89).** For
   integer-distance sets the number of distinct distances $|\Delta(A)|$
   is at most $\lfloor \mathrm{diam}(A) \rfloor$, so
   $|\Delta(A)| \geq cn/\log n$ implies
   $\mathrm{diam}(A) \geq cn/\log n$. The bridge lemma
   `distinctDistances_le_diam` formalizes this reduction.

3. **Sharp interplay between continuous and discrete.** Erdős–Anning
   (1945) shows the *infinite* version fails completely (any infinite
   integer-distance set in $\mathbb{R}^2$ is collinear), so the question
   is genuinely finite. Piepmeyer's 9-point configuration shows the
   strong form $\mathrm{diam}(A) \geq n - 1$ fails for small $n$,
   bounding the optimal linear constant by $5/9$.

4. **Standard test case for the polynomial method.** The Elekes–Sharir
   reduction used by Guth–Katz inherently loses a $\log n$ factor;
   closing the gap to linear would either require a fundamentally
   different technique or a counterexample family with sublinear
   diameter.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| erdos-89 | Distinct-distances conjecture. The Guth–Katz $\Omega(n/\log n)$ bound feeds directly into the diameter bound here via the bridge lemma. |
| erdos-94 | Distance multiplicities in convex polygons. Shares the distance-counting and pigeonhole techniques. |
| erdos-104 | Unit circles through points. Same incidence-counting setup. |
| erdos-1066 | Independence number of unit-distance graphs. Same underlying graph structure. |
| erdos-1007 | Graph dimension and unit-distance embedding. Geometric embedding companion. |

## Current Formalization Status

**COMPLETED (axiomatized)** — see `state.md`.

- `proofs/Proofs/Erdos100Problem.lean`: 482 lines, 0 sorries, 2 axioms.
- 14 theorems proved including the bridge lemma
  `distinctDistances_le_diam` and the main lower bound
  `diam_ge_n_over_log_n`.
- Axioms: `guthKatz_distinct_distances` (Guth–Katz 2015) and
  `piepmeyer_construction` (9-point integer-distance set, diam < 5).
- Conjectures `Erdos100Conjecture` (linear) and
  `Erdos100StrongConjecture` ($n - 1$) are stated formally and remain
  OPEN.

## References

- [Erdős Problems #100](https://erdosproblems.com/100) — primary
  problem statement and historical context.
- Guth, L. & Katz, N. (2015). *On the Erdős distinct distances problem
  in the plane.* Annals of Mathematics 181 (1), 155–190.
- Erdős, P. & Anning, N. H. (1945). *Integral distances.* Bulletin of
  the AMS 51 (8), 598–600.
- Piepmeyer, L. — explicit 9-point integer-distance construction with
  diameter $< 5$.
