# Problem: Eulerian-number interpretation of the h*-vector of the unit cube

## Statement

### Plain Language

For the unit d-cube $[0,1]^d$, prove in Lean 4 that the Ehrhart h*-vector $(h_0^*, h_1^*, \ldots, h_{d-1}^*)$ is the sequence of Eulerian numbers $(A(d, 0), A(d, 1), \ldots, A(d, d-1))$, where $A(d, k)$ counts permutations of $\{1, \ldots, d\}$ with exactly $k$ descents.

Equivalently, prove **Worpitzky's identity** for the cube:

$$ (n+1)^d \;=\; \sum_{k=0}^{d-1} A(d, k) \cdot \binom{n+1+k}{d} \qquad \text{for all } d \geq 1, \; n \geq 0. $$

### Formal Statement

```lean
theorem worpitzky_identity_cube (d : ℕ) (hd : 0 < d) (n : ℕ) :
    (n + 1)^d = ∑ k ∈ Finset.range d,
                eulerianNumber d k * Nat.choose (n + 1 + k) d
```

where `eulerianNumber : ℕ → ℕ → ℕ` is defined via the recurrence
$A(d+1, k+1) = (k+2) A(d, k+1) + (d - k) A(d, k)$
with $A(0, 0) = 1$, $A(0, k+1) = 0$, $A(d+1, 0) = A(d, 0)$.

### Equivalent Forms

1. **Worpitzky form** (above).
2. **Generating-function form** (after $1/(1-t)^{d+1} = \sum_m \binom{m+d}{d} t^m$):
$$ \sum_{n \geq 0} (n + 1)^d \cdot t^n \;=\; \frac{\sum_{k=0}^{d-1} A(d, k) \cdot t^k}{(1 - t)^{d+1}} \;\in\; \mathbb{Q}[[t]]. $$
3. **h*-vector form** (after the palindrome $A(d, k) = A(d, d-1-k)$):
$$ (n+1)^d \;=\; \sum_{k=0}^{d-1} A(d, k) \cdot \binom{n + d - k}{d}. $$

## Classification

```yaml
tier: B
significance: 6
tractability: 6
tags:
  - combinatorics
  - ehrhart-theory
  - eulerian-numbers
  - h-star-vector
  - worpitzky-identity
  - permutation-statistics
  - seeker-selected
  - gallery-extracted
```

**Significance**: 6/10
**Tractability**: 6/10

## Why This Matters

1. **Completes the Ehrhart h*-vector story for one of the three classical lattice polytopes.** The h*-vector of the unit cube is one of three classical h*-vector examples in Ehrhart theory:
   - Simplex $\Delta^d$: h* = $(1, 0, \ldots, 0)$ (trivial).
   - Cross-polytope $B_d$: h* = $\binom{d}{k}$ (Pascal).
   - **Cube $[0,1]^d$**: h* = Eulerian numbers $(A(d, k))$ — the *only* row of the three with non-trivial combinatorial content.

2. **Connects Ehrhart theory to permutation statistics.** The Eulerian numbers are foundational in algebraic combinatorics (Stanley's *EC1* §1.4), with applications to symmetric functions, $q$-analogues, and the Foulkes-Riffel cohomology. Closing this OQ-04 establishes a Lean-formal bridge between two communities.

3. **Validates Stanley's 1980 non-negativity theorem in a non-trivial case.** Stanley's theorem $h_k^* \geq 0$ for any lattice polytope is purely algebraic (Cohen-Macaulay rings); the cube case admits a *combinatorial* witness (descent count), which is a non-trivial reformulation.

4. **Mathlib contribution path.** Mathlib does not yet have explicit Eulerian numbers or permutation descents (verified: only graph-theoretic Eulerian paths exist). A successful formalization here would establish a foundation for a future Mathlib PR contributing `Mathlib.Combinatorics.Enumerative.Eulerian`.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `ehrhart-cube-proven` | Parent: axiom-free proof of $L([0,1]^d, n) = (n+1)^d$. Worpitzky converts $(n+1)^d$ into the Eulerian h*-vector form. |
| `ehrhart-cube-proven-oq-01` | Sibling: simplex Ehrhart polynomial $L(\Delta^d, n) = \binom{n+d}{d}$. Trivial h*-vector $(1, 0, \ldots, 0)$. |
| `ehrhart-cube-proven-oq-02` | Sibling: cross-polytope Ehrhart polynomial. h*-vector is the Pascal row $\binom{d}{k}$. |
| `picks-theorem-oq-03` | Related: Pick's theorem appears as the $d = 2$ specialization of Ehrhart linear-coefficient extraction. |

## References

1. **Euler, L.** (1755). *Institutiones calculi differentialis*. — Original generating-series introduction of Eulerian numbers.
2. **Worpitzky, J.** (1883). *Studien über die Bernoullischen und Eulerschen Zahlen*. Crelle's Journal. — Original statement of the identity $x^d = \sum A(d, k) \binom{x+k}{d}$.
3. **Stanley, R. P.** (1980). *Decompositions of rational convex polytopes*. Annals of Discrete Mathematics 6. — Theorem on h*-vector non-negativity.
4. **Stanley, R. P.** (1986/2012). *Enumerative Combinatorics, Volume 1*, §1.4. — Modern reference on Eulerian numbers and Worpitzky's identity.
5. **OEIS A008292**: Triangle of Eulerian numbers.

## Approach Outline (S1 SCAFFOLD; S2+ proof strategies)

### Approach A — Induction on $d$ (algebraic, recommended)

Induct on $d$. Base case $d = 1$: $(n+1)^1 = 1 \cdot \binom{n+1}{1}$, trivial. Inductive step: multiply Worpitzky at level $d$ by $(n + 1)$ and apply Pascal's identity to re-index:

$$ (n+1)^{d+1} = (n+1) \cdot \sum_{k=0}^{d-1} A(d, k) \binom{n+1+k}{d}. $$

Use $(n+1) \binom{n+1+k}{d} = (d+1) \binom{n+1+k}{d+1} - d \binom{n+k}{d+1} \cdot (\ldots)$ — the standard binomial identity. Re-index using the Eulerian recurrence; verify coefficients match. Expected proof length: ~80-120 Lean lines.

### Approach B — Combinatorial bijection (Stanley *EC1* §1.4)

Each sequence $(c_1, \ldots, c_d) \in \{0, 1, \ldots, n\}^d$ decomposes uniquely as (descent-pattern of associated permutation, position-pattern). The bijection partitions $(n+1)^d$ sequences into $A(d, k)$ groups of size $\binom{n+1+k}{d}$. Requires defining permutation descents — more scaffolding than Approach A.

### Approach C — Generating function

Prove the generating-function identity $\sum_n (n+1)^d t^n = A_d(t)/(1-t)^{d+1}$ directly using the recurrence and `PowerSeries.invOfUnit`, then extract coefficients. Cleanest mathematically but requires substantial Mathlib `PowerSeries` infrastructure.

**Recommended path: A.**
