# Problem: Multiplicity Version of Factor-Remainder Theorem

## Statement

### Plain Language

Formalize the multiplicity version of the Factor Theorem in Lean 4:
$(x - a)^k \mid p(x)$ if and only if $p(a) = p'(a) = \cdots = p^{(k-1)}(a) = 0$,
where $p^{(j)}$ denotes the $j$-th formal derivative of $p$.

### Formal Statement

$$
\forall k \geq 1, \quad (X - a)^k \mid p \iff p(a) = p'(a) = \cdots = p^{(k-1)}(a) = 0
$$

Equivalently, the **multiplicity** of $a$ as a root of $p$ equals the largest $k$ such
that $(X - a)^k \mid p$, which also equals the order of vanishing of $p$ at $a$ in the
Taylor expansion sense.

The Taylor expansion connection: over a field of characteristic 0,
$$p(X) = \sum_{j=0}^{n} \frac{p^{(j)}(a)}{j!} (X - a)^j$$
so $(X-a)^k \mid p$ iff the first $k$ Taylor coefficients vanish.

## Classification

```yaml
tier: B
significance: 6
tractability: 7
tags:
  - algebra
  - polynomials
  - multiplicity
  - taylor-expansion
  - formal-derivatives
  - lean-mathlib
  - seeker-selected
```

**Significance**: 6/10 — Extends the core Factor Theorem with a rich characterization
of root multiplicity; connects polynomial algebra to formal calculus in Lean.

**Tractability**: 7/10 — Mathlib has `Polynomial.derivative` and `rootMultiplicity`;
the key lemmas are likely already present or close to provable with existing infrastructure.

## Why This Matters

1. **Root multiplicity is fundamental** — Root multiplicity appears in Jordan normal form,
   partial fraction decomposition, Sturm's theorem on real roots, and the discriminant.
   Formalizing the multiplicity characterization closes a gap in the gallery's polynomial coverage.

2. **Taylor expansion connection** — The equivalence $(x-a)^k \mid p \iff p^{(j)}(a)=0$ for $j<k$
   is the polynomial Taylor theorem in disguise. Over characteristic 0 fields, this is the link
   between algebraic divisibility and analytic vanishing order.

3. **Builds on existing gallery work** — The base `factor-remainder-theorem` (gallery entry,
   0 sorries, Wiedijk #89) provides the $k=1$ case. This extends it to all $k$, completing
   the multiplicity picture.

4. **Lean infrastructure** — `Polynomial.rootMultiplicity` and `Polynomial.derivative` exist in
   Mathlib. The challenge is cleanly connecting them with a characterization theorem.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `factor-remainder-theorem` | Base case k=1; provides Factor Theorem infrastructure |
| `factor-remainder-nullstellensatz` | Extends to multivariate setting; related algebraic depth |
| `taylor-theorem` | Taylor expansion in real analysis; the polynomial analogue |
| `binomial-theorem` | Expansion of (x-a)^k; used in derivative calculations |
| `vietas-formulas` | Connects coefficients to root multiplicities via symmetric functions |

## Key Mathlib Identifiers to Explore

- `Polynomial.rootMultiplicity` — exact multiplicity count
- `Polynomial.derivative` — formal derivative
- `Polynomial.iteratedDerivative` — higher-order formal derivatives
- `Polynomial.dvd_iff_isRoot` — base Factor Theorem
- `Polynomial.pow_rootMultiplicity_dvd` — divisibility by (x-a)^k

## Approach Sketch

**Direction 1** (forward): If $(X-a)^k \mid p$, write $p = (X-a)^k \cdot q$.
Differentiating $j$ times for $j < k$ shows $p^{(j)}(a) = 0$ by the product rule and
the fact that $(X-a)^{k-j}$ vanishes at $a$ when $k-j \geq 1$.

**Direction 2** (backward): Induction on $k$. Base case $k=1$ is the Factor Theorem.
For the inductive step: if $p(a)=0$, write $p=(X-a)q$ by the Factor Theorem.
Then $p' = q + (X-a)q'$, so $p'(a) = q(a)$. If $p'(a)=\cdots=p^{(k-1)}(a)=0$, then
$q(a)=\cdots=q^{(k-2)}(a)=0$, so by induction $(X-a)^{k-1} \mid q$, giving $(X-a)^k \mid p$.

**Characteristic considerations**: The statement holds over any commutative ring
with the right formulation; for the Taylor expansion connection, characteristic 0
(or a field where $k!$ is invertible) is needed.
