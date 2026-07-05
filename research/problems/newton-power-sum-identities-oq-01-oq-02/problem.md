# Problem: Dual (Reverse) Newton Identities — e_k from Power Sums

**Slug**: newton-power-sum-identities-oq-01-oq-02
**Status**: Active
**Source**: proof-suggestion (open question from `newton-power-sum-identities-oq-01`)

## Problem Statement

### Formal Statement

Over a $\mathbb{Q}$-algebra, prove the *dual* (reverse) Newton identities expressing each elementary
symmetric polynomial $e_k$ as a polynomial in the power sums $p_1,\dots,p_k$. In low degree:

$$
e_1 = p_1,\quad
2e_2 = p_1^2 - p_2,\quad
6e_3 = p_1^3 - 3p_1 p_2 + 2p_3,
$$

and in general the determinant (Newton–Girard) form

$$
k!\,e_k = \det
\begin{pmatrix}
p_1 & 1 & 0 & \cdots \\
p_2 & p_1 & 2 & \cdots \\
\vdots & & & \\
p_k & p_{k-1} & \cdots & p_1
\end{pmatrix}.
$$

Establish at least the low-degree cases $k = 1,2,3$ (and if tractable, $k=4$), valid over a
commutative $\mathbb{Q}$-algebra where the required divisions by $k!$ make sense.

### Plain Language

The parent (`newton-power-sum-identities-oq-01`) went the forward direction: power sums $p_k$ from
elementary symmetric polynomials $e_k$. This reverses it — recover the $e_k$ from the $p_k$, which
requires dividing by factorials and hence a $\mathbb{Q}$-algebra base.

### Why This Matters

The reverse direction is what makes Newton's identities a genuine *change of basis* between the
$e$- and $p$-bases of symmetric functions. It underlies characteristic-polynomial-from-traces
computations (e.g. Faddeev–LeVerrier).

## Known Results

### What's Already Proven

- Forward low-degree Newton identities — parent `newton-power-sum-identities-oq-01`.
- Mathlib `MvPolynomial` symmetric-function API: `MvPolynomial.psum`, `esymm`, and
  `MvPolynomial.NewtonIdentities` (the $p$-from-$e$ recurrence).

### Our Goal

Prove the reverse identities for $k = 1,2,3$ over a $\mathbb{Q}$-algebra, 0 axioms, 0 sorries.
Prefer the recursive form over the full Toeplitz determinant if the latter is heavy in Mathlib.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| newton-power-sum-identities-oq-01 | Parent: forward identities | MvPolynomial, esymm/psum |

## Initial Thoughts

### Potential Approaches

1. **Solve the forward recurrence.** Rearrange Mathlib's Newton recurrence
   $p_k - e_1 p_{k-1} + \dots + (-1)^{k-1} e_{k-1} p_1 + (-1)^k k\,e_k = 0$ to isolate $e_k$; divide
   by $k$ (needs $\mathbb{Q}$-algebra). Induct.
2. **Direct verification in a concrete polynomial ring** for small $k$ via `ring`, then lift.

### Key Difficulties

- Division by $k!$ ⇒ must work over a $\mathbb{Q}$-algebra / field of characteristic 0.
- Toeplitz determinant form may be awkward; the recursive form is likely the pragmatic target.
