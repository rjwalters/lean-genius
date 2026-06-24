# Problem: Product of a Finite Abelian Group is the Identity when It Has At Least Three Involutions

**Slug**: wilsons-theorem-oq-02-ext-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $G$ be a finite abelian group. Then

$$
\prod_{x \in G} x \;=\; 1
\qquad\text{whenever}\qquad
\bigl|\{\, x \in G : x^2 = 1 \,\}\bigr| \;\ge\; 3 .
$$

More precisely, the product of all elements of a finite abelian group equals the product of its involutions (elements of order dividing $2$), and that product is the identity unless the set of involutions is exactly a single nontrivial element, in which case it equals that element.

### Plain Language

In the full product $\prod_{x\in G} x$, every element pairs off with its inverse, and a pair $\{x, x^{-1}\}$ contributes $x\cdot x^{-1} = 1$ unless $x = x^{-1}$, i.e. $x^2 = 1$. So only the involutions survive, and the whole product collapses to the product of the elements satisfying $x^2=1$. This problem asks to formalize the resulting general theorem: once there are three or more such self-paired elements (equivalently, the $2$-torsion subgroup is not cyclic of order $\le 2$), their product is forced to be the identity. This abstracts the two-involution pairing trick that underlies Wilson's theorem into a clean statement about finite abelian groups.

### Why This Matters

Wilson's theorem $(p-1)! \equiv -1 \pmod p$ is exactly the instance $G = (\mathbb{Z}/p\mathbb{Z})^\times$, where the only involutions are $\pm 1$ and the product is $-1$. The general lemma isolates the *reason* Wilson's theorem works and supplies a reusable building block: it immediately gives the product-of-units result for $(\mathbb{Z}/n\mathbb{Z})^\times$ (Gauss's generalization of Wilson's theorem) by counting solutions of $x^2 \equiv 1$. It is also a clean showcase of Mathlib's `Finset.prod_involution` / `Finset.prod_univ` machinery and the structure of the $2$-torsion subgroup.

## Known Results

### What's Already Proven

- Parent `wilsons-theorem-oq-02-ext` (verified): the two-involution pairing argument specialized to Wilson's theorem.
- Mathlib: `Finset.prod_univ`, `Finset.prod_involution`, `Finset.prod_eq_prod_of_...` pairing lemmas; `ZMod` unit groups.
- Mathlib: the $2$-torsion / elementary-abelian structure lemmas (`orderOf`, `Monoid.IsTorsion`, subgroup of square-one elements).

### What's Still Open

- A standalone Lean theorem: for a finite abelian group $G$, $\prod_{x\in G} x = \prod_{x : x^2=1} x$, and the latter equals $1$ when the involution set has cardinality $\ge 3$.
- The corollary recovering Gauss's generalization of Wilson's theorem for $(\mathbb{Z}/n\mathbb{Z})^\times$.

### Our Goal

State and prove $\prod_{x\in G} x = 1$ for a finite abelian group with at least three square-one elements, via the inverse-pairing involution on $G \setminus \{x : x^2 = 1\}$, then reduce the surviving product over the (elementary abelian) $2$-torsion subgroup to the identity using its non-cyclic structure.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| wilsons-theorem-oq-02-ext | Direct parent; two-involution trick | inverse pairing, finite products |
| wilsons-theorem-oq-01 | Wilson's theorem core | modular arithmetic, $(\mathbb{Z}/p)^\times$ |

## Initial Thoughts

### Potential Approaches

1. **Pairing involution via `Finset.prod_involution`.** Use $x \mapsto x^{-1}$ as the involution; fixed points are exactly the square-one elements, so the product reduces to $\prod_{x^2=1} x$. Then argue the residual product is $1$.
   - Why it might work: `Finset.prod_involution` is purpose-built; commutativity makes the residual a product over the elementary-abelian $2$-group $\{x : x^2 = 1\}$.
   - Risk: discharging the hypotheses of `prod_involution` (well-definedness, non-fixed cancellation) and handling the residual product cleanly.

2. **Reduce to the $2$-torsion subgroup $H = \{x : x^2 = 1\}$.** Show $\prod G = \prod H$ and that an elementary abelian $2$-group with $|H| \ge 3$ (hence $\ge 4$, non-cyclic) has trivial element-product by pairing each nonidentity $h$ with a complementary basis partner.
   - Why it might work: an elementary abelian $2$-group is a vector space over $\mathbb{F}_2$; the sum of all vectors is $0$ once the dimension is $\ge 2$.
   - Risk: bridging "product over $H$" to the $\mathbb{F}_2$-vector-space sum argument formally.
