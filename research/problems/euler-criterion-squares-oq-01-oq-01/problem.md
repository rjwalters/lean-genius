# Problem: Exactly (p−1)/2 Nonzero Quadratic Residues mod an Odd Prime

**Slug**: euler-criterion-squares-oq-01-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For an odd prime $p$, among the nonzero residues $\{1, 2, \dots, p-1\}$ modulo $p$ there are exactly

$$
\frac{p-1}{2}\ \text{quadratic residues}\quad\text{and}\quad \frac{p-1}{2}\ \text{quadratic non-residues}.
$$

Equivalently, the squaring map $x \mapsto x^2$ on $(\mathbb{Z}/p\mathbb{Z})^\times$ is two-to-one onto its image, so $|\{x^2 : x \in (\mathbb{Z}/p)^\times\}| = (p-1)/2$.

### Plain Language

A nonzero number mod an odd prime $p$ is a *quadratic residue* if it is a perfect square mod $p$. This problem asks to prove that exactly half of the $p-1$ nonzero residues are squares and the other half are not. The reason is that squaring pairs up $x$ and $-x$ (both have the same square, and they are distinct since $p$ is odd), so the squaring map is exactly two-to-one — collapsing $p-1$ inputs to $(p-1)/2$ outputs. This is the counting companion of Euler's criterion proved in the parent entry.

### Why This Matters

The "half are residues" count is the foundational fact of quadratic-residue theory: it underlies the Legendre symbol's multiplicativity, Euler's criterion, Gauss's lemma, and ultimately quadratic reciprocity. Formalizing it as a clean cardinality statement (the squaring map is two-to-one) gives every downstream reciprocity and character-sum entry a reusable counting lemma.

## Known Results

### What's Already Proven

- Parent `euler-criterion-squares-oq-01` (verified): Euler's criterion $a^{(p-1)/2} \equiv \pm 1$ characterizing quadratic residues.
- Mathlib: `ZMod.exists_sq_eq` / `ZMod` quadratic-residue API, `FiniteField.isSquare_iff`, `ZMod.card_units`, `Finset.card_image_of_...`, and the order/structure of $(\mathbb{Z}/p)^\times$ as cyclic of order $p-1$.
- Classical: the squaring map on a cyclic group of even order has image of index $2$.

### What's Still Open

- A Lean statement that the set of nonzero quadratic residues mod an odd prime has cardinality $(p-1)/2$, via the two-to-one squaring map (fibers $\{x, -x\}$).
- The complementary count of non-residues, and the link to the parent's Euler-criterion sign.

### Our Goal

Show the squaring map $(\mathbb{Z}/p)^\times \to (\mathbb{Z}/p)^\times$ has every nonempty fiber of size $2$ (namely $\{x,-x\}$ with $x \ne -x$ since $p$ is odd), hence the image has size $(p-1)/2$, giving the residue count and, by complement, the non-residue count.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| euler-criterion-squares-oq-01 | Direct parent; Euler's criterion | quadratic residues, finite fields |
| euler-criterion-squares-oq-01 (root family) | Legendre-symbol groundwork | modular arithmetic |

## Initial Thoughts

### Potential Approaches

1. **Two-to-one squaring map via `Finset.card_image`-with-fibers.** Prove each fiber of $x \mapsto x^2$ on $(\mathbb{Z}/p)^\times$ is exactly $\{x, -x\}$ with $x \ne -x$ (using $p$ odd), then apply a "constant fiber size" cardinality lemma to get $|\text{image}| = (p-1)/2$.
   - Why it might work: the fiber description is elementary ($y^2 = x^2 \iff y = \pm x$ in a field), and Mathlib has fiber-counting lemmas.
   - Risk: selecting the right Mathlib cardinality lemma and handling $-x \ne x$ cleanly in `ZMod p`.

2. **Kernel/image of the squaring homomorphism.** The squaring map is a group hom on the cyclic group $(\mathbb{Z}/p)^\times$ with kernel $\{\pm 1\}$ of order $2$; by the first isomorphism theorem the image has order $(p-1)/2$.
   - Why it might work: leverages Mathlib's group-hom cardinality (`Subgroup.card_eq_card_quotient_mul_card_subgroup` / `card_range`).
   - Risk: packaging squaring as a `MonoidHom` and identifying its kernel as `{±1}` formally.
