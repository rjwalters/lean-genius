# Problem: Type-Decomposition of Sums of 2k Squares via the Hyperoctahedral Group

**Slug**: four-square-distribution-oq-04
**Created**: 2026-06-14
**Status**: Active
**Source**: gallery-gap <!-- open question extending four-square-distribution -->

## Problem Statement

### Formal Statement

The gallery proof `four-square-distribution` decomposes the count $r_4(n)$ of representations $n = x_1^2+x_2^2+x_3^2+x_4^2$ by "ordering type", using the hyperoctahedral group $B_4 = S_4 \ltimes (\mathbb{Z}/2)^4$ (signed permutations) acting on representations, with each unordered solution of "shape" contributing an orbit whose size is

$$
2^{\#\{\text{nonzero parts}\}} \cdot \frac{(2k)!}{\prod_i m_i!}\quad(k=2 \text{ here}),
$$

where $m_i$ are the multiplicities of the distinct absolute values. **Open question:** does this orbit–stabilizer type-decomposition framework generalize to $r_{2k}(n)$, the number of representations as a sum of $2k$ squares, with the hyperoctahedral group $B_{2k} = S_{2k} \ltimes (\mathbb{Z}/2)^{2k}$ of order $(2k)!\,2^{2k}$?

For example, for $k=4$ (eight squares), $B_8 = S_8 \ltimes (\mathbb{Z}/2)^8$ has order $8!\cdot 2^8 = 10{,}321{,}920$.

### Plain Language

If you count the ways to write a number as a sum of four squares, many of those ways are just sign-changes and reorderings of each other. The gallery proof organizes them into neat families (orbits) using the group of "signed shuffles" of 4 coordinates. This question asks whether the *exact same bookkeeping* works for sums of 6, 8, 10, ... squares, where the relevant group is the signed-shuffle group on $2k$ coordinates.

### Why This Matters

Sums-of-squares counts $r_{2k}(n)$ are governed by Jacobi-type formulas and modular forms (e.g. $r_4(n) = 8\sum_{d\mid n,\,4\nmid d} d$). A clean, *group-theoretic* orbit decomposition that separates the "combinatorial multiplicity" (how many orderings/signs each shape has) from the "arithmetic content" (how many shapes there are) is a reusable lens: it isolates exactly the hyperoctahedral combinatorial factor and lets the arithmetic part be supplied by Jacobi's formula. Formalizing it for general $2k$ turns a single worked example into a parametric library.

## Known Results

### What's Already Proven

- The $k=2$ (four squares) type-decomposition — gallery proof `four-square-distribution`
- Lagrange's four-square theorem (existence) — Mathlib `Nat.sum_four_squares`
- Jacobi's four-square formula $r_4(n) = 8\sigma(n) - 32\sigma(n/4)$ — classical (not necessarily in Mathlib)
- $B_m = S_m \ltimes (\mathbb{Z}/2)^m$, the hyperoctahedral / signed-permutation group of order $m!\,2^m$ — standard group theory

### What's Still Open (in Lean)

- The general $2k$ orbit–stabilizer statement: orbit size $= 2^{\#\text{nonzero}}\cdot (2k)!/\prod m_i!$
- A parametric definition of the $B_{2k}$ action on representation tuples and a proof that orbits are exactly the "shape classes"
- The clean separation: $r_{2k}(n) = \sum_{\text{shapes } s \text{ of } n} (\text{orbit size of } s)$

### Our Goal

Formalize the orbit–stabilizer decomposition for general $2k$ (or at least for $2k \in \{4,6,8\}$): define the signed-permutation action of $B_{2k}$ on the set of representations of $n$ as an ordered sum of $2k$ squares, prove the orbit-size formula via orbit–stabilizer, and recover the total count as a sum over shapes. The arithmetic value of the total (Jacobi) can be taken as input.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| four-square-distribution | The $k=2$ case being generalized | Orbit–stabilizer, signed permutations |
| lagrange-four-squares-* | Existence of four-square representations | Descent / Minkowski |
| jacobi-two-square / sums-of-squares cluster | Arithmetic count formulas | Modular forms / divisor sums |

## Initial Thoughts

### Potential Approaches

1. **Orbit–stabilizer via `MulAction`** (recommended): model representations as `Fin (2k) → ℤ` tuples summing-of-squares to $n$; define the `B_{2k}` action (permute coordinates + flip signs); show the stabilizer of a tuple has order $\prod m_i! \cdot 2^{\#\text{zeros}}$, giving the orbit-size formula by `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`.
   - Why it might work: Mathlib has solid `MulAction`, `Equiv.Perm`, and orbit–stabilizer (`Fintype` cardinalities). The group $B_{2k}$ is `Equiv.Perm (Fin (2k)) ` combined with `(ZMod 2)^(2k)` sign flips.
   - Risk: defining $B_{2k}$ and its action with the right stabilizer computation; handling zero parts (which have trivial sign orbit) carefully.

2. **Generating-function / direct combinatorial count**: bypass the group action and count orderings directly via multinomials.
   - Risk: loses the conceptual orbit picture that is the point of the question.

### Key Difficulties

- Correctly accounting for zero coordinates (sign flip acts trivially on $0$) in the stabilizer.
- Assembling the semidirect product $S_{2k} \ltimes (\mathbb{Z}/2)^{2k}$ and its action cleanly in Mathlib.

### What Would a Proof Need?

- Key lemma 1: definition of the $B_{2k}$ action on $2k$-square representation tuples.
- Key lemma 2: stabilizer order $= 2^{\#\text{zeros}} \prod_i m_i!$ for a tuple of given shape.
- Key lemma 3: orbit size $= |B_{2k}| / |\text{stab}| = 2^{\#\text{nonzero}}\,(2k)!/\prod m_i!$.
- Technical requirements: `Mathlib.GroupTheory.GroupAction.*`, `Equiv.Perm`, `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`, `Fintype`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The hard arithmetic (how many representations exist) is *not* required — Jacobi's value can be an input; the open contribution is the purely group-theoretic orbit counting, which Mathlib supports well.
- The $k=2$ case is already done in the gallery, giving a concrete template to generalize.

**Estimated Effort**:
- Exploration: 1–2 days (study the existing four-square-distribution proof and Mathlib orbit–stabilizer)
- If tractable: 1–2 weeks for the general $2k$ orbit-size formula

## References

### Papers / Texts
- C. G. J. Jacobi, sums-of-squares formulas (classical).
- Grosswald, *Representations of Integers as Sums of Squares*.
- Any standard reference on the hyperoctahedral group $B_n$ (signed permutations).

### Mathlib
- `Mathlib.GroupTheory.GroupAction.Basic` — `MulAction`, orbits, stabilizers
- `Mathlib.GroupTheory.OrbitStabilizer` (or current location) — `card_orbit_mul_card_stabilizer_eq_card_group`
- `Mathlib.GroupTheory.Perm.*` — `Equiv.Perm`
- `Nat.sum_four_squares` — Lagrange's theorem

## Metadata

```yaml
tags:
  - number-theory
  - sums-of-squares
  - hyperoctahedral-group
  - representations
  - group-actions
related_proofs:
  - four-square-distribution
  - lagrange-four-squares-waring-g2
difficulty: medium
source: gallery-gap
created: 2026-06-14
```
