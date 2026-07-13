# Problem: Product of All Group Elements in the Non-Abelian Case (via Abelianization)

**Slug**: wilsons-theorem-oq-04-oq-02-oq-01
**Created**: 2026-06-30T22:49:26-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The parent proof establishes, for a finite **commutative** group $G$, that
$$
\prod_{g \in G} g \;=\; \tau \quad\text{when } \tau \text{ is the unique non-trivial involution, and } \prod_{g \in G} g = 1 \text{ otherwise.}
$$

The open question asks to generalize to **non-abelian** finite groups $G$. The first obstruction is that
$$
\prod_{g \in G} g
$$
is **not well-defined** when $G$ is non-abelian: the value depends on the chosen enumeration $g_1, g_2, \dots, g_n$ of the elements, since $g_i g_j \neq g_j g_i$ in general.

The clean, tractable formalization pushes the product through the **abelianization** $G^{\mathrm{ab}} = G / [G,G]$, where $[G,G]$ is the commutator subgroup. Let $\pi = \mathrm{Abelianization.of} : G \to G^{\mathrm{ab}}$ be the canonical projection. Because $\pi$ is a group homomorphism and $G^{\mathrm{ab}}$ is abelian:

**(a) Well-definedness of the image.** For *any* enumeration $g_1,\dots,g_n$ of the elements of $G$,
$$
\pi\!\left(\prod_{i=1}^{n} g_i\right) \;=\; \prod_{i=1}^{n} \pi(g_i) \;=\; \prod_{h \in G^{\mathrm{ab}}} h^{\,|\ker \pi \cap \pi^{-1}(h)|}
\;=\; \prod_{y \in \mathrm{im}\,\pi} y^{\,[G:G^{\mathrm{ab}}\text{-fiber}]},
$$
and in particular the **coset** $\left(\prod_i g_i\right)\,[G,G] \in G^{\mathrm{ab}}$ is **independent of the enumeration**. Concretely,
$$
\pi\!\left(\prod_{g\in G} g\right) \text{ is well-defined and equals } \prod_{g \in G} \pi(g).
$$

**(b) Characterization via the parent's abelian result.** Since $G^{\mathrm{ab}}$ is a finite abelian group, apply the parent theorem to the multiset $\{\pi(g) : g \in G\}$. When $[G:G']$-multiplicity is accounted for, the well-defined image satisfies:
$$
\pi\!\left(\prod_{g\in G} g\right) =
\begin{cases}
\bar\tau, & \text{if } G^{\mathrm{ab}} \text{ has a unique involution } \bar\tau \text{ and each fiber has odd size (mod 2 survives)},\\[4pt]
1, & \text{if } G^{\mathrm{ab}} \text{ has no unique involution (e.g. is trivial, odd order, or non-cyclic 2-part).}
\end{cases}
$$

Equivalently: **there exists an enumeration with $\prod_i g_i = 1$ iff the well-defined image $\pi(\prod g) = 1$ in $G^{\mathrm{ab}}$** — because the set of achievable products of a fixed multiset is exactly one coset of $[G,G]$ (a theorem of the Dénes–Hermann / Ore circle), so an ordering yielding the identity exists precisely when that coset is $[G,G]$ itself.

### Plain Language

In an abelian group the notation $\prod_{g\in G} g$ is unambiguous — you can multiply the elements in any order and get the same answer. The parent proof pins that answer down: it is the unique element of order 2 if there is exactly one (the "$-1$" in Gauss's Wilson theorem), and the identity otherwise.

In a non-abelian group this breaks immediately: reorder the factors and the product changes. So "$\prod G = e$?" has no answer as literally written. The rescue is the **abelianization** $G^{\mathrm{ab}} = G/[G,G]$: it is the largest abelian quotient of $G$, obtained by forcing all elements to commute. The projection $\pi$ is a homomorphism, so it sends products to products, and in the abelian target the order no longer matters. Therefore the *image* $\pi(\prod g)$ is a genuine, ordering-independent invariant of $G$ — and the parent theorem computes it. Moreover, the different orderings of $\prod g$ inside $G$ trace out exactly one coset of the commutator subgroup, so the image tells you whether you can order the factors to land on the identity.

### Why This Matters

- **Extends the Gauss–Wilson involution result beyond abelian groups.** The parent captures the classical "$(p-1)! \equiv -1$" phenomenon at the abelian level. This child gives the honest, well-posed statement for arbitrary finite groups, isolating exactly what survives (the commutator-quotient invariant).
- **Connects to a genuine research thread.** The "product of all the elements of a finite group" was studied by G. A. Miller (1903), and the coset-of-$[G,G]$ characterization is the Dénes–Hermann theorem; it is the subject of the Herzog–Kaplan–Lev work on rearrangements and sequenceable/complete-mapping groups. The clean punchline "the achievable products form one coset of $[G,G]$" is exactly why the abelianization image is the right invariant.
- **Illustrates a reusable formalization pattern.** "An ill-posed product becomes well-posed in the abelianization" is a technique that recurs (e.g. transfer maps, sign of a permutation as an abelianization). Formalizing it here builds a template.

## Known Results

### What's Already Proven

- Parent `wilsons-theorem-oq-04-oq-02` (`WilsonsTheoremOQ04OQ02.lean`): for finite commutative $G$, `prod_univ_of_unique_involution` ($\prod G = \tau$ for the unique involution), `prod_cyclic_even_group`, and `prod_univ_odd_order` ($\prod G = 1$ for odd order). Also `prod_eq_prod_involutions`: $\prod G = \prod_{x^2=1} x$.
- Classical Wilson `wilsons-theorem`: $(p-1)! \equiv -1 \pmod p$.
- Mathlib provides the abelianization functor and the homomorphism-preserves-products machinery outright.

### What's Still Open

- The genuinely non-abelian refinement: the exact multiplicity/parity bookkeeping (fiber sizes of $\pi$) needed to compute $\pi(\prod g)$ purely from group invariants of $G$ (not $G^{\mathrm{ab}}$ alone), and the full Dénes–Hermann coset theorem inside $G$ (which orderings are achievable) — the latter is a substantial combinatorial result.
- The complete determination for all non-cyclic 2-groups where $G^{\mathrm{ab}}$ has several involutions.

### Our Goal

Formalize the **well-posed** statement: define $\pi = \mathrm{Abelianization.of}$, prove $\pi(\prod_{g} g) = \prod_g \pi(g)$ (ordering-independent by construction), and then invoke the parent's abelian theorem on $G^{\mathrm{ab}}$ to characterize this image (equals the unique involution of $G^{\mathrm{ab}}$ if one exists with odd fibers, else $1$). We do **not** attempt the full achievable-orderings coset theorem inside $G$; the deliverable is the abelianization characterization plus a clear statement of why the raw $\prod G$ is ill-posed.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| wilsons-theorem-oq-04-oq-02 | Direct parent; supplies the abelian product-of-involutions theorem we transport | `Finset.prod_involution`, `IsCyclic.card_pow_eq_one_le`, `Finset.prod_pair` |
| wilsons-theorem-oq-02 | Sibling instantiation for $(\mathbb Z/n\mathbb Z)^\times$ | modular units, cyclicity classification |
| wilsons-theorem | Classical root $(p-1)!\equiv-1$ | pairing with inverses |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Push the product through `Abelianization.of` (recommended).**
   - Concrete first step: `Abelianization.of` is a `MonoidHom`, so
     `Abelianization.of (∏ g in Finset.univ, g) = ∏ g in Finset.univ, Abelianization.of g`
     is exactly `map_prod Abelianization.of _ _` (or `MonoidHom.map_prod`).
   - Then the RHS is a product over all elements of $G$ pushed into the abelian group $G^{\mathrm{ab}}$; regroup by fibers of $\pi$ and apply the parent theorem to $G^{\mathrm{ab}}$.
   - Why it works: the target is abelian, so `Finset.prod` is reorder-invariant automatically; no ordering choice is ever made. This sidesteps the ill-posedness entirely.
   - Risk: the fiber-multiplicity bookkeeping ($\prod_{g} \pi(g) = \prod_{h\in G^{\mathrm{ab}}} h^{|\text{fiber}|}$) needs `Finset.prod_fiberwise` / `Finset.prod_comp` and a parity argument; getting the exponents right is the main labor.

2. **Approach B — State the coset invariant directly.**
   - Prove the weaker but fully rigorous claim: the map `enumeration ↦ ∏ᵢ gᵢ` has image contained in a single coset of `commutator G`, i.e. all products agree modulo $[G,G]$. This is `Approach A` phrased without naming a canonical value.
   - Why it works: it is exactly the well-definedness in $G^{\mathrm{ab}}$ restated in $G$; provable from `Approach A` since $\pi(x)=\pi(y) \iff x^{-1}y \in [G,G]$.
   - Risk: quantifying over "all enumerations" (bijections `Fin n ≃ G`) and their ordered products is more setup than the `Finset.prod`-in-quotient formulation.

### Key Difficulties

- The literal $\prod_{g\in G} g$ cannot even be written in Lean for non-abelian $G$ without fixing an ordering (`List.prod` of some enumeration); the entire point is to avoid needing that.
- Fiber multiplicities: $\prod_{g\in G}\pi(g)$ counts each $h\in\mathrm{im}\,\pi$ with multiplicity $|\pi^{-1}(h)|=|[G,G]|$ (constant, since fibers are cosets), so the image is $\big(\prod_{h}h\big)^{|[G,G]|}$ — the exponent's parity governs the outcome.
- Determining when $G^{\mathrm{ab}}$ has a *unique* involution (its cyclic even-order 2-part) mirrors the parent's cyclic analysis.

### What Would a Proof Need?

- Key lemma 1: `Abelianization.of` is a `MonoidHom`; `map_prod`/`MonoidHom.map_prod` transports `Finset.prod` — gives ordering-independence for free.
- Key lemma 2: fiber decomposition $\prod_{g\in G}\pi(g) = \big(\prod_{h\in G^{\mathrm{ab}}} h\big)^{|[G,G]|}$ via `Finset.prod_fiberwise`/`Finset.prod_comp` (all fibers of $\pi$ are cosets of $[G,G]$, hence equinumerous).
- Key lemma 3: apply the parent's `prod_univ_of_unique_involution` / `prod_univ_odd_order` to the finite abelian group $G^{\mathrm{ab}}$, then raise to the $|[G,G]|$ power and reduce mod the involution's order 2.
- Technical requirements: `Fintype`/`DecidableEq` on $G$ (hence on $G^{\mathrm{ab}}$), `orderOf` bookkeeping for involutions.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The abelianization reduction is clean and every ingredient is in Mathlib: `Abelianization`, `Abelianization.of`, `map_prod`, `Finset.prod_fiberwise`, and the parent theorem itself is directly reusable on $G^{\mathrm{ab}}$.
- The honest caveat is that a fully general "$\prod G = e$" statement is **ill-posed**, so we cannot state the literal generalization; the deliverable is the abelianization characterization plus the coset invariant. This reframing is standard and defensible.
- Similar reorder-into-a-quotient arguments (sign of a permutation, transfer homomorphism) are already formalized, so the pattern is proven feasible.
- The only real labor is the fiber-multiplicity/parity computation; everything else is `map_prod` plus citing the parent.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable: 3–7 days
- If hard (full Dénes–Hermann achievable-orderings coset theorem inside $G$): unknown / out of scope

## References

### Papers
- G. A. Miller, "The product of the elements of a finite group," early group-theory studies (1903) — origin of the "product of all group elements" question.
- J. Dénes, A. D. Keedwell, and work of Dénes–Hermann on the set of products of all elements — the achievable products form a single coset of the commutator subgroup.
- M. Herzog, G. Kaplan, A. Lev, "Representation of permutations as products..." — modern treatment of orderings and complete mappings related to the product of all elements.
- C. F. Gauss, *Disquisitiones Arithmeticae* (1801) — the abelian/Wilson root and the unique-involution idea.

### Online Resources
- Wikipedia, "Wilson's theorem" — classical statement and the involution-pairing proof.
- Wikipedia, "Commutator subgroup" / "Abelianization" — the universal abelian quotient used to make $\prod G$ well-posed.

### Mathlib
- `Mathlib.GroupTheory.Abelianization` — `Abelianization`, `Abelianization.of` (the canonical `MonoidHom G → G^{ab}`), universal property.
- `Mathlib.GroupTheory.Commutator` / `Subgroup.commutator`, `commutator G` — the commutator subgroup $[G,G]$ (kernel of `Abelianization.of`).
- `Finset.prod`, `map_prod` / `MonoidHom.map_prod`, `Finset.prod_fiberwise`, `Finset.prod_comp` — transporting and regrouping products.
- `IsCyclic`, `IsCyclic.card_pow_eq_one_le`, `orderOf`, `orderOf ... = 2` — locating the unique involution in $G^{\mathrm{ab}}$ (reuses parent machinery).
- `Monoid.IsTorsionFree` — rules out involutions in the torsion-free / odd-order analysis.
- Parent module `Proofs/WilsonsTheoremOQ04OQ02.lean` — `prod_univ_of_unique_involution`, `prod_univ_odd_order`, `prod_eq_prod_involutions` applied to $G^{\mathrm{ab}}$.

## Metadata

```yaml
tags:
  - group-theory
  - abstract-algebra
  - abelianization
  - commutator-subgroup
  - gauss-wilson
  - involutions
related_proofs:
  - wilsons-theorem-oq-04-oq-02
  - wilsons-theorem-oq-02
  - wilsons-theorem
difficulty: medium
source: gallery-gap
created: 2026-06-30T22:49:26-07:00
```
