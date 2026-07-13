# Problem: Classification of Groups of Order p³

**Slug**: group-order-prime-squared-abelian-oq-01-oq-02
**Created**: 2026-07-09T16:03:14-07:00
**Status**: Active
**Source**: user-request <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

For a prime $p$, classify all groups $G$ with $|G| = p^3$ up to isomorphism. The claim to formalize is that, up to isomorphism, there are exactly five groups of order $p^3$ when $p$ is odd:

$$
\underbrace{C_{p^3},\quad C_{p^2}\times C_p,\quad C_p\times C_p\times C_p}_{\text{abelian (3)}},\qquad
\underbrace{\mathrm{Heis}(p)=\langle a,b,c\mid a^p=b^p=c^p=1,\ [a,b]=c,\ [a,c]=[b,c]=1\rangle,\quad M_{p^3}=\langle a,b\mid a^{p^2}=b^p=1,\ b^{-1}ab=a^{1+p}\rangle}_{\text{non-abelian (2)}}.
$$

Equivalently: every group of order $p^3$ is isomorphic to exactly one of these five, and the two non-abelian classes are distinguished by their exponent ($\exp = p$ for the Heisenberg group of exponent $p$, $\exp = p^2$ for the modular group $M_{p^3}$). For $p = 2$ the two non-abelian groups are the dihedral group $D_4$ (order $8$) and the quaternion group $Q_8$.

### Plain Language

Groups of order $p^2$ are always abelian, and there are exactly two of them (cyclic $C_{p^2}$ and elementary abelian $C_p \times C_p$). Order $p^3$ is the very first size at which a group of prime-power order can fail to be commutative. The goal is to prove the complete list: three abelian groups (given by the partitions of $3$ into prime-power exponents) and two non-abelian ones. For odd $p$ the non-abelian pair is the Heisenberg group (upper-triangular $3\times 3$ matrices over $\mathbb{F}_p$ with $1$'s on the diagonal, exponent $p$) and the modular group $M_{p^3}$ (exponent $p^2$). The prime $p = 2$ is exceptional: there the two non-abelian groups are $D_4$ and $Q_8$.

### Why This Matters

The classification of groups of order $p^3$ is a cornerstone of introductory finite group theory and the natural next step after the order-$p^2$ result already in the gallery. It is the smallest case exhibiting genuinely non-abelian $p$-group phenomena: a nontrivial center of order $p$, a commutator subgroup equal to the center, and a Frattini quotient of rank $2$. Extraspecial groups — of which $\mathrm{Heis}(p)$ is the exponent-$p$ prototype — recur throughout representation theory, the theory of central extensions, and coding/quantum information (the Pauli/Heisenberg group). Formalizing this classification exercises the machinery (class equation, center, commutator subgroup, exponent, group presentations) needed for any deeper $p$-group work in Lean.

## Known Results

### What's Already Proven

- Groups of order $p^2$ are abelian and split into the cyclic / elementary-abelian dichotomy — gallery proof `group-order-prime-squared-abelian-oq-01` (verified, 0 axioms).
- Finite abelian groups are classified as products of cyclic prime-power groups — Mathlib `CommGroup` structure theorem (`Mathlib.GroupTheory.FiniteAbelian`), which already pins down the three abelian classes of order $p^3$.
- Every $p$-group has a nontrivial center (`IsPGroup.center_nontrivial`) — the seed of the non-abelian analysis — Mathlib `Mathlib.GroupTheory.PGroup`.
- The Heisenberg group over a field/ring is defined and studied in Mathlib (`Mathlib.GroupTheory.SpecialLinearGroup` / Heisenberg constructions), giving one concrete non-abelian model.

### What's Still Open

- No Lean formalization enumerates the five isomorphism classes of order $p^3$ and proves the list is exhaustive and non-redundant.
- The exponent invariant $\exp(G) \in \{p, p^2\}$ as the discriminator between the two non-abelian classes is not packaged for general $p$.
- The $p = 2$ special case ($D_4$ vs $Q_8$) versus odd $p$ needs a unified or case-split treatment; Mathlib has $D_4$/$Q_8$ but not the linkage to this classification.
- Explicit `MulEquiv` isomorphisms between an abstract $G$ of order $p^3$ and the named representatives.

### Our Goal

A first tractable milestone: for odd $p$, prove that a non-abelian group of order $p^3$ has center $Z(G)$ of order $p$ with $Z(G) = [G,G] = \Phi(G)$ (Frattini subgroup), quotient $G/Z(G) \cong C_p \times C_p$, and is therefore extraspecial; then show it is determined up to isomorphism by its exponent ($p$ or $p^2$), giving exactly the two non-abelian classes. Combined with the (Mathlib) abelian classification this yields the count of five. Constructing the full `MulEquiv` to concrete presentations is a stretch goal.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| group-order-prime-squared-abelian-oq-01 | Direct predecessor: the order-$p^2$ classification this problem extends by one rung | Lagrange (`orderOf_dvd_natCard`), order trichotomy, cyclic/exponent-$p$ dichotomy, `IsPGroup.commutative_of_card_eq_prime_sq` |
| group-order-prime-squared-abelian-oq-01-oq-01 | Sibling extension isolating the exponent invariant `Monoid.exponent G`, the discriminator reused here for the two non-abelian classes | `Monoid.exponent`, order trichotomy |
| group-order-prime-squared-abelian-oq-01-oq-03 | Sibling extension computing the element-order census, technique reused for counting orders in the $p^3$ case | Element-order counting from Lagrange divisor structure |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Structural / extraspecial route (odd $p$).**
   Reduce the non-abelian case to extraspecial structure: show $|Z(G)| = p$, $Z(G) = [G,G] = \Phi(G)$, $G/Z(G) \cong C_p^2$, then classify the two central extensions by the exponent invariant.
   - Why it might work: mirrors the order-$p^2$ proof strategy (center + quotient + order arithmetic) and leans on existing Mathlib $p$-group center facts; the exponent discriminator is already partly formalized in a sibling entry.
   - Risk: cohomological classification of the central extension ($H^2$) is heavy; may need to substitute an explicit commutator-calculus argument instead.

2. **Approach B — Concrete representatives + isomorphism invariants.**
   Define the five groups concretely (cyclic products via Mathlib; $\mathrm{Heis}(p)$ as unitriangular $3\times 3$ matrices over $\mathbb{Z}/p$; $M_{p^3}$ as a semidirect product $C_{p^2} \rtimes C_p$; $D_4$, $Q_8$ from Mathlib) and prove pairwise non-isomorphism via invariants (abelian vs not, exponent, number of order-$p$ elements), then show any order-$p^3$ group matches one.
   - Why it might work: the "distinct" half becomes computations of invariants Mathlib can handle; concrete matrix/semidirect models are constructible.
   - Risk: the exhaustiveness half ("any $G$ is one of these") still requires the structural argument of Approach A, so this mostly helps with the non-redundancy half.

### Key Difficulties

- Proving exhaustiveness (every order-$p^3$ group is on the list) requires real $p$-group structure theory, not just Lagrange; the central-extension classification is the crux.
- The $p = 2$ exception must be handled separately: for $p = 2$ the "exponent-$p$" model degenerates and the two non-abelian groups are $D_4$ and $Q_8$.
- Building explicit `MulEquiv`s to presentations (`PresentedGroup`) is notoriously painful in Lean; word-problem reasoning is hard to automate.
- Counting isomorphism classes as a definite number "$5$" requires a decidable/quotient-level statement rather than an informal enumeration.

### What Would a Proof Need?

- Key lemma 1: for non-abelian $G$ of order $p^3$, $|Z(G)| = p$ (rule out $|Z(G)| = p^2$, which would force $G/Z$ cyclic and hence $G$ abelian).
- Key lemma 2: $Z(G) = [G,G] = \Phi(G)$ and $G/Z(G) \cong C_p \times C_p$ (extraspecial structure).
- Key lemma 3: the exponent of a non-abelian order-$p^3$ group (odd $p$) is $p$ or $p^2$, and this invariant determines $G$ up to isomorphism.
- Technical requirements: Mathlib's center/commutator/`Frattini` API, `IsPGroup` lemmas, `Monoid.exponent`, finite abelian classification, and (for representatives) unitriangular matrix groups / `SemidirectProduct` / `PresentedGroup`.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The abelian third of the classification is essentially free from Mathlib's finite abelian structure theorem, and the "$|Z(G)| = p$" step reuses the order-$p^2$ playbook already in the gallery.
- The non-abelian exhaustiveness and the explicit-isomorphism half are substantially harder: central-extension classification and group-presentation reasoning are not well automated in Lean, and the $p=2$ exception fragments the argument.
- Similar solved problems: the order-$p^2$ classification (gallery), and Mathlib's individual treatments of $D_4$, $Q_8$, and Heisenberg-type groups show the pieces exist but have not been assembled.

**Estimated Effort**:
- Exploration: 2–4 days (survey Mathlib center/commutator/Frattini API, decide on representatives).
- If tractable (structural milestone — center/quotient/exponent for odd $p$): 2–4 weeks.
- If hard (full five-class `MulEquiv` classification with $p=2$): unknown, likely months.

## References

### Papers
- Burnside, W., *Theory of Groups of Finite Order*, 1897 — original classification of small-order $p$-groups.
- Hall, P., "A contribution to the theory of groups of prime-power order", *Proc. LMS*, 1934 — foundational structure theory of $p$-groups (regular $p$-groups, commutator calculus).

### Online Resources
- Groupprops wiki, "Groups of order p^3" — https://groupprops.subwiki.org/wiki/Groups_of_order_p%5E3 — explicit list of the five classes, presentations, and invariants.
- Groupprops, "Classification of groups of order p^3" — presentations of $\mathrm{Heis}(p)$ and $M_{p^3}$ and the $p=2$ ($D_4$, $Q_8$) exception.

### Mathlib
- `Mathlib.GroupTheory.PGroup` — `IsPGroup`, `IsPGroup.center_nontrivial`, `IsPGroup.commutative_of_card_eq_prime_sq`; the entry point for $p$-group structure.
- `Mathlib.GroupTheory.FiniteAbelian` — classification of finite abelian groups, giving the three abelian classes directly.
- `Mathlib.GroupTheory.Commutator` / `Mathlib.GroupTheory.Frattini` — commutator subgroup $[G,G]$ and Frattini subgroup $\Phi(G)$ used to establish extraspecial structure.
- `Mathlib.GroupTheory.SpecificGroups.Dihedral` and `Mathlib.GroupTheory.SpecificGroups.Quaternion` — the $p=2$ non-abelian representatives $D_4$, $Q_8$.
- `Mathlib.GroupTheory.SpecificGroups.Cyclic` and `Monoid.exponent` — cyclic representatives and the exponent invariant discriminating the two non-abelian classes.

## Metadata

```yaml
tags:
  - group-theory
  - finite-groups
  - p-groups
  - abelian-groups
  - cyclic-groups
  - lagrange-theorem
  - algebra
related_proofs:
  - group-order-prime-squared-abelian-oq-01
  - group-order-prime-squared-abelian-oq-01-oq-01
  - group-order-prime-squared-abelian-oq-01-oq-03
difficulty: high
source: user-request
created: 2026-07-09T16:03:14-07:00
```
