# Problem: Full Wantzel–Galois Constructibility Theorem via Mathlib Galois Theory

**Slug**: angle-trisection-oq-02-oq-01-oq-02-oq-03
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

A complex number $\alpha$ is straightedge-and-compass constructible if and only if there is a tower
$$
\mathbb{Q} = F_0 \subseteq F_1 \subseteq \dots \subseteq F_m,\qquad [F_{i+1}:F_i] = 2,\qquad \alpha \in F_m .
$$
Equivalently (Wantzel–Galois form): $\alpha$ is constructible iff $\alpha$ is algebraic over $\mathbb{Q}$ and the Galois group of the Galois closure of $\mathbb{Q}(\alpha)/\mathbb{Q}$ is a $2$-group; in particular constructibility forces $[\mathbb{Q}(\alpha):\mathbb{Q}]$ to be a power of $2$.

### Plain Language

The parent entry establishes the constructibility framework and the degree-power-of-two necessary condition. This problem asks for the full biconditional using Mathlib's Galois correspondence `IntermediateField.orderIsoOfGal` together with the structure theory of finite $2$-groups (existence of a chief series with index-$2$ steps, since a $p$-group has normal subgroups of every order). The characterization then upgrades the "degree is a power of two" necessary condition to a genuine iff by building the quadratic tower from the group-side subnormal series.

### Why This Matters

This is the definitive statement behind the three classical impossibility theorems (trisecting the angle, doubling the cube, squaring the circle via constructibility). A Galois-theoretic proof, rather than an ad hoc tower argument, connects the gallery's constructibility work to Mathlib's substantial Galois correspondence and $p$-group theory, and gives a single reusable theorem from which all impossibility corollaries follow.

## Known Results

### What's Already Proven

- Constructibility implies $[\mathbb{Q}(\alpha):\mathbb{Q}]$ is a power of $2$ — parent `angle-trisection-oq-02-oq-01-oq-02`.
- Angle trisection / cube duplication impossibility from the degree obstruction — sibling gallery entries.
- Mathlib Galois correspondence `IntermediateField.orderIsoOfGal`, `IsGalois`, and fundamental theorem.
- $p$-groups have a normal subgroup of each order dividing $|G|$ — `Mathlib.GroupTheory.PGroup` / Sylow development.

### What's Still Open

- The sufficiency direction phrased through the Galois closure and a $2$-group chief series, i.e. building the index-$2$ tower from the group side.
- The clean biconditional `IsConstructible α ↔ (IsIntegral ℚ α ∧ IsPGroup 2 (Gal (normalClosure ...)))`.

### Our Goal

Prove the Wantzel–Galois biconditional: assemble the Galois-closure $2$-group condition, use $p$-group chief series to produce the quadratic tower, and connect it to the existing constructibility predicate — recovering the degree condition as a corollary.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| angle-trisection-oq-02-oq-01-oq-02 | Parent: degree power-of-two necessity | quadratic towers, field degree |
| angle-trisection-oq-02-oq-01 | Constructibility predicate setup | tower of quadratic extensions |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Galois closure + 2-group chief series**: Take $L$ = Galois closure of $\mathbb{Q}(\alpha)$; if $\mathrm{Gal}(L/\mathbb{Q})$ is a $2$-group, use the $p$-group normal-series theorem to get $1 = G_0 \trianglelefteq \dots \trianglelefteq G_m = G$ with $[G_{i+1}:G_i]=2$, then translate through `orderIsoOfGal` into the fixed-field tower with $[F_{i+1}:F_i]=2$.
   - Why it might work: every ingredient (`orderIsoOfGal`, $p$-group series) is in Mathlib.
   - Risk: connecting the abstract fixed-field tower to the gallery's concrete `IsConstructible` predicate may need bridging lemmas about towers of quadratic extensions.

2. **Approach B — direct induction on the tower without closure**: Strengthen the parent by induction, avoiding the Galois closure, matching each quadratic step to a constructibility step.
   - Why it might work: closer to the existing proof; less Galois machinery.
   - Risk: this is essentially the classical elementary route and may not exercise `orderIsoOfGal` as the problem intends; the "only if" with non-normal $\mathbb{Q}(\alpha)$ still needs the closure.

### Key Difficulties

- Relating the Mathlib `IntermediateField` fixed-field tower to the gallery's constructibility predicate.
- Handling non-Galois $\mathbb{Q}(\alpha)$ by passing to the normal/Galois closure and controlling its degree.
- $p$-group chief-series API: extracting an index-$2$ normal series in usable form.

### What Would a Proof Need?

- Key lemma 1: a finite $2$-group has a chief series with all factors of order $2$ (from `IsPGroup`).
- Key lemma 2: `orderIsoOfGal` turns that subgroup series into an intermediate-field tower with $[F_{i+1}:F_i]=2$.
- Key lemma 3: a quadratic tower over $\mathbb{Q}$ containing $\alpha$ implies `IsConstructible α` and conversely.

## Tractability Assessment

**Difficulty**: Medium–High

**Justification**:
- Mathlib's Galois correspondence and $p$-group theory are mature, which is a strong asset.
- The bridge between the abstract tower and the concrete geometric constructibility predicate is the real risk and may be the bulk of the work.
- Comparable but strictly easier (degree-only) results already live in the gallery.

**Estimated Effort**:
- Exploration: 2–3 days to map `orderIsoOfGal` and `IsPGroup` series API.
- If tractable: 1–2 weeks for the full biconditional.
- If hard: the closure-degree and predicate-bridge steps could extend this considerably.

## References

### Papers
- Wantzel, "Recherches sur les moyens de reconnaître si un problème de géométrie peut se résoudre avec la règle et le compas", *J. Math. Pures Appl.* (1837).
- Stewart, *Galois Theory* (4th ed.), Chapters on constructibility and the three classical problems.

### Online Resources
- https://leanprover-community.github.io/mathlib4_docs/ — `IntermediateField.orderIsoOfGal`, `IsGalois`, `IsPGroup`.

### Mathlib
- `Mathlib.FieldTheory.Galois` — Galois correspondence, `orderIsoOfGal`.
- `Mathlib.GroupTheory.PGroup` — $p$-group normal-subgroup existence.
- `Mathlib.FieldTheory.IntermediateField` — intermediate-field towers and degrees.

## Metadata

```yaml
tags:
  - geometry
  - galois-theory
  - constructibility
  - impossibility
  - p-groups
related_proofs:
  - angle-trisection-oq-02-oq-01-oq-02
  - angle-trisection-oq-02-oq-01
difficulty: high
source: gallery-gap
created: 2026-07-04
```
