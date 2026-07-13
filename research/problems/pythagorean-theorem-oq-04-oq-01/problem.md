# Problem: A Bijection Between Primitive Pythagorean Triples and Their (m,n) Generators

**Slug**: pythagorean-theorem-oq-04-oq-01
**Created**: 2026-07-01T22:11:21-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $\mathcal{P}$ be the set of primitive Pythagorean triples with odd first leg, and let
$$
\mathcal{G} = \{\, (m,n) \in \mathbb{N}^2 : m > n > 0,\ \gcd(m,n) = 1,\ m \not\equiv n \pmod 2 \,\}
$$
be the fundamental domain of generators. The claim is that the parameterization map
$$
\Phi : \mathcal{G} \longrightarrow \mathcal{P}, \qquad (m,n) \longmapsto (m^2 - n^2,\ 2mn,\ m^2 + n^2)
$$
is a **bijection**, formalized in Lean as an
$$
\texttt{Equiv} \;:\; \mathcal{P} \;\simeq\; \mathcal{G}.
$$
Equivalently, the parent's two-to-one squaring map $g = m + ni \mapsto g^2$ on $\mathbb{Z}[i]$, once restricted to the fundamental domain that kills the $\{\pm 1\}$ sign ambiguity, becomes a genuine one-to-one correspondence.

### Plain Language

Every primitive Pythagorean triple — one where $\gcd(a,b,c) = 1$, like $(3,4,5)$ or $(5,12,13)$ — comes from exactly one pair of integers $(m,n)$ via Euclid's formula $a = m^2 - n^2$, $b = 2mn$, $c = m^2 + n^2$, provided we require $m > n > 0$, $\gcd(m,n) = 1$, and $m, n$ of opposite parity. The parent proof showed the generating pair is unique **up to sign**, i.e. $(m,n)$ and $(-m,-n)$ give the same triple. This problem asks us to nail down a single canonical representative for each triple and package the whole thing as a Lean `Equiv`: a two-way, invertible correspondence between primitive triples and generator pairs.

### Why This Matters

A bijection is strictly stronger than "surjective with a uniqueness-up-to-sign lemma": it gives a *canonical enumeration* of primitive triples. With an `Equiv` in hand one can count — e.g. transport it to prove that the number of primitive triples with hypotenuse below a bound equals the number of admissible $(m,n)$ with $m^2 + n^2$ below that bound, feeding classical asymptotics (the count grows like $c \cdot N$). It also turns the parent's descriptive classification into a computable, invertible data structure usable elsewhere in the gallery, and cleanly quotients out the unit-group ambiguity that the parent left implicit.

## Known Results

### What's Already Proven

- **Euclid's formula / (m,n) parameterization** — classical (Euclid, *Elements* Book X); every primitive triple with $a$ odd has the form $(m^2 - n^2, 2mn, m^2 + n^2)$ for coprime $m > n > 0$ of opposite parity.
- **`PythagoreanTriple.isPrimitiveClassified` / `coprime_classification'`** — Mathlib's `Mathlib.NumberTheory.PythagoreanTriples`; produces coprime, opposite-parity generators for any primitive triple.
- **`generator_unique_up_to_sign`** — parent proof `pythagorean-theorem-oq-04` (`Proofs/PythagoreanTheoremOQ04.lean`); two Gaussian-integer generators of the same primitive triple differ only by $\pm 1$, and multiplying by the unit $i$ negates the square, so the map is exactly two-to-one and no finer.
- **`gaussian_completeness`** — parent proof; every primitive triple $(x,y,z)$ with $x$ odd, $z > 0$ is $(m+ni)^2$ in $\mathbb{Z}[i]$ with coprime $m,n$ and $z = N(m+ni)$ (surjectivity onto primitive triples).

### What's Still Open

- Upgrading uniqueness-**up-to-sign** to a full `Equiv`: choosing one representative per $\{\pm 1\}$-orbit (the fundamental domain $m > n > 0$) and proving the forward/backward maps are mutual inverses.
- Discharging the exact side conditions of membership in $\mathcal{G}$ ($\gcd(m,n)=1$ and $m \not\equiv n \pmod 2$) so that the target of $\Phi$ is precisely $\mathcal{P}$, not a superset.

### Our Goal

Construct a Lean `Equiv` between the subtype of primitive Pythagorean triples (with the normalization used by the parent) and the subtype $\mathcal{G}$ of admissible generator pairs, defining `toFun`, `invFun`, and proving `left_inv`/`right_inv` by leaning on `generator_unique_up_to_sign` (for injectivity after picking representatives) and `gaussian_completeness`/`coprime_classification'` (for surjectivity). Deliver it as a verified, 0-axiom entry.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| pythagorean-theorem-oq-04 | Direct parent; supplies the squaring map, completeness, and `generator_unique_up_to_sign` | Gaussian-integer norm, `Zsqrtd.norm_mul`, `sq_eq_sq_iff_eq_or_eq_neg` |
| pythagorean-triples | The (m,n) parameterization via Mathlib's `PythagoreanTriple` and the rational unit circle | `PythagoreanTriple.isPrimitiveClassified`, rational parametrization |
| pythagorean-theorem | Classical $a^2 + b^2 = c^2$ underlying the whole family | Euclidean geometry, algebra |
| fermat-two-squares | Sister result routed through $\mathbb{Z}[i]$; prime norms vs. square norms | Gaussian integers, norm multiplicativity, unique factorization |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Explicit forward/backward maps with inverse proofs**: Define `toFun : 𝒢 → 𝒫` by $\Phi(m,n) = (m^2-n^2, 2mn, m^2+n^2)$ (with the parity/coprimality side conditions proving primitivity), and `invFun : 𝒫 → 𝒢` by extracting $(m,n)$ from `coprime_classification'` and normalizing to $m > n > 0$. Prove `right_inv` by evaluating $\Phi$ on the extracted generator (arithmetic), and `left_inv` by `generator_unique_up_to_sign` plus the fundamental-domain choice forcing the sign.
   - Why it might work: both directions already exist as parent lemmas; only the representative choice and inverse-plumbing are new.
   - Risk: reconciling the parent's $\mathbb{Z}[i]$ / sign-orbit formulation with a $\mathbb{N}$-valued fundamental domain (sign normalization across $\mathbb{Z} \to \mathbb{N}$) is fiddly.

2. **Approach B — Quotient by the $\{\pm 1\}$ action**: Model generators as $\mathbb{Z}^2$ (or $\mathbb{Z}[i]$) modulo the sign involution $(m,n) \mapsto (-m,-n)$, show the squaring/parameterization map descends to the quotient and is injective there (`generator_unique_up_to_sign` is exactly injectivity mod sign), then identify the quotient with the fundamental domain $\{m > n > 0\}$ via a `Quotient`/`Equiv` and compose.
   - Why it might work: it matches the mathematical structure the parent already exposed (the ambiguity *is* a $\{\pm 1\}$ subgroup), so injectivity is nearly free.
   - Risk: building the `Quotient` and its section (canonical representative) in Lean adds boilerplate; identifying the quotient with a concrete subtype still requires the same sign-normalization work as Approach A.

### Key Difficulties

- Choosing the canonical fundamental-domain representative: mapping each $\{\pm 1\}$-orbit to the unique pair with $m > n > 0$ and proving the choice is well-defined and total.
- Carrying the two side conditions — $\gcd(m,n) = 1$ and $m \not\equiv n \pmod 2$ (equivalently $m - n$ odd) — through both maps so that the codomain is exactly the primitive triples, matching the parent's odd-first-leg normalization.
- Bridging the parent's Gaussian-integer / integer sign statements to a subtype over $\mathbb{N}$ without introducing spurious cases (e.g. $n = 0$ or $m = n$).

### What Would a Proof Need?

- Key lemma 1: `right_inv` — $\Phi$ of the classified-and-normalized generator returns the original triple (arithmetic on `coprime_classification'`).
- Key lemma 2: `left_inv` — classifying $\Phi(m,n)$ and normalizing recovers $(m,n)$; the sign choice is forced by `generator_unique_up_to_sign` restricted to the fundamental domain.
- Technical requirements: a primitivity/parity lemma showing $\Phi(m,n) \in \mathcal{P}$ under the $\mathcal{G}$ conditions; a normalization function selecting $m > n > 0$; `Equiv.mk` assembling the four pieces.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Mathlib already provides `PythagoreanTriple.isPrimitiveClassified` / `coprime_classification'`, so surjectivity and generator extraction are off-the-shelf.
- The parent proof supplies `gaussian_completeness` and `generator_unique_up_to_sign`, reducing the new content to representative choice + inverse plumbing.
- The remaining work is `Equiv` assembly and side-condition bookkeeping — routine but detail-heavy Lean, not new mathematics.

**Estimated Effort**:
- Exploration: 0.5–1 day
- If tractable: 2–4 days
- If hard: 1 week (if the sign-normalization / quotient plumbing proves stubborn)

## References

### Papers
- Euclid, *Elements*, Book X (Lemma before Prop. 29) — the original geometric derivation of the $(m,n)$ parameterization.

### Online Resources
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/PythagoreanTriples.html — Mathlib docs for `PythagoreanTriple` and its classification lemmas.

### Mathlib
- `Mathlib.NumberTheory.PythagoreanTriples` — `PythagoreanTriple`, `isPrimitiveClassified`, `coprime_classification'`: generator extraction and primitivity.
- `Mathlib.Logic.Equiv.Basic` — `Equiv` and `Equiv.mk`: the bijection package (`toFun`, `invFun`, `left_inv`, `right_inv`).
- `Mathlib.NumberTheory.Zsqrtd.GaussianInt` — `GaussianInt`, `Zsqrtd.norm`, `Zsqrtd.norm_mul`: the Gaussian-integer squaring/norm machinery inherited from the parent.

## Metadata

```yaml
tags:
  - number-theory
  - pythagorean-triples
  - gaussian-integers
  - parameterization
  - bijection
related_proofs:
  - pythagorean-theorem-oq-04
  - pythagorean-triples
  - fermat-two-squares
difficulty: medium
source: gallery-gap
created: 2026-07-01T22:11:21-07:00
```

**Significance**: 5/10
**Tractability**: 6/10
