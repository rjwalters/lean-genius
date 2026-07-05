# Problem: Cyclotomic ⇒ Quadratic Reciprocity via `galEquivUnits` on the Quadratic Subfield

**Slug**: hilbert-9-reciprocity-oq-01-oq-02
**Created**: 2026-07-04T03:23:44-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $p$ be an odd prime and $\zeta_p$ a primitive $p$-th root of unity. The gallery
already establishes the cyclotomic reciprocity isomorphism

$$
\mathrm{galEquivUnits} : \operatorname{Gal}\big(\mathbb{Q}(\zeta_p)/\mathbb{Q}\big)\ \xrightarrow{\ \sim\ }\ (\mathbb{Z}/p\mathbb{Z})^\times .
$$

The unique quadratic subfield of $\mathbb{Q}(\zeta_p)$ is
$\mathbb{Q}\big(\sqrt{p^\*}\big)$ with $p^\* = (-1)^{(p-1)/2}\,p$, corresponding under the
Galois correspondence to the index-2 subgroup of squares in $(\mathbb{Z}/p\mathbb{Z})^\times$.

**Goal.** Show that the composite

$$
\operatorname{Gal}\big(\mathbb{Q}(\zeta_p)/\mathbb{Q}\big) \xrightarrow{\ \mathrm{galEquivUnits}\ } (\mathbb{Z}/p\mathbb{Z})^\times \xrightarrow{\ \left(\tfrac{\cdot}{p}\right)\ } \{\pm 1\}
$$

coincides with the restriction map to $\operatorname{Gal}\big(\mathbb{Q}(\sqrt{p^\*})/\mathbb{Q}\big)\cong\{\pm1\}$;
equivalently, a residue $a$ is a square mod $p$ iff the corresponding automorphism fixes
$\sqrt{p^\*}$. As a corollary, deduce the law of quadratic reciprocity
$\left(\tfrac{p}{q}\right)\left(\tfrac{q}{p}\right) = (-1)^{\frac{p-1}{2}\frac{q-1}{2}}$
by evaluating the Frobenius at $q$ inside $\mathbb{Q}(\sqrt{p^\*})$.

### Plain Language

The cyclotomic field $\mathbb{Q}(\zeta_p)$ contains exactly one quadratic field
$\mathbb{Q}(\sqrt{p^\*})$. Squares mod $p$ correspond to Galois automorphisms that fix
this quadratic field, non-squares to those that swap $\pm\sqrt{p^\*}$. Making that
correspondence precise (the restriction of `galEquivUnits` to the quadratic subfield IS
the Legendre symbol) turns the already-formalized *cyclotomic* reciprocity into a proof of
the classical *quadratic* reciprocity law — one of the cleanest derivations, connecting two
gallery entries that currently stand apart.

### Why This Matters

Quadratic reciprocity is the historical seed of class field theory and of Hilbert's 9th
problem (general reciprocity). The cyclotomic route is Hilbert's own preferred proof and the
gateway to Artin reciprocity. Formalizing this bridge unifies two existing gallery proofs
(`hilbert-9-reciprocity` and `elementary-quadratic-reciprocity`) under a single conceptual
mechanism rather than leaving them as independent facts.

## Known Results

### What's Already Proven

- Cyclotomic reciprocity isomorphism `galEquivUnits` — gallery: `hilbert-9-reciprocity`
- Elementary (Eisenstein/Gauss-sum) proof of quadratic reciprocity — gallery: `elementary-quadratic-reciprocity`
- `(ℤ/pℤ)ˣ` is cyclic; squares form the unique index-2 subgroup — Mathlib `ZMod.instField`, `ZMod.unitsEquiv…`
- Quadratic Gauss sum $g^2 = p^\*$, hence $\sqrt{p^\*}\in\mathbb{Q}(\zeta_p)$ — Mathlib `GaussSum`, `Gauss sum` API

### What's Still Open (for this formalization)

- Identifying the fixed field of the squares subgroup with `ℚ(√p*)` inside the gallery's setup
- Proving `galEquivUnits` restricted to the quadratic subfield equals the Legendre symbol as maps to `{±1}`
- Packaging the Frobenius-at-$q$ evaluation to recover the reciprocity sign

### Our Goal

Formalize the single statement "restriction of `galEquivUnits` to the quadratic subfield =
Legendre symbol" and derive quadratic reciprocity as its corollary, reusing the gallery's
existing cyclotomic infrastructure rather than re-deriving Gauss sums from scratch.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| hilbert-9-reciprocity | Provides `galEquivUnits`, the Galois↔units isomorphism to build on | Cyclotomic Galois theory |
| hilbert-9-reciprocity-oq-01 | Direct parent open question (Frobenius/Artin-symbol layer) | Frobenius, Artin symbol |
| elementary-quadratic-reciprocity | The target law to be re-derived; sanity check | Gauss sums, Eisenstein |
| cyclotomic-polynomials-oq-01 | Structure of `ℚ(ζ_p)` and its subfields | Cyclotomic polynomials |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Fixed-field / character route**: Define the quadratic character
   $\chi = \left(\tfrac{\cdot}{p}\right)$ as the unique order-2 character of $(\mathbb{Z}/p)^\times$,
   transport it through `galEquivUnits`, and show its kernel's fixed field is `ℚ(√p*)`.
   - Why it might work: only uses the already-formalized isomorphism plus Mathlib's cyclic-group character API.
   - Risk: identifying the fixed field concretely as `ℚ(√p*)` may need the Gauss-sum value $g^2=p^\*$.

2. **Approach B — Gauss-sum route**: Use $\sqrt{p^\*}=g$ (a quadratic Gauss sum) directly, and
   compute $\sigma_a(g) = \left(\tfrac{a}{p}\right) g$ for $\sigma_a$ corresponding to $a$.
   - Why it might work: $\sigma_a(g)=\chi(a)g$ is a short Mathlib-friendly computation.
   - Risk: bridging Mathlib's `gaussSum` conventions to the gallery's `galEquivUnits` indexing.

### Key Difficulties

- Matching indexing/orientation conventions between the gallery's `galEquivUnits` and Mathlib's Gauss-sum lemmas.
- Cleanly stating "restriction to the quadratic subfield" without heavy field-embedding boilerplate.

### What Would a Proof Need?

- Key lemma 1: $\sigma_a(g) = \left(\tfrac{a}{p}\right)\,g$ where $g$ is the quadratic Gauss sum.
- Key lemma 2: $g^2 = p^\*$, so $\mathbb{Q}(g)=\mathbb{Q}(\sqrt{p^\*})$ is the quadratic subfield.
- Technical: transport of the order-2 character through `galEquivUnits`; Frobenius-at-$q$ specialization for the reciprocity corollary.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematics is classical and fully known (Hilbert's cyclotomic proof); no genuinely open step.
- Mathlib has strong Gauss-sum and cyclotomic support, and the gallery already supplies `galEquivUnits`.
- Similar character/Gauss-sum computations are already formalized in `elementary-quadratic-reciprocity`.

**Estimated Effort**:
- Exploration: 1–2 days (align gallery `galEquivUnits` with Mathlib Gauss-sum API)
- If tractable: 1–2 weeks for the restriction lemma + reciprocity corollary
- If hard: convention-matching could stall; fall back to the pure Gauss-sum statement

## References

### Papers
- Ireland & Rosen, *A Classical Introduction to Modern Number Theory*, ch. 6 — cyclotomic proof of QR.
- Hilbert, *Zahlbericht* — reciprocity via cyclotomic fields.

### Online Resources
- Milne, *Algebraic Number Theory* notes — quadratic subfield of `ℚ(ζ_p)` and QR.

### Mathlib
- `Mathlib.NumberTheory.GaussSum` — quadratic Gauss sums, $g^2 = p^\*$.
- `Mathlib.NumberTheory.Cyclotomic.*` — cyclotomic fields and Galois groups.
- `Mathlib.NumberTheory.LegendreSymbol.*` — Legendre symbol as a multiplicative character.

## Metadata

```yaml
tags:
  - number-theory
  - reciprocity
  - hilbert-9
  - cyclotomic
  - quadratic-reciprocity
  - gauss-sums
related_proofs:
  - hilbert-9-reciprocity
  - hilbert-9-reciprocity-oq-01
  - elementary-quadratic-reciprocity
  - cyclotomic-polynomials-oq-01
difficulty: medium
source: gallery-gap
created: 2026-07-04T03:23:44-07:00
```

**Significance**: 7/10
**Tractability**: 5/10
