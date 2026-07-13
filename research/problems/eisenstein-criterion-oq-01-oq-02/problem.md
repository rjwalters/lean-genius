# Problem: Degree of ℚ(ⁿ√p): the minimal polynomial Xⁿ − p via Eisenstein

**Slug**: eisenstein-criterion-oq-01-oq-02
**Created**: 2026-07-09T16:03:15-07:00
**Status**: Active
**Source**: user-request <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
p \text{ prime},\ n \ge 1 \;\Longrightarrow\; X^n - p \text{ is the minimal polynomial of } p^{1/n} \text{ over } \mathbb{Q}, \quad\text{hence}\quad [\mathbb{Q}(p^{1/n}) : \mathbb{Q}] = n.
$$

Equivalently, writing $\alpha = p^{1/n}$ for the real positive $n$-th root of a prime $p$:

$$
\mathrm{minpoly}_{\mathbb{Q}}(\alpha) = X^n - p \quad\text{and}\quad \dim_{\mathbb{Q}} \mathbb{Q}(\alpha) = n.
$$

### Plain Language

Eisenstein's criterion (already formalized in the gallery) shows that $X^n - p$ cannot be factored over the rationals for any prime $p$ and any exponent $n \ge 1$. This problem asks for the natural *field-theoretic* payoff of that fact: because $X^n - p$ is irreducible, monic, and vanishes at the real $n$-th root $p^{1/n}$, it must *be* the minimal polynomial of $p^{1/n}$ over $\mathbb{Q}$. The degree of the field extension $\mathbb{Q}(p^{1/n})$ over $\mathbb{Q}$ then equals the degree of that minimal polynomial, namely $n$. So Eisenstein supplies, on demand, an algebraic number of every degree $n = 1, 2, 3, \dots$.

### Why This Matters

- **Bridges irreducibility and field degree.** The gallery already has $X^n - p$ irreducible; this closes the loop to the standard corollary $[\mathbb{Q}(p^{1/n}):\mathbb{Q}] = n$ that every algebra course states but the gallery has not yet formalized.
- **Algebraic numbers of every degree.** It gives an explicit, uniform construction of algebraic numbers of arbitrarily large prescribed degree, a foundational fact underpinning Galois theory, transcendence arguments, and field-tower computations.
- **Reusable degree template.** The reasoning "irreducible + monic + root ⇒ minimal polynomial ⇒ degree" is the canonical way to compute extension degrees; formalizing it against the gallery's Eisenstein entry produces a template reusable for $\sqrt{2}$, $\sqrt[3]{2}$, cyclotomic fields, and more.

## Known Results

### What's Already Proven

- **Irreducibility of $X^n - p$ over $\mathbb{Z}$ (hence $\mathbb{Q}$)** — gallery entry `eisenstein-criterion-oq-01` (`irreducible_X_pow_sub_C_prime`), via Eisenstein at the prime ideal $(p)$.
- **Eisenstein's criterion in ideal form** — gallery entry `eisenstein-criterion-oq-01` (`irreducible_of_eisenstein`), a named restatement of `Polynomial.irreducible_of_eisenstein_criterion`.
- **Concrete irrationality of $\sqrt[3]{3}$** — gallery entry `cube-root-3-irrational-oq-01`, the $n=3$, $p=3$ instance of the general story pursued here.
- **Minimal-polynomial / degree API in Mathlib** — `minpoly`, `IntermediateField.adjoin`, `Field.finrank`, and `Polynomial.Monic.eq_of_...`/`minpoly.eq_of_irreducible_of_monic`-style lemmas provide the general machinery.

### What's Still Open

- No gallery entry currently states $\mathrm{minpoly}_{\mathbb{Q}}(p^{1/n}) = X^n - p$ for general prime $p$ and general $n$.
- No gallery entry currently states $[\mathbb{Q}(p^{1/n}):\mathbb{Q}] = n$ for the general family (only the concrete cube-root case is treated as irrationality, not as a degree computation).

### Our Goal

Formalize, in Lean 4 on top of the gallery's Eisenstein entry and Mathlib, the two statements: (i) $X^n - p$ is the minimal polynomial over $\mathbb{Q}$ of the real positive $n$-th root $p^{1/n}$ (for prime $p$, $n \ge 1$); and (ii) as a corollary, $[\mathbb{Q}(p^{1/n}):\mathbb{Q}] = n$. Include at least one concrete instance (e.g. $[\mathbb{Q}(\sqrt{2}):\mathbb{Q}] = 2$ or $[\mathbb{Q}(\sqrt[3]{2}):\mathbb{Q}] = 3$) certified by specialization.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| eisenstein-criterion-oq-01 | Supplies the irreducibility of $X^n - p$ that this problem converts into a minimal polynomial and field degree | Eisenstein criterion, ideal $(p)$, coefficient bookkeeping |
| cube-root-3-irrational-oq-01 | Concrete $n=3$, $p=3$ case — $\sqrt[3]{3} \notin \mathbb{Q}$ is the degree-$>1$ shadow of this degree computation | Irreducibility ⇒ irrationality |
| cyclotomic-polynomials-oq-01 | Companion field-degree story: $[\mathbb{Q}(\zeta_n):\mathbb{Q}] = \varphi(n)$ mirrors this "irreducible minimal polynomial ⇒ degree" pattern | Minimal polynomial, extension degree |

## Initial Thoughts

### Potential Approaches

1. **Approach A — `minpoly.eq_of_irreducible`/monic route (recommended).**
   Show $\alpha = p^{1/n}$ is a root of $X^n - p$ over $\mathbb{Q}$; the polynomial is monic (`monic_X_pow_sub_C`) and irreducible over $\mathbb{Q}$ (from the gallery result, transported $\mathbb{Z} \to \mathbb{Q}$ via `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map` / Gauss's lemma). Then a Mathlib lemma of the form "monic, irreducible, and $p(\alpha)=0$ ⇒ $p = \mathrm{minpoly}$" pins down the minimal polynomial. Degree then follows from `minpoly.degree` combined with `IntermediateField.adjoin.finrank` / `minpoly.natDegree`.
   - Why it might work: every ingredient exists in Mathlib; the irreducibility import is the only non-trivial bridge and is a standard Gauss-lemma transfer.
   - Risk: the $\mathbb{Z}\to\mathbb{Q}$ irreducibility transfer requires care (primitive/monic hypotheses) and picking the exactly-matching Mathlib lemma name.

2. **Approach B — realize $\alpha$ inside $\mathbb{C}$ or $\mathbb{R}$ and use `Polynomial.aeval`.**
   Work with $\alpha := (p : \mathbb{R})^{(1/n : \mathbb{R})}$ (or a chosen complex root), prove `aeval α (X^n - C p) = 0` by `Real.rpow` / `Real.rootn` arithmetic, then feed into the `minpoly` machinery as in Approach A.
   - Why it might work: makes the root concrete and the "is a root" obligation computational.
   - Risk: `rpow`/root-existence bookkeeping in $\mathbb{R}$ can be fiddly; may be cleaner to use an abstract root of the polynomial via `AdjoinRoot`.

3. **Approach C — `AdjoinRoot (X^n - C p)` abstract construction.**
   Instead of naming a real root, form $K := \mathbb{Q}[X]/(X^n - p) = $ `AdjoinRoot (X^n - C p)`. Since the polynomial is irreducible and monic, $K$ is a field extension of $\mathbb{Q}$ with `Module.finrank ℚ K = n` directly from `AdjoinRoot.powerBasis` / `PowerBasis.finrank`.
   - Why it might work: sidesteps analytic root existence entirely; degree is essentially immediate from the power basis of an irreducible monic polynomial.
   - Risk: gives the degree of the abstract quotient field, which is the cleanest theorem, but proving it *equals* $\mathbb{Q}(p^{1/n})$ for the real root still needs Approach A/B if that identification is wanted.

### Key Difficulties

- **Irreducibility transfer $\mathbb{Z} \to \mathbb{Q}$.** The gallery proves irreducibility over $\mathbb{Z}$; the field-degree statement lives over $\mathbb{Q}$. Bridging requires Gauss's lemma (`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map` or `IsPrimitive.Int.irreducible_iff_irreducible_map_cast`).
- **Choosing the "right" root.** Deciding between a concrete real/complex root $p^{1/n}$ and the abstract `AdjoinRoot` element changes which downstream lemmas apply; the abstract route (Approach C) is likely the least painful for the *degree* claim.
- **Matching Mathlib lemma names.** `minpoly` has several near-miss characterization lemmas (`minpoly.eq_of_irreducible_of_monic`, `minpoly.unique`, etc.); selecting the correct one and its exact hypotheses is the main friction.

### What Would a Proof Need?

- Key lemma 1: Irreducibility of $X^n - C p$ over $\mathbb{Q}$ (from gallery $\mathbb{Z}$-result + Gauss's lemma).
- Key lemma 2: $X^n - C p$ is monic of degree $n$ (`monic_X_pow_sub_C`, `degree_X_pow_sub_C`, `natDegree_X_pow_sub_C`).
- Key lemma 3: A minimal-polynomial uniqueness lemma: monic + irreducible + $\alpha$ a root ⇒ `minpoly ℚ α = X^n - C p`.
- Key lemma 4: Degree corollary: `Module.finrank ℚ ℚ⟮α⟯ = (minpoly ℚ α).natDegree = n` via `IntermediateField.adjoin.finrank` / `AdjoinRoot.powerBasis`.
- Technical requirements: `import Mathlib`; care with `Prime (p : ℤ)` vs `Nat.Prime p`; the analytic existence of $p^{1/n}$ if the concrete-root route is taken.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Mathlib has strong, directly applicable support: `minpoly`, `AdjoinRoot.powerBasis`, `IntermediateField.adjoin.finrank`, Gauss's lemma for irreducibility transfer, and the exact `X^n - C p` degree/monic lemmas.
- The mathematical content is a standard textbook corollary; the only real work is Lean plumbing (irreducibility transfer and lemma-name matching), not new mathematics.
- Similar degree computations already exist in Mathlib and the gallery (cyclotomic field degrees, `AdjoinRoot` power bases), so there is a proven template to imitate.

**Estimated Effort**:
- Exploration: 0.5–1 day
- If tractable: 1–3 days
- If hard: ~1 week (if the $\mathbb{Z}\to\mathbb{Q}$ transfer or concrete-real-root identification proves stubborn)

## References

### Papers
- Eisenstein, G. (1850). *Über die Irreductibilität ... der ganzen Lemniscate.* Crelle's Journal — origin of the criterion; Schönemann (1846) gave an equivalent form.
- Dummit, D. & Foote, R. *Abstract Algebra* — §13.2/§14 develop exactly "irreducible minimal polynomial ⇒ $[\mathbb{Q}(\alpha):\mathbb{Q}] = \deg \mathrm{minpoly}$", with $X^n - p$ as the standard example.

### Online Resources
- https://en.wikipedia.org/wiki/Eisenstein%27s_criterion — statement and the $X^n - p$ / $\sqrt[n]{p}$ consequence.
- https://en.wikipedia.org/wiki/Minimal_polynomial_(field_theory) — minimal polynomial and degree of a simple extension.
- https://leanprover-community.github.io/mathlib4_docs/ — Mathlib API for `minpoly`, `AdjoinRoot`, `IntermediateField`.

### Mathlib
- `Mathlib.FieldTheory.Minpoly.Basic` / `Minpoly.Field` — `minpoly`, `minpoly.degree`, `minpoly.eq_of_irreducible`-style uniqueness lemmas.
- `Mathlib.RingTheory.AdjoinRoot` — `AdjoinRoot.powerBasis`, `PowerBasis.finrank` for the abstract $\mathbb{Q}[X]/(X^n-p)$ degree.
- `Mathlib.FieldTheory.IntermediateField.Adjoin` / `Adjoin.finrank` — $[\mathbb{Q}(\alpha):\mathbb{Q}] = \deg \mathrm{minpoly}$.
- `Mathlib.RingTheory.Polynomial.GaussLemma` — `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map` for the $\mathbb{Z}\to\mathbb{Q}$ irreducibility transfer.
- `Mathlib.RingTheory.Polynomial.Basic` — `monic_X_pow_sub_C`, `degree_X_pow_sub_C`, `natDegree_X_pow_sub_C`.

## Metadata

```yaml
tags:
  - algebra
  - polynomials
  - irreducibility
  - number-theory
  - ring-theory
  - open-question
related_proofs:
  - eisenstein-criterion-oq-01
  - cube-root-3-irrational-oq-01
difficulty: medium
source: user-request
created: 2026-07-09T16:03:15-07:00
```
