# Problem: Hilbert Irreducibility for Uniform Sₙ / Aₙ Realizations

**Slug**: inverse-galois-a5-oq-03
**Created**: 2026-06-17
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
f(t,X) \in \mathbb{Q}(t)[X] \text{ with } \mathrm{Gal}(f/\mathbb{Q}(t)) = G
\;\Longrightarrow\;
\exists^{\infty}\, t_0 \in \mathbb{Q}:\ \mathrm{Gal}(f(t_0,X)/\mathbb{Q}) = G.
$$

Concretely: formalize (a usable special case of) **Hilbert's Irreducibility
Theorem** strong enough to convert the generic polynomials $f_n(t,X)$ realizing
$S_n$ and $A_n$ over $\mathbb{Q}(t)$ into infinitely many specializations
$t_0 \in \mathbb{Q}$ realizing $S_n$ (resp. $A_n$) as a Galois group over
$\mathbb{Q}$.

### Plain Language

The parent gallery proof realizes $A_5$ as a Galois group over $\mathbb{Q}$ by
exhibiting a specific quintic. A systematic way to realize *every* symmetric group
$S_n$ and alternating group $A_n$ is: write down a one-parameter family of
polynomials $f_n(t,X)$ whose Galois group over the function field $\mathbb{Q}(t)$
is provably $S_n$ (resp. $A_n$), then *specialize* the parameter $t$ to a rational
number while preserving the Galois group. The theorem guaranteeing that "most"
specializations preserve the group is **Hilbert's Irreducibility Theorem**. This
problem asks to formalize enough of that machinery to give uniform realizations of
$S_n$ and $A_n$ for all $n$.

### Why This Matters

This generalizes the single $A_5$ realization (the gallery's first non-solvable
example) into an *infinite family*, capturing the textbook route to the
"easy half" of the Inverse Galois Problem ($S_n$, $A_n$). Hilbert irreducibility
is currently absent from Mathlib in usable form, so even a restricted version is a
genuine, reusable contribution beyond this entry.

### Why This Matters (scope note)

This is a **challenging** target: full Hilbert irreducibility is a substantial
piece of arithmetic geometry. The intended deliverable is a *restricted but honest*
specialization statement sufficient for $S_n/A_n$, with any remaining analytic
input clearly marked as an assumption — not an over-claimed "verified" full HIT.

## Known Results

### What's Already Proven

- Parent `inverse-galois-a5` (`proofs/Proofs/InverseGaloisA5.lean`, 2067 lines, 1 axiom, 0 sorries): $A_5$ realizable over $\mathbb{Q}$ via an explicit quintic; Vandermonde-discriminant machinery (Parts VIII–XV)
- Companion oq-01 and oq-02 are completed in the gallery (active, productive vein)
- Mathlib has `Polynomial.Galois`, splitting fields, and discriminant/`galGroup` infrastructure

### What's Still Open

- A formal statement of Hilbert irreducibility (even the "thin set" / single-variable form)
- Generic polynomials $f_n(t,X)$ with $\mathrm{Gal} = S_n$ over $\mathbb{Q}(t)$ and the $A_n$ specialization (square discriminant)
- The specialization step preserving the Galois group on an infinite set of $t_0$

### Our Goal

Stage the result: (1) state `HilbertIrreducible` for one parameter as an interface
(assumption or restricted theorem); (2) formalize $\mathrm{Gal}(f_n/\mathbb{Q}(t)) = S_n$
for the standard generic family; (3) derive $S_n$ over $\mathbb{Q}$ for infinitely
many $t_0$ via (1); (4) pass to $A_n$ by adjoining $\sqrt{\mathrm{disc}}$. Be explicit
about which steps are assumptions.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| inverse-galois-a5 | Parent: explicit $A_5$ realization, discriminant machinery | splitting fields, discriminant, `galGroup` |
| abel-ruffini / galois-extensions entries | Galois-group computation and solvability infrastructure | field theory, group theory |

## Initial Thoughts

### Potential Approaches

1. **Approach A — interface-first specialization**: Introduce a clearly-scoped
   `HilbertIrreducible` hypothesis (specialization preserves Galois group on an
   infinite set), then build the $S_n \to A_n$ pipeline on top. Discharge later.
   - Why it might work: separates the hard analytic core from the algebraic pipeline; immediately useful.
   - Risk: the result remains *axiomatized* until HIT is formalized (must be labeled honestly).

2. **Approach B — generic-polynomial Galois computation**: Prove
   $\mathrm{Gal}(X^n + t_{n-1}X^{n-1} + \dots + t_0 / \mathbb{Q}(t_\bullet)) = S_n$
   via the symmetric-function / transitivity argument; reduce $A_n$ to a square
   discriminant.
   - Why it might work: this part is algebra Mathlib can largely support.
   - Risk: multivariate function fields and transitivity arguments are heavy in Lean.

### Key Difficulties

- Hilbert irreducibility itself is not in Mathlib (number-theoretic core)
- Function-field $\mathbb{Q}(t)$ Galois theory and specialization maps
- Keeping the assumption surface explicit (axiom integrity policy)

### What Would a Proof Need?

- Key lemma 1: $\mathrm{Gal}(f_n/\mathbb{Q}(t)) = S_n$ for the generic family
- Key lemma 2: a specialization theorem (HIT, possibly assumed) giving infinitely many $t_0$
- Technical requirements: `IsGalois`, `Polynomial.Gal`, discriminant API, rational-points density

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The algebraic pipeline ($S_n$ generic, $A_n$ via discriminant) is reachable in Mathlib.
- Hilbert irreducibility is the hard, currently-missing ingredient; expect to assume it initially.
- The parent vein (oq-01/oq-02 completed) shows the area is being actively and successfully formalized.

**Estimated Effort**:
- Exploration: days
- If tractable (interface + $S_n$ generic computation): weeks
- If hard (full HIT formalization): unknown / long-term

## References

### Papers
- D. Hilbert, "Über die Irreduzibilität ganzer rationaler Funktionen…", J. Reine Angew. Math. 110 (1892).
- J.-P. Serre, *Topics in Galois Theory* — Hilbert irreducibility and the $S_n/A_n$ realizations (Ch. 3–4).
- G. Malle and B. H. Matzat, *Inverse Galois Theory* — generic polynomials and specialization.

### Online Resources
- https://en.wikipedia.org/wiki/Hilbert%27s_irreducibility_theorem — statement and standard consequences.

### Mathlib
- `Mathlib.FieldTheory.Galois`, `Mathlib.FieldTheory.SplittingField` — Galois groups of polynomials.
- `Mathlib.RingTheory.Polynomial.Discriminant` — discriminant for the $A_n$ reduction.

## Metadata

```yaml
tags:
  - field-theory
  - galois-theory
  - inverse-galois-problem
  - number-theory
related_proofs:
  - inverse-galois-a5
  - abel-ruffini
difficulty: high
source: proof-suggestion
created: 2026-06-17
```
