# Problem: A Self-Contained Irreducible Quintic with Galois Group Exactly S₅

**Slug**: abel-ruffini-obstruction-oq-06-oq-01
**Created**: 2026-07-09T16:43:19-07:00
**Status**: Active
**Source**: user-request

## Problem Statement

### Formal Statement

$$
\text{Let } q(X) = X^5 - X - 1 \in \mathbb{Q}[X]. \quad q \text{ is irreducible over } \mathbb{Q}, \quad \operatorname{Gal}(q/\mathbb{Q}) \cong S_5, \quad \text{hence for any root } \alpha,\ \neg\, \mathrm{IsSolvableByRad}\,\mathbb{Q}\,\alpha.
$$

### Plain Language

The parent gallery entry proves the abstract engine of Abel–Ruffini: if a polynomial is irreducible and its Galois group is not solvable, then its roots cannot be written using radicals (nth roots, sums, products, quotients). But that engine needs to be *fed* an actual polynomial whose Galois group is verifiably non-solvable. This problem asks us to formalize such a witness end-to-end. We take the concrete quintic $q(X) = X^5 - X - 1$, prove it is irreducible over the rationals, prove its Galois group is exactly the full symmetric group $S_5$ (which is not solvable because $A_5$ is simple and non-abelian), and then chain this into the parent's criterion to conclude that the specific number "a root of $X^5 - X - 1$" is provably not expressible by radicals. The result is a completely self-contained, machine-checked statement that a named quintic has no radical formula — not merely the abstract impossibility theorem.

### Why This Matters

Abel–Ruffini is usually taught as an *existence* statement ("there exist unsolvable quintics"), but the pedagogically and mathematically satisfying payoff is a *specific named example*. The parent proof `abel-ruffini-obstruction-oq-06` supplies the reusable criterion `not_solvableByRad_of_not_solvable_gal` but deliberately stops short of instantiating it on a concrete polynomial. Closing that gap turns the abstract obstruction into a fully certified statement about an explicit algebraic number, demonstrating that the criterion is not vacuous and giving the gallery its first end-to-end "this exact equation is unsolvable" theorem. The standard textbook witness $X^5 - X - 1$ (three real roots, one complex-conjugate pair, prime-order transitive Galois action) is the canonical route: it exercises the two group-theoretic levers that force $S_5$ — a transitive subgroup of $S_5$ containing a transposition and an element of order 5 is all of $S_5$.

## Known Results

### What's Already Proven

- `symmetricGroup_not_solvable` — $S_n$ is not solvable for every $n \ge 5$; parent proof `abel-ruffini-obstruction-oq-06` (`Proofs/AbelRuffiniObstructionOQ06.lean`).
- `not_solvableByRad_of_not_solvable_gal` — a root of an irreducible $q$ with non-solvable Galois group is not solvable by radicals; parent proof `abel-ruffini-obstruction-oq-06`.
- `Equiv.Perm.not_solvable` and `Equiv.Perm.fin_5_not_solvable` — non-solvability of the symmetric group; `Mathlib.GroupTheory.Solvable` and `Mathlib.GroupTheory.PermGroup` / `Mathlib.FieldTheory.AbelRuffini`.
- Mathlib's `Polynomial.Gal` machinery and `solvableByRad.isSolvable'` — `Mathlib.FieldTheory.AbelRuffini`.

### What's Still Open

- No formalized proof that the *specific* polynomial $X^5 - X - 1$ has Galois group exactly $S_5$ (Mathlib has no library lemma pinning this concrete group).
- No formalized end-to-end statement in the gallery that a named quintic is unsolvable by radicals; only the abstract criterion exists.

### Our Goal

Formalize, in a companion file that imports the parent, the three ingredients — (1) irreducibility of $q = X^5 - X - 1$ over $\mathbb{Q}$, (2) $\operatorname{Gal}(q/\mathbb{Q}) \cong S_5$ (equivalently, $q.\mathrm{Gal}$ is not solvable), and (3) the application of `not_solvableByRad_of_not_solvable_gal` — to obtain a single theorem: every root of $X^5 - X - 1$ is not solvable by radicals over $\mathbb{Q}$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| abel-ruffini-obstruction-oq-06 | Parent: supplies the criterion `not_solvableByRad_of_not_solvable_gal` and the non-solvability of $S_5$ that this problem instantiates | Solvable groups, derived series, contrapositive of `solvableByRad.isSolvable'`, `Cardinal.mk_fin` |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Transposition-plus-5-cycle (real analysis + reduction mod p)**: Prove $q = X^5 - X - 1$ irreducible over $\mathbb{Q}$ (it stays irreducible mod a suitable prime, or via a rational-root plus factorization argument), then show its Galois group is transitive (from irreducibility), contains a 5-cycle (transitivity of degree 5 forces $5 \mid |G|$, hence an order-5 element by Cauchy), and contains a transposition (complex conjugation acts as a transposition because $q$ has exactly two non-real roots — established by counting real roots via the derivative $5X^4 - 1$). A transitive subgroup of $S_5$ with a transposition and a 5-cycle is $S_5$.
   - Why it might work: this is the textbook argument (Dummit–Foote, Stewart) and each step maps onto a discrete, checkable claim; the real-root count uses only calculus.
   - Risk: Mathlib may lack a packaged "complex conjugation acts as a transposition when there are exactly two non-real roots" lemma, forcing a from-scratch development of the root-permutation action.

2. **Approach B — Discriminant non-square + prime order**: Show the discriminant of $q$ is not a rational square (so $\operatorname{Gal} \not\subseteq A_5$, giving an odd permutation) and that $\operatorname{Gal}$ is transitive of prime-related order forcing a 5-cycle; combined, a transitive group containing an odd permutation and a 5-cycle that is not contained in $A_5$ is $S_5$ (using that the only transitive subgroups of $S_5$ are $C_5, D_5, F_{20}, A_5, S_5$, and only $S_5$ meets these conditions).
   - Why it might work: the discriminant computation is a finite algebraic identity, potentially `decide`- or `norm_num`-friendly, avoiding the analytic real-root count.
   - Risk: classifying transitive subgroups of $S_5$ inside Lean is heavy; and computing/reasoning about the quintic discriminant symbolically is nontrivial in Mathlib.

### Key Difficulties

- Pinning the *concrete* Galois group to $S_5$: Mathlib supports abstract Galois theory but offers little direct support for computing the Galois group of a specific numeric polynomial.
- Formalizing "complex conjugation restricts to a transposition of the roots" requires connecting the real-root count (via calculus on $5X^4 - 1$) to the action of $\operatorname{Gal}$ on roots.
- Irreducibility of $X^5 - X - 1$ over $\mathbb{Q}$: needs a clean argument (e.g. reduction mod 2, where $X^5 + X + 1 = (X^2+X+1)(X^3+X^2+1)$ fails, so choose the right modulus — actually $X^5 - X - 1$ is irreducible mod 3), which must be discharged with Mathlib's finite-field / irreducibility tooling.

### What Would a Proof Need?

- Key lemma 1: `Irreducible (X^5 - X - 1 : ℚ[X])` — via reduction modulo a prime or an explicit factorization-exclusion argument.
- Key lemma 2: `¬ IsSolvable (X^5 - X - 1).Gal` — either through an isomorphism `q.Gal ≃* S₅` or directly by exhibiting a non-solvable subgroup / showing the group is transitive with a transposition and a 5-cycle.
- Technical requirements: the root-permutation action of `q.Gal`, Cauchy's theorem for the order-5 element, complex conjugation as a field automorphism restricting to the splitting field, and the analytic count of real roots of $q$.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematical argument is entirely classical and standard (a staple final-exam problem in graduate algebra), so there is no research risk in the mathematics itself.
- The parent proof already delivers the hard half — non-solvability of $S_5$ and the radical criterion — so only the concrete "Galois group $= S_5$" and irreducibility pieces remain.
- Similar concrete Galois-group determinations are known to be labor-intensive in Lean because Mathlib lacks a "compute the Galois group of this polynomial" tactic; the real-root-count and transposition steps may need bespoke lemmas.

**Estimated Effort**:
- Exploration: 1–2 days to map Mathlib's `Polynomial.Gal` action and irreducibility tooling.
- If tractable: 1–3 weeks to formalize irreducibility, the transposition/5-cycle argument, and the final chaining.
- If hard: unknown, dominated by the missing "concrete Galois group" infrastructure.

## References

### Papers
- Abel, N.H., "Démonstration de l'impossibilité de la résolution algébrique des équations générales qui passent le quatrième degré", 1826 — the original unsolvability proof underlying the parent entry.
- Dummit, D.S. & Foote, R.M., "Abstract Algebra", 3rd ed., 2004 — the transposition-plus-5-cycle criterion for $\operatorname{Gal} = S_5$ and the $X^5 - X - 1$ worked example.
- Stewart, I., "Galois Theory", 4th ed., 2015 — transitive Galois groups, discriminant test, and radical solvability.

### Online Resources
- https://en.wikipedia.org/wiki/Abel%E2%80%93Ruffini_theorem — statement and the standard quintic examples.

### Mathlib
- `Mathlib.FieldTheory.AbelRuffini` — `Polynomial.Gal`, `solvableByRad.isSolvable'`, the radical-solvability equivalence.
- `Mathlib.GroupTheory.Solvable` — `IsSolvable`, `Equiv.Perm.not_solvable`, derived series.
- `Mathlib.FieldTheory.PolynomialGaloisGroup` — the Galois group of a polynomial and its action on roots.
- `Mathlib.RingTheory.Polynomial.Irreducible` / `Mathlib.FieldTheory.Finite.Basic` — irreducibility criteria and reduction modulo a prime.

## Metadata

```yaml
tags:
  - algebra
  - galois-theory
  - group-theory
  - solvability
  - symmetric-group
  - abel-ruffini
  - radicals
  - research
related_proofs:
  - abel-ruffini-obstruction-oq-06
difficulty: medium
source: user-request
created: 2026-07-09T16:43:19-07:00
```
