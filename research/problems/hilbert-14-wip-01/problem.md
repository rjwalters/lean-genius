# Problem: Completing the Lean Formalization of Hilbert's 14th Problem (Finiteness of Invariant Systems)

**Slug**: hilbert-14-wip-01
**Created**: 2026-07-09T17:33:18-07:00
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
R^{G} = \{\, f \in k[x_1, \ldots, x_n] : g \cdot f = f \ \text{for all } g \in G \,\}
\quad\text{is finitely generated as a } k\text{-algebra whenever } G \text{ is reductive.}
$$

In general $R^{G}$ need not be finitely generated (Nagata's counterexample with $G = \mathbb{G}_a^{13}$ acting on $k^{32}$), but reductivity of $G$ — via the existence of a Reynolds operator projecting $k[x_1,\ldots,x_n] \twoheadrightarrow R^{G}$ — combined with Hilbert's Basis Theorem yields finite generation.

### Plain Language

We want to advance the Lean 4 formalization of Hilbert's 14th problem from an expository scaffold toward genuine machine-checked content. The 14th problem asks whether the ring of polynomial functions left invariant by a group action is always finitely generated; Nagata (1959) showed the answer is no in general, while Hilbert, Mumford, and Haboush showed yes for reductive groups. The current gallery entry `hilbert-14` only formally proves Hilbert's Basis Theorem (re-exported from Mathlib) and defines the ring of invariants and linear reductivity; the substantive resolution is present merely as doc-comment prose. Our goal is to formalize the connective structural steps that are within Mathlib's reach — that $k[x_1,\ldots,x_n]$ is Noetherian, that $R^{G}$ is a subalgebra, and that a Reynolds operator plus Noetherianity gives finite generation — while keeping the deep inputs (Nagata's counterexample and the existence of the Reynolds operator for reductive groups) as clearly stated assumptions.

### Why This Matters

1. **Upgrading exposition to formal content**: The entry currently formalizes only Hilbert's Basis Theorem and two definitions; the resolution itself is prose. Formalizing the Reynolds-operator argument turns commentary into checked mathematics.
2. **Reusable invariant-theory scaffolding**: Formal definitions of the invariant subalgebra $R^{G}$, group actions on polynomial rings, and the reductivity/Reynolds structure are broadly reusable across algebra entries and are largely absent from Mathlib.
3. **Precise separation of hard from easy**: Isolating exactly which facts are deep (Nagata's counterexample; Haboush's theorem that reductive groups are geometrically reductive) versus which are formal bookkeeping clarifies the true assumption footprint of the entry.

## Known Results

### What's Already Proven

- Hilbert's Basis Theorem: if $R$ is Noetherian then $R[X]$ and $k[x_1,\ldots,x_n]$ are Noetherian — Hilbert (1890), formalized in Mathlib (`Polynomial.isNoetherianRing`, `MvPolynomial.isNoetherianRing`).
- Finite generation of $R^{G}$ for reductive $G$ in characteristic $0$ — Hilbert (1890), Mumford (1965), via the Reynolds operator.
- Finite generation for reductive $G$ in all characteristics — Haboush's theorem (1975), resolving geometric reductivity.
- Nagata's counterexample: a non-reductive $G = \mathbb{G}_a^{13}$ action whose invariant ring is not finitely generated — Nagata (1959).

### What's Still Open

- A complete characterization of which non-reductive groups nonetheless have finitely generated invariants.
- Optimal degree bounds for generators of $R^{G}$ for reductive groups (beyond the Noether bound in the finite-group case).
- Effective algorithms deciding finite generation for specific non-reductive group actions.

### Our Goal

Strengthen `Proofs/Hilbert14Invariants.lean` so that (i) the `InvariantElements` definition is upgraded from a set to a formally verified subalgebra $R^{G} \le k[x_1,\ldots,x_n]$; (ii) the finite-generation implication "reductive (Reynolds operator exists) + Noetherian ⇒ $R^{G}$ finitely generated" is formally proved, using Mathlib's Noetherian machinery, from a `Reynolds`/`LinearlyReductive` hypothesis; and (iii) Nagata's counterexample and the existence of the Reynolds operator for reductive groups are retained as explicitly disclosed assumptions rather than prose, so `meta.json`'s assumption list honestly reflects the formal content.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| hilbert-14 | Direct parent entry; supplies Hilbert's Basis Theorem, the `InvariantElements` and `LinearlyReductive` definitions, and the exposition to be formalized | Noetherian rings, polynomial ring theory, Reynolds operator |
| erdos-116 | Companion gallery entry following the same pattern where definitions are formal but the deep resolution stays axiomatized | Structure definitions, assumption isolation |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Formalize the Reynolds-operator finite-generation argument, assuming the Reynolds operator as a structure field.
   - Why it might work: Given a Reynolds operator $\rho : R \to R^{G}$ that is $R^{G}$-linear, the standard argument (the ideal generated by positive-degree invariants is finitely generated by Noetherianity, and $\rho$ transports generators) is a finite algebraic manipulation well-suited to Mathlib's `IsNoetherian`/`Subalgebra.FG` API.
   - Risk: Mathlib may lack graded-ring or homogeneous-decomposition support needed to run the classical degree argument cleanly, requiring workarounds.

2. **Approach B**: Focus first on formalizing $R^{G}$ as a `Subalgebra` and the Noetherianity of $k[x_1,\ldots,x_n]$, deferring finite generation.
   - Why it might work: These are the load-bearing structural facts and are directly supported by `MvPolynomial.isNoetherianRing` and `Subalgebra` closure lemmas, giving quick, robust wins.
   - Risk: Without the finite-generation step the entry remains mostly definitional, so the substantive theorem still lives only as an assumption.

### Key Difficulties

- Haboush's theorem (geometric reductivity in positive characteristic) and Nagata's counterexample are deep results with no realistic Lean formalization path; they must remain assumptions.
- Encoding a group action on a multivariate polynomial ring and the invariance condition faithfully in Mathlib requires careful setup of the action typeclass and the fixed subalgebra.

### What Would a Proof Need?

- Key lemma 1: $R^{G}$ is a `Subalgebra` of $k[x_1,\ldots,x_n]$ closed under the ring operations and containing $k$.
- Key lemma 2: A Reynolds operator hypothesis $\rho : R \to R^{G}$ together with Noetherianity of $R$ implies $R^{G}$ is finitely generated.
- Technical requirements: Mathlib's `IsNoetherianRing`, `Subalgebra.FG`, and a faithful `MulAction`/`DistribMulAction` encoding of $G$ on the polynomial ring.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The structural sub-goals (subalgebra, Noetherianity) are directly supported by Mathlib, but the finite-generation argument needs graded/homogeneous machinery that is only partially present.
- Similar formalization patterns in the gallery succeed by proving structural lemmas and assuming the deep theorem; the same applies to Haboush's theorem and Nagata's counterexample here.
- Mathlib provides `MvPolynomial.isNoetherianRing`, `Subalgebra`, and `IsNoetherian`, sufficient for the scaffold but not for geometric reductivity.

**Estimated Effort**:
- Exploration: 3–5 days to survey Mathlib's invariant-theory and graded-ring support.
- If tractable: 2–4 weeks to formalize the subalgebra and the Reynolds finite-generation implication.
- If hard: Haboush's theorem and Nagata's counterexample remain assumptions indefinitely.

## References

### Papers
- Hilbert, "Über die Theorie der algebraischen Formen" (1890) — Basis Theorem and finiteness for classical groups.
- Nagata, "On the 14th problem of Hilbert" (1959) — counterexample for a non-reductive group.
- Mumford, "Geometric Invariant Theory" (1965) — reductive-group finiteness in characteristic 0.
- Haboush, "Reductive groups are geometrically reductive" (1975) — resolution in all characteristics.

### Online Resources
- https://en.wikipedia.org/wiki/Hilbert%27s_fourteenth_problem — overview of the problem and its resolution.

### Mathlib
- Mathlib.RingTheory.Noetherian — `IsNoetherianRing` and finitely generated ideals.
- Mathlib.RingTheory.Polynomial.Basic — `Polynomial.isNoetherianRing` (Hilbert's Basis Theorem).
- Mathlib.Algebra.MvPolynomial.Basic — `MvPolynomial.isNoetherianRing` for multivariate rings.

## Metadata

```yaml
tags:
  - invariant-theory
  - commutative-algebra
  - group-actions
  - noetherian-rings
  - hilbert-problems
  - formalization
related_proofs:
  - hilbert-14
  - erdos-116
difficulty: high
source: proof-suggestion
created: 2026-07-09T17:33:18-07:00
```

**Significance**: 8/10
**Tractability**: 5/10
