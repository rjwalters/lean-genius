# Problem: Four consecutive integers with equal Euler totient

**Slug**: erdos-1003-oq-04
**Created**: 2026-07-02T16:50:31-07:00
**Status**: Active
**Source**: proof-suggestion <!-- open question spawned from erdos-1003 -->

## Problem Statement

### Formal Statement

$$
\exists\, n \in \mathbb{N},\quad \varphi(n) = \varphi(n+1) = \varphi(n+2) = \varphi(n+3)
$$

where $\varphi$ is Euler's totient function.

### Plain Language

Are there four consecutive integers that all share the same value of Euler's
totient function? Pairs of consecutive integers with equal totient are common
(e.g. $\varphi(1)=\varphi(2)=1$, $\varphi(3)=\varphi(4)=2$), and triples are known
(the smallest is $n = 5186,\ 5187,\ 5188$ with $\varphi = 2592$). Whether a run of
**four** consecutive equal-totient integers exists is the open question here.

### Why This Matters

Runs of consecutive integers with equal totient probe the fine multiplicative
structure of $\varphi$. This sits in the family of Erdős totient problems
(parent: erdos-1003) concerning the distribution of totient values and coincidences
$\varphi(n) = \varphi(n+k)$. A formalization would either exhibit an explicit
witness (making the existence machine-checked) or record the search framework and
known bounds.

## Known Results

### What's Already Proven

- Consecutive pairs $\varphi(n)=\varphi(n+1)$ occur infinitely often (classical) — number theory literature.
- Explicit totient triples exist; smallest $n=5186$ — computational number theory.
- `Nat.totient` and its multiplicativity are available in Mathlib — `Mathlib.NumberTheory.Totient`.

### What's Still Open

- Existence of four (or more) consecutive integers with equal totient is not settled in general.
- No known infinite family of equal-totient quadruples.

### Our Goal

Formalize the statement and either (a) certify an explicit quadruple witness by
`decide`/kernel computation on `Nat.totient`, or (b) formalize the triple result
and the exact search obstruction, documenting assumptions honestly.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1003 | Parent problem on totient coincidences | totient identities |
| euler-totient-* gallery entries | `Nat.totient` API, multiplicativity | number theory |

## Initial Thoughts

### Potential Approaches

1. **Explicit witness search**: search for the least $n$ with a quadruple, then
   certify via kernel evaluation of `Nat.totient`.
   - Why it might work: totient is computable; a witness makes existence decidable.
   - Risk: the least witness may be large; kernel `decide` on large `Nat.totient` is costly. If `native_decide` is used, the entry is `axiomatized` (`Lean.ofReduceBool`).

2. **Structural / CRT construction**: build a quadruple by prescribing prime
   factorizations that force equal totient across four residues.
   - Why it might work: mirrors constructions for triples.
   - Risk: no known clean construction; may not exist.

### Key Difficulties

- No guaranteed witness; the quadruple may be genuinely rare or nonexistent under extra constraints.
- Large-integer totient evaluation in the kernel.

### What Would a Proof Need?

- Key lemma: efficient/certified evaluation of `Nat.totient` on the witness.
- Technical requirements: `Nat.totient` API, possibly `Nat.factorization`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- If an explicit quadruple exists and is not too large, a certified witness is direct.
- Similar totient-coincidence witnesses have been formalized for smaller runs.
- Mathlib provides `Nat.totient` and its multiplicativity.

**Estimated Effort**:
- Exploration: hours to locate/confirm a candidate witness.
- If tractable: days to certify.
- If hard: unknown (no witness / kernel blowup).

## References

### Papers
- Erdős, on totient coincidences and the distribution of totient values — background.

### Online Resources
- OEIS sequences on consecutive equal-totient runs — candidate witnesses.

### Mathlib
- `Mathlib.NumberTheory.Totient` — `Nat.totient` definition and lemmas.

## Metadata

```yaml
tags:
  - number-theory
  - euler-totient
  - erdos
related_proofs:
  - erdos-1003
difficulty: medium
source: proof-suggestion
created: 2026-07-02T16:50:31-07:00
```

**Significance**: 5/10
**Tractability**: 5/10
