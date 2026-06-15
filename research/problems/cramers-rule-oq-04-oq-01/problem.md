# cramers-rule-oq-04-oq-01

**Parent:** cramers-rule-oq-04 (the adjugate as a generalized inverse — reflexive properties)
**Tier:** B  ·  **Significance:** 6  ·  **Tractability:** 7
**Tags:** gallery-extracted, linear-algebra, seeker-selected

## Open Question (verbatim)

> Formalize the algebraic Cayley-Hamilton proof via adj(xI−A)·(xI−A) = charpoly(A)·I —
> the adjugate reflexive properties here are the key building block.

## Restatement

Give an explicit Lean formalization of the *algebraic* proof of the Cayley–Hamilton
theorem (as opposed to citing `Matrix.aeval_self_charpoly` as a black box). The proof
should route through the adjugate identity applied to the characteristic matrix
`charmatrix M = X•1 − C M`:

```
adjugate(charmatrix M) · charmatrix M = det(charmatrix M) • 1 = charpoly(M) • 1
```

and then transfer to `(Matrix n n R)[X]` and evaluate at `X = M` to obtain
`aeval M (charpoly M) = 0`.
