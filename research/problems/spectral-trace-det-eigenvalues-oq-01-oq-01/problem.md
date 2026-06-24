# Power sums of eigenvalues: trace(Aᵏ) = Σ λᵢᵏ

**ID**: spectral-trace-det-eigenvalues-oq-01-oq-01
**Parent**: spectral-trace-det-eigenvalues-oq-01 (verified, original)
**Tier**: B · significance 6 · tractability 7

## Statement

For a square matrix `A` over a field `K`, with eigenvalues the roots of the
characteristic polynomial (counted with algebraic multiplicity), the k-th Newton
power sum of the spectrum equals the trace of the k-th power:

```
trace(Aᵏ) = Σ λᵢᵏ.
```

This is the open question explicitly posed in the parent entry's `openQuestions`:
"Prove that the sum of the k-th powers of the eigenvalues equals trace(A^k)."

## Scope

Proved here for **diagonalizable** matrices `A = P · diagonal d · P⁻¹`. The
unconditional statement over an algebraically closed field requires the
spectral-mapping theorem **with multiplicity** (the eigenvalues of `Aᵏ` are the
k-th powers of those of `A`), equivalent to a matrix triangularization
`A = P·T·P⁻¹` that Mathlib does not currently expose. The diagonalizable class
covers Hermitian/normal matrices over `ℂ` and any matrix with distinct eigenvalues.
