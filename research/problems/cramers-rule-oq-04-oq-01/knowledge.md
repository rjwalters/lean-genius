# Knowledge: cramers-rule-oq-04-oq-01 (algebraic Cayley-Hamilton via adjugate)

## Problem framing
Parent `CramersRuleOQ04.lean` proves constant-ring adjugate identities
(`A * adj A = det A • 1`, etc.). OQ-04-OQ-01 asks to lift these to the
characteristic matrix `xI − A` over `R[X]` and derive Cayley-Hamilton —
i.e. `adj(xI−A)·(xI−A) = charpoly(A)·I`, then substitute `A`.

## Insight 1 — The OQ's proof object IS Mathlib's Cayley-Hamilton proof
Mathlib defines `charpoly M := (charmatrix M).det` and proves
`aeval_self_charpoly` by exactly this adjugate-of-`charmatrix` route. So the OQ
is not asking for new mathematics; it asks the project to expose/wrap content
already upstream. Key bearers (master, 2026-06-14):
- `Matrix.charmatrix` (= `xI − A` over `R[X]`), `Matrix/Charpoly/Basic.lean:49`.
- `Matrix.charpoly := (charmatrix M).det`, same file :132.
- `Matrix.mul_adjugate` / `Matrix.adjugate_mul` (`Matrix/Adjugate.lean`).
- `Matrix.aeval_self_charpoly` (`Matrix/Charpoly/Coeff.lean`) — Cayley-Hamilton
  over arbitrary commutative rings. Also in `docs/100.yaml` (formalized).

## Insight 2 — The adjugate identity is ring-generic (why singular A is fine)
`A * adj A = det A • 1` holds over ANY commutative ring with NO invertibility
hypothesis — it is a polynomial identity in the entries (Mathlib: `mul_adjugate`).
That is precisely why the proof works for the singular characteristic matrix and
why Cayley-Hamilton needs no field assumption. The cert confirms this on a
det-0 matrix and over ℤ (non-field).

## Insight 3 — Numerical anchor (`verify_cayley_hamilton.py`, 14/14 PASS)
For explicit + seeded-random integer matrices (n=2..4) and a singular case:
(1) `charpoly = det(xI−A)`, (2) `adj(xI−A)(xI−A) = charpoly·I` (both sides),
(3) Cayley-Hamilton `Σ c_k A^k = 0`. Regression oracle for the Lean wrapper.

## Recommended wrapper (Docker-gated)
```
theorem cayley_hamilton (A : Matrix n n R) : aeval A A.charpoly = 0 :=
  Matrix.aeval_self_charpoly A
theorem charmatrix_adjugate_identity (A : Matrix n n R) :
    A.charmatrix * A.charmatrix.adjugate = A.charpoly • 1 := by
  rw [Matrix.mul_adjugate]   -- charpoly A = (charmatrix A).det by def
```

## Open threads
- Confirm exact defeq for the `• 1` step (`charpoly` vs `(charmatrix A).det`)
  once Docker is back — likely a single `rfl`/`Matrix.charpoly` unfold.

## Links
- Parent: [[cramers-rule-oq-04]] (adjugate generalized-inverse identities).
- Same make-ephemeral-verification-durable vein as the Matrix-Tree cert in
  [[project-researcher-3-20260614m-konigsberg-matrixtree-orient]].
