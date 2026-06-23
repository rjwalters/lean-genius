# Current State

**Phase**: ORIENT
**Since**: 2026-06-14 (S1, researcher-3)
**Iteration**: 1
**Last Updated**: 2026-06-14 (researcher-3, **S1 ORIENT** — Mathlib bearer survey + sympy Cayley-Hamilton cert)

## Problem

**OQ-04-OQ-01**: Formalize the algebraic Cayley-Hamilton proof via
`adj(xI − A) · (xI − A) = charpoly(A) · I` — the adjugate reflexive property of
the *characteristic matrix* — extending the parent file's static adjugate
identities (`proofs/Proofs/CramersRuleOQ04.lean`) to the polynomial-matrix
setting.

Parent `CramersRuleOQ04.lean` already proves the constant-ring adjugate
identities (`adjugate_right` = `mul_adjugate`, `adjugate_left` = `adjugate_mul`,
reflexive forms). OQ-04-OQ-01 asks to lift these to `R[X]` matrices and conclude
Cayley-Hamilton.

## S1 ORIENT verdict (build-free; Docker down)

**ANSWER: Yes — and the exact proof object is ALREADY in Mathlib. This is a
~10-40 LOC wrapper, NOT new mathematics.**

### Mathlib bearers PRESENT (master, surveyed 2026-06-14)
All in `Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean` unless noted:
- `Matrix.charmatrix M` — the characteristic matrix `xI − A` over `R[X]`
  (def L49: `charmatrix M := scalar n X - (C.mapMatrix) M`).
- `Matrix.charpoly M := (charmatrix M).det` (def L132) — literally `det(xI − A)`,
  the OQ's identity (1).
- `Matrix.adjugate`, `Matrix.mul_adjugate`, `Matrix.adjugate_mul`
  (`Mathlib/LinearAlgebra/Matrix/Adjugate.lean`) — applied to `charmatrix M`
  these give the OQ's identity (2):
  `charmatrix M * adjugate (charmatrix M) = charpoly M • 1` and the left form.
- `Matrix.aeval_self_charpoly` (Cayley-Hamilton, `Charpoly/Coeff.lean`) —
  `aeval M (charpoly M) = 0`, proved over arbitrary commutative rings
  (Basic.lean L17 docstring). Tracked as formalized in `docs/100.yaml`
  (Freek's 100 #wiedijk Cayley-Hamilton).

### Nothing ABSENT
The whole route — characteristic matrix, its determinant as the charpoly, the
adjugate identity over `R[X]`, and the final aeval=0 — is upstream. No
Cauchy-Binet-style gap, no missing infrastructure.

### Numerical cert (durable, `verify_cayley_hamilton.py`, sympy)
14/14 cases PASS over ℤ (a commutative ring that is not a field, matching the
ring-generic Mathlib statement), incl. a singular matrix (det 0) where the
adjugate identity still holds. Checks all three facts the wrapper rests on:
(1) `charpoly = det(xI−A)`, (2) `adj(xI−A)(xI−A) = charpoly·I` both sides,
(3) Cayley-Hamilton `p(A)=0`.

## Recommended ACT (Docker-gated, single cycle)
Add to `CramersRuleOQ04.lean` (keeps the file's "0 axioms, 0 sorries" status):
```
theorem charmatrix_adjugate_identity (A : Matrix n n R) :
    A.charmatrix * (A.charmatrix).adjugate = A.charpoly • (1 : Matrix n n R[X]) := by
  rw [Matrix.mul_adjugate]; rfl   -- det (charmatrix A) = charpoly A by def
theorem cayley_hamilton (A : Matrix n n R) :
    aeval A A.charpoly = 0 := Matrix.aeval_self_charpoly A
```
Expect minor name/defeq adjustments (`charpoly` is `(charmatrix A).det` by def,
so the `• 1` step is `mul_adjugate` + unfolding). Build-gated only for the
`rfl`/`simp` bookkeeping; the math is certified above.

## Next action
ACT is Docker-gated transcription of the two-line wrapper. Until then the cert +
bearer table are the durable surface. If the project prefers, this OQ can be
marked effectively-resolved-upstream (the substantive content is `aeval_self_charpoly`).
