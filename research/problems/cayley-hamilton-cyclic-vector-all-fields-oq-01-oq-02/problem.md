# Problem: Rational Canonical Form — Mathlib formalization connection

**Slug**: `cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02`
**Tier**: B
**Significance**: 6
**Tractability**: 5
**Parent**: `cayley-hamilton-cyclic-vector-all-fields-oq-01`

## The Question

Open question 3 from the parent entry (`cayley-hamilton-cyclic-vector-all-fields-oq-01.json`,
field `overview.openQuestions[2]`):

> **Mathlib's rational canonical form**: Is there a Mathlib formalization of the rational
> canonical form (RCF) that could simplify this proof further? The RCF directly gives a
> cyclic-vector decomposition for any matrix, and the nonderogatory case is a single-block
> special case. As of 2026, Mathlib has Smith normal form and the structure theorem for
> modules over PIDs but not the RCF specifically; integrating the two would be a useful
> Mathlib contribution.

## Operational Re-statement

The parent OQ asks whether RCF is in Mathlib. The answer (as of v4.26.0) is **no**: there is
no `Matrix.rationalCanonicalForm` typeclass, no `Matrix.companionMatrix` API, and no
similarity-to-companion theorem over a general field. There is `Matrix.SmithNormalForm`
for PIDs and the module structure theorem (`Module.IsTorsion.exists_isInternal`-style results),
but they have not been packaged into an RCF for matrices.

Given that, the operational question becomes: **what is the smallest stand-alone formalization
of the nonderogatory-case RCF — the statement that every nonderogatory matrix is similar to
its companion matrix — and can it be promoted toward a future Mathlib contribution?**

The nonderogatory case is the single-block special case of RCF: when `minpoly K M = charpoly M`,
the matrix is similar to one Frobenius block, namely the companion matrix of `minpoly K M`.

## Status — Session 1 (2026-05-08)

The Lean file `proofs/Proofs/CayleyHamiltonCyclicVectorAllFieldsOQ01OQ02.lean` already exists
on `origin/main` (added inadvertently as part of PR #16881, which was an audit-tracker PR
that side-effected several new Lean files). It was not registered in `proofs/Proofs.lean`,
had no gallery entry, and had no research scaffold. This session does the registration and
scaffolding; the file already proves the main result modulo one routine axiom.

**Existing content** (156 lines, 5 theorems, 2 definitions, 1 axiom, 0 sorries):

- `companionMx p : Matrix (Fin n) (Fin n) K` — the companion matrix of a polynomial
- `cyclicMatrix M v : Matrix (Fin n) (Fin n) K` — column j is M^j v (the Krylov matrix)
- `cyclicMatrix_injective`: `mulVec (cyclicMatrix M v)` is injective when `v` is cyclic
- `cyclicMatrix_isUnit`: cyclicMatrix is invertible (from injective mulVec)
- `M_mul_cyclicMatrix`: the conjugation identity `M · P = P · C(minpoly K M)`
- `nonderogatory_similar_to_companion`: the main theorem
- **Axiom**: `hMn_axiom` — `(M^n).mulVec v = -∑ k<n, c_k • (M^k).mulVec v` when
  `(minpoly K M).natDegree = n`. This is the Cayley-Hamilton-style relation:
  expanding `aeval M (minpoly K M) = 0` and isolating the `k = n` term using monicity.

## Session 1 Goals

1. Promote the existing file to a gallery entry (status: `axiomatized`, badge: `axiom`).
2. Register the file in `proofs/Proofs.lean` so it builds in CI.
3. Document the axiom-elimination roadmap (proof sketch, target Mathlib API, build risks).

## Why This Matters

- The nonderogatory RCF case is a clean stepping-stone toward a full Mathlib RCF contribution.
- It validates that the parent entry's `nonderogatory_has_cyclic_vector` is *constructive*:
  the cyclic vector built by primary decomposition gives an explicit similarity matrix.
- The conjugation identity `M · P = P · C(minpoly)` reveals the structural content of
  "nonderogatory = 1 RCF block" in coordinate terms.

## Pre-Work Assessment

- **Axiom Question**: 1 axiom (`hMn_axiom`), routinely provable from `minpoly.aeval` +
  `minpoly.monic` + `Polynomial.aeval_eq_sum_range`. Eliminate in next session.
- **Value Question**: YES — this is a concrete RCF result with a self-contained proof.
- **Proof Strategy**: Linear algebra + polynomial expansion. No infinite-case obstruction.
- **Build vs Block**: All required Mathlib API is in v4.26.0 (`minpoly`, `Polynomial`,
  `Matrix.mulVec`). The file already imports the ambient `Mathlib`.

**Decision**: SCAFFOLD this session; AXIOM HUNT next session.
