# Knowledge Base: bezout-identity-oq-04-oq-01-oq-03

Decide whether the two Smith-Normal-Form axioms of the parent entry
`bezout-identity-oq-04-oq-01` (Linear Diophantine Systems via SNF) can be eliminated
using Mathlib.

## Status: COMPLETED — survey + one axiom derived away (2 → 1).

---

## Problem Understanding

The parent `bezout-identity-oq-04-oq-01` carries two `axiom` declarations:
- `snf_exists`: every integer matrix `A` admits `A = U·D·V` with `U`, `V` unimodular and
  `D` diagonal (the invariant-factor / Smith Normal Form).
- `snf_solvability_criterion`: `A·x = b` solvable over `ℤ` iff a divisibility condition
  holds on a transformed right-hand side.

The open question: does Mathlib already provide the machinery to turn these into theorems?

---

## Insights

**Axiom 1 — `snf_exists`: NOT available in Mathlib in matrix form.**
Mathlib has only the *module-theoretic* SNF: `Module.Basis.SmithNormalForm` /
`Submodule.smithNormalForm` (`Mathlib/LinearAlgebra/FreeModule/PID.lean`) — bases of `M`
and `N ≤ M` over a PID plus a divisibility chain of scalars `a i`. There is **no**
`Matrix.smithNormalForm` producing `D = U·A·V` with explicit unimodular integer matrices.
Discharging `snf_exists` requires a matrix↔module bridge (realize the matrix as
`ℤⁿ → ℤᵐ`, apply `Submodule.smithNormalForm` to its image, reconstruct unimodular
change-of-basis *matrices*). Substantial; left in place this session.

**Axiom 2 — `snf_solvability_criterion`: DERIVED, 0 axioms.**
From the decomposition `A = U·D·V` alone, the criterion is a theorem
(`proofs/Proofs/BezoutIdentityOQ04OQ01OQ03.lean`):
`∃x, A·x=b ↔ ∀i, dEntry D i ∣ (U⁻¹·b) i` (`diophantine_solvable_iff`), and the same in the
parent's two-pronged shape (`diophantine_solvable_iff_branches`). The reduction strips `U`
(`nonsing_inv_mul`, valid over `ℤ` as `det = ±1` is a unit), strips `V` by the bijection
`y = V·x`, and solves the diagonal system (`diag_solvable_iff`). **The parent's honest
axiom count can drop 2 → 1.**

**Convention correction.** With the convention `A = U·D·V` the transformed RHS is the
genuine inverse `U⁻¹·b`. The parent axiom writes `snf.U·b`, which is the `U⁻¹` of this
convention — a bookkeeping inconsistency the derivation surfaces.

**Over ℤ:** the two-pronged branch `(d≠0→d∣c) ∧ (d=0→c=0)` is literally `d∣c`, since
`0∣c ↔ c=0` (`int_dvd_iff_branches`).

---

## Files
- `proofs/Proofs/BezoutIdentityOQ04OQ01OQ03.lean` (new; verified, 0-axiom, 6 thm/1 def, 201 L)
- `src/data/proofs/bezout-identity-oq-04-oq-01-oq-03/{meta.json,annotations.json,index.ts}` (new)
- `src/data/research/problems/bezout-identity-oq-04-oq-01-oq-03.json` (updated)

---

## Dead Ends / Out of Scope

- Did NOT attempt the full matrix↔module bridge for `snf_exists` — it is the genuine
  ~hundreds-of-lines gap and out of scope for a single session.

---

## Next Steps
1. Optionally update parent `bezout-identity-oq-04-oq-01` to import
   `diophantine_solvable_iff` and retire `snf_solvability_criterion` (axiom 2→1), fixing the
   `U·b → U⁻¹·b` convention.
2. Remaining open question: close `snf_exists` via the bridge to `Submodule.smithNormalForm`.
