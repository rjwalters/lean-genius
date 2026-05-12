# Current State

**Phase**: ACT (S2)
**Since**: 2026-05-12T12:30:00Z
**Iteration**: 2
**Last session**: S2 (researcher-9, 2026-05-12)

## Current Focus

S2 ACT: Route A (commutative quasideterminant `qdetF`) implemented over a
field. `proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean` created. The file
contains the uniform-in-n quotient definition, the multiplicative defining
identity, non-vanishing, and three specializations bridging back to
the parent 2×2 and 3×3 files.

## Active Approach

**Route A complete (S2)**: `qdetF (n+1)×(n+1)` over a field via
`A.det / (minor_{ij} A).det`. Three bridges proved:
- n=3 specialization: `qdetF_eq_qdet3` (by `rfl`).
- n=2 (0,0): `qdetF_eq_qdet00` (under `A 1 1 ≠ 0`).
- n=2 (1,1): `qdetF_eq_qdet11` (under `A 0 0 ≠ 0`).

**Route B (S3+ next)**: build the fully non-commutative `qdetN` via mutual
strong recursion with `qdetN_inv`. Plan unchanged from S1.

## Blockers

- **Mathlib has no `Matrix.quasideterminant`.** Route A is the first
  uniform-in-n Lean formalization.
- **Mutual recursion + invertibility witnesses (S3)**: Route B needs
  `WellFoundedRecursion` on `Σ n, Matrix (Fin n) (Fin n) D` carrying the
  `qdetN_inv` witnesses through the descent.

## Next Action

**S3 [NC-DEFINE]**: extend with a `*NC.lean` companion (or in the same file)
to add:

1. `qdetN : (n : ℕ) → Matrix (Fin n) (Fin n) D → Fin n → Fin n → D` over a
   division ring D, via strong recursion on n.
2. Mutually-recursive `qdetN_inv : Matrix (Fin n) (Fin n) D` (the
   homological-relations inverse).
3. Defer the recurrence theorem to S4.

Target ≤ 200 added lines; ≤ 2 sorries (preferably zero, accepting
`termination_by` annotations).

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Session-by-session

- **S1 (2026-05-12, researcher-12)**: OBSERVE. Formalized statement,
  surveyed Mathlib API, mapped 6-session plan (S2-S6). PR opened for
  problem.md + knowledge.md + state.md + JSON only.
- **S2 (2026-05-12, researcher-9)**: ACT. Route A implemented.
  `CramersRuleOQ01OQ02OQ01OQ01.lean` created (~175 lines) with:
  - 1 abbrev (`minorIJ`)
  - 1 def (`qdetF`)
  - 6 theorems (`qdetF_field_quotient`, `qdetF_ne_zero`,
    `qdetF_eq_qdet3`, `qdetF_eq_qdet00`, `qdetF_eq_qdet11`,
    `qdetF_summary`)
  - 2 supporting lemmas (`minorIJ_22_00_det`, `minorIJ_22_11_det`)
  - 0 sorries
  - Build status: docker build kicked off, build-pending precedent
    per PR #17990 / PR #17718.

## Done When

See `knowledge.md` "Done When" section.

- [x] **S2 (Route A)**: `qdetF` defined uniformly in n;
      `qdetF_field_quotient` proved; n=2/n=3 bridges proved.
- [ ] **S3 (Route B)**: `qdetN` defined inductively over a division ring.
- [ ] **S4**: `qdetN_recurrence` proved.
- [ ] **S5**: consistency `qdetN_eq_qdetF` over fields proved.
- [ ] **S6**: `cramer_rule_nxn_qdet` proved over division rings.
