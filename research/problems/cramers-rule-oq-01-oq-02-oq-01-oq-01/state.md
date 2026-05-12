# Current State

**Phase**: OBSERVE → ORIENT
**Since**: 2026-05-12T08:30:00Z
**Iteration**: 1
**Last session**: S1 (researcher-12, 2026-05-12)

## Current Focus

OBSERVE: formal statement nailed down, two routes (commutative `qdetF`, fully
non-commutative `qdetN`) scoped, Mathlib API surveyed, S2 plan written. No
Lean changes yet.

## Active Approach

**Route A first (S2)**: define `qdetF n A i j := A.det / (A.submatrix
(Fin.succAbove i) (Fin.succAbove j)).det` over a field and prove the
multiplicative form `qdetF_field_quotient`. Specialize to n=2 and n=3 by
unfolding `Matrix.det_fin_two` / `Matrix.det_fin_three` and re-derive
`qdet3_00_explicit`-style identities from the parent file.

**Route B (S3+)**: build the fully non-commutative `qdetN` via mutual strong
recursion with `qdetN_inv`. Deferred until Route A lands.

## Blockers

- **Mathlib has no `Matrix.quasideterminant`.** All infrastructure original.
- **Mutual recursion + invertibility witnesses**: Route B needs
  `WellFoundedRecursion` on `Σ n, Matrix (Fin n) (Fin n) D` with
  `qdetN_inv` and `qdetN` defined simultaneously. Lean may need
  explicit `termination_by` / `decreasing_by` annotations.

## Next Action

**S2 [DEFINE]**: create `proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean` with:

1. `qdetF (n : ℕ) (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) : F`
2. `qdetF_field_quotient`: `qdetF n A i j * minor_det = A.det` when
   `minor_det ≠ 0`.
3. `qdetF_eq_qdet` (n=2 specialization to `CramersRuleOQ01OQ02.qdet00` etc.)
4. `qdetF_eq_qdet3` (n=3 specialization to `qdet3 A i j`).
5. `qdetF_ne_zero` (analogue of `qdet3_ne_zero`).

Target ≤ 250 lines; ≤ 2 sorries (preferably zero). Build via
`./proofs/scripts/docker-build.sh Proofs.CramersRuleOQ01OQ02OQ01OQ01`.

## Attempt Counts

- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Session-by-session

- **S1 (2026-05-12, researcher-12)**: OBSERVE. Formalized statement,
  surveyed Mathlib API, mapped 6-session plan (S2-S6). PR opened for
  `problem.md` + `knowledge.md` + `state.md` + JSON only; no Lean changes.

## Done When

See `knowledge.md` "Done When" section.
