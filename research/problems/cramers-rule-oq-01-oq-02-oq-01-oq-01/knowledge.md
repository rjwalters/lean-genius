# Knowledge: cramers-rule-oq-01-oq-02-oq-01-oq-01

## Prior Sessions

| Session | Phase | Outcome |
|---------|-------|---------|
| S1 (this) | OBSERVE | Survey + formalization plan; no Lean changes |

## Prior Cumulative State (parent files)

**Already proved**:

- `CramersRule.lean` — n×n commutative Cramer (`A · (A.det⁻¹ • A.cramer b) = b`)
  via Mathlib's `Matrix.mulVec_cramer` and `Matrix.cramer`.
- `CramersRuleOQ01OQ02.lean` (463 lines) — full 2×2 theory: `qdet00`, `qdet01`,
  `qdet10`, `qdet11`; Schur complement formula; commutative reduction
  `qdet_ij = det / minor_ij`; Cramer for non-commutative 2×2.
- `CramersRuleOQ01OQ02OQ01.lean` (314 lines) — full 3×3 theory: 9 `qdet3 A i j`
  via `det A / det (block3 A i j)`; non-commutative `qdet3_00_nc` via Schur
  complement of `block3 A 0 0`; Cramer for non-commutative 3×3.
  Summary theorem `qdet3_recurrence_summary` ties the three together.

**Recursive principle stated but not formalized**: `CramersRuleOQ01OQ02OQ01.lean`
lines 29–36 spell out

```
n=1: |A|₀₀ = a₀₀
n=2: |A|₀₀ = a₀₀ - a₀₁·(a₁₁)⁻¹·a₁₀                            [OQ01OQ02]
n=3: |A|₀₀ = a₀₀ - [a₀₁,a₀₂]·(M^{00})⁻¹·[a₁₀;a₂₀]              [OQ01OQ02OQ01]
n=k: |A|₀₀ = a₀₀ - row₀\{0} · (A^{00})⁻¹ · col₀\{0}            [THIS SLUG]
```

with the inverse `(A^{00})⁻¹` itself expressed via `(n-2)×(n-2)`
quasideterminants (mutual recursion).

## Open Question (this slug)

Define `qdetN : (n : ℕ) → Matrix (Fin n) (Fin n) D → Fin n → Fin n → D` for a
division ring D, satisfying:

1. **Base.** `qdetN 1 A 0 0 = A 0 0`.
2. **Recurrence.** For `k ≥ 1` and `M = A.submatrix (Fin.succAbove i)
   (Fin.succAbove j)`,
   `qdetN (k+1) A i j = A i j − ∑_{p,q : Fin k}  A i (Fin.succAbove j q) ·
                                                  Minv q p ·
                                                  A (Fin.succAbove i p) j`
   where `Minv q p` is the `(q,p)`-entry of `M⁻¹`, itself expressible via
   `qdetN k M`.
3. **Specializations.** `qdetN 2 = CramersRuleOQ01OQ02.qdetIJ` (modulo
   index translation) and `qdetN 3 0 0 = CramersRuleOQ01OQ02OQ01.qdet3_00_nc`.
4. **Field reduction.** Over a field F:
   `qdetN n A i j * (A.submatrix (Fin.succAbove i) (Fin.succAbove j)).det
                  = A.det`
   whenever the minor is invertible (equivalently
   `qdetN n A i j = A.det / minor_det` when `minor_det ≠ 0`).

## Proof Strategy

### Definition (two viable routes)

**Route A — field-only first.** Define `qdetF : (n : ℕ) → Matrix (Fin n)
(Fin n) F → Fin n → Fin n → F` over a field by
`qdetF n A i j := A.det / (A.submatrix (Fin.succAbove i) (Fin.succAbove j)).det`.
The recurrence is then a theorem (proved via cofactor expansion on column `j`
plus `Matrix.det_succ_column_zero` / `Matrix.adjugate`). This avoids
mutual recursion and is the cleanest first iteration. It already generalizes
`qdet3` from the 3×3 file uniformly in n.

**Route B — division-ring inductive definition.** Use strong recursion on n
plus the inductive hypothesis that the complementary `(n)×(n)` submatrix is
invertible (its inverse expressible via lower-order quasideterminants). The
inverse can be assembled from `qdetN n` entries via the Gelfand–Retakh
"homological relations": `(A⁻¹)ⱼᵢ = (qdetN n A i j)⁻¹` (in the (i,j)-pivoted
form, where defined). This is the canonical Gelfand–Retakh framework and the
target of the slug, but it requires:
- A `qdetN_ne_zero` hypothesis chained through the recursion.
- A `WellFoundedRecursion` setup on `n` with the inductive hypothesis carrying
  invertibility witnesses.
- Mathlib has no analogue, so all infrastructure is original.

### Recommended split

- **S2 (DEFINE)**: implement **Route A** (`qdetF`) as the canonical commutative
  definition; prove `qdetF_field_quotient` (the multiplicative version of the
  defining identity), `qdetF_recurrence` (cofactor-expansion form), and the
  specializations to `qdet` (2×2) and `qdet3` (3×3) by unfolding
  `Matrix.det_fin_two` / `Matrix.det_fin_three`.
- **S3 (NC-DEFINE)**: implement **Route B** (`qdetN`) via strong recursion;
  define `qdetN_inv : Matrix (Fin n) (Fin n) D` (the homological-relations
  inverse) **simultaneously** with `qdetN` by mutual recursion on n.
- **S4 (RECURRENCE)**: prove `qdetN_recurrence` — the Schur identity at
  every n.
- **S5 (NC-FIELD)**: prove `qdetN_eq_qdetF` (consistency between Route A and
  Route B over a field), recovering `qdet3_00_nc_eq_qdet3` as the n=3 case.
- **S6 (CRAMER)**: prove the n×n Cramer identity over a division ring from
  the recurrence.

This sequencing means S2 alone already closes the **commutative** half of the
open question, which is itself a substantive contribution: an explicit
uniform-in-n quasideterminant definition over fields.

## Mathlib API Survey

Useful for Route A (S2):

- `Matrix.det_succ_column_zero` / `Matrix.det_succ_row` / `Matrix.det_succ_column`
  — cofactor expansion along a row or column of a `(n+1)×(n+1)` matrix.
- `Matrix.adjugate_def`, `Matrix.adjugate_mul`,
  `Matrix.mul_adjugate_eq_det` — adjugate satisfies `A · adj A = det A • 1`.
- `Matrix.det_submatrix_succAbove_succAbove` /
  `Matrix.det_fin_succ_above` (`Fin.succAbove`-indexed minors are exactly the
  cofactor minors, with sign `(-1)^(i+j)`).
- `Matrix.det_fin_two`, `Matrix.det_fin_three` — for the n=2, n=3
  specializations.
- `Matrix.nonsingInv` and `Matrix.inv_def` —
  `A⁻¹ = (1 / det A) • adjugate A` for `A : Matrix (Fin n) (Fin n) F`.

Useful for Route B (S3):

- `Matrix.fromBlocks`, `Matrix.fromBlocks_inv` — block-matrix inversion in
  `Mathlib.Data.Matrix.Block`. Realizes the Schur complement at n+1 via
  splitting off `Fin 1` (or `Fin n_l ⊕ Fin n_r`).
- `Fin.succAboveCases`, `Fin.cons` — index splitting that mirrors the
  "delete row i, column j" construction.
- `Matrix.submatrix_apply` and `Fin.succAbove_succAbove_` — for translating
  between `Matrix (Fin (n+1)) (Fin (n+1))` indexing and `Matrix (Fin n)
  (Fin n)`.

Mathlib gaps:

- **No `Matrix.quasideterminant`.** Mathlib has no entry for Gelfand–Retakh
  quasideterminants at any n. This file would be the first.
- **No homological-relations inverse for division rings.** Mathlib's
  `Matrix.nonsingInv` is field-only (uses `det`). The non-commutative
  formulation must be written from scratch.

## Risks / Subtleties

1. **Termination.** `qdetN` calls `qdetN` on submatrices of strictly smaller
   size. Lean's structural recursion does not see this (the recursive call is
   not on the original `A` but on `A.submatrix _ _`). We need either
   `decreasing_by simp_wf; omega` on `n` (Route B with explicit `n`-recursion)
   or a `WellFoundedRecursion` on `Σ n, Matrix (Fin n) (Fin n) D` ordered by
   the first projection.
2. **Mutual recursion with the inverse.** If `qdetN_inv` is defined via
   `qdetN`, but `qdetN` is defined via `qdetN_inv` of the submatrix, the
   recursion is mutual but the *size* still decreases — Lean accepts this if
   structured as `qdetN (n+1)` calling `qdetN_inv n` which calls `qdetN n`.
3. **Non-vanishing minors.** The Schur recurrence requires the minor to be
   invertible. We carry this as an explicit hypothesis at each step (mirrors
   `qdet3_mul_minor_eq_det _ _ _ h` in the parent).
4. **Sign conventions.** Gelfand–Retakh's papers use `det / minor` (no sign);
   Mathlib's `adjugate` uses `(-1)^(i+j) * minor`. The 3×3 parent file
   matches the Gelfand–Retakh convention (no sign); our `qdetF` must agree.
   Verify with `qdet3_00_explicit`: `qdet3 A 0 0 = A.det / (block3 A 0 0).det`
   = `A.det / (A 1 1 * A 2 2 - A 1 2 * A 2 1)` with the second `Fin.succAbove`
   pattern giving no extra sign at `i = j = 0`. ✓

## Next Steps (priority order)

1. **S2 [DEFINE]** Write `Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean`. Open with
   `qdetF n A i j := A.det / (A.submatrix (Fin.succAbove i) (Fin.succAbove j)).det`
   over a field. Prove `qdetF_field_quotient`, specialize to n=2 and n=3.
   Target ≤ 250 lines; ≤ 2 sorries.
2. **S3 [NC-DEFINE]** Add `qdetN` over a division ring via mutual
   strong recursion with `qdetN_inv`. Defer the recurrence theorem to S4.
3. **S4 [NC-RECURRENCE]** Prove `qdetN_recurrence`.
4. **S5 [CONSISTENCY]** Prove `qdetN n A i j = qdetF n A i j` over a field.
5. **S6 [CRAMER]** State and prove `cramer_rule_nxn_qdet`.

## Done When

- `qdetF` defined uniformly in n; `qdetF_field_quotient` proved.
- `qdetN` defined inductively; `qdetN_recurrence` proved.
- Consistency `qdetN_eq_qdetF` over fields proved.
- `cramer_rule_nxn_qdet` proved over division rings.
- All four `axiomCount = 0`; ≤ a small number of clearly-flagged technical
  `sorry`s (e.g. only termination annotations if structural recursion balks).
