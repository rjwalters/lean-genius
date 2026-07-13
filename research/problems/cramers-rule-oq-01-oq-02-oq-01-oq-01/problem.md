# Problem: Inductive n×n Quasideterminant Theory over Division Rings

## Statement

### Plain Language
Extend the 2×2 (`CramersRuleOQ01OQ02`) and 3×3 (`CramersRuleOQ01OQ02OQ01`)
Gelfand–Retakh quasideterminant theory to general n×n matrices over a division
ring D, with the recursive Schur-complement definition. Specifically, give a
Lean 4 inductive (or strong-recursion) definition

  `qdetN : (n : ℕ) → Matrix (Fin n) (Fin n) D → Fin n → Fin n → D`

satisfying `qdetN 1 A 0 0 = A 0 0`, the 2×2 Schur formula at `n = 2`, the 3×3
Schur formula at `n = 3`, and the recursive identity

  `qdetN (k+1) A i j  =  A i j  −  rowᵢⱼ(A) · invᵢⱼ(A) · colᵢⱼ(A)`

where `invᵢⱼ(A) : Matrix (Fin k) (Fin k) D` is the (componentwise) inverse of
the complementary submatrix
`A^{ij} := A.submatrix (Fin.succAbove i) (Fin.succAbove j)`,
expressed via lower-order quasideterminants by Gelfand–Retakh's
"homological relations." Establish the commutative reduction

  `qdetN n A i j  =  A.det / (A.submatrix (Fin.succAbove i) (Fin.succAbove j)).det`

when D is a field, recovering Cramer's rule for n×n.

### Formal Statement

Let D be a division ring. Define `qdetN n A i j : D` by strong induction on n:

- Base `n = 1`: `qdetN 1 A 0 0 = A 0 0`.
- Step `n = k + 1`: let `M = A.submatrix (Fin.succAbove i) (Fin.succAbove j)`,
  let `Minv : Fin k → Fin k → D` be the matrix of inverse entries expressed via
  `qdetN k M`, and define
  `qdetN (k+1) A i j = A i j − ∑_{p,q} A i (Fin.succAbove j q) · Minv q p
                                       · A (Fin.succAbove i p) j`.

The **main theorem** (`qdetN_recurrence`) is the Schur-complement recurrence:

  `qdetN (k+1) A i j = A i j − row · Minv · col`

with `Fin.succAbove`-indexed row/col vectors above. The **commutative reduction**
(`qdetN_field_quotient`) over a field F asserts

  `qdetN n A i j * M.det = A.det`  whenever `M.det ≠ 0`.

## Classification

```yaml
tier: B
significance: 6
tractability: 4
tags:
  - linear-algebra
  - matrices
  - non-commutative
  - division-rings
  - quasideterminants
  - cramer
  - schur-complement
  - recursion
  - induction
  - seeker-selected
  - gallery-extracted
```

**Significance**: 6/10 — gives a uniform-in-n analogue of Cramer's rule over
division rings; closes the explicit-formula 2×2 + 3×3 results from
`CramersRuleOQ01OQ02` / `CramersRuleOQ01OQ02OQ01`.

**Tractability**: 4/10 — the definition is mutually recursive (`qdetN k` for the
inverse entries appearing inside `qdetN (k+1)`), so termination must be
discharged on `Fin n` with strong recursion plus a non-vanishing-minor
hypothesis. The commutative reduction is routine given
`Matrix.det_succ_column` / `Matrix.adjugate`, but the non-commutative
recurrence requires the Gelfand–Retakh homological relations, which are
**not** in Mathlib.

## Why This Matters

1. **Generalization beyond explicit small-n calculations.** The 2×2 and 3×3
   files give complete explicit formulas, but the *recursive principle*
   (Gelfand–Retakh 1991) only becomes a theorem at general n. This slug closes
   the open question "does the recursion hold for all n?" inside our gallery.
2. **Cramer's rule over division rings.** Once `qdetN_field_quotient` is in
   place, the n×n Cramer identity `A · (A.det⁻¹ • A.cramer b) = b` lifts to
   division rings via `qdetN`-coefficients, generalizing
   `CramersRuleOQ01OQ02.cramer_rule_qdet`.
3. **Foundation for further follow-ups.** `OQ01OQ02OQ01` already states the
   3×3 result and explicitly references the n×n inductive principle (lines
   29–36 of `CramersRuleOQ01OQ02OQ01.lean`); this slug is the natural next step.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `CramersRule` | Commutative n×n Cramer's rule baseline (`A.cramer`, `A.det`). |
| `CramersRuleOQ01` | Cayley–Hamilton from Cramer (uses n×n Cramer machinery). |
| `CramersRuleOQ01OQ02` | Full 2×2 quasideterminant theory (4 qdets, Schur). |
| `CramersRuleOQ01OQ02OQ01` | Full 3×3 qdet theory + Schur recurrence (parent). |
| `CramersRuleOQ02` | Non-commutative 2×2 inverse via adjugate. |
| `CramersRuleOQ03` | Original 2×2 non-commutative Cramer's rule (qdet00 only). |

## References

- Gelfand, I. M.; Retakh, V. S. *Determinants of matrices over noncommutative
  rings.* Funct. Anal. Appl. 25 (1991), 91–102.
- Gelfand, I.; Gelfand, S.; Retakh, V.; Wilson, R. L. *Quasideterminants.*
  Adv. Math. 193 (2005), 56–141.
- Mathlib: `Mathlib.LinearAlgebra.Matrix.NonsingularInverse` (general n×n
  inverse via adjugate / det), `Mathlib.LinearAlgebra.Matrix.Adjugate`,
  `Mathlib.Data.Matrix.Block` (block matrices, Schur-complement-style
  decomposition via `Matrix.fromBlocks`).
