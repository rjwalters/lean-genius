# S4 — Vector-level Layer 2 corollary (researcher-1, 2026-05-30)

## Goal

Promote S3's matrix-level Layer 2 bridge `M^j = ∏ T_i` (over set bits of `j`)
to a vector-level form, expressing every Krylov vector `M^j · v` as the
matrix-vector image of a single squared-Krylov product matrix applied to
`v`. This is the operationally accurate restatement of the Keller-Gehrig
output: each Krylov vector is reached by `popcount(j)` matrix
multiplications building the squared-Krylov product, plus one matrix-vector
solve.

## Scope

Single small extension to `proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ02.lean`
adding 2 theorems (~22 LOC including docstrings, none with sorries):

| # | Theorem | Statement | Proof |
|---|---|---|---|
| 1 | `squareKrylovProd_mulVec` | `(squareKrylovProd M j).mulVec v = (M ^ j).mulVec v` | `rw [squareKrylovProd_eq_pow]` |
| 2 | `krylov_in_squareKrylov_range` | `∃ w, (squareKrylovProd M j).mulVec w = (M ^ j).mulVec v` | `⟨v, squareKrylovProd_mulVec M v j⟩` |

Both proofs are trivial corollaries of the S3 main bridge — vector form is
applying `mulVec` to both sides of the matrix-level identity.

## File delta

`proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ02.lean` 200 → ~228 LOC:
- New section header `-- Layer 2 vector form: Krylov vectors via squared-Krylov`
- 2 new theorems with docstrings
- Trailing Summary block updated: "9 theorems (3 Layer 1 + 4 Layer 2
  matrix-level + 2 Layer 2 vector-level)"

## Build verification

Docker build of `Proofs.CayleyHamiltonMinpolyOQ03OQ02` under recovered
INFRA (Docker 29.4.1, disk 57 Gi). Mathlib pin `2df2f0150c…` stable.

Result: **PASS** — 3062 jobs built clean in 7.7s of compile time on
fresh Mathlib cache. 0 errors. Log: `.loom/logs/build-researcher-1-cayley-s4.log`.

```
✔ [3062/3062] Built Proofs.CayleyHamiltonMinpolyOQ03OQ02 (7.7s)
Build completed successfully (3062 jobs).
=== Build succeeded ===
```

## Why this S4 stops here

The state.md S4 plan listed two follow-ups:
1. **Krylov-vector bound + matvec count** — partial in this S4 via
   `squareKrylovProd_mulVec`; explicit "popcount(j) ≤ log₂(n) + 1" bound
   deferred to S5 (needs `Nat.bitIndices` length lemmas; out of scope here).
2. **Operation-count axiomatized placeholder** — deferred to S5 per S3's
   explicit "Layer 3 is Mathlib-blocked" doctrine.

S4 ships the cleanest vector-level corollary that is a 1-line proof from
S3's main bridge. S5 can extend with the matvec-count bound or the
axiomatized complexity statement (per S3 §state nextAction).

## Out of scope

- Layer 3 quantitative complexity (Mathlib-blocked).
- Operation-count axiomatic placeholder (defer to S5).
- popcount/bitIndices length bound (needs Mathlib `Nat.bitIndices` API
  exploration; deferred).
- Span-style linear-algebraic restatement (covered partially by the range
  existential `krylov_in_squareKrylov_range`).

## Next action — S5 candidates

(a) Add `bitIndices_length_le_log` style bound and a `keller_gehrig_matmul_count`
    theorem giving an explicit matrix-multiplication count.

(b) Axiomatize Layer 3: `axiom omegaMM : ℝ` + `axiom omegaMM_bounds : 2 ≤ omegaMM ∧ omegaMM < 3`
    + `theorem keller_gehrig_op_count : ... := by sorry` with explicit
    "Mathlib gap" comment. Document `meta.status = axiomatized` in gallery
    promotion.

(c) Open a gallery entry. `meta.status = axiomatized` with formal claim
    covering Layers 1 + 2 (verified) + Layer 3 (assumption).
