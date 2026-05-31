# Knowledge Base: `bezout-identity-oq-04-oq-01-incomplete-01`

Insights accumulated during research on this problem.

---

## Problem Understanding (recovered S2 ORIENT 2026-05-31, researcher-1)

* **Originating slug** was a 2026-04-03 scaffold with placeholder
  problem statement. Lineage recovered via a parent-file survey:
  `proofs/Proofs/BezoutIdentityOQ04OQ01.lean` declares two axioms
  (`snf_exists` at line 146, `snf_solvability_criterion` at line 196);
  the `incomplete-01` suffix refers to the first of these.
* **Scope of this slug**: discharge `axiom snf_exists` with a
  constructive Lean 4 proof. See `problem.md` for the full statement.
* **Out of scope**: `snf_solvability_criterion` (separate slug
  potential); upstream Mathlib promotion (post-discharge follow-up).

## Parent file inventory

| Symbol | Lean line | Status | Notes |
|---|---|---|---|
| `IsUnimodular` | 49 | definition | `det = 1 ∨ det = -1` over ℤ |
| `isUnimodular_iff_abs_det` | 53 | proved | `↔ Int.natAbs det = 1` |
| `isUnimodular_one` | 64 | proved | identity is unimodular |
| `IsUnimodular.mul` | 69 | proved | closure under product |
| `IsUnimodular.transpose` | 78 | proved | closure under transpose |
| `IsUnimodular.det_ne_zero` | 86 | proved | unimodular → nonzero det |
| `SmithNormalForm` | 103 | structure | `U, D, V` + invariants |
| `SmithNormalForm.isDecompOf` | 122 | definition | `A = U · D · V` |
| **`snf_exists`** | **146** | **axiom** | **target of this slug** |
| `snf_exists_zero` | 153 | proved | zero matrix base case, ~14 LOC |
| `SmithNormalForm.invariantFactor` | 173 | definition | k-th diagonal entry |
| `SmithNormalForm.rank` | 182 | definition | `# nonzero invariant factors` |
| `snf_solvability_criterion` | 196 | axiom | out of scope this slug |
| `bezout_from_snf` | (later) | proved | classical 1×2 reduction |

## Mathlib status (v4.26.0, lake-manifest pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

* **Available**: `Matrix.IsDiag`, `Matrix.det_one`, `Matrix.det_mul`,
  `Matrix.transpose`, `Int.gcd_eq_gcd_ab`, `Int.gcd_dvd_left`,
  `Int.gcd_dvd_right`, `Matrix.mulVec` + linearity lemmas
  (`mulVec_add`, `mulVec_sub`, `mulVec_smul`).
* **Available (PID structure side)**: `Module.equiv_directSum_of_pid`
  (or similar — needs verification at v4.26.0); various
  `Submodule.IsPrincipal` infrastructure; `EuclideanDomain` typeclass.
* **Not available**: `Matrix.SmithNormalForm`, `Matrix.snf_exists`,
  `Matrix.invariantFactors`, `Matrix.elementaryRowOps` as a unified
  API. Per the parent file's `mathlibDependencies` list (no
  `SmithNormalForm` entry).
* **Possibly available** (needs S3 PREP confirmation): row/column
  swap operations, scalar row addition operations packaged as
  unimodular-matrix-multiplication.

## Algorithm sketch (Newman 1972, ch. 2)

1. **Pivot selection**: find `(i, j)` such that `|A[i,j]|` is minimal
   among nonzero entries.
2. **Pivot move**: swap row 0 with row i (left-multiply by a permutation
   matrix, unimodular); swap column 0 with column j (right-multiply).
3. **Row reduction**: for each `i' > 0`, write `A[i',0] = q · A[0,0] + r`
   with `0 ≤ r < |A[0,0]|` via Euclidean division. If `r ≠ 0`, this
   introduces a smaller entry in column 0 — start over (restart from step 1).
   Otherwise, subtract `q · row 0` from `row i'` (left-multiply by
   `I - q · e_{i',0}^T`, unimodular).
4. **Column reduction**: symmetric to step 3 on columns.
5. **Divisibility-chain check**: if any entry in the `(1..,1..)` submatrix
   is not divisible by `A[0,0]`, add that row to row 0 and restart from
   step 1.
6. **Recurse**: once row 0 and column 0 (except `(0,0)`) are zero and
   `(0,0)` divides every entry of the `(1..,1..)` submatrix, recurse on
   the submatrix.

**Termination measure**: `|A[0,0]|` (a positive natural number) strictly
decreases on each restart of step 1 from step 3 or step 5. When neither
restart triggers, recurse on the smaller submatrix (proper structural
recursion).

---

## Insights

* **Insight 1 (S2 ORIENT)**: Mathlib has *no* direct SNF API at v4.26.0,
  so this slug is genuinely original Lean 4 content (modulo the Approach
  B "PID structure theorem" bridge possibility).
* **Insight 2 (S2 ORIENT)**: The parent file's existing
  `snf_exists_zero` (lines 153–167, ~14 LOC, fully constructive) serves
  as both a sanity check on the `SmithNormalForm` structure and a
  template for the recursive base case (when `m = 0` or `n = 0`).
* **Insight 3 (S2 ORIENT)**: The parent file already declares
  `IsUnimodular`, `IsUnimodular.mul`, `IsUnimodular.transpose` —
  enough infrastructure to manipulate elementary row/column operations
  as unimodular-matrix multiplications. This reduces the
  "elementary-ops API" budget materially.

---

## Dead Ends

* **Dead end 1 (S2 ORIENT, hypothesised)**: relying on an imminent
  upstream Mathlib SNF PR is not viable — `grep -rn "SmithNormalForm"`
  on Mathlib v4.26.0's tagged release yields no top-level definition.
  Approach C is a non-starter today.

---

## Open Questions for Future Iterations

* **S3 PREP question**: does Approach B's `Module.equiv_directSum_of_pid`
  bridge actually reduce LOC versus Approach A? Concrete LOC estimate
  needed before committing.
* **S3 PREP question**: which Mathlib elementary-row-ops are already
  available (e.g., `Matrix.swap_rows`, `Matrix.updateRow`,
  `Equiv.Perm.permMatrix` for permutation matrices)? Need a grep
  inventory.
* **S3+ PREP question**: should the proof be `noncomputable` (using
  `Classical.choice` to pick the minimum entry) or genuinely
  `Computable` (using `Finset.argmin`)? The parent file uses
  `noncomputable def rank`, suggesting the project is comfortable with
  classical choice; however, a `Computable` version is more useful as
  a Mathlib contribution.
