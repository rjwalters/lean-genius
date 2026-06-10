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

* **Available (matrix/integer baseline)**: `Matrix.IsDiag`, `Matrix.det_one`,
  `Matrix.det_mul`, `Matrix.transpose`, `Int.gcd_eq_gcd_ab`, `Int.gcd_dvd_left`,
  `Int.gcd_dvd_right`, `Matrix.mulVec` + linearity lemmas
  (`mulVec_add`, `mulVec_sub`, `mulVec_smul`).
* **Available — Approach B' bearer (S3 PREP 2026-06-10)**:
  - **`Submodule.smithNormalForm`** at
    `Mathlib/LinearAlgebra/FreeModule/PID.lean:541` — SNF of a submodule
    of a finitely-generated free module over a PID. **Caveat**: diagonal
    entries are not certified to satisfy `a 0 ∣ a 1 ∣ ⋯ ∣ a (n-1)`
    (known Mathlib gap; see `MinpolyCharpolyOQ03.lean:80-82` audit).
  - **`Basis.SmithNormalForm`** at the same module — the basis-side variant.
  - **`Module.equiv_directSum_of_isTorsion`** at
    `Mathlib/Algebra/Module/PID.lean:233` — primary-form decomposition,
    witness `p : ι → R` with `Irreducible (p i)`. **Not directly usable
    for invariant-factor chain** (provides prime powers, not chain).
  - **`Module.equiv_free_prod_directSum`** at the same module —
    torsion-free splitting.
* **Available (PID infrastructure)**: `Submodule.IsPrincipal`,
  `IsPrincipalIdealRing`, `EuclideanDomain` typeclass.
* **Not available (verified by S3 PREP via in-repo audit cross-reference)**:
  - Top-level `Matrix.SmithNormalForm` for `Matrix (Fin m) (Fin n) ℤ`
    (per parent file's `mathlibDependencies` — no `SmithNormalForm` entry).
  - Divisibility-chain-certifying variant of `Submodule.smithNormalForm`
    (known Mathlib gap, shared with `minpoly-charpoly-oq-03-oq-02`).
  - `Matrix.elementaryRowOps` as a unified API.

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
* **Insight 4 (S3 PREP 2026-06-10)**: Mathlib v4.26.0 *does* have a
  Smith-Normal-Form bearer at `Submodule.smithNormalForm`
  (`Mathlib/LinearAlgebra/FreeModule/PID.lean:541`), reachable from `Matrix`
  via the column-space-as-submodule construction. S2's "no Mathlib SNF
  API" was an overstatement; the precise statement is "no *top-level
  Matrix* SNF API, and no divisibility-chain certification on the
  submodule-level SNF". The first is what our bridge supplies (B1).
  The second is the genuine remaining gap (B2), shared with
  `minpoly-charpoly-oq-03-oq-02`.
* **Insight 5 (S3 PREP 2026-06-10)**: The sibling slug
  `bezout-identity-oq-04-oq-01-oq-01` (COMPLETED, PR #16026) proved
  `snf_1x2_invariant_factor_pid` for any `GCDMonoid` and **explicitly
  flagged** in its `nextSteps`: "Use Mathlib FreeModule.PID to prove
  `snf_pid_exists` (axiom elimination)". Our slug's discharge of
  `snf_exists` (ℤ-version) is a strict precursor: a ℤ-side B1 bridge
  doubles as a template for the PID-side `snf_pid_exists` discharge,
  meaning a single ACT cycle here unblocks two axioms with one bridge.

---

## Dead Ends

* **Dead end 1 (S2 ORIENT, hypothesised)**: relying on an imminent
  upstream Mathlib SNF PR is not viable — `grep -rn "SmithNormalForm"`
  on Mathlib v4.26.0's tagged release yields no top-level definition.
  Approach C is a non-starter today.

---

## Open Questions for Future Iterations

* **Resolved (S3 PREP 2026-06-10)**: "does Approach B's bearer exist?"
  Yes — `Submodule.smithNormalForm` at
  `Mathlib/LinearAlgebra/FreeModule/PID.lean:541`. Confirmed via in-repo
  cross-reference audit (`MinpolyCharpolyOQ03.lean:79-82`,
  `CayleyHamiltonMinpolyOQ05OQ01OQ04WIP01.lean:240-242`,
  `bezout-identity-oq-04-oq-01-oq-01.json` insights).
* **S4 ACT question (cycle 1)**: does the bridge from `Submodule.smithNormalForm`
  (basis-side) to the parent file's `SmithNormalForm m n` (matrix-side)
  structure fit in ~80-120 LOC, or does basis-coordinate plumbing balloon?
  Empirical answer after first ACT cycle.
* **S5 ACT question (B2)**: divisibility-chain certification. Re-sort/re-group
  approach (~100-150 LOC) or genuine algorithmic proof? Shared Mathlib gap
  with `minpoly-charpoly-oq-03-oq-02` — coordinate or split?
* **S3+ PREP question (carried forward)**: should the proof be `noncomputable`
  or genuinely `Computable`? Parent file uses `noncomputable def rank`,
  suggesting Classical is acceptable for in-repo discharge. For potential
  upstream Mathlib promotion, `Computable` is more valuable but not
  required for axiom discharge.
* **Cross-slug Mathlib upstream candidate (S3 PREP)**: if B2 succeeds, can
  the divisibility-chain-certifying variant of `Submodule.smithNormalForm`
  be PR'd to Mathlib? This would simultaneously unblock
  `minpoly-charpoly-oq-03-oq-02` (elementary-divisors → invariant-factors
  regrouping uses the same chain). Track as a post-merge follow-up.

---

## Approach Decomposition (S3 PREP 2026-06-10)

**Approach B'** (`Submodule.smithNormalForm` bridge — committed primary path):

| Sub-step | Content | Estimated LOC | Sorry exit |
|---|---|---|---|
| **B1 (bridge)** | Lift `Submodule.smithNormalForm` to parent file's `SmithNormalForm m n` structure. Extract `U, V` from basis change; extract `D` from certified diagonal entries. Discharge `hU`, `hV`, `hD_diag`, `isDecompOf`. | 80-120 | leave `hD_div` as `sorry` |
| **B2 (chain)** | Prove the diagonal entries satisfy `d_k ∣ d_{k+1}`. Re-sort/re-group of B1's diagonal. Shared Mathlib gap with `minpoly-charpoly-oq-03-oq-02`. | 100-150 | none (or spin out to sibling slug) |
| **B3 (close)** | Combine B1 + B2 to discharge `axiom snf_exists` at parent file line 146. | 20-40 | none |

**Total Approach B' budget**: ~200-310 LOC across 3 ACT cycles.

**Approach A (fallback)**: ~500 LOC constructive Euclidean reduction;
unchanged from S2 ORIENT. Activated only if B1 plumbing balloons or
B2 proves intractable.

**Approach C**: still not viable at v4.26.0; no top-level `Matrix.SmithNormalForm`.
