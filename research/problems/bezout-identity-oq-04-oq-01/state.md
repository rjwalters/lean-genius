# Current State

**Phase**: AXIOM_REMOVAL_SCOPED
**Since**: 2026-04-27T17:10:00Z
**Iteration**: 2

## Current Focus

The Lean file `proofs/Proofs/BezoutIdentityOQ04OQ01.lean` is in `axiomatized` state with 2 axioms and 0 sorries (407 lines). The two axioms are well-known classical theorems:

1. `snf_exists` — every integer matrix admits a Smith Normal Form decomposition `A = U·D·V`
2. `snf_solvability_criterion` — `Ax = b` solvable over ℤ iff invariant factors divide the transformed RHS

The natural next research step is to derive these from Mathlib rather than postulate them.

## Active Approach

**Approach: Derive matrix SNF from Mathlib's `Module.Basis.SmithNormalForm`**

Mathlib already provides a Smith Normal Form basis result over any PID (including ℤ):

- `Mathlib/LinearAlgebra/FreeModule/PID.lean` defines `Module.Basis.SmithNormalForm (N : Submodule R M) (ι : Type*) (n : ℕ)` — bases for `M` and `N` such that the inclusion is `bN i = a i • bM (f i)` (diagonal in Smith form).
- `Submodule.smithNormalForm` constructs such a basis when `R` is a PID and `M` is finite free.
- Companion APIs: `Submodule.smithNormalFormOfLE`, `Submodule.smithNormalFormOfRankEq`, `Submodule.smithNormalFormTopBasis`.

**Bridge to derive `snf_exists` for matrices:**
1. Treat `A : Matrix (Fin m) (Fin n) ℤ` as a linear map `ℤⁿ → ℤᵐ` via `Matrix.toLin'` or `Matrix.mulVecLin`.
2. Apply `Submodule.smithNormalForm` to the range submodule (or via the cokernel formulation on `ker A`).
3. Extract change-of-basis matrices `U : GL_m(ℤ)`, `V : GL_n(ℤ)` from the basis transformations; show `det U, det V = ±1` (follows from being a `Basis` of a ℤ-free module of equal rank).
4. Build the diagonal `D` from the invariant-factor vector `a : Fin n → ℤ` and prove `A = U * D * V`.

**`snf_solvability_criterion` follows from `snf_exists`** by direct linear algebra:
- Substitute `y = V⁻¹ x` to reduce `A x = b` to `D y = U b`.
- Diagonal system splits into `n` independent 1D divisibility conditions `dᵢ yᵢ = (U b)ᵢ`.
- Fully constructive — no further axiom needed once existence is in hand.

## Mathlib API Survey (confirmed present in Mathlib 4.26.0)

| Mathlib symbol | Use |
|---|---|
| `Module.Basis.SmithNormalForm` (struct) | The basis-pair version of SNF |
| `Submodule.smithNormalForm` | Existence over PIDs |
| `Submodule.smithNormalFormOfLE` | SNF for nested submodules |
| `Matrix.toLin'`, `Matrix.mulVecLin` | Matrix → linear map bridge |
| `Basis.toMatrix`, `LinearMap.toMatrix` | Linear map → matrix bridge |
| `Matrix.det_units` / determinant of basis change | Unimodularity proof |

No file in Mathlib provides the matrix-form `A = U·D·V` decomposition directly under a `SmithNormalForm` name, but it is straightforwardly derivable from the basis form above.

## Blockers

**Disk space tight (2026-04-27): host filesystem fluctuating between 87%–99% capacity (231 MB – 1.8 GB free).** Per researcher feedback memory, Docker builds corrupt at 100% disk and `Edit`/`Write` operations can silently revert under pressure. No Lean-build verification of new code is safe in this session.

The bridge above touches ~150–250 lines of new Lean (toLin/toMatrix coercion, basis-to-matrix unimodular extraction, diagonal-matrix recovery, `U·D·V` equality proof). This needs several Docker iteration cycles to debug Mathlib-API call signatures — not feasible without disk headroom.

## Next Action

For a future researcher session (disk > 5 GB free):

1. Add a new section "## Mathlib-Derived Existence" to `BezoutIdentityOQ04OQ01.lean` between the current `axiom snf_exists` and `axiom snf_solvability_criterion` blocks.
2. Define `def matrixToLinearMap (A : Matrix (Fin m) (Fin n) ℤ) : (Fin n → ℤ) →ₗ[ℤ] (Fin m → ℤ) := A.mulVecLin` or use the existing `Matrix.toLin'`.
3. Construct `theorem snf_exists_via_mathlib` returning a `SmithNormalForm` whose `U`, `V`, `D` are extracted from `Submodule.smithNormalForm` applied to the range submodule.
4. Once that theorem is proved, replace `axiom snf_exists` with `theorem snf_exists := snf_exists_via_mathlib` (or restructure callers to use the new theorem directly).
5. Then prove `snf_solvability_criterion` constructively from `snf_exists` via the diagonal-substitution argument; remove its axiom.
6. Build with `./proofs/scripts/docker-build.sh Proofs.BezoutIdentityOQ04OQ01`.
7. Update `meta.json`: `axiomCount` 2 → 0, `status` `axiomatized` → `verified`, `badge` → `verified`, drop `axiom`-related `assumptions` text, update `originalContributions`.

Estimated effort: 1–2 multi-iteration sessions with Docker builds. The bridge is well-documented in Mathlib via `Submodule.basisOfPidOfLE` (the underlying induction); the SNF extension just adds the divisibility-chain refinement.

## Attempt Counts

- Total attempts: 1 (Mathlib API survey only — no code changes)
- Current approach attempts: 1
- Approaches tried: 1 (Mathlib basis-form derivation — confirmed feasible, deferred for build verification)
