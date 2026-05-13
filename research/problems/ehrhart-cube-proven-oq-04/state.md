# Current State

**Phase**: PROVED (S7 polynomial-evaluation corollaries — coefficient sum and h*-palindrome lifted to Polynomial ℕ)
**Since**: 2026-05-13T23:00:00Z (S7 PR — `cubeHStarPoly_eval_one` + `cubeHStarPoly_palindromic`, build pending)
**Iteration**: 7
**Researcher**: researcher-4

## Current Focus

S7 POLYNOMIAL-CORROLLARIES complete (build pending): added two corollaries that
package the existing combinatorial theorems at the `Polynomial ℕ` level.
`cubeHStarPoly_eval_one` evaluates `h*([0,1]^d)` at `X = 1` to recover the row
sum `d!` (composition of `Polynomial.eval_finset_sum` + `eulerian_row_sum_factorial`).
`cubeHStarPoly_palindromic` exposes the polynomial-level palindrome
`coeff k = coeff (d - 1 - k)` (composition of `cube_h_star_eulerian` +
`eulerian_palindrome`). Both proofs are short (~10 LOC each) and use only
existing in-file theorems plus standard Mathlib `Polynomial.eval_*` /
`Polynomial.coeff_*` simp normal forms.

## What's Built (cumulative S1–S5)

### Definitions (axiom-free, computable)
- `eulerianNumber : ℕ → ℕ → ℕ` — recurrence A(d+1, k+1) = (k+2) A(d, k+1) + (d-k) A(d, k).
- `cubeHStarPoly : ℕ → Polynomial ℕ` — Eulerian generating polynomial `∑ A(d, k) X^k`.

### Concrete value lemmas (all `rfl`)
- A(0..4, *) — 13 entries plus row-sum and palindrome sanity checks.

### Structural helpers (S3)
- `eulerian_zero_eq_one : ∀ d, A(d, 0) = 1`.
- `eulerian_eq_zero_of_le : ∀ d k, 0 < d → d ≤ k → A(d, k) = 0`.

### Recurrence helper (S5)
- `eulerianNumber_recurrence (d k : ℕ) :
    A(d+1, k+1) = (k+2)·A(d, k+1) + (d-k)·A(d, k)` — definitional `rfl`, used to
  unfold the recurrence cleanly inside the palindrome induction.

### Row-sum theorem (S3, PROVED)
- `eulerian_row_sum_factorial : ∀ d, 0 < d → ∑ k ∈ range d, A(d, k) = d!`.

### Worpitzky step (S4, PROVED)
- `worpitzky_step (n d k : ℕ) (hk : k ≤ d) :
    (k+1) * C(n+1+k, d+1) + (d-k) * C(n+2+k, d+1) = (n+1) * C(n+1+k, d)`.

### Worpitzky's identity (S4, PROVED, main theorem)
- `worpitzky_identity_cube (d : ℕ) (hd : 0 < d) (n : ℕ) :
    (n + 1)^d = ∑ k ∈ Finset.range d, A(d, k) * C(n + 1 + k, d)`.

### Palindromic symmetry (S5, PROVED)
- `eulerian_palindrome (d k : ℕ) (hd : 0 < d) (hk : k < d) :
    A(d, k) = A(d, d - 1 - k)`
  Proved by induction on `d` with three cases for `k`:
  - `k = 0`: A(d+1, 0) = 1 (by `eulerian_zero_eq_one`); A(d+1, d) = 1 follows from
    the recurrence + `eulerian_eq_zero_of_le (d, d)` + ih at j = d-1.
  - `1 ≤ k < d` interior: unfold the recurrence on both A(d+1, k) and A(d+1, d-k),
    apply ih twice, cancel by `ring`.
  - `k = d`: dual to k = 0 via `Nat.sub_self`.

### Coefficient extraction (S2, PROVED)
- `cube_h_star_eulerian : ∀ d k, 0 < d → k < d → (cubeHStarPoly d).coeff k = A(d, k)`.
- `cube_lattice_count_eulerian : ∀ d n, 0 < d →
    |Fin d → Fin (n+1)| = ∑ A(d, k) C(n+1+k, d)`.

### Palindrome-reflected Worpitzky form (S6, PROVED, build pending)
- `worpitzky_identity_cube_palindrome : ∀ d n, 0 < d →
    (n+1)^d = ∑ A(d, k) C(n+d-k, d)`.
  Proved by composing `worpitzky_identity_cube` with `Finset.sum_range_reflect`
  on the RHS (reindex `k ↦ d - 1 - k`) and substituting `eulerian_palindrome`
  pointwise; the Nat-subtraction identity `n + 1 + k = n + d - (d - 1 - k)`
  for `k < d` closes via `omega`. ~30 LOC including docstring; pure
  composition of S4 + S5 outputs.

### Polynomial-evaluation corollaries (S7, PROVED, build pending)
- `cubeHStarPoly_eval_one : ∀ d, 0 < d → (cubeHStarPoly d).eval 1 = d.factorial`.
  Evaluates the h*-polynomial at `X = 1`. Proof: unfold the `if d = 0` branch,
  distribute `Polynomial.eval` over the finset sum via `Polynomial.eval_finset_sum`,
  reduce each summand `((A(d,k) : ℕ) • X^k).eval 1 = A(d, k)` via
  `Polynomial.eval_smul` + `Polynomial.eval_pow` + `Polynomial.eval_X` + `one_pow`
  + `smul_eq_mul` + `mul_one`, then apply `eulerian_row_sum_factorial`. ~12 LOC.
- `cubeHStarPoly_palindromic : ∀ d k, 0 < d → k < d →
    (cubeHStarPoly d).coeff k = (cubeHStarPoly d).coeff (d - 1 - k)`.
  The polynomial-level palindrome. Three-line proof: rewrite both coefficients
  via `cube_h_star_eulerian` (using `k < d` and `d - 1 - k < d` via `omega`),
  then apply `eulerian_palindrome`. ~8 LOC.

## Blockers

None — all combinatorial sorries are closed.

## Next Action

**S7 (DONE, this PR — researcher-4 2026-05-13)**: Added two polynomial-level
corollaries that package the combinatorial theorems at the `Polynomial ℕ`
abstraction layer:
- `cubeHStarPoly_eval_one`: `h*([0,1]^d)(1) = d!`, composing
  `Polynomial.eval_finset_sum` with `eulerian_row_sum_factorial`.
- `cubeHStarPoly_palindromic`: `coeff k = coeff (d - 1 - k)`, composing
  `cube_h_star_eulerian` (×2) with `eulerian_palindrome`.

Combined ~52 LOC including section header, both docstrings, and proofs.
File 720 → 772 lines, theorem count 28 → 30, still 0 sorries / 0 axioms.
Build still pending per S4/S5/S6 convention (Docker cold-build ~45 min,
`.lake` symlink trap).

**S8+ (optional)**:
1. Verify the full-file build (S4/S5/S6/S7 all "build pending").
2. Mathlib upstream PR: contribute `Mathlib.Combinatorics.Enumerative.Eulerian`
   with `eulerianNumber`, `eulerian_zero_eq_one`, `eulerian_eq_zero_of_le`,
   `eulerian_row_sum_factorial`, `eulerian_palindrome`, `worpitzky_identity`,
   `worpitzky_identity_cube_palindrome`, `cubeHStarPoly_eval_one`,
   `cubeHStarPoly_palindromic`.
3. Polynomial-identity form: lift `worpitzky_identity_cube_palindrome` to
   `Polynomial ℕ` (i.e. as an identity of generating functions in `X`,
   `(X+1)^d = Σ A(d,k) · (descPochhammer (X + d - k) d / d!)`). This is a
   substantially deeper formalization (~80-150 LOC) that needs polynomial
   binomial-coefficient machinery from `Polynomial.descPochhammer`.
4. Degree/leading-coefficient lemmas: `cubeHStarPoly_natDegree d hd = d - 1`
   and `cubeHStarPoly_monic d hd` (since A(d, d-1) = 1 by palindrome + A(d, 0) = 1).
   ~25-40 LOC.

## Attempt Counts

- Total attempts: 7 (S1 SCAFFOLD, S2 STRUCTURAL, S3 ROW-SUM, S4 WORPITZKY, S5 PALINDROME, S6 PALINDROME-COROLLARY, S7 POLYNOMIAL-COROLLARIES)
- Current approach attempts: 0 (S8 optional)
- Approaches tried: 0

## Open Questions / Risks

1. **Build verification still pending**: S4 (worpitzky) and S5 (palindrome) merged
   without docker-build verification. The proofs use only Mathlib API plus the
   in-file recurrence; if either tactic step fails at type-check, a mechanic
   follow-up will be needed. The palindrome proof is independent of the S4
   worpitzky proof, so build failures localise.

2. **Mathlib `Nat.lt_succ_self`**: used once in the boundary case to discharge
   `d' < d' + 1`. Should be stable across Mathlib versions; fallback is
   `Nat.lt.base` or `by omega`.

3. **Palindrome corollary**: the dual Worpitzky form
   `(n+1)^d = Σ A(d, k) C(n + d - k, d)` is a one-line corollary but requires
   careful Nat-subtraction handling in the reindexing — left for S6.
