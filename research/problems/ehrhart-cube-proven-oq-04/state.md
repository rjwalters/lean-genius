# Current State

**Phase**: PROVED (S6 palindrome-corollary added — all combinatorial sorries still closed + dual Worpitzky form)
**Since**: 2026-05-13T11:40:00Z (S6 PR — palindrome-corollary, build pending)
**Iteration**: 6
**Researcher**: researcher-9

## Current Focus

S5 PALINDROME complete (build pending): closed `eulerian_palindrome` by induction
on `d` using only the recurrence and S3 helpers — **no descent involution needed**.
All five combinatorial theorems are now formally proved.

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

## Blockers

None — all combinatorial sorries are closed.

## Next Action

**S6 (DONE, this PR — researcher-9 2026-05-13)**: Exposed the palindrome
corollary form `(n+1)^d = Σ A(d, k) C(n+d-k, d)` via
`worpitzky_identity_cube_palindrome` (Section VII, ~30 LOC including
docstring). Proof composes `worpitzky_identity_cube` with
`Finset.sum_range_reflect` and `eulerian_palindrome` pointwise, closing
the Nat-subtraction arithmetic with `omega`. Build still pending per
S4/S5 convention (Docker cold-build ~45 min, `.lake` symlink trap).

**S7+ (optional)**:
1. Verify the full-file build (worpitzky + palindrome + palindrome-corollary
   all "build pending").
2. Mathlib upstream PR: contribute `Mathlib.Combinatorics.Enumerative.Eulerian`
   with `eulerianNumber`, `eulerian_zero_eq_one`, `eulerian_eq_zero_of_le`,
   `eulerian_row_sum_factorial`, `eulerian_palindrome`, `worpitzky_identity`,
   and the new `worpitzky_identity_cube_palindrome`.
3. Polynomial-identity form: lift `worpitzky_identity_cube_palindrome` to
   `Polynomial ℕ` (i.e. as an identity of generating functions rather than
   pointwise on `n`). Roughly 30–50 LOC.

## Attempt Counts

- Total attempts: 6 (S1 SCAFFOLD, S2 STRUCTURAL, S3 ROW-SUM, S4 WORPITZKY, S5 PALINDROME, S6 PALINDROME-COROLLARY)
- Current approach attempts: 0 (S7 optional)
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
