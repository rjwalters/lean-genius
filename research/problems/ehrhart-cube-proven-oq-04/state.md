# Current State

**Phase**: SCAFFOLDED (S2 complete, → S3)
**Since**: 2026-05-12T03:30:00Z (S2 PR)
**Iteration**: 2
**Researcher**: researcher-11

## Current Focus

S2 STRUCTURAL complete: closed two of the five sorries (`cube_h_star_eulerian` and `cube_lattice_count_eulerian`) — both follow structurally from the SCAFFOLD definition and `Fintype.card_fun`. The three combinatorial sorries (`worpitzky_identity_cube`, `eulerian_row_sum_factorial`, `eulerian_palindrome`) remain for S3+.

## Active Approach

**Approach A — Induction on $d$ (algebraic)**.
Inductive step uses Pascal's identity (`Nat.choose_succ_succ`) and the Eulerian recurrence on `eulerianNumber`. No additional Mathlib infrastructure required.

## What's Been Built (S1)

### Definitions (axiom-free, computable)
- `eulerianNumber : ℕ → ℕ → ℕ` — via recurrence A(d+1, k+1) = (k+2) A(d, k+1) + (d-k) A(d, k).
- `cubeHStarPoly : ℕ → Polynomial ℕ` — Eulerian generating polynomial $\sum_{k=0}^{d-1} A(d, k) X^k$.

### Concrete value lemmas (all `rfl`)
- A(0, 0) = 1, A(0, 1) = 0
- A(1, 0) = 1, A(1, 1) = 0
- A(2, 0) = A(2, 1) = 1, A(2, 2) = 0
- A(3, 0) = A(3, 2) = 1, A(3, 1) = 4, A(3, 3) = 0
- A(4, 0) = A(4, 3) = 1, A(4, 1) = A(4, 2) = 11, A(4, 4) = 0

### Row-sum consistency checks (all `rfl`)
- $\sum_k A(1, k) = 1!$, $\sum_k A(2, k) = 2!$, $\sum_k A(3, k) = 3!$, $\sum_k A(4, k) = 4!$.

### Palindrome consistency checks (all `rfl`)
- A(3, 0) = A(3, 2), A(4, 0) = A(4, 3), A(4, 1) = A(4, 2).

### Worpitzky cases proved (no sorry)
- `worpitzky_d1`: $(n + 1) = 1 \cdot \binom{n+1}{1}$.
- `worpitzky_d2`: $(n+1)^2 = \binom{n+1}{2} + \binom{n+2}{2}$ — by induction on n using Pascal's identity + `omega`.
- 7 concrete `decide`-verifications at $(d, n) \in \{(2,0), (2,1), (3,0), (3,1), (3,2), (4,1), (4,2)\}$.

### Theorems closed in S2 (no sorry)
- `cube_h_star_eulerian` — coefficient extraction. Closed via `Polynomial.finset_sum_coeff` + `Polynomial.coeff_smul` + `Polynomial.coeff_X_pow` + `Finset.sum_ite_eq'`. ~10 lines.
- `cube_lattice_count_eulerian` — bridging corollary with `EhrhartCubeProven`. Closed via `Fintype.card_fun` + `Fintype.card_fin` + the still-deferred `worpitzky_identity_cube`. ~3 lines.

### Theorems stated and deferred (3 remaining sorries)
1. `worpitzky_identity_cube` — main theorem.
2. `eulerian_row_sum_factorial` — Σ A(d, k) = d!.
3. `eulerian_palindrome` — A(d, k) = A(d, d-1-k).

## Blockers

None for S3. Mathlib has all required ingredients: `Nat.choose_succ_succ` (Pascal), `Finset.sum_range_succ`, basic arithmetic via `omega`/`ring`.

## Next Action

**S3 — Close `worpitzky_identity_cube`** via induction on `d`.

Concrete plan:
1. Base case d = 1: closed by `simp [eulerian_1_0, Nat.choose_one_right]`.
2. Inductive step: assume Worpitzky for $d$. Prove for $d + 1$.
3. Use the key identity $(d+1) \binom{n+1+k}{d+1} = (n+1+k) \binom{n+k}{d}$ to bring $(n+1)$ through the sum.
4. Re-index using the Eulerian recurrence $A(d+1, k+1) = (k+2) A(d, k+1) + (d-k) A(d, k)$.
5. Apply Pascal's identity `Nat.choose_succ_succ` to match coefficients.

Expected: ~80-120 lines of Lean. Helper lemmas may decompose the algebra.

**Alternative if Approach A stalls**: prove the small-d cases d = 3, d = 4 (analogous to the existing `worpitzky_d2`) to build intuition before attempting the general induction. Then `eulerian_row_sum_factorial` may be closed in S4 by the algebraic-recurrence argument:
$\sum_{k} A(d+1, k) = (d+1) \sum_k A(d, k) = (d+1) d! = (d+1)!$ via the identity
$\sum_{k=0}^{d-1}[(k+2) A(d, k+1) + (d-k) A(d, k)] + A(d, 0) = (d+1) \sum_{k=0}^{d-1} A(d, k)$
(verified by combining the index-shifted sums with $A(d, d) = 0$).

## Attempt Counts

- Total attempts: 2 (S1 SCAFFOLD, S2 STRUCTURAL)
- Current approach attempts: 0 (S3 Approach A — induction on d for Worpitzky)
- Approaches tried: 0

## Open Questions / Risks

1. **Recurrence boundary handling**: the `(d - k)` Nat-subtraction in the recurrence requires careful proof when k = d - 1 (border between non-zero and zero Eulerian values). May need a `by_cases` split in the inductive proof.

2. **Off-by-one in the binomial**: Worpitzky has two common forms — $\binom{n+1+k}{d}$ and $\binom{n+d-k}{d}$ (after palindrome). The form chosen here ($\binom{n+1+k}{d}$) is more direct from the combinatorial bijection but less standard than the h*-vector form. S2 should keep this consistent; the palindrome conversion to $\binom{n+d-k}{d}$ is a separate corollary.

3. **`cubeHStarPoly` is `noncomputable`**: `Polynomial ℕ` carries `noncomputable` operations through `Finsupp`. This doesn't affect correctness but means `decide` will not unfold the polynomial coefficient. If problematic, switch to a `Fin d → ℕ` representation for `cubeHStarPoly`.
