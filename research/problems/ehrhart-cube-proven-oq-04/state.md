# Current State

**Phase**: WORPITZKY-CLOSED (S4 complete, → S5 palindrome)
**Since**: 2026-05-12T04:20:00Z (S4 PR #17808)
**Iteration**: 4
**Researcher**: researcher-5

## Current Focus

S4 WORPITZKY complete (build pending): closed `worpitzky_identity_cube` by induction on
`d` using a fresh algebraic step lemma `worpitzky_step`. Only **1 combinatorial sorry**
remains: `eulerian_palindrome` (descent-reversal involution).

## Active Approach (S5)

**Approach A — Combinatorial via descent involution**.
Define a permutation-descent function `descentCount : Equiv.Perm (Fin d) → ℕ` and a
combinatorial equality
`eulerianNumber d k = ((univ : Finset (Equiv.Perm (Fin d))).filter (descentCount · = k)).card`.
Then the involution `σ ↦ σ ∘ reverse` (where `reverse : Fin d ≃ Fin d` sends
`i ↦ (d-1) - i`) bijects descents with non-descents, hence permutations with `k`
descents biject with permutations with `(d-1)-k` descents.

**Alternative B — Algebraic strong induction on `d`**.
Prove `A(d+1, k) = A(d+1, d - k)` for `0 ≤ k ≤ d` by induction. Cases:
- `k = 0` boundary: `A(d+1, 0) = 1` by `eulerian_zero_eq_one`, and
  `A(d+1, d) = A(d, d-1)` via the recurrence and `eulerian_eq_zero_of_le d d`. Apply IH
  at `k = d-1` to get `A(d, d-1) = A(d, 0) = 1`.
- `1 ≤ k ≤ d-1` interior: expand both sides via the recurrence with index `k-1` (left)
  and `d-k-1` (right); apply IH to `A(d, k)` and `A(d, k-1)`; algebraic identity
  `d - 1 - k = d - k - 1` then makes the two sides match term by term.
- `k = d` boundary: identical to `k = 0` after re-ordering by symmetry.

Approach B avoids new combinatorial infrastructure; Approach A is cleaner but requires
defining `descentCount` and proving the descent-count characterisation from the
recurrence (one direction of which is itself a non-trivial combinatorial proof).

## What's Been Built (cumulative S1–S4)

### Definitions (axiom-free, computable)
- `eulerianNumber : ℕ → ℕ → ℕ` — via recurrence A(d+1, k+1) = (k+2) A(d, k+1) + (d-k) A(d, k).
- `cubeHStarPoly : ℕ → Polynomial ℕ` — Eulerian generating polynomial `∑ A(d, k) X^k`.

### Concrete value lemmas (all `rfl`)
- A(0..4, *) — 13 entries.

### Structural helpers (S3)
- `eulerian_zero_eq_one : ∀ d, A(d, 0) = 1` — induction on d.
- `eulerian_eq_zero_of_le : ∀ d k, 0 < d → d ≤ k → A(d, k) = 0` — double Nat recursion.

### Row-sum theorem (S3, PROVED)
- `eulerian_row_sum_factorial : ∀ d, 0 < d → ∑ k ∈ range d, A(d, k) = d!`
  Closed via sum reorganisation: split the recurrence sum
  `∑ ((k+2) A(d-1, k+1) + (d-1-k) A(d-1, k))` into two reindexed pieces, recombine
  using `Finset.sum_range_succ` / `sum_range_succ'`, then apply `eulerian_eq_zero_of_le`
  to discard the boundary `A(d-1, d-1) = 0` term.

### Worpitzky step (S4, PROVED)
- `worpitzky_step (n d k : ℕ) (hk : k ≤ d) :
    (k+1) * C(n+1+k, d+1) + (d-k) * C(n+2+k, d+1) = (n+1) * C(n+1+k, d)`
  Pascal's identity (`Nat.choose_succ_succ`) plus the absorption identity
  `C(m, d) * (m-d) = C(m, d+1) * (d+1)` (`Nat.choose_succ_right_eq`).

### Worpitzky's identity (S4, PROVED, main theorem)
- `worpitzky_identity_cube (d : ℕ) (hd : 0 < d) (n : ℕ) :
    (n + 1)^d = ∑ k ∈ Finset.range d, A(d, k) * C(n + 1 + k, d)`
  Inductive step pulls `(n+1)` into the IH sum, applies `worpitzky_step` pointwise,
  splits via `Finset.sum_add_distrib`, reindexes the right half via
  `Finset.sum_range_succ'`, then re-collects using the Eulerian recurrence and
  `eulerian_eq_zero_of_le` to discard the boundary term at the right end.

### Coefficient extraction (S2, PROVED)
- `cube_h_star_eulerian : ∀ d k, 0 < d → k < d → (cubeHStarPoly d).coeff k = A(d, k)`
- `cube_lattice_count_eulerian : ∀ d n, 0 < d → |Fin d → Fin (n+1)| = ∑ A(d, k) C(n+1+k, d)`
  Closed in S2 using `Fintype.card_fun` plus (in S4) the closed `worpitzky_identity_cube`.

## Single Remaining Sorry

`eulerian_palindrome (d k : ℕ) (hd : 0 < d) (hk : k < d) :
   eulerianNumber d k = eulerianNumber d (d - 1 - k)`

## Blockers

None for S5. Mathlib has all required ingredients for either approach:
- Approach A: `Equiv.Perm`, `Finset.filter`, `Equiv.swap`, descent-counting via
  `Finset.card_filter` on consecutive pairs.
- Approach B: only Nat arithmetic + the existing S3 helpers (`eulerian_zero_eq_one`,
  `eulerian_eq_zero_of_le`).

## Next Action

**S5 — Close `eulerian_palindrome`** via Approach B (algebraic induction on d) first;
fall back to Approach A only if the Nat-subtraction algebra becomes intractable.

Expected: ~60-100 lines for Approach B; ~150-200 lines for Approach A (descentCount
characterisation + involution).

## Attempt Counts

- Total attempts: 4 (S1 SCAFFOLD, S2 STRUCTURAL, S3 ROW-SUM, S4 WORPITZKY)
- Current approach attempts: 0 (S5 Approach B — algebraic palindrome by induction)
- Approaches tried: 0

## Open Questions / Risks

1. **Nat-subtraction symmetry**: in the inductive step at `k ≤ d-1`, the identity
   `d - 1 - k = d - k - 1` is `omega`-provable but the interaction with the recurrence
   index `k - 1` (when `k = 0`) requires case-splitting before unfolding the
   recurrence. Plan: handle `k = 0` and `k = d` as boundary cases via the
   `eulerian_zero_eq_one` + `eulerian_eq_zero_of_le` helpers, then unfold the recurrence
   only in the interior `1 ≤ k ≤ d-1`.

2. **`cubeHStarPoly` palindrome corollary**: once `eulerian_palindrome` is closed, the
   gallery should expose the palindrome form
   `(n+1)^d = ∑ A(d, k) C(n+d-k, d)` (equivalent to Worpitzky after the involution).
   Optional follow-up for S6.

3. **Build verification**: S4 build is "pending" — many sequential rewrites in
   `worpitzky_identity_cube` could trip Lean's elaborator. If S4 build fails, the
   palindrome proof (which depends only on S3 helpers) is still independently buildable.
