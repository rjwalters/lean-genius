# combinations-formula-oq-08-oq-01 — The Fibonacci Recurrence as a Shadow of Pascal's Rule

**Status**: COMPLETED (verified, 0 sorries, 0 axioms)
**Lean file**: `proofs/Proofs/CombinationsFormulaOQ08OQ01.lean`
**Gallery**: `src/data/proofs/combinations-formula-oq-08-oq-01/meta.json`

## Problem

Parent `combinations-formula-oq-08` proves `fib(n+1) = ∑_{k} C(n-k, k)` (Fibonacci as
shallow-diagonal sums of Pascal's triangle) and posed as its first open question:
derive the recurrence `F(n+2) = F(n+1) + F(n)` *directly* from that identity by applying
Pascal's rule term-by-term, and relate it to the Lucas partial-sum identity
`∑_{i<n} fib(i) = fib(n+1) − 1`.

## Result

Let `D(n) = ∑_{k<n+1} C(n-k, k)` be the n-th shallow-diagonal total.

- **`D_recurrence`** (core): `D(n+2) = D(n+1) + D(n)`, proved purely by term-by-term
  Pascal expansion — **no use of `Nat.fib_add_two`**.
- **`fib_recurrence_via_pascal`**: `fib(n+3) = fib(n+2) + fib(n+1)`, recovered from
  `D_recurrence` via `D_eq_fib : D(n) = fib(n+1)`. The Fibonacci recurrence is thus
  exhibited as a shadow of Pascal's rule.
- **`fib_partial_sum_sub`**: `∑_{i<n} fib(i) = fib(n+1) − 1` (Lucas), by induction.
- **`shallow_diag_partial_sum`**: `∑_{i<n} D(i) = fib(n+2) − 1` — the same identity
  recast over the diagonal totals.

10 theorems, 1 definition, 3 `decide` sanity checks. `#print axioms` shows only
`propext, Classical.choice, Quot.sound`.

## Session 2026-06-25 (Session 1) — FRESH, COMPLETED

### What I Did
- Designed the peeling-then-Pascal proof of `D(n+2) = D(n+1) + D(n)`.
- Reproved the parent identity `fib_eq_sum_range_choose` inline so the file is
  self-contained (parent olean was not built locally; Docker down → offline
  `lake env lean`).
- Proved the Lucas partial-sum identity and recast it over the diagonal totals.
- Built clean offline; verified 0-axiom 0-sorry.

### Key Findings / Techniques
- **Peeling**: `Finset.sum_range_succ'` strips the `k=0` boundary term (giving the
  constant `1` via `Nat.choose_zero_right`); `Finset.sum_range_succ` exposes the
  vanishing top term `C(0, n+2) = 0` (discarded via `Nat.choose_eq_zero_of_lt`). This
  reduces both `D(n+2)` and `D(n+1)` to `(∑_{k<n+1} …) + 1`.
- **Pascal step**: for `k ≤ n`, `n+1-k = (n-k)+1`, so `Nat.choose_succ_succ` gives
  `C(n+1-k, k+1) = C(n-k, k) + C(n-k, k+1)` term-by-term; `Finset.sum_add_distrib`
  splits the result into `D(n)` and (shifted) `D(n+1)`.
- **Gotcha**: keep `simp only [Nat.choose_zero_right]` (NOT `Nat.sub_zero` too) so simp
  touches only the boundary `_ 0` term and does **not** pre-normalize `n+1-(k+1)` inside
  the sum — otherwise the later `congr 1; omega` per-term step hits "No goals".
- **Gotcha**: `rw [choose_shift_succ hk]` closes its goal by rfl, so a trailing `ring`
  errors with "No goals to be solved" — drop it.
- Natural-subtraction index identities all fall to `omega` using the `range` membership
  bound (`Nat.lt_succ_iff`).

### Next Steps (optional follow-up)
- Stride-`s` diagonals `D_s(n) = ∑_k C(n-(s-1)k, k)` and the `s`-step recurrence
  `D_s(n+s) = D_s(n+s-1) + D_s(n)`; same peeling-then-Pascal method should formalize it.
