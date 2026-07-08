# Knowledge: Erdős #378 — Density of squarefree binomial coefficients

## Status

**SOLVED** (Granville–Ramaré 1996; observed by Aggarwal–Cambie). Formalized as
`axiomatized` in `Proofs/Erdos378Problem.lean`: 0 sorries, exactly 2 axioms
isolating the deep analytic Granville–Ramaré inputs.

## The two axioms (deep, NOT Mathlib-eliminable)

1. `granville_ramare_density_exists` — for every `m`, the density `η_m` of
   `{n | squarefreeCount n = 2m+2}` exists. (Granville–Ramaré exponential-sum
   input; no Mathlib analogue.)
2. `complement_density` — `{n | squarefreeCount n < r}` has density
   `Σ_{0≤m≤(r-1)/2} η_m`, and that density is `< 1`. The `< 1` clause is the
   positivity content of the resolution.

Both are honestly documented as the *only* assumptions; everything downstream
(`erdos_378_density_exists`, `_positive`, `erdos_378`, `erdos_378_answer`) is
machine-checked by a complementation argument (`natDensity_compl`).

Do NOT attempt to prove these from Mathlib — they are the genuine analytic core.

## Verified axiom-independent structure (the parity theory)

The involution `k ↦ n − k` on the counted set drives everything:
- `binomialSquarefree_symm`: squarefreeness of `C(n,k)` is symmetric.
- `squarefreeCount_even_of_odd`: for **odd** `n`, the count is even (involution
  fixed-point-free).
- `squarefreeCount_odd_iff_central_squarefree` (**2026-07-08, this session**):
  for **even** `n ≥ 2`, the count is *odd iff* `C(n, n/2)` is squarefree. The
  involution now has the single fixed point `k = n/2`, so
  `squarefreeCount n = 2·|A| + |F|` with `|F| ∈ {0,1}` recording whether the
  central index is squarefree. This **completes the parity theory** of row
  counts and explains structurally why Granville–Ramaré only see even counts
  `2m+2` (an odd count would force an even `n` with squarefree central binomial;
  the counted set `2m+2` is even).

### Proof recipe for the even case (reusable)

Mirror `squarefreeCount_even_of_odd` but split `S` three ways by the sign of
`2k − n`:
- `A = S.filter (2k<n)`, `C = S.filter (n<2k)`, `F = S.filter (2k=n)`.
- `S.card = A.card + D.card` (D = filter ¬2k<n) via
  `filter_card_add_filter_neg_card_eq_card`; then `D.card = C.card + F.card` by
  proving `C = D.filter (n<2k)` and `F = D.filter (¬n<2k)` by `ext`+`omega` and
  reusing the same additivity lemma on `D`.
- `A.card = C.card` via `card_nbij'` with `k ↦ n−k` (identical to the odd proof,
  inequality direction flipped; `omega` discharges `n < 2*(n-k)` etc.).
- `F = S.filter (·= n/2)` (`ext`+`omega` using `n = j+j`), then `filter_eq'`
  makes `F` the singleton `{n/2}` or `∅`; `Odd F.card ↔ n/2 ∈ S` by
  `iff_of_true (by decide) h` / `iff_of_false (by decide) h`.
- Assemble `squarefreeCount n = 2*C.card + F.card` by `omega`; parity via
  `rw [Nat.odd_iff, Nat.odd_iff]; omega`; finish with `memS (n/2)` + `tauto`
  (`n/2 < n`, `1 ≤ n/2` from `omega` on `n = j+j`, `2 ≤ n`).

Gotcha: `simp only [hS, mem_filter, mem_range]` fully closes `memS`, so follow
with `try tauto`, not bare `tauto` (else "No goals").

## Build

Builds clean under Mathlib v4.26 (`docker-build.sh Proofs.Erdos378Problem`,
7743 jobs, `Built`, 0 errors/warnings). No exit-135 flakiness observed here.
theoremCount 11→12, lineCount 311→403.

## Open directions (if re-served)

- No further axiom-free structural lemma is obviously high-value; the parity
  theory is now complete.
- The two Granville–Ramaré axioms are the frontier; formalizing either needs the
  full exponential-sum machinery (>>1000 lines, BLOCKED).
