# Session 2026-07-12 (researcher-5) — sharp closed-form lower bound on maxAvoidingSize

**Mode**: REVISIT (RICH tier) | **Outcome**: progress (1 new theorem, VERIFIED 0 new
axiom / 0 sorry; host `proofs/bin/lake env lean` exit 0, NO ERRORS)

## Context

`Erdos771Problem.lean` is 0-sorry / 2-axiom (the two axioms `erdos_graham_lower_bound`
and `alon_freiman_upper_bound` are the deep external Erdős–Graham / Alon–Freiman
asymptotics `f(n)=(1/2+o(1))·n/log n`, genuinely irreducible — not session-provable).
`maxAvoidingSize n m` (max size of an `m`-avoiding subset of `{1,…,n}`) had **exact
values only for `m ≤ 4`**: `n-1, n-1, n-2, n-2`, and a general lower bound
`interval_avoiding_lower : ≥ n - m` (via the interval `{m+1,…,n}`).

## What I did

Added `maxAvoidingSize_ge_sub_ceil_half`: for `1 ≤ m ≤ n`,

  `maxAvoidingSize n m ≥ n − ⌈m/2⌉`   (with `⌈m/2⌉ = (m+1)/2` in `ℕ`).

Witness `S = {⌈m/2⌉,…,n} \ {m}`, of size `n − ⌈m/2⌉`. Avoidance:
- the singleton `{m}` is killed by erasing `m`;
- any subset of size `≥ 2` has two *distinct* elements `≥ ⌈m/2⌉`, summing to
  `≥ ⌈m/2⌉ + (⌈m/2⌉+1) = 2⌈m/2⌉ + 1 > m`.

This **strictly improves** `interval_avoiding_lower` (`n − m`, since `⌈m/2⌉ < m` for
`m ≥ 2`) and is **tight**: it reproduces the exact `m = 1..4` values (all `= n − ⌈m/2⌉`).

## Key observations / proof notes

- The bound is conjecturally **exact** (`= n − ⌈m/2⌉` for `1 ≤ m ≤ n`). Upper-bound
  sketch (follow-up, not formalised): the `⌈m/2⌉` pairwise-disjoint sum-`m` subsets
  `{m}` and `{i, m−i}` (`i = 1..⌊(m−1)/2⌋`) force any `m`-avoiding set to omit `≥ 1`
  element from each, hence `≥ ⌈m/2⌉` distinct omitted elements → `card ≤ n − ⌈m/2⌉`.
  Formalising needs a transversal-injection counting argument (~50L).
- Lean gotcha: `Finset.exists_ne_of_one_lt_card (by omega) a₀` left the Finset as a
  metavariable (`omega` saw `1 < #?m`), so it failed. Use
  `Finset.one_lt_card.mp h1lt` → `⟨x,hx,y,hy,hxy⟩` which pins the set to `A`.
- `∑A ≥ x + y` for distinct `x,y ∈ A`: `Finset.sum_le_sum_of_subset` over
  `{x,y} ⊆ A` + `Finset.sum_pair hxy`; then `omega` (with `x≠y`, `x,y ≥ ⌈m/2⌉`,
  `∑A = m`) closes the `2⌈m/2⌉+1 > m` contradiction. `omega` handles the `(m+1)/2`.

## Files modified
- `proofs/Proofs/Erdos771Problem.lean` (+~55L, 47 → 48 theorems, still 0-sorry/2-axiom)
- `src/data/research/problems/erdos-771.json`

## Next steps
- Formalise the matching **upper bound** to upgrade to the exact closed form
  `maxAvoidingSize n m = n − ⌈m/2⌉` (`1 ≤ m ≤ n`) — the transversal argument above.
- The 2 deep asymptotic axioms remain external (out of session scope).
