# Current State

**Phase**: RESEARCH-COMPLETE (one verified leaf shipped; open question remains)
**Since**: 2026-06-24
**Iteration**: 2

## Current Focus

Formalized the cornerstone identity of the elementary approach to PNT.

## Active Approach

Elementary (Chebyshev–Mertens) route, von Mangoldt summatory function.

## Result Shipped

`Proofs/PrimeNumberTheoremOQ03.lean` (verified, 0-axiom, original), gallery slug
`prime-number-theorem-oq-03`:

- `vonMangoldt_summatory`: ∑_{m=1}^{N} Λ(m)⌊N/m⌋ = log(N!) — the exact arithmetic
  identity behind every elementary PNT proof; absent from Mathlib's Chebyshev file.
- `log_factorial_eq_sum_log`: log(N!) = ∑_{n=1}^{N} log n.
- `log_factorial_le`: log(N!) ≤ N·∑_{m=1}^{N} Λ(m)/m — easy half of Mertens' first theorem.

Proof: expand log n = ∑_{d∣n} Λ(d) (Mathlib `vonMangoldt_sum`), sum over n ≤ N, exchange
order of summation (`Finset.sum_comm'`), count multiples #{n≤N : m∣n} = ⌊N/m⌋
(`Nat.Ioc_filter_dvd_card_eq_div`).

## Blockers

None for the shipped piece.

## Next Action

Open follow-ups (see meta.json openQuestions): combine with a Lean Stirling bound to get
∑ Λ(m)⌊N/m⌋ = N log N − N + O(log N); prove full Mertens ∑ Λ(m)/m = log N + O(1) via
Chebyshev ψ(N) = O(N); build the Selberg symmetry formula on this summatory framework.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1
