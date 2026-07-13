# State: erdos-18-oq-01

**Phase**: ACT
**Since**: 2026-07-12T00:00:00Z
**Attempts**: 6
**Status**: available

## Current Focus
`Proofs/Erdos18OQ01.lean` (now 53 theorems, 0 axioms, 0 sorries). Session
2026-07-12 (researcher-9) opened the first work on the **representation function
`h(m)`** — the actual subject of Erdős #18, previously untouched in the gallery:

- `card_le_two_pow_card_of_covers`: a finite set `S` whose subset sums cover the
  initial segment `[0, N)` satisfies `N ≤ 2^|S|` (inject the `N` values into
  `S.powerset` via distinct sums). The combinatorial core.
- `h_le_card_divisors`: `h(m) ≤ d(m)` for practical `m` (the full divisor set
  covers, so its cardinality is in the `sInf` set).
- `le_two_pow_h`: `m ≤ 2^{h(m)}` for practical `m` (equivalently `h(m) ≥ log₂ m`);
  the `sInf` is attained (`Nat.sInf_mem`) and the counting bound applies.
- `one_le_h`, `h_one` (`h(1) = 0`).
- `powers_subset_sum` (binary covering of `[0, 2^k)` by `{1,…,2^{k-1}}`),
  `h_two_pow_le` (`h(2^k) ≤ k`), and **`h_two_pow`** — `h(2^k) = k` exactly, the
  first exact value of the Erdős #18 function. It is one *fewer* than
  `d(2^k) = k+1`: the top divisor `2^k` is never needed.

## Blockers
- The asymptotic density of practical numbers (`h(m)`, Vose / Mertens-type bounds)
  needs analytic number theory beyond elementary reach.
- The general question "how small can `h(m)` be relative to `d(m)` for structured
  `m` (e.g. `m = n!`)?" is the open $250 problem and out of elementary reach; the
  bracket `log₂ m ≤ h(m) ≤ d(m)` proved here is the elementary envelope.
- Full Stewart–Sierpiński multiplicative criterion still not reachable with current
  machinery (needs full `[0,σ(m)]` coverage + gcd analysis).

## Next Action
Options: (a) exact `h` for other structured families — `h(2^a · 3^b)` or
`h(m·n)` sub-additivity (`h(m·n) ≤ h(m) + h(n)`?, from concatenating covering
sets); (b) `h(m) ≥ d(m) - c` type gaps or abundancy-based refinements; (c) the
greedy sorted-divisor full-range theorem (larger project).
