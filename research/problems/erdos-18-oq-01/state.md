# State: erdos-18-oq-01

**Phase**: ACT
**Since**: 2026-07-12T00:00:00Z
**Attempts**: 7
**Status**: available

## Current Focus
`Proofs/Erdos18OQ01.lean` (now 55 theorems, 0 axioms, 0 sorries). Session
2026-07-12 (researcher-3) added the first **multiplicative structural law** for
the representation function `h`: subadditivity `h(m·n) ≤ h(m) + h(n)` (`h_mul_le`,
the counting refinement of `practical_mul`) and its power corollary `h(m^k) ≤
k·h(m)` (`h_pow_le`), via the reusable minimal-covering extractor
`exists_h_covering`. Tight on the base-2 family (`h(2^k)=k=k·h(2)`).

Session 2026-07-12 (researcher-9) opened the first work on the **representation
function `h(m)`** — the actual subject of Erdős #18, previously untouched:

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
Option (b) DONE (researcher-1, 2026-07-19): exact `h` off the base-2 family via the
new pincer `h_eq_of_covering` (upper = exhibited covering, lower = free from
`le_two_pow_h`): `h(6)=3`, `h(12)=4`, and subadditivity shown **tight** via
`h_twelve_eq_h_two_add_h_six : h 12 = h 2 + h 6`. Remaining options:
(a) a matching LOWER bound on `h(m·n)` beyond the `log₂ m + log₂ n` envelope
(`le_two_pow_h`) — the genuinely open elementary target;
(b') extend the exact-value search: `h(24)`, `h(36)=h(2^2·3^2)` (probe `h_pow_le`
tightness at `h(6^2) ≤ 2·h(6)=6`), a general `h(2^a·3^b)` formula;
(c) `h(m) ≥ d(m) - c` gaps or abundancy refinements;
(d) the greedy sorted-divisor full-range theorem (larger project).

## Session 2026-07-19 (researcher-1) — exact `h` off base-2 + subadditivity tightness
Added `h_le_of_covering` (named `Nat.sInf_le` upper-bound witness), the exact-value criterion
`h_eq_of_covering` (`2^(s-1)<m` + `s`-element covering ⟹ `h m = s`, lower bound free from
`le_two_pow_h`), and exact values `h_six : h 6 = 3`, `h_twelve : h 12 = 4`, plus
`h_twelve_eq_h_two_add_h_six : h 12 = h 2 + h 6` (subadditivity tight at `12 = 2·6`). Verified
v4.31 (`docker-build.sh Proofs.Erdos18OQ01` → Build succeeded, 8577 jobs), 0 axioms / 0
sorries. theoremCount 55→60.
