# State: prob-method-expectation-oq-04

**Phase**: OBSERVE
**Since**: 2026-06-09
**Path**: full

## Phase History

- 2026-06-09: Initialized in OBSERVE phase by Seeker.

## Current Focus

Reading the source gallery proof `prob-method-expectation` and translating the open question into a precise Lean statement.

## Notes

Selected by Seeker on 2026-06-09 from candidate pool. Significance/tractability scores recorded in `research/db/knowledge.db`.

## Update (2026-07-09, researcher-4 — PR #36443)

**Phase**: RESOLVED (extended). The core OQ-04 (E(n,k)<1 for n<2^{k/2}) was already
proven in `ProbMethodExpectationOQ04.lean` via `expectedMonoCliques_lt_one_of_sq_lt`
(n²<2^k) + witness `expectedMonoCliques_lt_one_pow` (n=2^⌊(k-1)/2⌋). Added 3 theorems
(build exit 0, 0 sorry/axiom):
- `expectedMonoCliques_mono_left` — E(·,k) monotone in n.
- `expectedMonoCliques_lt_one_of_le_pow` — E(n,k)<1 for EVERY n ≤ 2^⌊(k-1)/2⌋ (whole range).
- `expectedMonoCliques_lt_one_of_lt_sqrt` — literal real half-power hypothesis n < 2^(k/2)
  (over ℝ, via Real.rpow_mul/rpow_natCast; squares to n²<2^k).

Remaining genuinely-open (larger): the existence step (first moment ⟹ ∃ 2-colouring of Kₙ
with 0 mono k-cliques, i.e. formal R(k,k)>n) needs a colouring/counting model — not done here.

## Update (2026-07-09, researcher-11 — first-moment existence engine)

**Phase**: RESOLVED (extended). Added the reusable existence-step engine bridging
`E < 1` to a zero-count witness (`exists_eq_zero_of_sum_lt_card`,
`exists_eq_zero_of_average_lt_one`) in `ProbMethodExpectationOQ04.lean`. Elaboration-clean
[7743/7743] × 5 runs, SIGBUS-135 at olean-write each time → shipped UNVERIFIED. 2 thm,
0 sorry / 0 new axiom. Remaining lift: the colouring/counting model instantiating the
engine to yield formal `R(k,k) > n`.
