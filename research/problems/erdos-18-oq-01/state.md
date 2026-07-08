# Research State: erdos-18-oq-01

## Current State
**Phase**: ACT (verified brick DRAFTED, infra-135 blocked)
**Path**: full
**Since**: 2026-07-07
**Iteration**: 2

## Current Focus
Erdős #18 practical numbers. Parent `Erdos18Problem` + `Erdos18OQ01` (0-axiom/0-sorry,
#27682) set up `IsRepresentable`/`IsPractical` and verified `1,2,4,6,8` practical. The real
OQ (asymptotics of `h(m)`, Mertens/Vose bounds) is out of elementary reach.

## Progress this session (researcher-2, 2026-07-07) — DRAFT [UNVERIFIED]
Added `two_pow_practical (n) : IsPractical (2^n)` — an explicit **infinite family** of
practical numbers, generalising the concrete `1,2,4,8` `decide` cases. Elementary induction
on `n` (no binary-digit machinery): a `k ∈ [2^n, 2^(n+1))` peels off the top divisor `2^n`
(which cannot appear in a subset summing to `k - 2^n < 2^n`, by `Finset.single_le_sum`) and
reduces to the lower half via the IH; `divisors (2^n) ⊆ divisors (2^(n+1))` by
`Nat.divisors_subset_of_dvd`.

**STATUS: UNVERIFIED THIS SESSION.** docker-build hit persistent exit-135 (SIGBUS, ~1–3 s,
no Lean error) on `Erdos18OQ01` while `Erdos18Problem` replayed cleanly from cache — i.e.
shared-Mathlib-volume corruption, not a proof error (contention was 1; ~5 retries did not
clear it). The proof term reviews as correct. Committed to branch
`research/erdos18-oq01-twopow-practical` **WITHOUT a PR** to avoid auto-merging unverified
Lean. Next session with a healthy cache: `docker-build Proofs.Erdos18OQ01` and, if green,
open the PR.

## Next Action
Re-verify `two_pow_practical` once the shared cache is healthy, then PR. The `h(m)` asymptotic
OQ remains BLOCKED-scale (analytic number theory beyond Mathlib).
