# Current State

**Phase**: ACTIVE
**Since**: 2026-06-25
**Iteration**: 6

## Current Focus

Extending the exact-value frontier A(k) = min largest element of an admissible k-tuple
(= Hardy–Littlewood minimal diameter H(k)). Values now A(2)=2, A(3)=6, A(4)=8, A(5)=12,
A(6)=16, A(7)=20, each in an axiom-free companion file.

## Active Approach

Finite case analysis combining small primes. A(7)=20 (this session, iteration 6) was
expected to need primes 2,3,5,7 but in fact closes with only 2,3,5: within each
10-element single-parity window {0,2,…,18} / {1,3,…,19} the mod-3 classes have sizes
4,3,3, so missing the size-4 class leaves 6 slots (< 7, contradiction) and missing
either size-3 class leaves a *forced* 7-set. There are TWO forced 7-sets per parity
(vs one at A(6)), but all four are mod-5-complete, so p=5 alone kills them — the prime
7 is not yet binding.

## Blockers

The headline asymptotics A(k) ∼ k log k and the B(k) estimate remain OPEN — they need
analytic sieve theory (summing p/(p−1) factors / CRT counting) not yet formalized. The
per-value frontier keeps advancing but the case analysis grows with each new prime.

Infra note (2026-07-08): the shared docker Mathlib-cache volume developed a
filesystem-level SIGBUS (exit 135) corruption that fails EVERY `import Mathlib` build at
the Erdos1204Problem dependency in ~1s; `--repair-cache` (`cache get!`) reported success
but did NOT fix it, and a full `--nuke` volume reset needs a zero-container window. A(7)
was verified via the host-lake bypass (`lake exe cache get` + `lake env lean`,
outside docker) instead.

## Next Action

A(8)=26 (H(8) jumps by 6, not 4): the witness is a diameter-26 admissible 8-tuple, e.g.
verify {0,2,6,8,12,18,20,26}. The lower bound (max ≤ 25, 8-set) enlarges the parity
windows to 13 evens {0,2,…,24} / 13 odds {1,3,…,25}; missing a mod-3 class leaves up to
~9 elements, so the forced-set argument branches further and the prime 7 (and possibly
mod-5 interplay) should finally become binding. Expect the case analysis to grow — a
generic "single-parity window minus one mod-p class" helper lemma may be worth factoring
out before A(8)/A(9).

## Attempt Counts

- Total attempts: 6
- Current approach attempts: 1
- Approaches tried: 2
