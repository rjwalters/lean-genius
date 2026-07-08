# Current State

**Phase**: ACTIVE
**Since**: 2026-06-25
**Iteration**: 5

## Current Focus

Extending the exact-value frontier A(k) = min largest element of an admissible k-tuple
(= Hardy–Littlewood minimal diameter H(k)). Verified values now A(2)=2, A(3)=6, A(4)=8,
A(5)=12, A(6)=16, each in an axiom-free companion file.

## Active Approach

Finite case analysis combining small primes. A(6)=16 (this session) is the first value
whose lower bound needs THREE primes: parity + mod 3 no longer close it (a single-parity
6-set inside {0..15} can dodge mod 3), so the two forced 6-sets are killed by covering
all classes mod 5. This realizes the "combine primes 2 and 3" direction one prime further.

## Blockers

The headline asymptotics A(k) ∼ k log k and the B(k) estimate remain OPEN — they need
analytic sieve theory (summing p/(p−1) factors / CRT counting) not yet formalized. The
per-value frontier keeps advancing but the case analysis grows with each new prime.

## Next Action

A(7)=20: needs primes 2,3,5,7 combined in the lower bound. Find/verify a diameter-20
admissible 7-tuple witness, then adapt the parity → mod-3 → mod-5 (→ mod-7) slot-count.

## Attempt Counts

- Total attempts: 5
- Current approach attempts: 1
- Approaches tried: 2
