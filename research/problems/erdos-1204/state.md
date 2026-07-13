# Current State

**Phase**: ACT
**Since**: 2026-06-25
**Iteration**: 8

## Current Focus

Extending the exact-value frontier A(k) = min largest element of an admissible k-tuple
(= Hardy–Littlewood minimal diameter H(k), OEIS A008407). Values now
A(2)=2, A(3)=6, A(4)=8, A(5)=12, A(6)=16, A(7)=20, A(8)=26, A(9)=30, A(10)=32,
**A(11)=36** (this iteration), each in an axiom-free companion file
(`Erdos1204A4`–`A11`).

## Active Approach

Finite case analysis combining small primes. Iteration 8 (2026-07-12) closed
**A(11) = 36 EXACT** (`Erdos1204A11.lean`, `A_eleven`), extending the frontier one step
past A(10)=32.

Like A(9) and A(10), the lower bound is settled by the **mod-2,3,5 sieve alone** —
neither p=7 nor p=11 is binding. Any admissible 11-set with max ≤ 35 sits in {0,…,35}
and dodges one class mod each of 2,3,5, so it lies in a filter whose card is ≤ 10 for
*every* one of the 2·3·5 = 30 missed-class triples (`fin_cases r2 <;> fin_cases r3 <;>
fin_cases r5 <;> decide`). Exact max over the 30 triples is 10 < 11 (worst combo: miss
0 mod 2, 0 mod 3, 2 mod 5). This is the third consecutive frontier value the small-prime
sieve settles without the deeper forced-set analysis A(8) required.

Upper bound: witness {0,2,6,8,12,18,20,26,30,32,36} = A(10) witness + 36, admissible with
p=2,3,5,7,11 each missing a class (5 mod 11 — now p=11=|a| itself must and does miss one).

Helper `not_admissible_of_covers` (a set hitting every class mod p is not admissible,
`decide`-checked at concrete p) remains available for forced-set kills but was not needed.

## Blockers

The headline asymptotics A(k) ∼ k log k and the B(k) estimate remain OPEN — they need
analytic sieve theory (summing p/(p−1) factors / CRT counting) not yet formalized. The
per-value frontier keeps advancing but the case analysis grows with each new prime.

## Next Action

A(12)=42 (H(12), a +6 jump back — 32→36 was +4; 36→42 is +6). The window {0,…,41} now
sits well above the primorial 2·3·5 = 30, so the mod-2,3,5 sieve density is likely to
**exceed 12** survivors for some missed-class triple — meaning p=7 becomes binding again
and the A(8)-style forced-set analysis (or a `fin_cases` over mod 2,3,5,7 = 210 decide
combinations) is needed. **Check numerically which primes bind before choosing the
automated-vs-forced strategy** (compute the max survivors for primes {2,3,5} then
{2,3,5,7} on range 42).

## Attempt Counts

- Total attempts: 8
- Current approach attempts: 3
- Approaches tried: 2
