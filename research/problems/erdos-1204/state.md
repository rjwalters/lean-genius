# Current State

**Phase**: ACT
**Since**: 2026-06-25
**Iteration**: 7

## Current Focus

Extending the exact-value frontier A(k) = min largest element of an admissible k-tuple
(= Hardy–Littlewood minimal diameter H(k)). Values now A(2)=2, A(3)=6, A(4)=8, A(5)=12,
A(6)=16, A(7)=20, **A(8)=26** (this iteration), each in an axiom-free companion file.

## Active Approach

Finite case analysis combining small primes. Iteration 7 (2026-07-11) closed
**A(8) = 26 EXACT** (`Erdos1204A8.lean`, `A_eight`), upgrading the previous file which
had only the upper bound `A(8) ≤ 26` and a weak `A(8) ≥ 21` (one-step monotonicity),
explicitly left as future work.

This is the first frontier value where the prime **7 becomes binding**. The lower bound
(max ≤ 25 ⇒ 8-set in a 13-element single-parity window {0,2,…,24} / {1,3,…,25}): the
mod-3 classes now have sizes **5,4,4** (vs 4,3,3 at A(7)).
- Missing the size-5 class leaves exactly 8 slots = one *forced* 8-set, which is
  mod-5-complete ⇒ killed at p=5.
- Missing a size-4 class leaves a 9-element pool. Four of its five mod-5 classes have
  two elements and one is a singleton; an admissible 8-subset must miss a mod-5 class,
  but a two-element class can't be dropped by removing a single element, so the missed
  class is the singleton — pinning the 8-subset to a *forced* set that is mod-7-complete
  ⇒ killed at p=7. (Even branches mod3≡1,2 and odd branches mod3≡0,2 each give one.)

Helper `not_admissible_of_covers` (a set hitting every class mod p is not admissible,
`decide`-checked at concrete p) cleanly kills all forced sets.

## Blockers

The headline asymptotics A(k) ∼ k log k and the B(k) estimate remain OPEN — they need
analytic sieve theory (summing p/(p−1) factors / CRT counting) not yet formalized. The
per-value frontier keeps advancing but the case analysis grows with each new prime.

Infra note (2026-07-11): the shared docker Mathlib-cache volume STILL has the SIGBUS
(exit 135) corruption — this session it failed at `Mathlib.Algebra.CharP.Frobenius`
(`unexpected end of input` on the `.trace` file) during cache download/decompress. A(8)
was verified via the **host-lake bypass**: symlink existing `Proofs/*.olean` into a tmp
LEAN_PATH root, then `~/.elan/.../v4.26.0/bin/lean Proofs/Erdos1204A7.lean -o …` then
`…A8.lean` (host Mathlib oleans are intact). `#print axioms A_eight` = only
propext/Classical.choice/Quot.sound (axiom-free; `decide`, not `native_decide`).

## Next Action

A(9)=30 (H(9)=30, back to +4). Lower bound: 15-element parity windows {0,2,…,28} /
{1,3,…,29}; mod-3 class sizes 5,5,5. Expect p=7 firmly binding and the case analysis to
grow again — worth factoring a generic "single-parity window minus one mod-p class"
helper (pool → forced set → killed by next prime) before A(9)/A(10) to tame growth.

## Attempt Counts

- Total attempts: 7
- Current approach attempts: 2
- Approaches tried: 2
