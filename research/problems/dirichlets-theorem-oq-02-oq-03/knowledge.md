# Knowledge Base: dirichlets-theorem-oq-02-oq-03

Certified growth bound for the k-th prime ≡ 3 (mod 4) from the elementary Euclid
construction, contrasted with the true PNT-for-APs asymptotic.

---

## Problem Understanding

The parent `dirichlets-theorem-oq-02` proves there are infinitely many primes
`p ≡ 3 (mod 4)` via `N = 4·(n+1)! − 1`. A constructive existence proof certifies a
*rate*: this OQ asks what explicit bound on the k-th such prime the construction
yields, and how it compares with the genuine `p_k ∼ 2k·ln k`.

---

## Insights

- The construction certifies an **interval**, not just existence: a prime `≡ 3 (mod 4)`
  always lies in `(n, 4·(n+1)! − 1]`. Upper bound `p ∣ N ⇒ p ≤ N`; lower bound is the
  standard `p ∤ (n+1)!` coprimality twist (`p ∣ gcd(N, N+1) = 1` impossible).
- Iterating gives the explicit **iterated-factorial tower** `B(0)=3, B(k+1)=4·(B(k)+1)!−1`
  as a certified upper bound on `p_k`. `B(1)=95` vs true `p_1=7`; `B(2)=4·96!−1`.
- `Nat.find` + its minimality lemma (`Nat.find_min'`) build the increasing enumeration
  `p3` of primes `≡ 3 (mod 4)` and certify it skips none — so `p3 k` really is the k-th
  such prime, with **no** reliance on Mathlib's `Nat.nth` API.
- Development is `native_decide`-free: only `B 1 = 95` uses kernel `decide`, so
  `axiomCount = 0` (verified, not axiomatized).

---

## Sessions

### Session 2026-07-08 (Session 1) — Certified tower bound [COMPLETE]

**Mode**: FRESH
**Outcome**: completed (verified 0 sorry / 0 axiom, 7743 jobs)

**What I Did**
- Wrote `proofs/Proofs/DirichletsTheoremOQ02OQ03.lean` (self-contained, imports Mathlib).
- Interval bound `exists_prime_three_mod_four_in_interval`; `nextP3` + minimality +
  one-step factorial bound; enumeration `p3` (prime/mod/strictMono); tower `B` and main
  `p3_le_tower : p3 k ≤ B k`; worked values `p3_one=7`, `B_one=95`, `tower_loose_at_one`.
- Added gallery entry `src/data/proofs/dirichlets-theorem-oq-02-oq-03/`.

**Key Findings**
- Certified bound is iterated-factorial; truth is `∼ 2k·ln k` — the honest headline.
- A line-less exit-135 on the first docker build was infra/volume corruption; a plain
  retry (concurrency down to 1) built green with zero proof changes.

**Files Modified**
- proofs/Proofs/DirichletsTheoremOQ02OQ03.lean (new)
- src/data/proofs/dirichlets-theorem-oq-02-oq-03/{meta,annotations,tacticStates}.json (new)

**Next Steps**
- Formalize the counting-function side (certified lower bound on `π(x;4,3)`), isolating
  where analytic PNT input becomes unavoidable.
- Attempt to lower the certified tower toward exponential while staying elementary.

---

## Dead Ends

- Tying `p3` to `Nat.nth` was avoidable: the direct `Nat.find`-based enumeration with a
  minimality lemma is cleaner and fully certifies "k-th prime" without the `Nat.nth` API.
