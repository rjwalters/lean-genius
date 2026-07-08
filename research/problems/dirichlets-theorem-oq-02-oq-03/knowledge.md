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

### Session 2026-07-08 (Session 2, researcher-1) — certified linear lower bound

Re-served the already-completed slug. Added two verified theorems bracketing the
k-th prime ≡ 3 (mod 4):
- `p3_ge_linear : 4*k + 3 ≤ p3 k` — since the `p3` values are strictly increasing
  and all ≡ 3 (mod 4), consecutive ones differ by ≥ 4. One-line induction: feed
  `p3_lt_succ`, `p3_mod k`, `p3_mod (k+1)` to `omega` (omega reasons mod-4).
- `p3_bracketed : 4*k + 3 ≤ p3 k ∧ p3 k ≤ B k` — combines the new lower bound with
  the existing tower upper bound; the true value `∼ 2k·ln k` sits between them.
File 250 L, 23 thm / 3 def, 0 axioms, 0 sorries. VERIFIED (rotating olean
corruption: line-less 135 then named Cyclotomic/Discriminant.olean.private invalid
header → rm + retry green).

### Session 2026-07-08 (Session 3, researcher-1) — counting-function lower bound

Advanced the "Next Steps" item from Session 1: bounded the **counting function**
`π(x;4,3)` from below (dual to the k-th-prime bounds). 3 verified theorems + 1 def,
0 axioms, `native_decide`-free.
- `def countP3 x := #{n ≤ x : Nat.Prime n ∧ n % 4 = 3}` (Finset.range (x+1) filter).
- `countP3_ge (K x) (hx : 4^(2^K) ≤ x) : K+1 ≤ countP3 x` — inject the K+1 distinct
  primes `p3 0 < ⋯ < p3 K` (each `≤ p3 K ≤ 4^(2^K)` by `p3_le_doubly_exp`) into the
  counted set via `Finset.range (K+1) |>.image p3 ⊆ filter …`, `card_image_of_injective`
  with `p3_strictMono.injective`, then `Finset.card_le_card`. Certifies `π(x;4,3) ≳
  log₂log₄x` (truth `∼ x/(2 ln x)`, needs analytic PNT-for-APs).
- `countP3_unbounded K : ∃ x, K ≤ countP3 x` — take `x = 4^(2^K)`, one-liner.
- `countP3_sixteen : countP3 16 = 3 := by decide` — kernel decide (NOT native_decide,
  stays 0-axiom); shows the bound `≥2` from `countP3_ge 1` is loose (true = {3,7,11}).

File now 851 L, 59 thm/lemma, 6 def, 0 axioms, 0 sorries. VERIFIED (first build
line-less exit-135 SIGBUS after [7743/7743] 3.9s no elab errors = fleet volume
corruption; retry at MEM=24576 built green in 9.0s, zero proof changes).

**Recipe (reusable):** to turn a strict-mono enumeration bound `f k ≤ g k` into a
counting-function lower bound, inject `(range (K+1)).image f` into the filtered
Finset and count via `card_image_of_injective ∘ StrictMono.injective` + `card_le_card`;
the membership proof only needs `f k ≤ f K ≤ g K ≤ x` (monotone + the height bound).
