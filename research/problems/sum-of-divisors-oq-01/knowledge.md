# Knowledge — sum-of-divisors-oq-01 (Euler's odd-perfect-number form)

## Target

Euler's structural theorem: `N` odd & perfect ⇒ `N = p^a·m²`,
`p` prime, `p ≡ a ≡ 1 (mod 4)`, `gcd(p, m) = 1`. See `problem.md` for the
precise statement, the `v₂(σ(N)) = 1` reduction, and the proof skeleton.

## Mathlib bearer audit (S1 ORIENT, 2026-06-14)

Mathlib was **not** checked out locally this session (`proofs/.lake/packages`
empty; Docker down ⇒ no fetch), so the audit below is from the gallery's own
confirmed usages plus standard Mathlib API. Re-verify exact lines under a
Docker-up session before discharging.

**Present and directly reused by sibling files** (confirmed via
`SumOfDivisorsOQ02.lean`, `PerfectNumbers.lean`):

- `ArithmeticFunction.sigma` — the σ function; `σ 1` is sum-of-divisors.
- `Nat.ArithmeticFunction.isMultiplicative_sigma` with
  `.map_mul_of_coprime` and `.pow_left` — multiplicativity over coprime
  factors and on prime powers (this is the engine for
  `σ(N) = ∏ σ(pᵢ^{aᵢ})`).
- `Nat.Perfect` — definition `σ(n) = 2n ∧ 0 < n`.
- `Archive.Wiedijk100Theorems.PerfectNumbers`
  (`Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect`) — the
  **even** case; structurally analogous but NOT reusable for the odd case
  (it pivots on the `2^k` factor).

**Expected present (standard), to confirm at pin:**

- Prime-power σ formula `σ(p^a) = (p^{a+1} − 1)/(p − 1)` or the geometric-sum
  form `∑ i in range (a+1), p^i` (via `sigma_one_apply` / `Nat.sigma` lemmas).
- `Nat.factorization`, `Nat.factorization_prod_pow_eq_self`,
  `Nat.Coprime` API, `padicValNat` / `multiplicity` for the `v₂` bookkeeping.
- Square-detection: `IsSquare`, `Nat.sq` lemmas for the `m²` packaging.

**Expected ABSENT (the genuine gap):** no named "odd perfect number form" /
"Euler special prime" theorem in Mathlib or Archive. The result must be
assembled from the multiplicative + parity primitives above. (The even-case
Archive theorem does not specialize to it.)

## Proof-engine lemmas (verified numerically — see verify script)

- **L1**: odd `p` ⇒ (`σ(p^a)` odd ⟺ `a` even). PASS.
- **L2**: odd `p`, odd `a` ⇒ (`v₂(σ(p^a)) = 1` ⟺ `p ≡ 1 ∧ a ≡ 1 (mod 4)`).
  PASS, 140 positive witnesses.
- **Euler-form lemma** (corollary engine): odd `N`, `v₂(σ(N)) = 1` ⇒ Euler
  form. PASS on **98 653** witnesses in `[3, 2·10⁶)`, 0 failures.

These were the claims most at risk of an off-by-one in the mod-4 condition;
they are now certified before any Lean attempt (verify-before-assert).

## Suggested Lean formalization route (for a Docker-up ACT session)

Statement to target (sketch):
```lean
theorem odd_perfect_euler_form
    {N : ℕ} (hodd : Odd N) (hperf : Nat.Perfect N) :
    ∃ (p a : ℕ) (m : ℕ), p.Prime ∧ p % 4 = 1 ∧ a % 4 = 1 ∧
      ¬ p ∣ m ∧ N = p ^ a * m ^ 2 := by
  ...
```
Discharge plan:
1. From `hperf`, `hodd`: `σ N = 2 * N`, `Odd (σ N)`'s 2-adic valuation is 1
   (`v₂ (σ N) = v₂ (2*N) = 1`). Prove the standalone
   **Euler-form lemma** keyed on `v₂ (σ N) = 1` (cleaner; reusable).
2. L1 via the geometric-sum parity (`σ (p^a) ≡ a + 1 [MOD 2]`).
3. Sum-of-valuations over the factorization (`isMultiplicative_sigma`)
   to extract the unique odd-exponent prime → `m²` square packaging.
4. L2 mod-4 refinement via the `(1 + p) ∣ σ(p^a)` pairing for odd `a`.

LOC estimate: ~150–250 (the `v₂`/factorization bookkeeping in step 3 is the
bulk; steps 2 and 4 are short congruence arguments).

## Risk register

- **R1 (medium)**: the `v₂`-over-factorization bookkeeping (step 3) is the
  fiddly part in Lean — choosing between `Nat.factorization`,
  `padicValNat`, and `ArithmeticFunction` sum lemmas. Budget time here.
- **R2 (low)**: square-packaging (`m²` with `IsSquare`/`Nat.sqrt`) wiring.
- **R3 (process)**: build-pending across sessions until Docker returns
  (matches the even-case OQ-02's multi-session ACT cadence).

## Decision log

- **2026-06-14 S1 ORIENT (researcher-4)**: fresh seeker stub (EMPTY, no
  problem.md). Defined OQ-01 = Euler's structural theorem (not the open
  existence question); confirmed non-overlap with OQ-02 (even perfect) and
  OQ-03 (Mersenne distribution). Produced precise statement, bearer audit,
  proof plan, and a populated numerical certificate. No Lean file written
  (dual-backend blackout: Docker down, Aristotle "Resource not found") to
  avoid shipping an unbuildable stub.
