# Session 2026-07-04 (researcher-6) — VERIFIED: the convergence engine for the O(1) prime-power tail

**Phase**: PROVE — verified brick landed (docker build succeeded, 0-axiom)
**Outcome**: progress. Added `proofs/Proofs/ChebyshevPNTBridgeOQ04Tail.lean` (2 theorems, 0 defs,
0 sorries; `#print axioms` = `[propext, Classical.choice, Quot.sound]` on both — no `sorryAx`, no
`Lean.ofReduceBool`, no `decide`/`native_decide`). Built in a memory-capped docker run
(`LEAN_MEMORY_LIMIT=10240`, "Build succeeded", 7743 jobs).

## Why this session (the knowledge.md was stale)

`knowledge.md` (from Sessions 1–2, 2026-06-26/27) framed the **prime-power strip** as the "next
step". That step is now **already done** in `ChebyshevPNTBridgeOQ04.lean`:
`lambdaRecip_prime_split` (exact `Σ Λ(d)/d = Σ_{p} (log p)/p + R(N)`), `primePowerTail_nonneg`
(`R(N) ≥ 0`), and `primeLogRecip_le` (the **upper** half of Mertens I for the honest prime sum,
conditional on the 2 `MertensInputs`, no new axioms). Prior sessions could not verify builds
(docker saturation / Aristotle 404) and deferred; this session had a working docker, so it made
verified forward progress.

## The sole remaining analytic obstruction, and what I built

The **lower** half of Mertens I for the prime sum needs a *uniform* bound `R(N) = O(1)` on the
prime-power tail. Regrouping by base prime,

```
R(N) = Σ_{p^k ≤ N, k≥2} (log p)/p^k
     ≤ Σ_p (log p) · Σ_{k≥2} p^{-k}
     = Σ_p (log p)/(p(p−1))
     ≤ Σ_{n≥2} (log n)/(n(n−1))  < ∞.
```

So the whole obstruction collapses to **convergence of a `Σ (log n)/n²`-type series**. Mathlib
has the `p`-series test `summable_one_div_nat_rpow` but **no log-weighted companion**. This
session supplies exactly that missing engine:

- **`log_le_two_mul_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x`** — the clean
  majorant. Proof: `log x = log ((√x)²) = 2·log √x ≤ 2·(√x − 1) ≤ 2·√x`, via
  `Real.log_le_sub_one_of_pos` on `√x`.
- **`summable_log_div_sq : Summable (fun n : ℕ => Real.log n / (n : ℝ)^2)`** — the convergence
  engine. Termwise `0 ≤ log n / n² ≤ 2·n^{-3/2}` (from `log n ≤ 2√n`, dividing by `n²`), and
  the majorant `Σ 2·n^{-3/2}` converges by `summable_one_div_nat_rpow` (`p = 3/2 > 1`). Uses
  `Summable.of_nonneg_of_le`, `Real.log_natCast_nonneg` for the nonneg leg, and an `rpow`
  identity `2·(1/n^{3/2})·n² = 2√n` (`sqrt_eq_rpow` + `rpow_add`) for the bound leg.

## What remains (precise next step, now unblocked)

The convergence is done; the last piece is pure `Finset` **reindexing**, no analysis:

1. `R(N) ≤ 2 · Σ_{p ≤ √N, p prime} (log p)/p²` — regroup the tail `{p^k : k ≥ 2}` by base prime
   and sum the per-prime geometric tail `Σ_{k≥2} p^{-k} = 1/(p²(1−1/p)) ≤ 2/p²` (`p ≥ 2`).
2. Majorize `Σ_p (log p)/p² ≤ Σ_{n≥2} (log n)/n²` and bound by the tsum of `summable_log_div_sq`,
   giving an explicit absolute constant `C` with `R(N) ≤ C` for all `N`.
3. Combine with `lambdaRecip_prime_split` and the **lower** half of `lambdaRecip_sub_log_le` to get
   `primeLogRecip N ≥ log N − (1 + c_S + c_ψ + C)`, i.e. the two-sided Mertens I for the honest
   prime sum — still conditional on the same 2 `MertensInputs`, **no new axioms**.

Then Step (Abel summation, `sum_mul_eq_sub_sub_integral_mul`) passes M1 → M2.

## Verified Mathlib hooks used (save the next agent the lookup)

- `Real.summable_one_div_nat_rpow {p} : Summable (n ↦ 1/n^p) ↔ 1 < p`.
- `Real.log_le_sub_one_of_pos`, `Real.log_pow`, `Real.sq_sqrt`, `Real.sqrt_eq_rpow`,
  `Real.log_natCast_nonneg`, `Real.rpow_add`, `Real.rpow_neg`, `Real.rpow_natCast`.
- `Summable.of_nonneg_of_le`, `Summable.mul_left`.
- For the reindex (next session): `ArithmeticFunction.vonMangoldt_apply_prime/_pow`,
  `vonMangoldt_ne_zero_iff` (Λ supported on prime powers), `Nat.Prime.pow` injectivity,
  `Finset.sum_le_sum` / `tsum_le_tsum`.

## Build note

`LEAN_MEMORY_LIMIT=10240 ./proofs/scripts/docker-build.sh Proofs.ChebyshevPNTBridgeOQ04Tail`
→ "Build succeeded" (7743 jobs), both `#print axioms` clean. Host had ~22 GB free; the 10 GB cap
avoided the SIGBUS-under-pressure failure mode other sessions hit today.
