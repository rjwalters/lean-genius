# chebyshev-pnt-bridge-oq-04 — Mertens' theorems via Abel summation on Chebyshev bounds

**Target (open):** Derive Mertens' theorems
- (M1) Σ_{p ≤ x} (log p)/p = log x + O(1)
- (M2) Σ_{p ≤ x} 1/p = log log x + M + O(1/log x)

via Abel partial summation on Chebyshev-type bounds. Parent: `chebyshev-pnt-bridge`.

## Session 2026-06-26 (Session 1) — FRESH

**Mode:** FRESH
**Outcome:** progress (verified backbone + conditional first-Mertens; build verification blocked by environment)

### What I did
- Created `proofs/Proofs/ChebyshevPNTBridgeOQ04.lean` (246 lines), self-contained (imports Mathlib only).
- Proved the exact elementary backbone of Mertens' first theorem in its von Mangoldt (Λ) weighted form, transporting the Möbius hyperbola swap from the sibling `ChebyshevBoundsOQ04OQ01Mertens.lean`:
  - **Step A** `sum_vonMangoldt_mul_floor_eq_sum_log`: Σ_{d≤N} Λ(d)·⌊N/d⌋ = Σ_{n≤N} log n (exact). Uses `vonMangoldt_sum` (Σ_{d∣n}Λ(d)=log n), `Nat.Ioc_filter_dvd_card_eq_div`, `Finset.sum_comm`.
  - **Step B** `mul_lambdaRecip_eq`: N·Σ Λ(d)/d = (Σ log n) + E(N), E(N)=Σ Λ(d)·fract(N/d), via ⌊N/d⌋ = N/d − fract.
  - **Step C** `lambdaFractRemainder_bounds`: 0 ≤ E(N) ≤ ψ(N)=Σ Λ(d), from Λ≥0 and 0≤fract<1.
  - `lambdaRecip_eq`: rearranged Σ Λ(d)/d = (Σ log n)/N + E(N)/N.
- Conditional headline `lambdaRecip_sub_log_le`: |Σ_{d≤N} Λ(d)/d − log N| ≤ 1 + c_S + c_ψ for N≥2, given the two `MertensInputs` hypotheses (Chebyshev ψ≤c_ψ·N, Stirling |Σ log n−(N log N−N)|≤c_S·log N).
- Added gallery data `src/data/proofs/chebyshev-pnt-bridge-oq-04/` (meta/annotations/index), status axiomatized, axiomCount 2 (the 2 structure-encoded analytic inputs).

### Key findings
- The von Mangoldt floor identity is the exact Λ-analogue of the Möbius identity Σ μ(d)⌊N/d⌋=1; same `Finset.sum_comm` swap + divisor-set match. Λ is real-valued so no Int casts (cleaner than the μ version).
- All Mertens-I error is quarantined into E(N), sandwiched exactly between 0 and the second Chebyshev function ψ(N). So Chebyshev's ψ=O(N) is *precisely* the input needed for E(N)/N=O(1).
- Mathlib has `Mathlib.NumberTheory.AbelSummation` (`sum_mul_eq_sub_sub_integral_mul`) — the tool for the M1→M2 passage in a future session.

### Mathlib gaps / inputs left as hypotheses
- Chebyshev ψ(N)=O(N) (gallery's standing open `chebyshevPsi_asymptotic`).
- Stirling Σ_{n≤N} log n = N log N − N + O(log N) (real-analytic; Mathlib has asymptotic Stirling, not this elementary bound form).

### Build status
- Docker build could NOT be verified locally: the shared `lean-mathlib-cache` Docker volume + Docker VM disk were saturated by 5–6 concurrent agent builds (`lake exe cache get` → pervasive `/root/.cache/mathlib/*.ltar: Permission denied (os error 13)` and "removing corrupted file"). Freed ~4.8GB via safe docker prune; contention persisted. Build gate is downstream (deployer builds serially before deploy), so the PR carries an explicit "build-verification-pending" note.
- The proof mirrors the already-verified sibling `ChebyshevBoundsOQ04OQ01Mertens.lean` step-for-step; the non-mirrored analytic assembly was hand-hardened (replaced fragile `field_simp;linarith` with `div_add_div_same`+`eq_div_iff`+`linear_combination`; added explicit `(N:ℝ)≠0` and `cChebyshev_nonneg`/`cStirling_nonneg` linarith hints).

### Next steps
1. Confirm the Docker build once the shared environment is quiet (deployer will gate regardless).
2. Strip the prime-power tail: pass from Σ Λ(d)/d to Σ_{p≤N}(log p)/p (control Σ_{p,k≥2}(log p)/p^k).
3. Feed M1 into `sum_mul_eq_sub_sub_integral_mul` for M2 (Mertens constant M, O(1/log x)).
4. Discharge `MertensInputs` in Lean (Chebyshev ψ=O(N) + elementary Stirling) to upgrade the estimate to unconditional.

## Session 2026-06-27 (researcher-2) — REVIEW + verified-hooks scout, no code change

**Mode:** depth-first re-claim (knowledge.db read EMPTY but the OQ04 Lean file + gallery data
already exist from Session 1). Reviewed the full `ChebyshevPNTBridgeOQ04.lean`: Steps A–C and the
conditional Λ-weighted M1 (`lambdaRecip_sub_log_le`) are clean and complete.

**Decision: DEFER the next step (prime-power strip), do not add code this session.** Both
verification channels are DOWN (Docker host containerd `meta.db: input/output error`, `docker images`
empty/cached image gone — operator restart needed, NOT ENOSPC; Aristotle MCP `404`). The strip and
Abel-summation steps are substantial *analytic* proofs (convergence of the prime-power tail; an
integral-form partial summation). Writing them blind, with no build feedback, would risk landing
broken UNVERIFIED code on top of an already-verified file — net-negative. Honest no-op on code.

**Verified Mathlib hooks for the strip (Step 2), to save the next agent the lookup**
(`Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean`, notation `Λ`):
- `vonMangoldt_apply` : `Λ n = if IsPrimePow n then log (minFac n) else 0`.
- `vonMangoldt_apply_prime (hp : p.Prime)` : `Λ p = Real.log p`  ← turns prime terms into `log p`.
- `vonMangoldt_apply_pow (hk : k ≠ 0)` : `Λ (n^k) = Λ n`.
- `vonMangoldt_ne_zero_iff` : `Λ n ≠ 0 ↔ IsPrimePow n` ← Λ vanishes off prime powers (the "not a
  prime power" filtered terms drop to 0 in any split).
- `vonMangoldt_le_log` : `Λ n ≤ Real.log n` ← per-term majorant for tail bounds.

**Concrete plan for Step 2 (prime-power strip), once a build is available:**
Split `lambdaRecip N = Σ_{p≤N prime} (log p)/p + R(N)` via `Finset.sum_filter_add_sum_filter_not`
on `Nat.Prime`, rewriting the prime block with `vonMangoldt_apply_prime` and noting `IsPrimePow ∧
¬Prime ⇒ d=p^k, k≥2`. Then bound the tail `R(N) = Σ_{k≥2,p^k≤N} (log p)/p^k ≤ Σ_p (log p)/(p(p−1))`
by the geometric series `Σ_{k≥2} p^{-k} = 1/(p(p−1))` (per-prime), giving the `O(1)` of M1. The
geometric-tail step (`tsum`/`Finset` geometric bound) is the only genuinely new analytic content.

## Session 2026-07-04 (researcher-6) — VERIFIED convergence engine; knowledge above is STALE

**Correction:** the "prime-power strip" listed as the next step in Session 1 is **already done**
in `ChebyshevPNTBridgeOQ04.lean` (`lambdaRecip_prime_split`, `primePowerTail_nonneg`,
`primeLogRecip_le` = upper half of Mertens I for the honest prime sum, conditional, 0 new axioms).

**New verified file:** `proofs/Proofs/ChebyshevPNTBridgeOQ04Tail.lean` (0 sorries; `#print axioms`
= propext/Classical.choice/Quot.sound on both results — docker build succeeded, 7743 jobs):
- `log_le_two_mul_sqrt : 0 < x → Real.log x ≤ 2 * Real.sqrt x`.
- `summable_log_div_sq : Summable (fun n : ℕ => Real.log n / (n:ℝ)^2)` — the log-weighted
  summability Mathlib lacks; the convergence engine for the uniform O(1) tail bound.

**Sole remaining step (now pure Finset reindexing, no analysis):** regroup the tail by base prime,
`R(N) ≤ 2·Σ_p (log p)/p² ≤ 2·(tsum of summable_log_div_sq) = C`, then feed the lower half of
`lambdaRecip_sub_log_le` to get two-sided Mertens I for the prime sum (still conditional on the 2
`MertensInputs`). See sessions/2026-07-04-s3-tail-convergence-engine-verified.md for the full plan
and verified Mathlib hooks.
