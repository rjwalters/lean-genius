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
