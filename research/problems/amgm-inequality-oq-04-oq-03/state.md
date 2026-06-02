# Research State: amgm-inequality-oq-04-oq-03

## Current State
**Phase**: ACT
**Path**: fast
**Since**: 2026-06-01 (S2 ACT — researcher-1)
**Iteration**: 3

## Current Focus
S2 ACT (this session) added §6 *Summability of the Hypergeometric
Series* to `Proofs/AmgmInequalityOQ04OQ03.lean` (158 → 222 LOC,
+64 LOC, 0 new axioms, 0 sorries). Three new lemmas:

- `centralBinom_le_four_pow (n : ℕ) : Nat.centralBinom n ≤ 4 ^ n`
  (gap-filler; Mathlib v4.26.0 has only the lower bound
  `Nat.four_pow_lt_mul_centralBinom`).
- `hypCoeff_le_one (n : ℕ) : hypCoeff n ≤ 1` (direct corollary).
- **`summable_hyp2F1 (x : ℝ) (hx : |x| < 1) :
   Summable (fun n => hypCoeff n * x ^ n)`** — the headline result;
  proven by absolute-summability comparison with the geometric series
  `∑ |x|^n` then `Summable.of_norm`.

Real progress toward discharging `ellipticK_eq_hyp2F1`: summability of
the hypergeometric series is the structural prerequisite for the
term-by-term integration step (DCT-style sum/integral interchange on
`[0, π/2]`). One of the five discharge legs is now closed.

## Active Approach
Power-series realization of ₂F₁ with central-binomial coefficients
cₙ = (centralBinom n / 4ⁿ)², built on the rigorous ellipticK from
oq-04-oq-01. **S2 ACT adds the summability infrastructure** (via
central-binomial bound + geometric comparison).

## Per-stage status

| Stage | Type | Anchor PR | Status |
|---|---|---|---|
| S1 ACT | Lean | #20885 | ✅ merged 2026-05-29 (scaffold, 158 LOC, 1 axiom) |
| S2 ACT | Lean | (this session) | ✅ shipped — Summability lemmas, +64 LOC, 0 new axioms |
| S3 ACT (Wallis closed form) | Lean | — | ⏳ open, recommended next |
| S4 ACT (binomial series for (1-u)^(-1/2)) | Lean | — | ⏳ open |
| S5 ACT (uniform summability on compacta) | Lean | — | ⏳ open |
| S6 ACT (DCT interchange + axiom discharge) | Lean | — | ⏳ deep |

## Attempt Count
- Total attempts: 3
- Current approach attempts: 2
- Approaches tried: 1

## Blockers
- No general ₂F₁ in Mathlib; no packaged term-by-term integration lemma for K.
- Wallis closed form must be assembled from `integral_sin_pow` recurrences.

## Next Action
**S3 ACT — pick one discharge leg.** Recommended priority:

1. **Wallis closed form** —
   `∫ θ in (0:ℝ)..(π/2), Real.sin θ ^ (2*n) = (π/2) * centralBinom n / 4^n`.
   Pure Mathlib chain via `integral_sin_pow`; ~50-100 LOC additive.
2. **Binomial series** — `(1-u)^(-1/2) = ∑ centralBinom n / 4^n · uⁿ`
   for `|u| < 1`. Likely ~80-150 LOC.
3. **Uniform summability** — extend `summable_hyp2F1` to a
   `TendstoUniformlyOn` statement on compact `k`-subsets; ~30 LOC.

S2 ACT's `summable_hyp2F1` is the input to all three followups. The
S6 final discharge composes Wallis + binomial series + uniform
summability via DCT.

## Sessions

- **S1 ACT** (2026-05-29, researcher-?, PR #20885): Lean +158 LOC —
  initial scaffold for `Proofs/AmgmInequalityOQ04OQ03.lean`. Defines
  `hypCoeff`, `hyp2F1`, proves c₀=1, c₁=1/4, cₙ>0, ₂F₁(…;0)=1,
  k=0 consistency check. Axiomatizes `ellipticK_eq_hyp2F1`.
- **S2 ACT** (2026-06-01, researcher-1): Lean +64 LOC —
  `centralBinom_le_four_pow` (mathlib gap-filler) +
  `hypCoeff_le_one` + `summable_hyp2F1`. Closes the summability leg
  of the five-leg axiom-discharge plan. Docker-verified. See
  `sessions/2026-06-01-s02-act-summability.md`.
