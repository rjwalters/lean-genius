# Current State

**Phase**: ACT (S4b step-4 *Tonelli interchange* `tsum_integral_weight_trunc_sq_le` SHIPPED & VERIFIED — the `∑'ᵢ`–`∫` swap itself is now done; remaining: integrate the dominating `g` to `C·𝔼|X|ᵖ`, then S5 assembly + step-3 centering + final combination)
**Since**: 2026-07-04
**Iteration**: 13 (S4b step-4 **Tonelli interchange** `tsum_integral_weight_trunc_sq_le` `∑'ᵢ ∫ i^{-s}·(𝟙{|X|≤i^{1/p}}·X)² ≤ ∫ (max 1 |X|ᵖ)^{1-s}·s/(s-1)·X²` — the actual measure-theoretic `∑'`–`∫` swap via `MeasureTheory.integral_tsum`, dominating the inner sum by iter-12 `tsum_weight_trunc_sq_le`, finiteness side-goal via `lintegral_tsum`+`ofReal_tsum_of_nonneg`, `g` left as an integrability hypothesis — SHIPPED & build-VERIFIED, 0-axiom, 7743 jobs; iter 12 pointwise integrand `tsum_weight_trunc_sq_le`; iter 11 inner-tail bound `tsum_indicator_ge_rpow_neg_le`; iter 10 inclusive tail `tsum_ge_rpow_neg_le`; iter 9 exclusive backbone `∑_{j>N}j^{-s}≤N^{1-s}/(s-1)`; step-3/4 kernels; step-1 truncation; step-2 tail-sum; S4a variance L¹-bound; S3 martingale; S2 Kronecker; S1 survey)

## Current Focus

**S2 (Kronecker), S3 (Kolmogorov martingale assembly), S4a (variance L¹ bound),
S4b step-2 (tail-sum) and S4b step-1 (i.i.d. truncation) are ALL DONE — do not
re-derive any.** All in `proofs/Proofs/LawsOfLargeNumbersOQ01OQ02OQ01.lean`,
verified 0-sorry / 0-axiom (only propext/Classical.choice/Quot.sound).

## S4b step-1 — DONE (iteration 7, this session)

The **i.i.d. Borel–Cantelli truncation reduction** — connecting the step-2 tail-sum bound
to the actual truncation event — is now in the file (§ TruncationReduction), all
**0-sorry / 0-axiom** (`#print axioms` = propext/Classical.choice/Quot.sound on all three):

- `rpow_inv_lt_iff_lt_rpow` — elementary threshold reindex `a^{1/p} < b ↔ a < bᵖ`
  (`0<p`, `0≤a`, `0≤b`), via `Real.rpow_lt_rpow_iff` + `Real.rpow_inv_rpow`.
- `tsum_measure_truncation_ne_top_of_identDistrib` — for i.i.d. `Xᵢ` with `𝔼|X₀|ᵖ<∞`,
  the truncation tail sum `∑ᵢ μ{i^{1/p} < |Xᵢ|} ≠ ∞`. Proof: transfer each tail measure
  to `X₀` (`IdentDistrib.measure_mem_eq` on the measurable set `{y | i^{1/p}<|y|}`),
  reindex to `{i < |X₀|ᵖ}` (`rpow_inv_lt_iff_lt_rpow`), peel the `i=0` term
  (`tsum_eq_zero_add'`, bounded by `1`), and dominate the rest by
  `tsum_measure_add_one_ne_top` (step 2) with `Z=|X₀|ᵖ`.
- `ae_eventually_abs_le_rpow_of_identDistrib` — feeds the finiteness into
  `MeasureTheory.ae_eventually_notMem` ⟹ `∀ᵐ ω, ∀ᶠ i, |Xᵢ ω| ≤ i^{1/p}`, the exact
  Borel–Cantelli output reducing MZ to its truncated version.

**Do NOT re-derive.** The truncation is now justified: a.s. `Xᵢ = Yᵢ` eventually where
`Yᵢ = Xᵢ·𝟙{|Xᵢ| ≤ i^{1/p}}`.

### Reusable gotcha (Mathlib v4.26)

- **`Summable.tsum_eq_zero_add` (dot form) is `whnf`-pathological** on a
  `μ {ω | … }`-valued summand: `rw [Summable.tsum_eq_zero_add ENNReal.summable]` blows past
  1 000 000 heartbeats at `whnf`, *even on a fully abstract `g : ℕ → ℝ≥0∞`* and even when
  stated as a fully-typed `have`. **Fix: use the primed, non-dot idiom
  `rw [tsum_eq_zero_add' ENNReal.summable]`** (this is exactly how Mathlib's own
  `Topology/Instances/ENNReal/Lemmas.lean` peels ENNReal tsums). Compiles instantly.

## S4b steps 3–4 (kernels) — SHIPPED & VERIFIED (iteration 8 written r14, verified r8)

> **VERIFICATION STATUS: VERIFIED (researcher-8, 2026-07-04).** The disk-full blocker
> cleared (9.3 Gi free); `./proofs/scripts/docker-build.sh Proofs.LawsOfLargeNumbersOQ01OQ02OQ01`
> → **Built (7743 jobs, 54s, exit 0)**. Both kernels are pure `Real.rpow` real-analysis
> with no `decide`/`native_decide`/`sorry`/`axiom` and depend only on already-0-axiom
> Mathlib lemmas, so 0-axiom by construction (`propext`/`Classical.choice`/`Quot.sound`).

The two **pointwise truncation-moment kernels** — the analytic hearts of the two
remaining S4b estimates — are now in the file (§ TruncationMomentKernels), pure
real-analysis (no measure theory), 0-sorry / 0-`axiom`, machine-checked:

- `abs_le_rpow_mul_rpow_of_tail` — **step-3 kernel (centering):** for `1 ≤ p`,
  `0 < t`, `t < |x|`, one has `|x| ≤ t^{1-p} · |x|^p`. Proof: split
  `|x| = |x|^p·|x|^{1-p}` (`Real.rpow_add`), then `1-p ≤ 0` + `0 < t < |x|` give
  `|x|^{1-p} ≤ t^{1-p}` (`Real.rpow_le_rpow_of_nonpos`). With `t = i^{1/p}` this is
  the pointwise bound behind `|𝔼Yᵢ| ≤ i^{(1-p)/p}·𝔼|X|^p` (a
  `tendsto_weighted_average_zero`-summable null sequence).
- `sq_le_rpow_mul_rpow_of_trunc` — **step-4 kernel (variance):** for `p < 2`,
  `0 < t`, `|x| ≤ t`, one has `x² ≤ t^{2-p} · |x|^p`. Proof: `x=0` is RHS-nonneg;
  else split `x² = |x|^p·|x|^{2-p}` (`Real.rpow_add`, `sq_abs`, `Real.rpow_natCast`),
  then `0 ≤ 2-p` + `0 < |x| ≤ t` give `|x|^{2-p} ≤ t^{2-p}` (`Real.rpow_le_rpow`).
  With `t = i^{1/p}` this is the pointwise bound behind `𝔼[Yᵢ²] ≤ i^{(2-p)/p}·𝔼|X|^p`;
  the `p < 2` hypothesis enters exactly through the sign `0 ≤ 2-p`, making the scaling
  factor super-linear so `∑ᵢ i^{-2/p}` converges.

**Do NOT re-derive.** The two pointwise inequalities are settled and verified; the
surviving work is the *integral-level* lift of each (indicator/`integral_mono` plumbing
to reach `|𝔼Yᵢ|` and `𝔼[Yᵢ²]`), then the two sums, then assembly.

## Active Approach

None in-flight. Next work item is the integral lift of the two kernels below.

## Blockers

- **S4b step-3 integral lift (~1 session):** turn `abs_le_rpow_mul_rpow_of_tail` into
  `|𝔼Yᵢ| ≤ i^{(1-p)/p}·𝔼|X|^p` (via `𝔼X = 0` ⟹ `𝔼Yᵢ = -𝔼[X·𝟙{|X|>i^{1/p}}]`,
  `abs_integral_le`, `integral_mono` against the kernel), then
  `∑_{i<n} 𝔼Yᵢ / n^{1/p} → 0` via `tendsto_weighted_average_zero` with the null
  sequence `cᵢ = 𝔼[|X|^p·𝟙{|X|>i^{1/p}}] → 0` and weight `i^{(1-p)/p}` (needs the
  weight partial-sum asymptotic `∑_{i<n} i^{1/p-1} ~ p·n^{1/p} → ∞`).
- **S4b step-4 integral lift (~1–2 sessions):** turn `sq_le_rpow_mul_rpow_of_trunc`
  into `𝔼[Yᵢ²] ≤ i^{(2-p)/p}·𝔼|X|^p` (`integral_mono` on `Yᵢ² = Xᵢ²·𝟙{|Xᵢ|≤i^{1/p}}`),
  then `Var(Yᵢ) ≤ 𝔼[Yᵢ²]` and `∑ᵢ Var(Yᵢ)/i^{2/p} ≤ 𝔼|X|^p · ∑ᵢ i^{-2/p} < ∞`
  (Mathlib `Real.summable_one_div_nat_rpow` / `summable_nat_rpow`, `2/p > 1`).
- **Assembly:** `ae_tendsto_average_zero_of_variance_weighted_bdd` (S5) on the centered
  truncations `Yᵢ − 𝔼Yᵢ`, combined with step-1's a.s. eventual `Xᵢ = Yᵢ` and step-3's
  centering control, gives the full M–Z SLLN.

**DONE (do not re-derive):** S1 survey · S2 Kronecker · S3 martingale · **S4a variance
L¹-bound** (`ae_tendsto_sum_of_indep_of_variance_bdd` + `eLpNorm_two_sq_eq_evariance` +
`eLpNorm_two_partialSum_le`) · **S4b step-2 tail-sum** · **S4b step-1 i.i.d. truncation**
· **S4b step-3/step-4 pointwise moment kernels** (this iteration). All 0-axiom.

## ⚠️ Correction to the previous plan (iteration 9)

The prior "Next Action" claimed `∑ᵢ Var(Yᵢ)/i^{2/p} < ∞` needs only `integral_mono` + a
Mathlib `∑ i^{-2/p}` convergence lemma applied **per-term**. **That route diverges.** The
step-4 kernel gives `𝔼[Yᵢ²] ≤ (i^{1/p})^{2-p}·M = i^{(2-p)/p}·M`; dividing by `aᵢ² = i^{2/p}`
leaves `M·i^{(2-p)/p − 2/p} = M·i^{-1}`, and `∑ i^{-1}` **diverges**. So `integral_trunc_sq_le`
alone is NOT summable term-by-term. The classical argument instead does a **Tonelli
interchange**: keep the truncated moment `𝔼[X²·𝟙{|X| ≤ i^{1/p}}]` intact and sum the *weight*
`i^{-2/p}` against the indicator, giving
`∑ᵢ i^{-2/p} 𝔼[X²𝟙{|X|≤i^{1/p}}] = 𝔼[X² ∑_{i ≥ |X|ᵖ} i^{-2/p}] ≤ C·𝔼[X²·|X|^{p-2}] = C·M`.

## Next Action

- **S4b step-4 Tonelli interchange is now DONE (iteration 13):** `tsum_integral_weight_trunc_sq_le`
  supplies, for `1<s`, `0<p`, measurable `X`, and an integrable dominating `g`, the **actual
  `∑'ᵢ`–`∫` swap**
  `∑'ᵢ ∫ i^{-s}·(𝟙{|X|≤i^{1/p}}·X)² ≤ ∫ (max 1 |X|ᵖ)^{1-s}·s/(s-1)·X²`, via
  `MeasureTheory.integral_tsum` with the finiteness side-goal discharged by
  `lintegral_tsum`+`ENNReal.ofReal_tsum_of_nonneg` and the inner sum dominated by iter-12
  `tsum_weight_trunc_sq_le`. **Do not re-derive.** The dominating `g` is a hypothesis, not yet
  discharged.
- **Next: integrate the dominating `g`** at `s = 2/p` (the one remaining step-4 analytic step).
  Prove `∫ (max 1 |X|ᵖ)^{1-2/p}·s/(s-1)·X² ≤ C·(𝔼|X|ᵖ + 𝔼X²)` (or `≤ C·𝔼|X|ᵖ` on a probability
  space via `MemLp X 2`): `|X|≥1` branch `(max 1 |X|ᵖ)^{1-2/p}=|X|^{p-2}` so `X²·bound=|X|ᵖ →
  𝔼|X|ᵖ`; `|X|<1` branch collapses to `const·X² → const·𝔼X²`. This discharges
  `tsum_integral_weight_trunc_sq_le`'s `hg` and yields `∑ᵢ 𝔼[Yᵢ²]/i^{2/p} ≤ C·𝔼|X|ᵖ`. Then bridge
  `variance(Yᵢ)/aᵢ² ≤ 𝔼[Yᵢ²]/i^{2/p}` and feed `ae_tendsto_average_zero_of_variance_weighted_bdd`
  (S5). Watch weight positivity (use `aᵢ=(i+1)^{1/p}` or `max 1 i^{1/p}`).
- **Then: step-3 centering** (via `integral_tail_abs_le` + `tendsto_weighted_average_zero`) and
  the final combination with the step-1 truncation reduction into the MZ statement.

## Attempt Counts

- Total attempts: 13 (S1 survey; S2 Kronecker; S3 martingale assembly; +glue; S4a variance L¹ bound; S4b step-2 tail-sum; S4b step-1 i.i.d. truncation; S4b step-3/4 moment kernels; S4b step-4 tail p-series backbone; iter-10 inclusive tail; iter-11 pointwise inner-tail bound; iter-12 pointwise Tonelli integrand; iter-13 Tonelli interchange `tsum_integral_weight_trunc_sq_le`)
- Current approach attempts: 1 (S4b step-4 Tonelli interchange `tsum_integral_weight_trunc_sq_le` — `integral_tsum` to move `∑'ᵢ` inside; finiteness `hf'` via `simp_rw [Real.enorm_eq_ofReal]`+`← lintegral_tsum`+`ENNReal.ofReal_tsum_of_nonneg`+`hasFiniteIntegral_iff_enorm`; inner-sum domination by iter-12 `tsum_weight_trunc_sq_le` after `Set.indicator_apply`+`ring` reconciling ω- vs index-indicator; final `integral_mono_of_nonneg`; one fix — `enorm_eq_ofReal*` needed `Real.` prefix — then clean build, 7743 jobs, 0-axiom)
- Approaches tried: 7 (S1 literature/decomposition; S2 Abel+Toeplitz;
  S3 natural-filtration martingale + upcrossing engine; S4a orthogonality + eLpNorm bridge;
  S4b step-2 discrete layer cake via lintegral_tsum + floor count;
  S4b step-1 IdentDistrib transfer + rpow reindex + tsum peel + first Borel–Cantelli;
  S4b step-3/4 pointwise rpow kernels via rpow_add split + rpow_le_rpow(_of_nonpos))
