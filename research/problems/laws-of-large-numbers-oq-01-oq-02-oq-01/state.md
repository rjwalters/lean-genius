# Current State

**Phase**: ACT (S5 CENTERING BRIDGE + step-3 NULL SEQUENCE + step-3 TAIL-RESTRICTED INTEGRAL LIFT now SHIPPED. Remaining for step-3 centering `(∑𝔼Yᵢ)/aₙ→0`: (i)(b) centering identity `𝔼X=0`⟹`𝔼Yᵢ=−𝔼[X𝟙{|X|>aᵢ}]` so `|𝔼Yᵢ| = |∫X𝟙{|X|>aᵢ}| ≤ ∫𝟙{|X|>aᵢ}·|X|` [`integral_sub`/`integral_add` split truncation vs identity, `abs_integral_le_integral_abs`, `abs_of...`]; chain with new `integral_tail_abs_le_tail_moment` ⟹ `|𝔼Yᵢ| ≤ aᵢ^{1-p}·eᵢ`; (ii) weight partial-sum bound `∑_{i<n}(i+1)^{(1-p)/p} ≤ Aₙ` for the Toeplitz `hdom` at normaliser `aₙ=(n+1)^{1/p}`; then feed `tendsto_weighted_average_zero` with `cᵢ=aᵢ^{1-p}`, `eᵢ=tendsto_integral_tail_rpow_zero`→0. Then final combination with step-1 truncation.)
**Since**: 2026-07-04
**Iteration**: 22 (STEP-3 TAIL-RESTRICTED INTEGRAL LIFT — 1 new 0-axiom leaf `integral_tail_abs_le_tail_moment` in § TruncationIntegralLifts, docker build 7743 jobs exit 0 [note: transient SIGBUS exit-135 during `--json` output flush on ~2/3 runs — RE-RUN, elaboration is deterministic], `#print axioms`=propext/Classical.choice/Quot.sound: for measurable `X`, `1≤p`, `0<t`, `Integrable |X|ᵖ`, the tail absolute integral is bounded by `t^{1-p}` times the **tail-restricted** `p`-moment: `∫𝟙{t<|X|}·|X| ≤ t^{1-p}·∫𝟙{t<|X|}·|X|ᵖ`. This is the SHARP form of `integral_tail_abs_le` (which bounds by the FULL moment `M=∫|X|ᵖ`, constant/non-vanishing): here the RHS integrand is exactly `eₜ=∫𝟙{t<|X|}·|X|ᵖ`, the null sequence `tendsto_integral_tail_rpow_zero`→0, so at `t=aᵢ=(i+1)^{1/p}` it is the `tendsto_weighted_average_zero` input `|𝔼Yᵢ|≤aᵢ^{1-p}·eᵢ` with a VANISHING factor — the full-moment bound `aᵢ^{1-p}·M` alone gives a divergent Cesàro weight. Proof: the pointwise kernel `abs_le_rpow_mul_rpow_of_tail` already lives on the tail `{t<|X|}`, so restricting BOTH sides to that set via `Set.indicator_apply`×2 + `split_ifs` preserves it — kernel verbatim on the tail, `0≤t^{1-p}·0` (`simp`) off it; tail moment integrable as `hint.indicator hset` [`hset=measurableSet_lt measurable_const hX.abs`], then `integral_mono_of_nonneg`+`hintTail.const_mul`+`integral_const_mul`. Same 3-line calc skeleton as `integral_tail_abs_le`. PR r6.) (prior: iter 21 STEP-3 NULL SEQUENCE — 1 new 0-axiom leaf `tendsto_integral_tail_rpow_zero` in § TailMomentNull, docker build 7743 jobs exit 0, `#print axioms`=propext/Classical.choice/Quot.sound: for measurable `X`, `Integrable |X|ᵖ`, ANY threshold seq `t i→∞`, the tail `p`-moments `∫ 𝟙{t i<|X|}·|X|ᵖ → 0`. Proof by **dominated convergence** `MeasureTheory.tendsto_integral_of_dominated_convergence` [ARG ORDER: `bound, hF_meas, bound_integrable, h_bound, h_lim` — NOT `h_bound` before `bound_integrable`]: tail integrand `≤ |X|ᵖ` in norm [`Real.norm_eq_abs`+`Set.indicator_apply`+`split_ifs`], and for each fixed `ω` the indicator is EVENTUALLY 0 [`ht.eventually_gt_atTop |X ω|`: once `t i>|X ω|` indicator vanishes] so integrands→0 pointwise [`(tendsto_congr' hev).mpr tendsto_const_nhds`]; `f:=fun _=>0`⟹`∫f=0` by `simpa`. At `t i=(i+1)^{1/p}` [`mz_normaliser_tendsto`] this is EXACTLY the `tendsto_weighted_average_zero` null sequence `eᵢ=𝔼[|X|ᵖ𝟙{|X|>aᵢ}]→0` driving MZ step-3 centering. PR r6.) (prior: iter 20 S5 CENTERING BRIDGE — 1 new 0-axiom leaf `ae_tendsto_centered_average_zero_of_variance_weighted_bdd`, docker build 7743 jobs exit 0, `#print axioms`=propext/Classical.choice/Quot.sound: takes indep L² `Y` [NOT mean-zero], pos/mono/→∞ weight `a`, `∑Var(Yᵢ)/aᵢ²≤V` ⟹ a.s. `(∑_{i<n}(Yᵢ−𝔼Yᵢ))/aₙ→0`. Applies the iter≤18 S5 engine `ae_tendsto_average_zero_of_variance_weighted_bdd` to `Zᵢ=Yᵢ−𝔼Yᵢ`: measurability/L²/indep transfer by const-subtraction [`StronglyMeasurable.sub`/`MemLp.sub`/`iIndepFun.comp`], `𝔼Zᵢ=0` by `integral_sub`+`integral_const`, and **`Var(Zᵢ)=Var(Yᵢ)` by Mathlib `variance_sub_const`** — the translation-invariance brick prior iters flagged as "still to build" ALREADY EXISTS in Mathlib v4.26 [`AEStronglyMeasurable X`, `IsProbabilityMeasure μ`], so the whole centering step is one-line bookkeeping and the supplied `hV` feeds S5 verbatim. This closes the "instantiate S5 on centered truncations" gap iter-19 flagged as the ONLY remaining S5 obstacle. PR r6.) (prior: iter 19 S5 NUMERIC INPUTS — four 0-axiom leaves, docker build 7743 jobs exit 0, `#print axioms`=propext/Classical.choice/Quot.sound: **`summable_trunc_sq_weight_shift_of_integrable`** the shifted real summability `Summable (fun i => ((i+1)^{1/p})⁻²·∫(𝟙{|X|≤(i+1)^{1/p}}·X)²)`, from iter-17 `summable_trunc_sq_weight_of_integrable` via `(summable_nat_add_iff 1).mpr` [dropping the i=0 term the bare normaliser `i^{1/p}` zeroes] then `.congr` identifying `f(i+1)`=target by `push_cast` `((i+1:ℕ):ℝ)=(i:ℝ)+1` + exponent bookkeeping `(((i+1)^{1/p})²)⁻¹=(i+1)^{-2/p}` via `Real.rpow_natCast`/`Real.rpow_mul`/`Real.rpow_neg` — this is EXACTLY S5's `hV` total at `a=(i+1)^{1/p}` [feed it through iter-18 (b) brick `weighted_variance_partial_sum_le_tsum`]; **`mz_normaliser_pos`** (needs NO p-hyp, base>0), **`mz_normaliser_mono`** (`Real.rpow_le_rpow`+`1/p≥0`), **`mz_normaliser_tendsto`** (`tendsto_rpow_atTop (div_pos one_pos hp)`∘`(i+1)→∞`) — the three S5 shape hyps for `aᵢ=(i+1)^{1/p}`. PR r8. **All numeric S5 inputs now in hand; the ONLY remaining S5 gap is the centering rework — mean-zero forces `Zᵢ=Yᵢ−𝔼Yᵢ`, not raw truncations, with `Var(Zᵢ)=Var(Yᵢ)`.** prior: iter 18 (S5 HAND-OFF — two 0-axiom leaves in § WeightedVariancePartialSum, docker build 7743 jobs exit 0, `#print axioms` = propext/Classical.choice/Quot.sound: **`variance_trunc_le_integral_sq`** the (a) brick `Var(𝟙{|X|≤t}·X) ≤ ∫(𝟙{|X|≤t}·X)²` via Mathlib `variance_le_expectation_sq` on the truncation's `AEStronglyMeasurable` (`exact` closes it, `μ[Y^2]`↔`∫(Y ω)^2` by defeq); **`weighted_variance_partial_sum_le_tsum`** the (b) brick — for ANY `a:ℕ→ℝ` and summability of `i↦(aᵢ²)⁻¹∫(𝟙{|X|≤aᵢ}·X)²`, `∀n, ∑_{i≤n}Var(Yᵢ)/aᵢ² ≤ ∑'ᵢ(aᵢ²)⁻¹∫Yᵢ²` via per-term `div_eq_mul_inv`+`mul_le_mul_of_nonneg_left` on the (a) brick then `Finset.sum_le_sum`+`Summable.sum_le_tsum` (nonneg summand); **aᵢ=i^{1/p} doubles as threshold AND weight so the leaf is abstract in `a` and needs NO a-positivity** (division-by-zero-is-zero); this is exactly S5's `hV`. This CLOSES the two (a)/(b) gaps state.md flagged under "Next: feed S5". iter 17 S4b step-4 **real `Summable` hand-off** `summable_trunc_sq_weight_of_integrable`: for `Integrable |X|ᵖ`, `0<p<2`, finite measure, the real weighted variance sequence `i ↦ i^{-2/p}·∫(𝟙{|X|≤i^{1/p}}·X)²` is `Summable` — `ENNReal.summable_toReal` on the iter-16 ℝ≥0∞ finiteness, each `.toReal` term identified via `ofReal_integral_eq_lintegral_ofReal` [per-term integrability from new reusable `integrable_trunc_sq`: truncation bounded by `t`, `Integrable.mono'` vs `integrable_const t²` on finite measure] + `integral_const_mul` const-pull + `ENNReal.toReal_ofReal` — SHIPPED & build-VERIFIED, 0-axiom, 7743 jobs, PR #34421. **This is the real `∑ᵢ 𝔼[Yᵢ²]/aᵢ² < ∞` the S5 criterion consumes.** iter 16 S4b step-4 **ℝ≥0∞ finiteness** `tsum_lintegral_trunc_sq_weight_lt_top`: for `Integrable |X|ᵖ`, `0<p<2`, the weighted variance sum `∑'ᵢ ∫⁻ i^{-2/p}·(𝟙{|X|≤i^{1/p}}·X)² < ∞` — `.trans_lt` the iter-15 master bound then `ENNReal.mul_lt_top ENNReal.ofReal_lt_top` with moment factor finite via `(hasFiniteIntegral_iff_ofReal hnn).mp hint.hasFiniteIntegral` (`hnn` by `Real.rpow_nonneg`) — SHIPPED & build-VERIFIED, 0-axiom, 7743 jobs, PR #34406; iter 15 master bound `lintegral_tsum_trunc_sq_weight_le_moment`; iter 14 RHS-integrand domination `trunc_rpow_weight_sq_le_rpow`; iter 13 S4b step-4 **Tonelli interchange** `lintegral_tsum_trunc_sq_weight_le`: `∑'ᵢ ∫⁻ i^{-s}·(𝟙{|X|≤i^{1/p}}·X)² ≤ ∫⁻ (max 1 |X|ᵖ)^{1-s}·s/(s-1)·X²` — `MeasureTheory.lintegral_tsum` pushes `∑'ᵢ` inside the lower integral (unconditional for nonneg, sidestepping Bochner `integral_tsum`'s `∑∫‖·‖<∞` which is the very finiteness sought), then `lintegral_mono` dominates the pointwise `∑'ᵢ` by iter-12 `tsum_weight_trunc_sq_le` at `x=X ω` via `ENNReal.ofReal_tsum_of_nonneg` — SHIPPED & build-VERIFIED, 0-axiom, 7743 jobs; iter 12 pointwise integrand `tsum_weight_trunc_sq_le` `∑ᵢ 𝟙{|x|≤i^{1/p}}·(i^{-s}·x²) ≤ (max 1 |x|ᵖ)^{1-s}·s/(s-1)·x²` — the exact per-`ω` summand of the variance series, root-form region `{i|`|x|`≤i^{1/p}}` bridged to power-form `{i|`|x|ᵖ`≤i}` — SHIPPED & build-VERIFIED, 0-axiom, 7743 jobs; iter 11 inner-tail bound `tsum_indicator_ge_rpow_neg_le`; iter 10 inclusive tail `tsum_ge_rpow_neg_le`; iter 9 exclusive backbone `∑_{j>N}j^{-s}≤N^{1-s}/(s-1)`; step-3/4 kernels; step-1 truncation; step-2 tail-sum; S4a variance L¹-bound; S3 martingale; S2 Kronecker; S1 survey)

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

- **S4b step-4 Tonelli interchange is now DONE (iteration 13):** `lintegral_tsum_trunc_sq_weight_le`
  supplies, for measurable `X`, `1<s`, `0<p`, the **master lower-integral estimate**
  `∑'ᵢ ∫⁻ ω, i^{-s}·(𝟙{|X|≤i^{1/p}}·X)² ≤ ∫⁻ ω, (max 1 |X|ᵖ)^{1-s}·s/(s-1)·X²`. Proof:
  `MeasureTheory.lintegral_tsum` (per-term measurability only — **unconditional for nonneg
  summands**, deliberately avoiding Bochner `integral_tsum` whose `∑'ᵢ∫‖·‖<∞` side goal is the
  very finiteness we seek) pushes `∑'ᵢ` inside `∫⁻`; then `lintegral_mono` dominates the pointwise
  `∑'ᵢ` by iter-12 `tsum_weight_trunc_sq_le` at `x=X ω`, pulling `ENNReal.ofReal` through the real
  tsum via `ENNReal.ofReal_tsum_of_nonneg` (per-`ω` summand summable: an indicator of the `i^{-s}`
  `p`-series scaled by `X ω ^ 2`). **Do not re-derive.**
- **RHS-integrand pointwise domination core is now DONE (iteration 14):**
  `trunc_rpow_weight_sq_le_rpow` — for `0<p<2`, any `x`, the interchange integrand core at
  `s=2/p` is dominated by `|x|ᵖ`: `(max 1 |x|ᵖ)^{1-2/p}·x² ≤ |x|ᵖ`. Two branches, both under
  `|x|ᵖ`: `|x|≥1` gives equality `(|x|ᵖ)^{1-2/p}·|x|²=|x|^{(p-2)+2}=|x|ᵖ` (`Real.rpow_mul`+
  `rpow_add`, exponent `p·(1-2/p)+2=p` by `field_simp;ring`); `|x|<1` splits `|x|²=|x|ᵖ·|x|^{2-p}`
  (`Real.rpow_add_of_nonneg`) with `|x|^{2-p}≤1` (`Real.rpow_le_one`). **Do not re-derive.**
- **Master variance-sum bound is now DONE (iteration 15):** `lintegral_tsum_trunc_sq_weight_le_moment`
  collapses the whole weighted sum to a constant times the `p`-th moment (in ℝ≥0∞):
  `∑'ᵢ ∫⁻ i^{-2/p}·(𝟙{|X|≤i^{1/p}}·X)² ≤ ofReal((2/p)/(2/p-1)) · ∫⁻ |X|ᵖ`. Proof: chain
  `lintegral_tsum_trunc_sq_weight_le` at `s=2/p` (`hs: 1<2/p` via `lt_div_iff₀`), `lintegral_const_mul'`
  (const pull, needs only `ofReal_ne_top` — no measurability), `lintegral_mono` + `ENNReal.ofReal_mul`
  + `trunc_rpow_weight_sq_le_rpow`. **This is the quantitative `∑ᵢ Var(Yᵢ)/aᵢ² ≤ C·𝔼|X|ᵖ`.**
  **Do not re-derive.**
- **ℝ≥0∞ finiteness extraction is now DONE (iteration 16, PR #34406):**
  `tsum_lintegral_trunc_sq_weight_lt_top` — for measurable `X`, `0<p<2`, and
  `Integrable (fun ω => |X ω|ᵖ)`, the whole weighted variance sum is finite:
  `∑'ᵢ ∫⁻ i^{-2/p}·(𝟙{|X|≤i^{1/p}}·X)² < ∞`. Proof: `.trans_lt` the iter-15 master bound
  `lintegral_tsum_trunc_sq_weight_le_moment` (`= ofReal(C)·∫⁻|X|ᵖ`), then
  `ENNReal.mul_lt_top ENNReal.ofReal_lt_top` with the moment factor finite via
  `(hasFiniteIntegral_iff_ofReal hnn).mp hint.hasFiniteIntegral` (nonneg iff on integrand
  `|X|ᵖ`; `hnn : (0:Ω→ℝ) ≤ᵐ[μ] fun ω => |X ω|ᵖ` from `Real.rpow_nonneg`). **Do not re-derive.**
  **Gotcha:** the naive route `Integrable.lintegral_lt_top` does NOT exist; the working
  bridge is `hasFiniteIntegral_iff_ofReal` (in `L1Space/HasFiniteIntegral.lean`), which needs
  the pointwise-nonneg `0 ≤ᵐ[μ] f` hypothesis.
- **Real `Summable` conversion is now DONE (iteration 17, PR #34421):**
  `summable_trunc_sq_weight_of_integrable` — for `Integrable |X|ᵖ`, `0<p<2`, finite measure,
  `Summable (fun i => i^{-2/p}·∫(𝟙{|X|≤i^{1/p}}·X)²)`. Proof: `ENNReal.summable_toReal` on the
  iter-16 ℝ≥0∞ finiteness, then `.congr` identifying each `.toReal` term via
  `ofReal_integral_eq_lintegral_ofReal` (integrability from new reusable `integrable_trunc_sq`:
  `|𝟙{|X|≤t}·X| ≤ t` ⟹ `Integrable.mono'` vs `integrable_const t²`), `integral_const_mul`,
  `ENNReal.toReal_ofReal`. **Do not re-derive.** **Gotcha:** `Integrable.const_mul` puts the
  constant on the LEFT (`fun ω => c * f ω`), matching the `ofReal(i^{-2/p} * …)` integrand order.
- **Next: feed S5.** Two small gaps remain before `ae_tendsto_average_zero_of_variance_weighted_bdd`:
  (a) `variance (Yᵢ) μ ≤ ∫ Yᵢ²` (Mathlib `variance_le_expectation_sq` / `variance_le_...`; needs
  `μ[Yᵢ²]` finite — from `integrable_trunc_sq`), and (b) `∀ n, ∑_{i≤n} Var(Yᵢ)/aᵢ² ≤ V` from the
  `Summable` total via `sum_le_tsum` (nonneg terms, partial ≤ total). **Weight positivity:** S5's
  `ha_pos`/`ha_mono` need `aᵢ>0`; `aᵢ=i^{1/p}` fails at `i=0`, so reindex to `aᵢ=(i+1)^{1/p}` (the
  `i=0` variance term is `Var(𝟙{|X|≤0}·X)=Var(0)=0`, harmless) or `max 1 i^{1/p}` — reconcile with
  the `i^{-2/p}` weight in the Summable (note `(i+1)^{-2/p} ≤ i^{-2/p}` only for `i≥1`; cleanest is
  to prove the Summable directly at weight `(i+1)^{-2/p}` by the same route, or dominate).
- **Then: step-3 centering** (via `integral_tail_abs_le` + `tendsto_weighted_average_zero`) and
  the final combination with the step-1 truncation reduction into the MZ statement.

## Attempt Counts

- Total attempts: 13 (S1 survey; S2 Kronecker; S3 martingale assembly; +glue; S4a variance L¹ bound; S4b step-2 tail-sum; S4b step-1 i.i.d. truncation; S4b step-3/4 moment kernels; S4b step-4 tail p-series backbone; iter-10 inclusive tail; iter-11 pointwise inner-tail bound; iter-12 pointwise Tonelli integrand; iter-13 Tonelli interchange `lintegral_tsum_trunc_sq_weight_le`)
- Latest approach attempts: 1 (S4b step-4 real `Summable` hand-off `summable_trunc_sq_weight_of_integrable` + reusable `integrable_trunc_sq` — `ENNReal.summable_toReal` on iter-16 ℝ≥0∞ finiteness, `.congr` via `ofReal_integral_eq_lintegral_ofReal`+`integral_const_mul`+`ENNReal.toReal_ofReal`; landed clean on first build, 7743 jobs, 0-axiom, PR #34421)
- Prior approach attempts: 1 (S4b step-4 ℝ≥0∞ finiteness `tsum_lintegral_trunc_sq_weight_lt_top` — `.trans_lt` iter-15 master bound `lintegral_tsum_trunc_sq_weight_le_moment`, then `ENNReal.mul_lt_top ENNReal.ofReal_lt_top` + `(hasFiniteIntegral_iff_ofReal hnn).mp hint.hasFiniteIntegral`; landed clean on first build, 7743 jobs, 0-axiom, PR #34406)
- Prior approach attempts: 1 (S4b step-4 Tonelli interchange `lintegral_tsum_trunc_sq_weight_le` — `lintegral_tsum` [per-term `Measurable.indicator`∘`measurableSet_le`∘`pow_const`∘`const_mul`∘`ENNReal.measurable_ofReal`] to push `∑'ᵢ` inside `∫⁻`, then `lintegral_mono` + `ENNReal.ofReal_tsum_of_nonneg` [summand summable via `Real.summable_nat_rpow`.`mul_right`.`indicator`] + `tsum_weight_trunc_sq_le`; one binder-type fix [`fun i : ℕ`], then clean build 7743 jobs, 0-axiom)
- Prior approach attempts: 1 (S4b step-4 pointwise Tonelli integrand `tsum_weight_trunc_sq_le` — `Set.indicator_apply`+`ring` to pull `x²` out of the indicator, `tsum_mul_right` to pull it out of the tsum, root→power region rewrite via `not_lt` on `rpow_inv_lt_iff_lt_rpow`, then `tsum_indicator_ge_rpow_neg_le` + `mul_le_mul_of_nonneg_right`; landed clean on first build, 7743 jobs, 0-axiom)
- Approaches tried: 7 (S1 literature/decomposition; S2 Abel+Toeplitz;
  S3 natural-filtration martingale + upcrossing engine; S4a orthogonality + eLpNorm bridge;
  S4b step-2 discrete layer cake via lintegral_tsum + floor count;
  S4b step-1 IdentDistrib transfer + rpow reindex + tsum peel + first Borel–Cantelli;
  S4b step-3/4 pointwise rpow kernels via rpow_add split + rpow_le_rpow(_of_nonpos))
