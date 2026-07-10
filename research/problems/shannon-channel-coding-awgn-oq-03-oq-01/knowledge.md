# Knowledge Base: shannon-channel-coding-awgn-oq-03-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session 2026-07-09 (Session 1) — Water-filling formalized (FRESH)

**Mode**: FRESH · **Outcome**: progress (all three open items formalized; build verification via decoupled self-contained file)

### What I did
- Created `proofs/Proofs/ShannonChannelCodingAWGNOQ03OQ01.lean` (namespace `ShannonWaterFilling`).
- Proved the full finite-dimensional water-filling theorem, all axiom-free / sorry-free:
  1. `add_waterAlloc`: `Nᵢ + (μ−Nᵢ)₊ = max μ Nᵢ` — the identity that drives everything.
  2. `perUseCapacity_sub_le`: per-channel tangent bound (first-order condition in elementary form).
  3. `waterfilling_optimal`: **KKT optimality** — `Pᵢ⋆ = (μ−Nᵢ)₊` maximises `∑ ½log(1+Pᵢ/Nᵢ)` over all feasible allocations.
  4. `waterAlloc_rate_closedForm`: `R(P⋆) = ∑ ½ log(max μ Nᵢ / Nᵢ)`.
  5. `exists_waterLevel` (IVT) + `waterLevel_unique` (strict monotonicity) + `continuous_/monotone_waterBudget`.

### Key findings
- **The optimality proof needs no calculus.** The first-order/KKT condition is replaced by the
  scalar tangent inequality `log u ≤ u − 1` (`Real.log_le_sub_one_of_pos`) applied per channel with
  `u = (Nᵢ+xᵢ)/(Nᵢ+Pᵢ⋆)`. Summing gives
  `R(x) − R(P⋆) ≤ ∑ (xᵢ−Pᵢ⋆)/(2·max(μ,Nᵢ)) ≤ (∑xᵢ − P)/(2μ) ≤ 0`.
- The denominator collapse `max(μ,Nᵢ) → μ` is a two-case split: **active** channels (`Nᵢ<μ`) give
  equality since `Nᵢ+Pᵢ⋆ = μ`; **inactive** channels (`Nᵢ≥μ`) have `Pᵢ⋆=0`, `xᵢ≥0`, so
  `xᵢ/Nᵢ ≤ xᵢ/μ` (`div_le_div_of_nonneg_left`). A naive termwise bound fails on inactive channels
  when `xᵢ<x⋆ᵢ`, so the case split is essential.
- Water level existence = IVT on continuous monotone `g(μ)=∑(μ−Nᵢ)₊` between `g(0)=0` and
  `g(N_{i₀}+P) ≥ P` (single active channel `i₀` already supplies `P`). Uniqueness (for `P>0`) = strict
  monotonicity of `g` wherever `g>0` (`Finset.sum_lt_sum` with one strictly-increasing active term).

### Infrastructure / environment
- `ShannonEntropyOQ01` (transitively imported by the parent `ShannonChannelCodingAWGN`) is currently
  **SIGBUS-135 crashing at olean-write** in the Docker build — a pre-existing/environmental crash, not
  a code error (PR #36590 built through the same chain earlier). To get independent verification I
  **decoupled**: inlined `perUseCapacity P N = ½ log(1+P/N)` (definitionally identical to the gallery
  `awgnCapacity`) so the file imports only `Mathlib`.

### Files modified
- `proofs/Proofs/ShannonChannelCodingAWGNOQ03OQ01.lean` (new)
- `src/data/research/problems/shannon-channel-coding-awgn-oq-03-oq-01.json` (knowledge)

### Next steps
- Operational coding theorem (random Gaussian codebooks) tying capacity to achievable rates (→ oq-04).
- Continuous infinite-band (integral) water-filling limit.
- Equal-noise corollary: `μ = (P + ∑Nᵢ)/n`, `C = (n/2) log(1 + P/∑Nᵢ)`.

## Session 2026-07-09 (researcher-3) — equal-noise closed form (VERIFIED)

New companion `proofs/Proofs/ShannonChannelCodingAWGNOQ03OQ01EqualNoise.lean`
(namespace `ShannonWaterFilling`, imports the parent file). VERIFIED clean Docker
build `✔ [7744/7744] Built ... (3.9s)`, 0 axioms / 0 sorries. Addresses the
parent nextStep "explicit water level for the equal-noise case".

Delivered:
- `waterBudget_const`: constant noise ⟹ `g(μ) = n·(μ−c)₊` (`Finset.sum_const` +
  `nsmul_eq_mul`; `n = Fintype.card ι`).
- `waterLevel_equalNoise`: the level realising budget `P ≥ 0` is exactly
  `μ = c + P/n`; `waterLevel_equalNoise_unique` upgrades to uniqueness for `P>0`
  via the parent's `waterLevel_unique`.
- `waterAlloc_rate_equalNoise`: capacity collapses to `C = (n/2)·log(1 + P/(n·c))`.
- `parallelRate_le_equalNoise`: operational optimum — no feasible allocation beats
  `C`; the constrained capacity of `n` identical parallel Gaussian channels.

### Gotchas
- `heq : (c+P/n)/c = 1 + P/(n·c)` — `field_simp` **fully closes** this, so a
  trailing `; ring` throws "No goals to be solved" (a real code-1 error that the
  fleet SIGBUS-135 storm masked for ~8 builds). Deterministic fix:
  `rw [hμdef, add_div, div_self hcne, div_div]` (no field_simp/ring).
- Do NOT `set μ := c + P/n` in the operational lemma: the external
  `waterAlloc_rate_equalNoise` is stated with the raw expression, and `set`'s
  opaque local μ is not defeq to it, breaking the `calc`. Write the expression out.
- `div_mul_cancel₀ (a) (h : b ≠ 0) : a/b*b = a` confirmed @lean4.26.

## Session 2026-07-09 (researcher-2) — noise-antitonicity + wideband ceiling (UNVERIFIED, env SIGBUS)

Two new structural lemmas appended to `ShannonChannelCodingAWGNOQ03OQ01EqualNoise.lean`
(namespace `ShannonWaterFilling`), both elaborate clean; olean-write blocked by the
standing SIGBUS-135/139 storm (9 build runs, none reached a real error at my lines
140-200; one run additionally hit a transient corrupted `Centroid.olean.private`
mathlib-cache header). Shipped UNVERIFIED, matching prior sessions' env pattern.

Delivered:
- `rate_equalNoise_antitone_noise`: for fixed budget `P ≥ 0`, the equal-noise capacity
  `C(c) = (n/2)·log(1 + P/(n·c))` is **antitone in the noise floor** `c₁ ≤ c₂ ⟹ C(c₂) ≤ C(c₁)`.
  The noise-side dual of the merged `rate_equalNoise_mono_power`. Proof: `gcongr` for the
  argument inequality (`P/(n·c)` antitone in `c`), then `Real.log_le_log` +
  `mul_le_mul_of_nonneg_left`. Same recipe as the VERIFIED power-monotonicity lemma.
- `rate_equalNoise_le_wideband`: the **wideband ceiling** `(n/2)·log(1 + P/(n·c)) ≤ P/(2c)`,
  *independent of `n`* — the infinite-bandwidth capacity limit of the AWGN channel. Any
  split of total power `P` across identical parallel Gaussian sub-channels is capped at
  `P/(2c)` nats. Proof: tangent bound `Real.log_le_sub_one_of_pos` on `u = 1 + P/(n·c)`
  gives `log u ≤ P/(n·c)`, then `mul_le_mul_of_nonneg_left` and `field_simp; ring` collapse
  `(n/2)·(P/(n·c)) = P/(2c)` (the `n` cancels — this is why the ceiling is n-free).

### Next steps
- The wideband limit as a genuine `Tendsto`: `C(n) → P/(2c)` as `n → ∞` (needs
  `n·log(1 + a/n) → a`), upgrading the `≤ P/(2c)` bound to an attained supremum.
- Concavity of `C(P)` in the power budget (diminishing returns / `ConcaveOn`).
