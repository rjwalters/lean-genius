# Current State

**Phase**: S3 PREP — Cauchy condensation recipe verified against pinned Mathlib SHA, with uniform-in-k condensed-term lower bound
**Since**: 2026-05-13 (S3 PREP); 2026-04-28 (AXIOMATIZED baseline)
**Iteration**: 3
**Owner**: researcher-9 (S3 PREP, 2026-05-13)

## Current Focus

Pre-ACT audit + refinement of the existing recipe (knowledge.insights[6]–[7]) for eliminating `axiom harmonic_log_plus2_diverges` (Erdos892Problem.lean:172) via Mathlib's Cauchy condensation test. This session is **doc-only** — no Lean file changes. Goal: pin every Mathlib lemma to the lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, give file paths + line numbers, and replace the existing `for k ≥ 1` condensed-term bound with a uniform-in-k bound that avoids the k=0 edge case.

**Complementary to in-flight PR #18763** (researcher-11, 2026-05-13 11:27 UTC) which adds a `~90-LOC ACT skeleton under research/problems/erdos-892/sessions/` and explicitly scopes out state.md / knowledge.md / gallery JSON edits. This PR fills exactly that scope gap (state.md / knowledge.md / `src/data/research/problems/erdos-892.json`) and refines the condensed-term bound used in their §3 from the `k ≥ 1` form `2^k · f(2^k) ≥ 1/(2 log 2 (k+2))` to the **uniform-in-k** form `2^k · f(2^k) ≥ 1/(4 log 2 (k+2))` (valid for all k ∈ ℕ via `2^k + 2 ≤ 2^(k+2)`), which lets the future ACT writer drop the k=0 special-case argument.

## S3 PREP — Verified Mathlib API (pinned SHA 2df2f0150c…)

All names + signatures cross-checked via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<sha>` against the SHA in `proofs/lake-manifest.json`.

| Mathlib lemma | File:line | Signature (abridged) |
|---|---|---|
| `summable_condensed_iff_of_nonneg` | `Mathlib/Analysis/PSeries.lean:228` | `(h_nonneg : ∀ n, 0 ≤ f n) (h_mono : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) → (Summable fun k => (2:ℝ)^k * f (2^k)) ↔ Summable f` |
| `not_summable_iff_tendsto_nat_atTop_of_nonneg` | `Mathlib/Topology/Algebra/InfiniteSum/Real.lean:61` | `(hf : ∀ n, 0 ≤ f n) → ¬Summable f ↔ Tendsto (fun n => ∑ i ∈ range n, f i) atTop atTop` |
| `summable_iff_not_tendsto_nat_atTop_of_nonneg` | `Mathlib/Topology/Algebra/InfiniteSum/Real.lean:66` | dual of the above |
| `tendsto_sum_range_one_div_nat_succ_atTop` | `Mathlib/Analysis/PSeries.lean:337` | `Tendsto (fun n => ∑ i ∈ range n, (1:ℝ)/(i+1)) atTop atTop` |
| `not_summable_natCast_inv` | `Mathlib/Analysis/PSeries.lean:327` | `¬Summable (fun n => n⁻¹ : ℕ → ℝ)` |
| `not_summable_one_div_natCast` | `Mathlib/Analysis/PSeries.lean:333` | `¬Summable (fun n => 1 / n : ℕ → ℝ)` |
| `Real.log_pos` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:173` | `1 < x → 0 < log x` |
| `Real.log_le_log` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:148` | `0 < x → x ≤ y → log x ≤ log y` |
| `Real.log_lt_log` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:152` | `0 < x → x < y → log x < log y` |
| `Real.log_pow` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:273` | `log (x^n) = n * log x` |

## S3 PREP — Refined Recipe (replacing knowledge.insights[7])

Define `f : ℕ → ℝ` by `f n := 1 / ((↑n + 2) * Real.log (↑n + 2))`. Goal: prove
`harmonic_log_plus2_diverges : ∀ S : ℝ, ∃ N : ℕ, S + 1 < ∑ n ∈ range N, f n`.

### Step 1 — Non-negativity (`h_nonneg`)
For all `n : ℕ`, `0 ≤ f n`. Both factors are positive:
- `(↑n + 2 : ℝ) > 0` since `n + 2 ≥ 2 > 0` — `by positivity` or `Nat.cast_add_pos`.
- `Real.log (↑n + 2) > 0` via `Real.log_pos` with hypothesis `1 < ↑n + 2` (which is `Nat.one_lt_succ_succ` cast to ℝ).
- Reciprocal of a positive real is positive.

### Step 2 — Antitone (`h_mono`)
For `m n : ℕ`, `0 < m → m ≤ n → f n ≤ f m`. Equivalently (since denominators positive),
`(↑m + 2) * Real.log (↑m + 2) ≤ (↑n + 2) * Real.log (↑n + 2)`.
- `↑m + 2 ≤ ↑n + 2` from `m ≤ n` via `Nat.cast_le`.
- `Real.log (↑m + 2) ≤ Real.log (↑n + 2)` via `Real.log_le_log` with positivity from Step 1.
- Both factors are non-negative, so product is monotone — `mul_le_mul` with two `le` hypotheses + non-negativity.
- (Note: the antitonicity hypothesis form `0 < m → m ≤ n → f n ≤ f m` is what `summable_condensed_iff_of_nonneg` expects. The `0 < m` hypothesis is not actually needed here since `f` is antitone on all of ℕ, but accepting and discarding the hypothesis is fine.)

### Step 3 — Uniform-in-k condensed-term lower bound (replaces "for k ≥ 1")
**Key improvement over knowledge.insights[7]**: the existing recipe uses `2^k + 2 ≤ 2 · 2^k` which fails at `k = 0` (`2^0 + 2 = 3 > 2 = 2·2^0`). Replace with the looser-but-uniform bound:
- For all `k : ℕ`, `2^k + 2 ≤ 2^(k+2)`.
  - Algebraic check: `2^(k+2) = 4 · 2^k ≥ 2^k + 2 ⟺ 3 · 2^k ≥ 2`, which holds for all `k ∈ ℕ` since `2^k ≥ 1`.
  - In Lean: `Nat.lt_pow_self`-style induction or `by omega`-after-`pow_succ`-rewriting, or simply `Nat.add_le` + `Nat.one_le_two_pow`.
- Consequently, for all `k : ℕ`:
  - `Real.log (2^k + 2) ≤ Real.log (2^(k+2)) = (↑k + 2) * Real.log 2` (via `Real.log_le_log` + `Real.log_pow`).
  - `(↑(2^k) + 2) * Real.log (↑(2^k) + 2) ≤ ↑(2^(k+2)) * (↑k + 2) * Real.log 2 = 4 * ↑(2^k) * (↑k + 2) * Real.log 2`.
  - Therefore `(2:ℝ)^k * f (2^k) = (2:ℝ)^k / ((↑(2^k) + 2) * Real.log (↑(2^k) + 2)) ≥ (2:ℝ)^k / (4 * ↑(2^k) * (↑k + 2) * Real.log 2) = 1 / (4 * (↑k + 2) * Real.log 2)`.

### Step 4 — Lower bound diverges
`g k := 1 / (4 * (↑k + 2) * Real.log 2)` is `1 / (4 * Real.log 2)` times the harmonic-tail `1/(k+2)`.
- ¬Summable `(fun k => 1/(↑k + 2))` — from `not_summable_natCast_inv` after the index-shift `k ↦ k + 2`, or directly from the divergence of `tendsto_sum_range_one_div_nat_succ_atTop` after a one-term shift.
- ¬Summable `g` follows by scalar multiplication: `(1/(4*Real.log 2)) > 0` so summability is preserved by `Summable.const_smul_iff` (or contrapositive).

### Step 5 — Lift to the condensed series, then to f
- ¬Summable `(fun k => (2:ℝ)^k * f (2^k))` via comparison Step 3 + Step 4: if the condensed series were summable, comparison `g k ≤ 2^k * f(2^k)` gives `Summable g`, contradicting Step 4. Use `Summable.of_nonneg_of_le` contrapositively, or `Summable.mono` after non-negativity.
- ¬Summable `f` via `summable_condensed_iff_of_nonneg` (Step 1 + Step 2).

### Step 6 — Extract existential N
- From ¬Summable `f` + non-negativity of `f` (Step 1), apply `not_summable_iff_tendsto_nat_atTop_of_nonneg.mp` to get
  `Tendsto (fun N => ∑ n ∈ Finset.range N, f n) atTop atTop`.
- `Tendsto.eventually_gt` (or its specialization for `atTop`) applied to the target `S + 1` then provides the desired `N`.

### Estimated LOC
- Step 1: ~3 lines (positivity)
- Step 2: ~6 lines (antitone via `Real.log_le_log` + `mul_le_mul`)
- Step 3: ~15 lines (uniform bound + algebraic manipulation; bulk of the proof)
- Step 4: ~5 lines (harmonic divergence + scalar bridge)
- Step 5: ~6 lines (comparison)
- Step 6: ~3 lines (existential extraction)
- Total: **~40 lines of tactic proof + ~10 lines of `have` scaffolding ≈ 50 lines**, matching the existing estimate (50-70 lines).

## Active Approach (post-S3 PREP)

Gallery entry uses an "axiomatized" formalization:
- 6 definitions: `IsPrimitive`, `IsStrictlyIncreasing`, `IsDominatedBy`, `ErdosProblem892`, `IsGCDFree`, `ErdosProblem892GCDFree`.
- 7 proved theorems: `primitive_elements_ge_two`, `strict_inc_lower_bound`, `strict_inc_eventually_ge`, `product_log_comparison`, `reciprocal_log_comparison`, `erdos_1935_necessary`, `linear_growth_no_primitive_dominator`.
- 2 axioms: `primitive_reciprocal_log_convergent` (Erdős 1935 deep result), `harmonic_log_plus2_diverges` (now S3-PREP-ready for Mathlib-derived theorem replacement).

The Erdős 1935 necessary condition is fully proved in Lean. The Erdős–Sárközy–Szemerédi 1968 problem itself remains open (no characterization of necessary AND sufficient conditions for primitive domination is known).

## Active Approach

Gallery entry uses an "axiomatized" formalization:
- 6 definitions: `IsPrimitive`, `IsStrictlyIncreasing`, `IsDominatedBy`, `ErdosProblem892`, `IsGCDFree`, `ErdosProblem892GCDFree`.
- 7 proved theorems: `primitive_elements_ge_two`, `strict_inc_lower_bound`, `strict_inc_eventually_ge`, `product_log_comparison`, `reciprocal_log_comparison`, `erdos_1935_necessary`, `linear_growth_no_primitive_dominator`.
- 2 axioms: `primitive_reciprocal_log_convergent` (Erdős 1935 deep result), `harmonic_log_plus2_diverges` (standard Cauchy condensation, not yet in Mathlib).

The Erdős 1935 necessary condition is fully proved in Lean. The Erdős–Sárközy–Szemerédi 1968 problem itself remains open (no characterization of necessary AND sufficient conditions for primitive domination is known).

## Blockers

- Problem is OPEN (1968): no known sufficient condition; characterization is conjectural.
- Cannot run Docker builds in this session (host disk at 99% — 153Mi free).

## Next Action

When disk capacity returns and Mathlib gains a `Real.summable_one_div_n_log_n` analog,
replace `harmonic_log_plus2_diverges` with a Mathlib-derived theorem.

A second tractable refinement: instantiate `linear_growth_no_primitive_dominator` for
specific `b_n` (e.g., `b_n = n^2`) where the necessary condition fails or is non-trivial
to verify directly — this would not solve the open question but would strengthen the
"tightness" of the necessary condition narrative.

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 1
- Approaches tried: 2 (metadata reconciliation 2026-04-28; S3 PREP recipe refinement 2026-05-13 — Mathlib API pinned + uniform-in-k condensed-term bound)
