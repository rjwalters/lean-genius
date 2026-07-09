# Knowledge: erdos-1138-oq-03-oq-01 — BHP ⟹ prime gaps are sublinear

## Session 2026-07-02 (researcher-7): SURVEY (build-free; no Lean built)

Environment was fully build-blocked (Docker daemon down; host disk ~97%, ≈455Mi free,
#33336; 0 Mathlib oleans on disk — cache only in the unreachable Docker volume). No Lean
was compiled. This is a survey/scoping deliverable to enable a future build-capable session.

### Scoped target
In `namespace Erdos1138OQ03`, from the existing `axiom baker_harman_pintz`
(`(maxPrimeGap x : ℝ) ≤ (x:ℝ)^(0.525:ℝ)` for `x ≥ 25`), derive:

```lean
theorem bhp_implies_gap_littleo :
    Filter.Tendsto (fun x : ℕ => (maxPrimeGap x : ℝ) / x) Filter.atTop (nhds 0)
```

This is the unconditional twin of the parent's conditional `cramer_implies_gap_sublinear`.

### Proof sketch (real-analysis, squeeze)
1. **Upper envelope.** For `x ≥ 25`, `x > 0`, so from the axiom and `x^0.525 = x^1 · x^(-0.475)`:
   `maxPrimeGap x / x ≤ x^0.525 / x = x^(0.525 - 1) = (x:ℝ)^(-(0.475:ℝ))`.
   Uses `Real.rpow_natCast`/`Real.rpow_sub` (or `div` = `rpow (a-b)`), `Real.rpow_neg`,
   and monotonicity of division by positive `x`.
2. **Envelope → 0.** `Tendsto (fun x:ℝ => x^(-(0.475))) atTop (𝓝 0)` is
   `Real.tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 0.475)`
   (`Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean:48`). Compose with
   `tendsto_natCast_atTop_atTop` (`Mathlib/Order/Filter/AtTopBot/Archimedean.lean:39`) to
   move from `x : ℕ` cast to `ℝ`.
3. **Lower bound.** `0 ≤ maxPrimeGap x / x` trivially (`Nat.cast_nonneg`, `div_nonneg`).
4. **Squeeze.** `squeeze_zero` (or `tendsto_of_tendsto_of_tendsto_of_le_le`) with the
   `0`-limit constant below and the `x^(-0.475)` envelope above, valid eventually
   (`∀ᶠ x, 25 ≤ x`). Yields the `𝓝 0` limit.

### Verified Mathlib references (static check against pinned Mathlib on disk)
- `Real.tendsto_rpow_neg_atTop {y : ℝ} (hy : 0 < y) : Tendsto (fun x:ℝ => x^(-y)) atTop (𝓝 0)`
  — Pow/Asymptotics.lean:48. RHS `𝓝 0` matches target. ✓
- `tendsto_natCast_atTop_atTop` — AtTopBot/Archimedean.lean:39. ✓
- `squeeze_zero`, `Real.rpow_neg`, `Real.rpow_sub`, `Real.rpow_natCast` — standard, present.

### Optional companion form
```lean
theorem bhp_gap_eventually_le_eps (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in Filter.atTop, (maxPrimeGap x : ℝ) ≤ ε * x
```
Follows from `bhp_implies_gap_littleo` via `Metric.tendsto_nhds` / `eventually` unfolding,
mirroring the ε-form of the conditional lemma.

### Status / next step
No axioms added beyond the parent's existing `baker_harman_pintz`; no `native_decide`.
NEXT (build-capable session): add the two theorems to a new
`proofs/Proofs/Erdos1138OQ03OQ01.lean` importing `Proofs.Erdos1138OQ03`, build via
`./proofs/scripts/docker-build.sh Proofs.Erdos1138OQ03OQ01`, confirm `#print axioms` shows
only `{propext, Classical.choice, Quot.sound}` plus the inherited `baker_harman_pintz`,
then create the `src/data/proofs/erdos-1138-oq-03-oq-01/` gallery entry
(status `axiomatized` — it depends on the BHP axiom).

## Session 2026-07-09 (researcher-1): SOLVED — asymptotics-idiom + effective forms (VERIFIED)

Entry was already SOLVED (5 thm, 0 sorry, 1 inherited `baker_harman_pintz` axiom, merged #36057).
Looked outward and added 3 genuinely distinct theory-level theorems (5 → 8):

- `bhp_gap_isLittleO_id`: `maxPrimeGap =o[atTop] (x ↦ x)` — the little-o idiom form. The
  entry's title claim ("sublinearity") *is* the `=o` statement; the file previously only had
  the `Tendsto (·/x) → 0` form and a `=O` at exponent 0.525. Bridged via `isLittleO_iff_tendsto'`
  (denominator eventually nonzero).
- `bhp_gap_isLittleO_rpow (a) (ha : 0.525 < a)`: `maxPrimeGap =o[atTop] (x ↦ x^a)` — idiom form
  of `bhp_gap_div_rpow_littleo`, using the full BHP exponent (sublinear at every a > 0.525, not
  just a = 1).
- `bhp_gap_le_eps_effective (ε x) (hx25 : 25 ≤ x) (hthr : 1 ≤ ε·x^0.475)`: `maxPrimeGap x ≤ ε·x`.
  Effective/pointwise replacement for the qualitative `bhp_gap_eventually_le_eps`: an explicit
  sufficient threshold. Proof multiplies the envelope `x^(-0.475) ≤ ε` (equivalent to hthr via
  `x^(-0.475)·x^0.475 = x^0 = 1`) by `x`. `ε > 0` NOT assumed — forced by the threshold.

Build: VERIFIED clean (`Completed successfully!`, 0 warnings) at `LEAN_MEMORY_LIMIT=16384`
(32768/24576 both hit fleet SIGBUS-135 at olean-write after clean elab [7744/7744] ~1s).
No new axioms (`axiomCount` stays 1: inherited `baker_harman_pintz`), no `native_decide`.
meta synced 5→8 thm / 131→186 lines at both `.meta.*` and `.leanFile.*`.

NEXT: entry is saturated for elementary work; only remaining lever is proving/replacing the
`baker_harman_pintz` axiom itself (deep analytic number theory — out of session scope).
