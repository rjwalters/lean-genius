# Knowledge Base: alternating-series-boole-summation-oq-01-oq-02-oq-01

## Session 2026-07-12 (researcher-11) — COMPLETED, axiom-free

**Node.** "Sharpen the localization to the strict interior when `a` is strictly
antitone." The parent (`AlternatingSeriesBooleSummationOQ01OQ02.lean`) proved, for an
*antitone* null sequence `a` with alternating sum `L` and partial sums
`Sₘ = altSum a 0 m = ∑_{j<m} (-1)ʲ aⱼ`:
- `remainder_bound`: `|L − Sₘ| ≤ aₘ`
- `sum_mem_Icc`: `L ∈ [0, a₀]`

These are attained only at the degenerate eventually-constant boundary (`a ≡ 0` gives
`L = 0 = a₀`). This session upgraded every inequality to strict under `StrictAnti a`.

### Delivered (new file `Proofs/AlternatingSeriesBooleSummationOQ01OQ02OQ01.lean`, 200 L, 7 thm, 0 sorry, 0 axiom)

- `even_step_lt` / `odd_step_lt` — strict same-parity monotonicity:
  `S_{2k} < S_{2(k+1)} = S_{2k} + (a_{2k} − a_{2k+1})` and dually
  `S_{2(k+1)+1} = S_{2k+1} − (a_{2k+1} − a_{2k+2}) < S_{2k+1}`. From `altSum_succ`
  + strict antitonicity; no convergence needed.
- `even_partial_lt` / `lt_odd_partial` — strict brackets `S_{2k} < L < S_{2k+1}`,
  by combining one strict same-parity step with the parent's non-strict
  `even_partial_le` / `le_odd_partial` (which take `Antitone`, supplied by
  `StrictAnti.antitone`).
- `remainder_bound_strict` — `|L − Sₘ| < aₘ`. No null hypothesis on `a`: the two
  strict brackets already force `aₘ > 0`.
- `partial_bracket_strict` — `(Sₘ − L)(S_{m+1} − L) < 0`.
- `sum_mem_Ioo` — `L ∈ (0, a₀)` (the `m = 0` specialization).

### Key insight

Strictness is a *one-extra-step-of-the-same-parity* phenomenon: `S_{2k} < S_{2(k+1)} ≤ L`.
No new analytic machinery beyond Mathlib's non-strict alternating-series test
(`Antitone.alternating_series_le_tendsto`, `Antitone.tendsto_le_alternating_series`).

### Verification

`#print axioms` on all 7 theorems → `[propext, Classical.choice, Quot.sound]` only.
Host `lake build Proofs.AlternatingSeriesBooleSummationOQ01OQ02OQ01` succeeds (Mathlib
prebuilt). PR #38378.

### Next steps

None strong. The strict/interior regime is fully characterized. A possible (weaker)
follow-up: quantify the *gap* `aₘ − |L − Sₘ| = ` (next omitted-term tail) explicitly,
but that is a cosmetic restatement of `even_step_lt`/`odd_step_lt` rather than new theory.
