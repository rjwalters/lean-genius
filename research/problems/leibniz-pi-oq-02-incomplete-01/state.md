# Research State: leibniz-pi-oq-02-incomplete-01

## Current State
**Phase**: ACT
**Path**: full
**Iteration**: 1

## Status (researcher-1, 2026-07-20) — 5 of 9 sorries discharged, axiom-free

Target file: `proofs/Proofs/LeibnizPiOQ02.lean` (Leibniz-type series for π/4, Catalan's
constant G = β(2), the Dirichlet β/η functions). Started at 9 sorries; **closed 5**,
leaving 4. Every new proof is machine-checked axiom-free
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`, i.e. no `sorryAx`, no
`native_decide`, and independent of the file's one remaining `eta_zeta_relation` axiom).
Host-verified via `lake env lean` against prebuilt Mathlib v4.31 oleans (file is
`import Mathlib` only — no Docker needed).

### Closed this session
1. `dirichlet_beta_one` — β(1) = π/4. The `s=1` partial sum is Mathlib's Leibniz
   partial sum after `Real.rpow_one`; discharged by `Real.tendsto_sum_pi_div_four`.
2. `catalan_series_convergent` — the β(2) partial sums converge to G. Route: introduce
   `catG n = 1/(2n+1)²`, prove `Summable catG` by domination against the p-series
   `∑ 1/(n+1)²`, then `Summable.tendsto_alternating_series_tsum`. The rpow-vs-npow gap
   between `dirichletBetaPartialSum 2` (`^(2:ℝ)`) and `catalansConstant` (`^(2:ℕ)`) is
   bridged with `Real.rpow_natCast`.
3. `catalan_pos` — G > 0. `Antitone.alternating_series_le_tendsto` at k=1 gives the even
   partial sum `1 - 1/9 = 8/9 ≤ G`.
4. `catalan_bounds` — 0.91 < G < 0.92. `alternating_series_error_bound` at n=8 terms
   (`|G − S₈| ≤ catG 8 = 1/289`, S₈ ≈ 0.91502) + `norm_num`/`linarith`.
5. `leibniz_error_bound` — `|βₙ(1) − π/4| ≤ 1/(2n+1)`. Mathlib's
   `alternating_series_error_bound` needs *absolute* convergence, which the Leibniz
   series lacks; proved directly from the conditional-convergence squeeze
   `Antitone.alternating_series_le_tendsto` / `Antitone.tendsto_le_alternating_series`
   with an even/odd case split.

### Reusable infrastructure added
`catG`/`leibG` magnitude sequences with `_pos`/`_nonneg`, `_anti` (Antitone), `catG_summable`,
`catG_alt_tsum`, `catalan_alt_conv`, `leib_alt_conv`.

## Open next (remaining 4 sorries — all genuinely deeper)
- `alternating_harmonic_series` / `dirichlet_eta_one` (η(1) = ln 2). The alternating
  harmonic series is only conditionally convergent; Mathlib has `∑ xⁿ/n = −log(1−x)`
  for |x|<1 but not the Abel boundary value at x = −1. Needs an Abel-summation lemma.
- `dirichlet_beta_three` (β(3) = π³/32). Requires the Fourier series of x² (Euler-type).
- `dirichlet_eta_two` (η(2) = π²/12). Follows from ζ(2) = π²/6 (`NumberTheory/ZetaValues`)
  and the eta–zeta relation, but the rearrangement over the alternating series is
  nontrivial; the file currently *axiomatizes* `eta_zeta_relation` (1 axiom remaining).

## Adversarial checklist (for the 5 closed claims)
- `dirichlet_beta_one`: confirm the target is π/4 (not −π/4, not arctan at another point);
  the `rpow_one` step must not silently change the `s` argument.
- `catalan_series_convergent`: `catalansConstant` uses `^(2:ℕ)` while the β partial sum
  uses `^(2:ℝ)`; the `Real.rpow_natCast` bridge must match both, else the tsum identified
  is the wrong series. Summability is genuine (dominated by a p-series), not assumed.
- `catalan_pos` / `catalan_bounds`: the bound direction depends on even vs odd partial
  sums; verify k=1 gives an *even* (lower-bound) partial sum and n=8 is even. The numeric
  window (0.91, 0.92) must strictly contain [S₈−1/289, S₈+1/289].
- `leibniz_error_bound`: the even/odd split must pair each `n` with the correct one-sided
  bound; `(-1)^(2k)=1` and `(-1)^(2k+1)=−1` sign handling is where an off-by-one would hide.
- None of the five may route through `eta_zeta_relation` (confirmed via `#print axioms`).
