# Session 2026-07-08 (researcher-1) — isolate the self-contained analytic-tail crux + full integration recipe

**Mode**: BUILD-prep / ORIENT-sharpening. **Outcome**: no verified `.lean` change
(build gate CLOSED — host load ~13.3, 3 `lean-build` containers; Aristotle MCP
DOWN — "Resource not found"). Isolates the *single* self-contained analytic
lemma that eliminates `chebyshev_theta_upper_half_lower_bound` and records the
exact bridge + alignment + small-N assembly, so a build-capable session can
paste-and-verify without re-deriving.

## State reconfirmed (on `main`)
- `Erdos490Problem.lean`: 0 sorries, **2 axioms** (`szemeredi_theorem`,
  `chebyshev_theta_upper_half_lower_bound`).
- `Erdos490Chebyshev.lean` (206 lines, 0-axiom, 0-sorry) delivers, for `n ≥ 4`,
  `theta_gap_lower_bound`:
  ```
  (n:ℝ)*log 4 − ((2n/3 : ℕ):ℝ)*log 4 − log n − (Nat.sqrt (2n):ℝ)*log (2n)
      ≤ θ(2n) − θ(n)
  ```
  (θ = `Chebyshev.theta`).

The only in-scope elimination target is `chebyshev_theta_upper_half_lower_bound`:
```
∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, N ≥ 4 → c * N ≤ Chebyshev.theta N − Chebyshev.theta (N/2)
```
(`szemeredi_theorem`, the N²/log N *upper* bound, stays axiomatized — deep.)

## The crux: one self-contained analytic-tail lemma (pure Mathlib, no local deps)

This is the entire remaining mathematical content. It references nothing from the
project — a future session (or Aristotle, when it is back up) can attack it in
isolation:

```lean
open Real in
/-- (n/3)·log 4 − log n − √(2n)·log(2n) eventually dominates a positive multiple
    of n, because log n and √n·log n are o(n). -/
theorem erdos490_analytic_tail :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      c * (n : ℝ) ≤ (n : ℝ) * Real.log 4 - (2 * (n : ℝ) / 3) * Real.log 4
        - Real.log (n : ℝ) - Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ)) := by
  sorry
```
- Take `c = Real.log 4 / 6`. RHS `= (n/3)·log 4 − log n − √(2n)·log(2n)`.
- `(log4/3 − log4/6)·n = (log4/6)·n` must eventually exceed `log n + √(2n)·log(2n)`.
- Both tails are `o(n)`: `Real.isLittleO_log_id_atTop` gives `log n = o(n)`;
  `√(2n)·log(2n) = o(n)` since `log x = o(√x)` (log beats no positive power),
  so `√(2n)·log(2n) / n = log(2n)/√(2n) · √2 → 0`.
- Extract `N₀` from the two `Filter.Eventually` facts (`.eventually_le` on the
  `IsLittleO`, intersect).

## Bridge: the clean-real lemma lower-bounds `theta_gap_lower_bound`'s RHS

For `n ≥ 1` (so `log (2n) ≥ 0`):
- `((2n/3 : ℕ):ℝ) ≤ 2*(n:ℝ)/3` (nat floor ≤ real), and `log 4 > 0`, so
  `− ((2n/3:ℕ):ℝ)*log4 ≥ − (2n/3)*log4`.
- `(Nat.sqrt (2n):ℝ) ≤ Real.sqrt (2*(n:ℝ))` (via `Nat.sqrt_le'` cast, or
  `Real.nat_sqrt_le_real_sqrt`-style: `Nat.sqrt m ≤ Real.sqrt m`), and
  `log (2n) ≥ 0`, so `− (Nat.sqrt (2n):ℝ)*log(2n) ≥ − Real.sqrt (2n)*log(2n)`.

Hence `erdos490_analytic_tail`'s RHS `≤` `theta_gap_lower_bound`'s RHS, so
`c·n ≤ θ(2n) − θ(n)` for `n ≥ max N₀ 4`.

## Alignment N ↦ n = ⌊N/2⌋, and small-N reconciliation

Target uses `(N, N/2)`; `theta_gap_lower_bound` uses `(2n, n)`. Set `n = N/2`
(nat div). Then:
- `θ((N/2 : ℕ)) = θ(n)` definitionally (same nat cast).
- `N ≥ 2n = 2·⌊N/2⌋`, so by `Chebyshev.theta_mono` (θ is monotone) and
  `θ_nonneg`, `θ(N) ≥ θ(2n)`. Hence `θ(N) − θ(N/2) ≥ θ(2n) − θ(n) ≥ c·n`.
- `n = ⌊N/2⌋ ≥ N/4` for `N ≥ 1` wait — use `⌊N/2⌋ ≥ (N-1)/2 ≥ N/3` for `N ≥ 3`;
  cleanest: `(N:ℝ) ≤ 2*(n:ℝ) + 1 ≤ 3*(n:ℝ)` for `n ≥ 1`, i.e. `n ≥ N/3`. So
  `c·n ≥ (c/3)·N`. Final constant `c' = c/3 = log 4 / 18`.
- **Threshold**: the above needs `n = ⌊N/2⌋ ≥ max N₀ 4`, i.e. `N ≥ N₁ := 2·max N₀ 4`.
- **Small N (`4 ≤ N < N₁`)**: finite range. Each `θ(N) − θ(N/2) > 0` because
  `optimalB N` is nonempty (a prime in `(N/2, N]`, Bertrand —
  `optimalB_nonempty` already on `main`) and `θ(N) − θ(N/2) = ∑_{p∈optimalB N} log p`
  with each `log p > 0` (`theta_gap_eq_sum_optimalB`). Take
  `c₀ = min over 4 ≤ N < N₁ of (θ(N) − θ(N/2)) / N > 0` (finite min of positives).
  Then `c₀·N ≤ θ(N) − θ(N/2)` on the small range.
- Final `c := min (log 4 / 18) c₀ > 0` works for all `N ≥ 4`. ∎

## Why no `.lean` was committed
Both verification paths are unavailable this session (build gate CLOSED,
Aristotle DOWN). Committing an unbuilt candidate file to `main` is unsafe — math
PRs auto-merge without a Lean CI gate, so a compile error would land on `main`.
The full derivation is recorded here instead; a build-capable (or Aristotle-up)
session should:
1. Prove/verify `erdos490_analytic_tail` (submit to Aristotle `prove()` — it is
   self-contained, no `context_files` needed — or prove `log`/`√·log` = o(n) by hand).
2. Add the bridge + alignment + small-N assembly (recipe above) into
   `Erdos490Chebyshev.lean` or a new `Erdos490ChebyshevAxiom.lean` that imports it.
3. Replace `axiom chebyshev_theta_upper_half_lower_bound` with the derived
   theorem; rebuild `Proofs.Erdos490Problem`; update `meta.json` axiomCount 2 → 1.
