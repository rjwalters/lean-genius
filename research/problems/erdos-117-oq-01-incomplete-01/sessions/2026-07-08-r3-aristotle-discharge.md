# erdos-117-oq-01-incomplete-01 — Session (researcher-3, 2026-07-08)

## Result: discharged 12 of 13 Aristotle scaffold sorries (13 → 1)

The main gallery proof `Erdos117OQ01.lean` was already complete (0 sorries,
3 structural axioms). Its Aristotle companion `Erdos117OQ01Aristotle.lean` still
held 13 scaffold `sorry`s. Discharged 12 of them, leaving 1.

### Discharged from Mathlib (one-liners)
- `liminf_eq_lim_of_tendsto`, `limsup_eq_lim_of_tendsto`, `liminf_ge_of_tendsto`
  — `Filter.Tendsto.liminf_eq` / `.limsup_eq` (`.ge`).
- `log_pow_c`, `log_pow_div` — `Real.log_pow` (args `(x:ℝ) (n:ℕ)`, not `(n,x)`).
- `log_pos_of_gt_one` — `Real.log_pos`; `exp_log_eq` — `Real.exp_log`;
  `exp_continuous_at` — `Real.continuous_exp.continuousAt`.

### Discharged with a short proof
- `fekete_subadditive` — `Subadditive.tendsto_lim` with
  `BddBelow (Set.range fun n => a n / n)` (lower bound 0: `n=0` term `a0/0=0`,
  `n≥1` from `hpos`).
- `log_subadditive_of_submultiplicative` — `Real.log_le_log` on the cast
  submultiplicativity + `Real.log_mul`.
- `growth_rate_converges_of_submultiplicative` — Fekete applied to `log ∘ h`.

### Corrected + proved (was a FALSE statement)
`tendsto_implies_exponential_base` originally read `∀ ε > 0, …`, which is false:
for `ε ≥ exp L` the base `exp L − ε ≤ 0`, and `(exp L − ε)ⁿ` at even `n` is a
large positive number that can exceed `h n`. This is the exact defect that a
prior session fixed in the main file's `base_implies_behavior`. Corrected to
`ε ∈ (0, exp L)` (added `hpos : ∀ n, 1 ≤ h n`) and proved: `log(exp L − ε) < L`,
`Filter.Tendsto.eventually_lt` (const vs growth rate) gives eventually
`log(exp L − ε) < log(h n)/n`, then `lt_div_iff₀` + `Real.log_pow` +
`Real.exp_lt_exp`/`Real.exp_log` lift to `(exp L − ε)ⁿ < h n`.

### Remaining (1 sorry)
`liminf_le_limsup` — needs the `BoundedAtFilter atTop f → IsBoundedUnder (·≤·)`
and `(·≥·)` conversion to apply `Filter.liminf_le_limsup`. Left as a documented
scaffold sorry.

## Verification
Host `lake env lean Proofs/Erdos117OQ01Aristotle.lean` → EXIT 0, 0 errors.
`#print axioms growth_rate_converges_of_submultiplicative` /
`tendsto_implies_exponential_base` → `[propext, Classical.choice, Quot.sound]`
(no sorryAx, no native_decide). Real sorry count 13 → 1.

## Scope note
The underlying convergence question for #117 (does `lim log h(n)/n` exist? the
Pyber `c₁ < c₂` gap) remains genuinely OPEN and out of scope.
