# Knowledge Base: brouwer-fixed-point-oq-04-oq-04-incomplete-01

**Status**: PROVED — 0 sorries (was 2 from `all_goals sorry` in `approx_fp_limit_1d`)

---

## Session 2026-04-13 (Session 1) — Completed Limit Theorem

**Mode**: FRESH | **Outcome**: completed (2 sorries → 0)

### What Was Proved
`approx_fp_limit_1d` goals: `F.lower x* ≤ x*` and `x* ≤ F.upper x*`

### Proof Technique (Squeeze + ContinuousWithinAt)
1. From `hx_approx (φ n)`: extract `y n ∈ [F.lower(x(φ n)), F.upper(x(φ n))]` with `|x(φ n) - y n| < ε(φ n)`
2. `ε ∘ φ → 0` via `StrictMono.tendsto_atTop`
3. `x(φ n) - y n → 0` via `squeeze_zero_norm`
4. `y n → x*` by `hφ_conv.sub h_diff` + `sub_sub_cancel`
5. `F.lower(x(φ n)) → F.lower(x*)` via `ContinuousWithinAt.comp + Filter.tendsto_nhdsWithin_iff`
6. `F.lower x* ≤ x*` by `le_of_tendsto_of_tendsto` (takes `∀ n, f n ≤ g n`, non-prime version)

### Key Mathlib Facts Used
- `Filter.tendsto_nhdsWithin_iff`: `Tendsto f l (nhdsWithin x s) ↔ Tendsto f l (nhds x) ∧ ∀ᶠ n, f n ∈ s`
- `ContinuousOn.continuousWithinAt`: gives `ContinuousWithinAt` at any point in the domain
- `ContinuousWithinAt.comp`: chains continuity-within-at with a tendsto-within
- `squeeze_zero_norm`: `‖f n‖ ≤ g n` and `g n → 0` implies `f n → 0`
- `le_of_tendsto_of_tendsto`: (non-prime) takes `∀ n, f n ≤ g n` to conclude `a ≤ b` from limits

### Remaining: 1 Axiom
`scarf_approx_fixed_point` — genuine axiom (Sperner's lemma + Kakutani labeling, n-dimensional)

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]
