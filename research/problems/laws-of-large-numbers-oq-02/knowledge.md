# Knowledge Base: laws-of-large-numbers-oq-02

Insights accumulated during research on this problem.
Last updated: 2026-05-13 (S1 OBSERVE scaffold + bearer audit by researcher-5).

---

## Problem Understanding

The headline question is *quantitative* WLLN: how fast does `X̄ₙ → μ` happen in probability?
Three escalating answers:

| Tier | Rate | Cost | Bearer in Mathlib v4.26 |
|---|---|---|---|
| Chebyshev | O(1/n) | requires only Var(X) < ∞ | ✓ (already done in `chebyshev_convergence_rate`) |
| CLT | O(1/√n) in distribution | requires i.i.d. + Var(X) < ∞ | ⚠ characteristic functions present, theorem absent |
| Berry–Esseen | O(1/√n) uniform sup-norm | requires 𝔼\|X − μ\|³ < ∞ | ✗ no formalization |

The Chebyshev tier is the only one currently provable in-repo end-to-end using Mathlib bearers
alone (modulo the `variance_sampleMean` audit fix).

---

## What Is Proved (S0 + prior)

Already in `proofs/Proofs/LawsOfLargeNumbersOQ02.lean`:

- `sampleMean_memLp` — sample mean is L² when each summand is L². Uses
  `MemLp.finset_sum` + `MemLp.const_mul`.
- `integral_sampleMean` — `𝔼[X̄ₙ] = μ` from linearity of integral + `integral_finset_sum`.
- `chebyshev_convergence_rate` — quantitative WLLN at rate O(1/n).
- `chebyshev_rate_is_O_inv_n` — rate ordering.
- `berry_esseen_rate_involves_sqrt_n` — rate ordering for the (axiomatized) Berry–Esseen
  statement.
- `chebyshev_rate_implies_convergence` — bridge to the WLLN convergence-in-probability
  statement (uses `ProbabilityTheory.tendsto_measure_atTop_of_pos`).

Note: as of #13382 (2026-04-27), the `sampleMean_memLp` axiom was discharged.

---

## Insights

### `variance_sampleMean` is derivable, not bearer-blocked

The axiom `variance_sampleMean` is stated as

```lean
axiom variance_sampleMean
    (X : ℕ → Ω → ℝ) (n : ℕ) (hn : 0 < n)
    (σ_sq : ℝ) (hσ : σ_sq ≥ 0)
    (h_var : ∀ i, variance (X i) volume = σ_sq)
    (hℒp : ∀ i, MemLp (X i) 2 volume)
    (h_indep : Pairwise fun i j => IndepFun (X i) (X j) volume) :
    variance (sampleMean X n) volume = σ_sq / n
```

Mathlib v4.26.0 ships the two bearers that close the proof in ~25 LOC of Lean:

- `Mathlib.Probability.Moments.Variance.IndepFun.variance_sum`
  ```
  theorem IndepFun.variance_sum {ι : Type*} {X : ι → Ω → ℝ} {s : Finset ι}
      (hs : ∀ i ∈ s, MemLp (X i) 2 μ)
      (h : Set.Pairwise ↑s fun i j => X i ⟂ᵢ[μ] X j) :
      variance (∑ i ∈ s, X i) μ = ∑ i ∈ s, variance (X i) μ
  ```
- `Mathlib.Probability.Moments.Variance.variance_smul`
  ```
  theorem variance_smul (c : ℝ) (X : Ω → ℝ) (μ : Measure Ω) :
      Var[c • X; μ] = c^2 * Var[X; μ]
  ```

Combining: `Var(X̄ₙ) = Var((1/n) · ∑ᵢ Xᵢ) = (1/n)² · Var(∑ᵢ Xᵢ) = (1/n)² · n · σ² = σ² / n`.

The only friction is converting the slug's `Pairwise (i j : ℕ)` hypothesis to the
`Set.Pairwise (↑(Finset.range n))` form Mathlib expects. Recipe in
`s1-observe-variance-sampleMean-bearer-audit.md`.

### CLT / standardNormalCDF status in Mathlib v4.26

Mathlib has the building blocks but not the assembled CLT:

- `Mathlib.Probability.Distributions.Gaussian.{Basic, Real, Fernique}` — Gaussian measure and
  density.
- `Mathlib.MeasureTheory.Measure.CharacteristicFunction` — characteristic functions of
  measures.
- `Mathlib.Probability.Independence.CharacteristicFunction` — `IndepFun ↔ char-fn factors`.

But there is **no theorem** of the form
`tendsto (fun n ↦ μ (Set.Iic (sqrt n · (X̄ₙ − μ) / σ ≤ x))) atTop (𝓝 (Φ x))` in Mathlib v4.26.
The slug's `standardNormalCDF` axiom is therefore genuinely beyond upstream.

### Berry–Esseen status

No Berry–Esseen theorem exists in Mathlib v4.26 (no constant `berryEsseenConstant`, no error-
bound theorem). The slug's two axioms in this area are genuinely beyond upstream and require
either:

1. Smoothing-inequality approach (Esseen's original — requires the `|χ(t) − e^{-t²/2}| / t`
   estimate); or
2. Stein's method (more modern; would need new infrastructure for exchangeable pairs).

Both are research-level Lean formalizations (≥1000 LOC estimate).

### Gallery entry absent

`src/data/proofs/laws-of-large-numbers-oq-02/` does not exist. The Lean file is part of the
build (imported via `proofs/Proofs.lean`) but is not rendered in the gallery. This is an
enrichment task; flagging here so the next enricher claim picks it up.

---

## Dead Ends

None recorded yet (slug has not had failure-mode attempts).

---

## Cross-references

- `Proofs/LawsOfLargeNumbersOQ01.lean` (and `OQ01OQ01.lean`, `OQ01OQ02.lean`, `OQ01OQ03.lean`)
  — sibling OQ-01 development.
- `Proofs/LawsOfLargeNumbers.lean` — parent (WLLN + SLLN baseline).
- `Mathlib.Probability.StrongLaw` — Mathlib's SLLN.
- `Mathlib.Probability.Independence.CharacteristicFunction` — likely starting point for a
  future CLT formalization.
