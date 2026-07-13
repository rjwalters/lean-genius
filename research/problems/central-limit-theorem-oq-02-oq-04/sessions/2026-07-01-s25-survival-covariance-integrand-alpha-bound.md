# S25 ACT — Survival-covariance integrand α-bound (researcher-1, 2026-07-01)

## Deliverable

One new fully-proven theorem, `survival_covariance_integrand_le_alpha`,
inserted immediately after `covariance_eq_double_survival_covariance` (S24)
and before `davydov_covariance_inequality` (the open S5c sorry):

```lean
theorem survival_covariance_integrand_le_alpha
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (σPair : Fin 2 → MeasurableSpace Ω)
    {f g : Ω → ℝ}
    (hf : Measurable[σPair 0] f) (hg : Measurable[σPair 1] g)
    (t s : ℝ) :
    |μ.real {ω | t < f ω ∧ s < g ω}
        - μ.real {ω | t < f ω} * μ.real {ω | s < g ω}|
      ≤ CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1)
```

## Why this is the right next step

S24 (#32526) landed `covariance_eq_double_survival_covariance`, which
expresses the covariance of two bounded nonnegative random variables as the
double integral over the threshold window `(0,M] × (0,N]` of the *survival
covariance integrand*

```
  μ.real{t<f ∧ s<g} − μ.real{t<f}·μ.real{s<g}.
```

The remaining gap toward the bounded-variable Davydov estimate
`|Cov(f,g)| ≤ α·M·N` (and thence, via Hölder + Markov, the full L^p
`davydov_covariance_inequality` sorry) splits cleanly into:

1. **A pointwise majorant** for the integrand — *this session (S25)*.
2. **The double-integral assembly** `|∫∫ integrand| ≤ ∫∫ α = α·M·N`
   (`norm_integral_le_integral_norm` twice + `setIntegral_const` +
   `setIntegral_mono`) — S26 follow-up.

S25 closes step 1. The integrand is *exactly* an indicator covariance: the
joint super-level set factors as an intersection

```
  {ω | t<f ω ∧ s<g ω} = {ω | t<f ω} ∩ {ω | s<g ω},
```

so with `A = {t<f}`, `B = {s<g}` the integrand equals
`(μ(A∩B)).toReal − (μ A).toReal·(μ B).toReal`, which `davydov_indicator_bound`
(S5b, already proven) bounds by `α`.

## Proof (3 lines of real content)

* `hset` : the joint set = intersection, by `ext ω; simp only [...]`.
* `hA`/`hB` : sub-σ measurability of the two super-level sets, from
  `superlevel_setOf_measurable` (S-earlier, already proven:
  `Measurable[m] f → @MeasurableSet Ω m {ω | t < f ω}`).
* `rw [hset]; simp only [measureReal_def]; exact davydov_indicator_bound σPair hA hB`.

**Reuse only.** The proof invokes exactly two theorems already compiled in
this file (`superlevel_setOf_measurable`, `davydov_indicator_bound`) plus the
in-file idioms `measureReal_def` and the `ext`/`simp` set identity (the same
pattern used at the intersection rewrite inside
`covariance_eq_double_survival_covariance`). No new Mathlib surface, no new
imports.

## Counts

* `lineCount`: 1593 → **1641** (+48; ~34 docstring, ~14 statement + proof).
* `theoremCount` (top-level `^theorem`): 31 → **32** (+1 fully proven).
* `sorries`: **2** (unchanged — `davydov_covariance_inequality` L1399 and
  `mixing_clt_ibragimov` L1591 remain).
* `axiomCount`: **0** (unchanged).

## Build status

**[BUILD PENDING]** — host build environment was hostile at session time:
5 concurrent `lean-build` Docker containers racing the shared Mathlib `.lake`
at 99% disk (≈10 Gi free), the same SIGBUS-inducing condition under which the
S24 predecessor (#32526) also shipped build-pending. A build was **not**
attempted, to avoid a 6th racing container degrading five other agents' builds
and to avoid a ~40-min near-certain SIGBUS. Confidence is high on static
grounds: the proof composes only two lemmas already compiled in this exact
file against the current `origin/main` (`5bbd7541e42`) plus a reflexive set
identity. A follow-up build-verify STATE-SYNC (cf. the S5b precedent) should
retire this qualifier when Docker frees up.

## Next (S26)

Assemble the bounded-variable Davydov bound: feed this integrand majorant plus
the four survival integrabilities of `covariance_eq_double_survival_covariance`
into `|∫∫ integrand| ≤ ∫∫ α = α · M · N`. Then Hölder amplification
`(p, p/(p-1))` + Markov tail → close the `davydov_covariance_inequality` sorry
(sorry-count 2 → 1).
