# Knowledge Base: egorov-theorem-oq-01-oq-03

Sharpness of Egorov's theorem: the **finite-measure hypothesis is essential**.

---

## Problem Summary

Egorov's theorem upgrades a.e. convergence to uniform convergence off a set of
arbitrarily small measure — but only on a measure space of **finite** measure.
This problem asks to formalize that the finiteness hypothesis cannot be dropped:
on `(ℝ, Lebesgue)` exhibit a sequence converging to `0` everywhere pointwise that
admits no finite-measure set off which the convergence is uniform.

**Witness:** the marching indicators `fₙ = 𝟙_[n,n+1]`.

---

## Status: COMPLETED (verified, 0-axiom)

Proved in `proofs/Proofs/EgorovTheoremOQ01OQ03.lean` (163 lines, 6 theorems,
1 definition, 0 sorries, 0 axioms — only `propext`/`Classical.choice`/`Quot.sound`).

---

## Session 2026-06-28 (researcher-3) — integral-side face (mass escape)

Added the integral reading of the same marching counterexample (SOLVED → looked outward):
- `marching_integral_eq_one (n) : ∫ marching n = 1` — each bump has unit mass.
- `marching_integral_not_tendsto_zero` — `∫ fₙ = 1 ↛ 0 = ∫(lim fₙ)`, so the same
  example also breaks the limit–integral interchange on `(ℝ, vol)`. Constant-1 integral
  sequence converges to 1 ≠ 0 via `tendsto_const_nhds_iff`.

GOTCHA: `setIntegral_const` yields `volume.real (Icc ..)` (the `Measure.real` form), NOT
`(volume ..).toReal` syntactically — `Real.volume_Icc` does not match. Use
`Real.volume_real_Icc_of_le (h : a ≤ b) : volume.real (Icc a b) = b - a`, then
`smul_eq_mul; ring`.

---

## Session 2026-06-27 (Session 1) - Construct and prove

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Defined `marching n = (Set.Icc n (n+1)).indicator 1`, the unit bump on `[n,n+1]`.
- Proved `marching_tendsto_zero`: `fₙ(x) → 0` at **every** `x ∈ ℝ` (eventually-0
  via `exists_nat_gt` + `Set.indicator_of_notMem`, then `tendsto_congr'`).
- Proved the headline `marching_not_tendstoUniformlyOn_of_volume_lt_top`: for any
  `s` with `vol s < ⊤`, `fₙ` is not uniform on `sᶜ`.
- Packaged `volume_finite_hypothesis_essential` (no finite-measure exceptional set
  exists) and `marching_not_tendstoUniformlyOn_univ` (`s = ∅` corollary).

### Key Findings
- The negation of `TendstoUniformlyOn` is clean via `Metric.tendstoUniformlyOn_iff`
  at `ε = 1/2`: since the indicator is `{0,1}`-valued, `dist(0, fₙ x) < 1/2` forces
  `fₙ x = 0`, i.e. `[n,n+1] ⊆ s` for all large `n`.
- The contradiction is purely measure-monotone: `[N,∞) ⊆ s` ⇒ `vol s ≥ vol[N,∞) = ∞`
  via `Real.volume_Ici` + `measure_mono`. **No measurability of `s` is needed**, so
  the statement is slightly stronger than the textbook (measurable-`s`) version.
- This is genuinely distinct from the parent `egorov-theorem-oq-01`, which proves
  the *removed null set* cannot be omitted on a finite-measure example (`xⁿ` on
  `[0,1]`). Here the *ambient finiteness* itself is what fails. Together they bound
  Egorov from both sides.

### Mathlib notes
- `Real.volume_Ici : volume (Set.Ici a) = ∞` — exactly the infinite-tail fact needed.
- `Set.indicator_of_not_mem` is deprecated → use `Set.indicator_of_notMem`.
- Floor placement of `x ≥ N` into a bump: `Nat.le_floor`, `Nat.floor_le`,
  `Nat.lt_floor_add_one`.

### Files Modified
- `proofs/Proofs/EgorovTheoremOQ01OQ03.lean` (new)
- `src/data/proofs/egorov-theorem-oq-01-oq-03/{meta,annotations}.json` (new)

### Next Steps
- None required; problem resolved. Possible future follow-up: derive the same
  sharpness from a σ-finite-but-infinite abstract measure space rather than the
  concrete `(ℝ, Lebesgue)` instance.

## Session 2026-06-28 (Session 3, researcher-1) — convergence-in-measure face

SOLVED → looked outward. Added the fourth reading of the marching counterexample:
`marching_not_tendstoInMeasure` — fₙ → 0 everywhere pointwise but does NOT converge
to 0 in measure on (ℝ, vol). On a finite-measure space a.e. convergence forces
convergence in measure (the easy half behind Egorov); this is the infinite-measure
failure.

- For ε = 1/2 the bad set `{x | 1/2 ≤ edist (marching n x) 0}` is exactly `Icc n (n+1)`,
  volume constant 1 → the measure sequence is const 1 ↛ 𝓝 0.
- `TendstoInMeasure` (Mathlib MeasureTheory.Function.ConvergenceInMeasure) uses
  `edist` (ℝ≥0∞), ε : ℝ≥0∞: `∀ ε>0, Tendsto (fun i => μ {x | ε ≤ edist (f i x) (g x)}) l (𝓝 0)`.
- GOTCHAs: `edist_dist`+`Real.dist_eq`+`sub_zero`+`abs_one`+`ENNReal.ofReal_one` to compute
  edist 1 0 = 1; `ENNReal.half_le_self : a/2 ≤ a`; `ENNReal.half_pos one_ne_zero : 0 < 1/2`;
  `edist_self` for the x∉Icc branch; finish via `hmeas.congr hvol` + `tendsto_const_nhds_iff`.
  Needed an explicit `import Mathlib.MeasureTheory.Function.ConvergenceInMeasure`.
- Verified: lake env lean clean; #print axioms = [propext, Classical.choice, Quot.sound].
  File now 210 lines, 7 theorems, 0 sorry / 0 axiom.
