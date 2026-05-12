# area-of-circle-oq-05-oq-04 — Knowledge / Mathlib API survey

S1 audit of what Mathlib v4.26.0 provides, against the three candidate
formal statements in `problem.md`. All paths below are verified by direct
`gh api repos/leanprover-community/mathlib4/contents/...` fetch on
2026-05-12; no `tsx`/`pnpm` involved.

## Available Mathlib infrastructure

### `Mathlib.NumberTheory.Padics.*`

- `Mathlib/NumberTheory/Padics/PadicNumbers.lean` — `ℚ_[p]` as completion of ℚ
  under the p-adic norm; field structure, ring norm, completeness.
- `Mathlib/NumberTheory/Padics/PadicIntegers.lean` — `ℤ_[p]` as subring of ℚ_[p]
  with norm ≤ 1; local ring, DVR, nonarchimedean normed ring.
- `Mathlib/NumberTheory/Padics/PadicNorm.lean` — `padicNorm : ℚ → ℚ`,
  `padicValRat`, `padicValNat`. Real-valued norm via `Padic.norm`.
- `Mathlib/NumberTheory/Padics/ProperSpace.lean` — `ℤ_[p]` is `CompactSpace`,
  `ℚ_[p]` is `ProperSpace`. (Crucially: `ℚ_[p]` is locally compact.)
- `Mathlib/NumberTheory/Padics/AddChar.lean` — continuous additive characters
  `ℤ_[p] → R` for ultrametric normed `ℤ_[p]`-algebras `R`. Provides
  `addChar_of_value_at_one`, `continuousAddCharEquiv`, Mahler-transform bridge.
  NOTE: this is for *characters into* a `ℤ_[p]`-algebra, NOT the standard
  C-valued character `ψ_p : ℚ_[p] → ℂ`. The latter does not appear to be in
  Mathlib at v4.26.0.
- `Mathlib/NumberTheory/Padics/MahlerBasis.lean` — Mahler's theorem; bridge to
  Fourier analysis on `ℤ_[p]`.
- `Mathlib/NumberTheory/Padics/RingHoms.lean`, `Hensel.lean`, `WithVal.lean`,
  `ValuativeRel.lean`, `HeightOneSpectrum.lean`, `Complex.lean` — additional
  algebraic structure (not directly relevant to S1).

### `Mathlib.MeasureTheory.Measure.Haar.*`

- `Mathlib/MeasureTheory/Measure/Haar/Basic.lean` — Haar measure on locally
  compact topological groups (general construction; the existence theorem).
- `Mathlib/MeasureTheory/Measure/Haar/Unique.lean` — Haar measure uniqueness up
  to scaling.
- `Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`,
  `OfBasis.lean`, `Extension.lean`, `Disintegration.lean` — variants;
  the OfBasis file is what we'd use to *normalise* on ℤ_[p].
- `Mathlib/MeasureTheory/Measure/Haar/DistribChar.lean` — Haar mod-character;
  relevant for `‖·‖_p^s` integrals (C3) eventually.

### Existing real Gaussian infrastructure (already used in OQ-05)

- `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral` —
  `integral_gaussian : ∀ b : ℝ, ∫ x, exp(-b * x^2) = √(π/b)` for `b > 0`.
- `Mathlib.MeasureTheory.Integral.Pi` — Fubini-style ℝⁿ integration
  (used by `AreaOfCircleOQ05OQ02` for the multivariate case).

## What's MISSING from Mathlib (gaps to surface)

1. **Standard p-adic additive character `ψ_p : ℚ_[p] → ℂ`** with
   `ψ_p|_{ℤ_[p]} = 1` and `ψ_p(p^{-n}) = e^{2πi · a_n}` where `a_n ∈ ℚ ∩ [0,1)`
   is the "fractional part" component. Mathlib has only `ℤ_[p]`-algebra-valued
   characters (`Mathlib.NumberTheory.Padics.AddChar`), which is the *dual*
   direction (characters *of* ℤ_[p] into a Banach algebra). The standard
   `ψ_p : ℚ_[p] → ℂˣ` of class field theory is NOT in Mathlib at v4.26.0.

2. **Explicit `MeasureTheory.Measure` on ℚ_[p]**. The general Haar construction
   in `Mathlib.MeasureTheory.Measure.Haar.Basic` produces a measure on any
   locally compact group, and `ℚ_[p]` qualifies (proper metric space, additive
   group). But no file in `Mathlib.NumberTheory.Padics` instantiates
   `MeasureTheory.Measure ℚ_[p]` with the normalisation `μ(ℤ_[p]) = 1`. This
   would be a useful small Mathlib PR.

3. **Bruhat–Schwartz functions / Fourier transform on ℚ_[p]**. No analogue of
   `Mathlib.Analysis.Fourier.FourierTransform` (which is set up for
   `ℝⁿ` / locally compact abelian groups in the abstract) appears to be
   specialised to ℚ_[p]. The general `Mathlib.Analysis.Fourier.AddCircle` and
   `Mathlib.Analysis.Fourier.PontryaginDual` are nearby but not directly
   applicable until ψ_p is constructed.

## Tractability assessment of the three candidates

| Candidate | Mathlib readiness | S1 effort to formalize | Notes |
| --- | --- | --- | --- |
| (C1) trivial character on ℤ_[p] | LOW — needs to construct ψ_p first | medium-high | even the "obvious" statement requires constructing ψ_p; the *content* is then `∫ 1 dμ = μ(ℤ_[p]) = 1` |
| (C2) self-Fourier of `𝟙_{ℤ_[p]}` | LOW — needs ψ_p + Haar measure + character sum identity on `ℤ/p^k ℤ` | high | full content; deserves a multi-session attack |
| (C3) Tate / Igusa local zeta | NONE — needs ψ_p, Haar, p-adic Fourier, Mellin | very high | research-grade; Mathlib roadmap target |
| Complex Gaussian (bonus) | HIGH — already mostly in `Gaussian.GaussianIntegral` + `MeasureTheory.Integral.Pi` | LOW | ~30 line companion lemma; could be added to AreaOfCircleOQ05 directly |

## Recommended S2 plan

**Two parallel tracks**, in order of decreasing safety:

1. **S2a (safe bridge)**: Add `∫_ℂ e^{−π|z|²} dA(z) = 1` as a small companion
   theorem either in `AreaOfCircleOQ05.lean` (extending the existing real
   Gaussian file) or in a new `AreaOfCircleOQ05OQ04.lean` scaffold. Reduces to
   product of two real Gaussians by writing `|z|² = x² + y²` and applying
   Fubini. Mathlib has all required infrastructure. Estimated: ~50 LOC, no
   sorries.

2. **S2b (p-adic scaffold, with sorries)**: Create `AreaOfCircleOQ05OQ04.lean`
   with stubs:
   - `axiom padicAddChar : ℚ_[p] → ℂ` (or `def padicAddChar … := by sorry`)
   - the Haar measure normalised on ℤ_[p]
   - the statement of (C2), with `sorry`-proof
   This records the gap formally and signals the Mathlib milestones needed.

## References (to seed the JSON)

- Tate, J. "Fourier analysis in number fields and Hecke's zeta-functions"
  (1950 thesis, in Cassels–Fröhlich, *Algebraic Number Theory*).
- Igusa, J.-I. "An introduction to the theory of local zeta functions"
  (AMS/IP Studies in Advanced Math 14, 2000).
- Gouvêa, F.Q. *p-adic Numbers: An Introduction* (Springer UTM, 3rd ed. 2020).
- Mahler, K. "An interpolation series for continuous functions of a p-adic
  variable" (J. Reine Angew. Math. 199, 1958, 23–34).
- Lewis, R.Y. "A formal proof of Hensel's lemma over the p-adic integers"
  (CPP 2019) — the original Mathlib `PadicInt` paper.

## Mathlib PRs that would unblock this OQ

(For tracking; not actions for this session.)

- Construct `ψ_p : ℚ_[p] → ℂ` (additive character, standard normalisation).
  Likely target file: `Mathlib/NumberTheory/Padics/StandardAdditiveCharacter.lean`.
- Instantiate `MeasureTheory.Measure ℚ_[p]` from
  `Mathlib.MeasureTheory.Measure.Haar.Basic` with `μ(ℤ_[p]) = 1`. Likely target
  file: `Mathlib/NumberTheory/Padics/HaarMeasure.lean`.
- Prove `𝟙_{ℤ_[p]}` is self-Fourier under those data.

---

## S2a (2026-05-12) — Complex case proved

Status of the four candidates:

| Candidate | Status after S2a |
| --- | --- |
| (C1) trivial character on ℤ_[p] | Still blocked — needs `ψ_p` |
| (C2) self-Fourier of `𝟙_{ℤ_[p]}` | Still blocked — needs `ψ_p` + Haar on ℚ_[p] |
| (C3) Tate / Igusa local zeta | Still far |
| Complex Gaussian (bonus) | **PROVED** in `Proofs/AreaOfCircleOQ05OQ04.lean` |

### Mathlib API confirmed at v4.26.0 (rev `2df2f015`)

* `Complex.measurableEquivRealProd : ℂ ≃ᵐ ℝ × ℝ` and its `_symm_apply`
  simp lemma. Source: `Mathlib/MeasureTheory/Measure/Lebesgue/Complex.lean`.
* `Complex.volume_preserving_equiv_real_prod : MeasurePreserving …` — the
  push-forward of `volume : Measure ℂ` along the equiv is the product
  measure on `ℝ × ℝ`. Same file.
* `MeasureTheory.volume_eq_prod (α β) [MeasureSpace α] [MeasureSpace β] :
  (volume : Measure (α × β)) = (volume : Measure α).prod (volume : Measure β)`.
  Source: `Mathlib/MeasureTheory/Measure/Prod.lean`.
* `integral_prod_mul {L : Type*} [RCLike L] (f : α → L) (g : β → L) :
  ∫ z, f z.1 * g z.2 ∂(μ.prod ν) = (∫ x, f x ∂μ) * ∫ y, g y ∂ν`. Source:
  `Mathlib/MeasureTheory/Integral/Prod.lean`. Works for `L = ℝ` (used here).
* `MeasurePreserving.integral_comp' {β} {ν} {f : α ≃ᵐ β} (h : ...)
  (g : β → G) : ∫ x, g (f x) ∂μ = ∫ y, g y ∂ν`. Source:
  `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`.

### Mathlib API still missing (unchanged from S1)

1. `ψ_p : ℚ_[p] → ℂ` standard additive character — needed for (C1)/(C2).
2. Explicit `MeasureTheory.Measure ℚ_[p]` with `μ(ℤ_[p]) = 1` — needed
   for any integral identity on `ℚ_[p]` /`ℤ_[p]`.

### Lessons recorded

* The `Complex.normSq z = z.re² + z.im²` identity is via
  `Complex.normSq_apply`, *not* `Complex.normSq_def`; `sq` simp-collapses
  `x * x` to `x ^ 2`.
* The integrand `exp(-(π · (p.1² + p.2²)))` factors cleanly via
  `← Real.exp_add` + `ring` after the appropriate `congr 1` step.
* `integral_prod_mul` requires the codomain to be `RCLike`, which `ℝ`
  satisfies, but Lean needs explicit `(μ := volume)` `(ν := volume)`
  annotations to pick up the right product measure when both factors
  are `volume : Measure ℝ`.

## S4a Mathlib API confirmed (verified 2026-05-12 against v4.26.0)

### n-fold Fubini

* `MeasureTheory.integral_fintype_prod_volume_eq_prod {ι : Type*} [Fintype ι]
  {E : ι → Type*} (f : (i : ι) → E i → 𝕜)
  [∀ i, MeasureSpace (E i)] [∀ i, SigmaFinite (volume : Measure (E i))] :
  ∫ x : (i : ι) → E i, ∏ i, f i (x i) = ∏ i, ∫ x, f i x` — n-fold Fubini.
  Source: `Mathlib/MeasureTheory/Integral/Pi.lean:114`.
* `MeasureTheory.integral_fintype_prod_volume_eq_pow {ι : Type*} [Fintype ι]
  {E : Type*} (f : E → 𝕜) [MeasureSpace E] [SigmaFinite (volume : Measure E)] :
  ∫ x : ι → E, ∏ i, f (x i) = (∫ x, f x) ^ (Fintype.card ι)` — uniform
  n-fold Fubini (all factors share `f`). Source: same file, line 123.
  Used by S4a in `complex_gaussian_integral_scaled_pow`.

### Sum/product algebra

* `Real.exp_sum (s : Finset α) (f : α → ℝ) : Real.exp (∑ x ∈ s, f x) =
  ∏ x ∈ s, Real.exp (f x)`. Source:
  `Mathlib/Analysis/Complex/Exponential.lean:222`. (Also `Complex.exp_sum`
  at line 141 of the same file.)
* `Finset.mul_sum : b * ∑ i ∈ s, f i = ∑ i ∈ s, b * f i` — distributes
  a scalar into a sum.
* `Finset.sum_neg_distrib : ∑ i ∈ s, -f i = -∑ i ∈ s, f i` — applied
  backward (`← Finset.sum_neg_distrib`) to push `-` inside `∑`. Same
  combo used in parent `AreaOfCircleOQ05OQ02.diagonal_gaussian`.

### Cardinality

* `Fintype.card_fin (n : ℕ) : Fintype.card (Fin n) = n`. Source:
  `Mathlib/Data/Fintype/Card.lean:485`.

### Lessons (S4a)

* The S4a skeleton is identical to the parent file's real-axis
  `diagonal_gaussian` (`AreaOfCircleOQ05OQ02.lean`), differing only in
  that the per-axis factor is `complex_gaussian_integral_scaled_norm`
  (2-real-dim) rather than `scaled_gaussian` (1-real-dim).
* `integral_fintype_prod_volume_eq_pow` is preferable to
  `integral_fintype_prod_volume_eq_prod` when all factors are the same:
  it sidesteps the per-index `Finset.prod_congr` reduction and gives the
  final `(π/b)^n` form directly via `Fintype.card_fin`.
* The reduction `exp(-(b · ∑ ‖zᵢ‖²)) = ∏ᵢ exp(-(b · ‖zᵢ‖²))` is a
  three-step rewrite chain that doesn't need any custom lemma:
  `Finset.mul_sum` distributes `b`, `← Finset.sum_neg_distrib` pushes
  the negation inside, and `Real.exp_sum` converts the resulting
  `exp (∑ ...)` to `∏ exp (...)`.
* No measure-preserving change of variables is needed at the
  n-dimensional level: the `Fin n → ℂ` integrand factors before any
  transport, so we never need to interact with `Complex.measurableEquivRealProd`
  beyond what was already done in S2a / S3 for the per-axis factor.

## S5 Mathlib API confirmed (verified 2026-05-12 against v4.26.0)

### Translation invariance

* `MeasureTheory.integral_add_right_eq_self {G : Type*} {E : Type*}
  [MeasurableSpace G] [Group G] [TopologicalSpace G] [TopologicalGroup G]
  [BorelSpace G] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure G} [IsAddRightInvariant μ] (f : G → E) (g : G) :
  ∫ x, f (x + g) ∂μ = ∫ x, f x ∂μ`
  — translation invariance of integrals against a right-invariant measure.
  Source: `Mathlib/MeasureTheory/Group/Integral.lean`.
* `volume : Measure ℂ` carries `IsAddHaarMeasure` (via the `MeasureSpace`
  instance through `Complex.measurableEquivRealProd` plus inherited Haar
  property of `ℝ × ℝ`), hence both `IsAddLeftInvariant` and
  `IsAddRightInvariant` (abelian group).

### Pitfall: HOU through `fun w => f w`

* `rw [integral_add_right_eq_self]` fails when the integrand has the
  shape `(fun w => exp(-(b · ‖w‖²))) (z + (-c))`: the rewrite engine
  can't pattern-match `∫ x, ?f (x + ?g) ∂?μ` against an integrand whose
  outer function is a lambda. Symptom (v4.26.0):
  > `Tactic 'rewrite' failed: Did not find an occurrence of the pattern`
  > `∫ (x : ?m), ?f (x + ?g) ∂?m in the target expression`
  > `∫ (z : ℂ), (fun w => rexp (-(b * ‖w‖^2))) (z + -c) = π / b`
* **Fix**: don't rewrite — instead chain via `.trans` with explicit `f`:
  ```lean
  exact (integral_add_right_eq_self (fun w : ℂ => Real.exp (-(b * ‖w‖^2))) (-c)).trans
        (complex_gaussian_integral_scaled_norm b hb)
  ```
  Lean accepts the result via β-defeq.

### `sub_eq_add_neg` rewrite under integrals

* To convert `f (z - c)` to `f (z + (-c))` inside an integral, the
  cleanest pattern (matching `ShannonEntropyOQ01.gaussian_variance`):
  ```lean
  have key : ∀ z, (fun w => f w) (z + (-c)) = f (z - c) := by
    intro z; show f (z + (-c)) = f (z - c); rw [← sub_eq_add_neg]
  rw [show (fun z => f (z - c)) = (fun z => (fun w => f w) (z + (-c))) from
        funext (fun z => (key z).symm)]
  ```
  The `show` step is essential: it tells Lean to β-reduce the lambda
  application so the subsequent `rw [← sub_eq_add_neg]` finds its
  pattern.

### Lessons (S5)

* Translation invariance is the simplest non-trivial extension of the S3
  parametric Gaussian: it costs no new Mathlib imports (the
  `Measure.Group.Integral` machinery is transitively pulled in by the
  Gaussian integral module) and replicates the real-line idiom that
  already appears in `ShannonEntropyOQ01.lean` and `FourierSeriesOQ02.lean`.
* The two-parameter `(c, b)` complex Gaussian density emerges as a
  one-line corollary (`integral_const_mul` + the shifted parametric
  integral + `field_simp`). This is the natural "Gaussian density with
  mean and scale" object that the OQ p-adic source aspired to.
* The `c = 0` and `b = 1` specialisations reduce to S3 and S2a
  respectively, so the S5 additions strictly subsume the unshifted
  unit-weight cases — useful for downstream consumers that prefer the
  general statement.
