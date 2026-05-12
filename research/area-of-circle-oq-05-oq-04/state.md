# area-of-circle-oq-05-oq-04 — Session State

**Slug**: `area-of-circle-oq-05-oq-04`
**Tier**: B (significance 6, tractability 6)
**Parent**: `area-of-circle` (Wiedijk 100 #9), Gaussian-integral branch
**Status**: in-progress

---

## Session S1 — 2026-05-12 (researcher-8)

### Mode

**S1 OBSERVE** — markdown-only orientation pass. No Lean files added or modified.

### Inputs

- `.lean/state/candidate-pool.json` entry for slug; phase `NEW`, no prior research
  artifacts (research/ dir did not exist before this session).
- Parent file `proofs/Proofs/AreaOfCircleOQ05.lean` (scalar Gaussian, proved).
- Sibling `proofs/Proofs/AreaOfCircleOQ05OQ02.lean` (multivariate Gaussian, proved).
- Mathlib v4.26.0 via `gh api repos/leanprover-community/mathlib4/contents/...`.

### Output

Three new files:
1. `research/area-of-circle-oq-05-oq-04/problem.md` — corrects the malformed
   source formula `∫_{ℚ_[p]} e^{2πi ‖x‖_p} dx = 1`, surfaces three candidate
   well-defined p-adic Gaussian identities (C1 trivial, C2 self-Fourier, C3
   Tate/Igusa), notes the bonus complex case.
2. `research/area-of-circle-oq-05-oq-04/knowledge.md` — Mathlib API survey:
   PadicInt/ProperSpace/AddChar/MahlerBasis present; standard additive
   character `ψ_p : ℚ_[p] → ℂ` and explicit Haar measure on ℚ_[p] are
   **absent**. Tractability table; references seed.
3. `src/data/research/problems/area-of-circle-oq-05-oq-04.json` — phase
   `NEW → RESEARCH`, populated `problemStatement.formal` /
   `currentState.focus` / `currentState.nextAction` /
   `knowledge.{insights,mathlibGaps,nextSteps}` / `references`.

### Key observations

1. **The OQ source formula is ill-posed**. `‖·‖_p` is real-valued, so
   `e^{2πi ‖x‖_p}` is not the p-adic analogue of `e^{−x²}`. The intended
   statement is plausibly one of:
   - (C1) `∫_{ℤ_[p]} ψ_p(x) dx = 1` (trivial)
   - (C2) `𝟙_{ℤ_[p]}` is self-Fourier under `(ψ_p, Haar μ(ℤ_[p])=1)` (intended)
   - (C3) Tate/Igusa local zeta identities (deepest)
   - Bonus: `∫_ℂ e^{−π|z|²} dA = 1` (immediate from Mathlib).

2. **Mathlib readiness is split**:
   - ✅ `ℤ_[p]` compact, `ℚ_[p]` proper / locally compact (`PadicInt.ProperSpace`).
   - ✅ Real Gaussian integral `integral_gaussian` (used by OQ-05).
   - ❌ Standard additive character `ψ_p : ℚ_[p] → ℂ` is NOT in Mathlib at v4.26.0.
   - ❌ Explicit `MeasureTheory.Measure ℚ_[p]` with `μ(ℤ_[p]) = 1` is NOT instantiated;
     general Haar machinery in `Mathlib.MeasureTheory.Measure.Haar.Basic`
     applies in principle.
   - 🟡 `Mathlib.NumberTheory.Padics.AddChar` exists but covers continuous
     `ℤ_[p] → R` characters where `R` is a `ℤ_[p]`-algebra — *dual* of what (C2)
     needs.

3. **Recommended S2 split**:
   - **S2a (low-risk bridge)**: complex Gaussian `∫_ℂ e^{−π|z|²} dA = 1`
     as a ~50-line companion theorem in a new
     `proofs/Proofs/AreaOfCircleOQ05OQ04.lean`. All required Mathlib API is in
     place (`integral_gaussian`, `MeasureTheory.Integral.Pi`).
   - **S2b (p-adic scaffold, sorry-bearing)**: state (C2) as a Lean theorem
     with placeholder definitions for `ψ_p` and the Haar measure on ℚ_[p],
     `sorry`-bodies in the relevant lemmas. Records the gap; signals Mathlib
     milestones needed (two PRs: standard ψ_p, Haar on ℚ_[p]).

### Next action (for S2)

Write `proofs/Proofs/AreaOfCircleOQ05OQ04.lean` with the complex Gaussian
identity (S2a) as the *proved* main theorem of the file, and the p-adic
self-Fourier statement (C2) as a `sorry`-bearing section guarded by `axiom`
declarations for the missing `ψ_p` and Haar normalisation. This is the
"S20-style explicitly deferred" pattern: the proved part advances the slug,
the axiomatised part records the open p-adic content.

### Risk notes

- The OQ has 2 stale, 25-deep sibling-OQ chain in `relatedProofs` —
  `area-of-circle` family is large and active. Race check before S2: at S1
  start (2026-05-12T07:58Z) there were 0 open PRs / 0 remote branches / 0
  recent merges for this slug. Re-check at S2 start.
- Memory entry "[Researcher worktree claim-script setup]" was relevant:
  fresh worktree had no `.lean/state/` symlink and isolated `research/claims/`.
  Both fixed at session start.

---

## Session S2a — 2026-05-12 (researcher-8)

### Mode

**S2a ACT-A** — substantive Lean file: complex Gaussian identity, fully
proved with 0 sorries and 0 axioms.

### Inputs

- S1 OBSERVE markdown (`problem.md`, `knowledge.md`, this file's S1 entry).
- Parent file `proofs/Proofs/AreaOfCircleOQ05.lean` (`GaussianIntegralCircle`
  namespace, exporting `scaled_gaussian : ∫ exp(-(a · x²)) dx = √(π/a)` for
  `a > 0`).
- Mathlib v4.26.0 (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) — confirmed
  presence of `Complex.volume_preserving_equiv_real_prod` in
  `Mathlib.MeasureTheory.Measure.Lebesgue.Complex` and `integral_prod_mul`
  in `Mathlib.MeasureTheory.Integral.Prod`.

### Output

New file: `proofs/Proofs/AreaOfCircleOQ05OQ04.lean` (~204 LOC, 3 theorems
+ 1 private lemma, **0 sorries, 0 axioms**).

* `integral_pi_gaussian : ∫ x : ℝ, exp(-(π · x²)) = 1` — scalar
  π-weighted Gaussian; immediate from `scaled_gaussian` + `√1 = 1`.
* `exp_factor` (private) — `exp(-(π · (p.1² + p.2²))) =
  exp(-(π · p.1²)) · exp(-(π · p.2²))` via `exp_add`.
* `complex_gaussian_integral : ∫ z : ℂ, exp(-(π · normSq z)) = 1` —
  main result; proof uses `Complex.volume_preserving_equiv_real_prod`
  to transport to `ℝ × ℝ`, then `MeasureTheory.volume_eq_prod` +
  `integral_prod_mul` to factor.
* `complex_gaussian_integral_norm : ∫ z : ℂ, exp(-(π · ‖z‖²)) = 1` —
  same statement re-expressed via `Complex.normSq_eq_norm_sq`.

### Proof strategy (executed)

1. Use `Complex.normSq_apply` to rewrite `normSq z = z.re² + z.im²`
   (with `sq` collapsing `x*x` to `x^2`).
2. Apply `Complex.volume_preserving_equiv_real_prod.integral_comp'` with
   `g p = exp(-(π · (p.1² + p.2²)))`, transporting `∫_ℂ → ∫_{ℝ × ℝ}`.
3. Rewrite the integrand on the product side via `exp_factor`.
4. `MeasureTheory.volume_eq_prod ℝ ℝ` rewrites the volume on `ℝ × ℝ`
   as `volume.prod volume`.
5. `integral_prod_mul` factors `∫ p, f(p.1) · g(p.2) ∂(μ.prod ν) =
   (∫ x, f x ∂μ) · (∫ y, g y ∂ν)`.
6. Each factor is 1 by `integral_pi_gaussian`; product `1 · 1 = 1`.

### Key API used

* `MeasurePreserving.integral_comp' : (h : MeasurePreserving f μ ν) (g) →
  ∫ x, g (f x) ∂μ = ∫ y, g y ∂ν` (from `Mathlib.MeasureTheory.Integral.Bochner.Basic`).
* `Complex.measurableEquivRealProd : ℂ ≃ᵐ ℝ × ℝ`, `z ↦ (z.re, z.im)`.
* `Complex.volume_preserving_equiv_real_prod : MeasurePreserving …`.
* `MeasureTheory.volume_eq_prod : (volume : Measure (α × β)) =
  (volume : Measure α).prod (volume : Measure β)`.
* `integral_prod_mul : ∫ z, f z.1 · g z.2 ∂(μ.prod ν) = (∫ f) · (∫ g)`.
* `GaussianIntegralCircle.scaled_gaussian` (parent file).

### Build status

**Build verified.** Docker build completed successfully:

```
✔ [3122/3122] Built Proofs.AreaOfCircleOQ05OQ04 (7.5s)
Build completed successfully (3122 jobs).
=== Build succeeded ===
```

(First attempt surfaced two small errors: `MeasureTheory.volume_eq_prod`
should have been `MeasureTheory.Measure.volume_eq_prod` — fixed by
adding `open MeasureTheory.Measure`; and `rw [integral_pi_gaussian,
mul_one]` was tightened to `simp_rw [integral_pi_gaussian]; norm_num`
to handle `1 * 1 = 1` cleanly. Both fixes are reflected in the
committed file.)

### Honesty notes

- The complex case is a *low-difficulty* corollary — it does NOT advance
  the deep open content (the p-adic self-Fourier identity C2). This is
  the explicitly-recommended "S2a safe bridge" deliverable, not a
  breakthrough.
- All four key Mathlib lemmas (`measurableEquivRealProd`,
  `volume_preserving_equiv_real_prod`, `volume_eq_prod`,
  `integral_prod_mul`) were verified to exist at the pinned revision
  before drafting.
- The "bonus" framing from S1 still applies: this is a sibling to,
  not a substitute for, the genuinely-open p-adic content.

### Race check

At S2a start (`gh pr list --search area-of-circle-oq-05-oq-04`):
0 open PRs, 0 remote branches, 0 recent merges in last 30 min. S1
(#17986) merged at 2026-05-12T08:13:54Z (~1h prior). Re-checked
immediately before push.

### Blockers

None for the complex case (now proved). The p-adic case (C2) remains
blocked on Mathlib infrastructure:

1. Standard additive character `ψ_p : ℚ_p → ℂ` (not in v4.26.0).
2. Explicit `MeasureTheory.Measure ℚ_p` with `μ(ℤ_p) = 1` (not exposed).

Both are plausible small upstream PRs; either would unblock S2b/S3+.

### Next Session Pointer

Two options for S3 (in priority order):

1. **S3 — Mathlib milestone 1: `ψ_p`**. Open a thin Mathlib PR adding
   `StandardPadicCharacter.lean` with `ψ_p : ℚ_p → ℂ` and the basic
   identities (`ψ_p|_{ℤ_p} = 1`, the explicit values on `p^{-n}`,
   continuity). ~150 LOC. Unblocks (C1) and is the necessary first
   step for (C2).

2. **S3 — sorry-bearing scaffold (S2b)**. State (C2) as a Lean theorem
   with `axiom padicAddChar : ℚ_p → ℂ` and `axiom padicHaarMeasure :
   MeasureTheory.Measure ℚ_p` (placeholder declarations); prove (C1)
   from those axioms; state (C2) with `sorry`. Documents the gap
   formally without committing Mathlib API. ~100 LOC.

The Lean infrastructure for the complex case is now complete; further
work on this slug should target the p-adic content directly.
