# Problem: Fourier series — generalize to vector-valued functions f : AddCircle T → E

**Slug**: `fourier-series-oq-02-oq-01-oq-02`
**Tier**: B (significance 6 / tractability 5, seeker-selected)
**Parent**: `fourier-series-oq-02-oq-01` (Riemann-Lebesgue via L² for Hölder f : AddCircle T → ℂ)
**Grandparent**: `fourier-series-oq-02` (quantitative Hölder RL: `‖ĉ_n‖ ≤ (C/2)(T/2|n|)^α`)
**Great-grandparent**: `fourier-series` (Mathlib's L²-Parseval RL infrastructure)

---

## Statement (Informal)

Does the L² Riemann-Lebesgue proof for Hölder f : AddCircle T → **ℂ** (parent slug
`fourier-series-oq-02-oq-01`, ~83 LOC, 0 sorries, 0 axioms) generalize to vector-valued
f : AddCircle T → **E**, where E is a Banach (or Hilbert) ℂ-vector space, using `MemLp` for
Bochner integrals?

Two sub-questions split by target structure on E:

1. **Hilbert E** (E carries an `InnerProductSpace ℂ E` instance). Parseval's identity
   generalizes to E-valued L²: `Σ ‖ĉ_n‖² = ∫ ‖f‖² < ∞` when E is a separable Hilbert space.
   The parent slug's 5-step chain (Hölder → Continuous → MemLp 2 → toLp → Parseval-RL)
   should port directly.

2. **General Banach E** (only `NormedSpace ℂ E`, no inner product). Parseval is **unavailable**
   (no Hilbert basis / orthonormality). The qualitative `ĉ_n → 0` still holds for L¹ ⊃ L²
   functions but requires a different route: **L¹ density of trigonometric polynomials**
   (the classical Riemann-Lebesgue lemma). For f Hölder, this is overkill compared to the
   Parseval route.

The seeker pool entry's tags (`harmonic-analysis`, `fourier-series`, `l2-spaces`) suggest
sub-question 1 is the intended scope, but the slug name does not commit to either.

---

## Formal Lean Signature (Target — Hilbert E Branch)

```lean
variable {T : ℝ} [hT : Fact (0 < T)]
variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  -- (separability inherited from second-countable-topology assumption needed for HilbertBasis)

theorem riemannLebesgue_of_holder_via_L2_vec
    (C : ℝ≥0) (α : ℝ≥0)
    (f : AddCircle T → E) (hf : HolderWith C α f)
    (hα : 0 < α) :
    Tendsto (fun n : ℤ => fourierCoeff f n) cofinite (𝓝 0) := by
  sorry  -- multi-cycle target; see knowledge.md §5 for skeleton
```

**Companion Banach-E variant (if separately tractable):**

```lean
variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem riemannLebesgue_of_continuous_Banach
    (f : AddCircle T → E) (hf : Continuous f) :
    Tendsto (fun n : ℤ => fourierCoeff f n) cofinite (𝓝 0) := by
  sorry  -- requires L¹ density route, not Parseval
```

---

## Prior Art

### Local Gallery

| Slug | Statement | Method | Status |
|------|-----------|--------|--------|
| `fourier-series` | RL for L² ℂ-valued via Parseval | Parseval `hasSum_sq_fourierCoeff` (Mathlib) | 0 sorries / 0 axioms |
| `fourier-series-oq-02` | Quantitative Hölder RL: `‖ĉ_n‖ ≤ (C/2)(T/2|n|)^α` | Direct integration by parts | (see meta.json) |
| `fourier-series-oq-02-oq-01` | Qualitative Hölder RL via L² route (ℂ-valued) | Chain: HolderWith → Continuous → MemLp 2 → `fourierCoeff_tendsto_zero` | 0 sorries / 0 axioms (~83 LOC) |
| **THIS SLUG** | Same as parent but for f : AddCircle T → E | **Open** — Parseval generalization to Hilbert E, or L¹-density route to Banach E | not yet attempted |

### Mathlib Status (pin `2df2f0150c…`, v4.26.0)

**Already generalized to E in Mathlib:**
- `fourierCoeff (f : AddCircle T → E) (n : ℤ) : E` at `Mathlib/Analysis/Fourier/AddCircle.lean:297`
  — typeclasses `[NormedAddCommGroup E] [NormedSpace ℂ E]` (Banach over ℂ).
- `fourierCoeff_eq_intervalIntegral`, `fourierCoeff.const_smul`, `fourierCoeff_congr_ae`,
  `fourierCoeffOn` — all generalized to E-valued, ~lines 302-360.

**ℂ-only Parseval / RL infrastructure:**
- `hasSum_fourier_series_L2 : ∀ (f : Lp ℂ 2 haarAddCircle), HasSum (... fourierLp ...) f`
  at `Mathlib/Analysis/Fourier/AddCircle.lean:408` — uses `HilbertBasis` (ℂ-only).
- `hasSum_sq_fourierCoeff` at line 415 — Parseval for L² ℂ.
- `tsum_sq_fourierCoeff` (line ~430) — tsum form.

**Local gallery (ℂ-only):**
- `Proofs.FourierSeries.fourierCoeff_tendsto_zero` at `proofs/Proofs/FourierSeries.lean:417`
  — uses Parseval-summability from Mathlib's `hasSum_sq_fourierCoeff`.

---

## Significance

- **Theoretical bridge.** The L² Parseval route is conceptually cleaner than the quantitative
  Hölder bound and uses standard Hilbert-space techniques; the proof should port to any
  separable Hilbert E with minimal adaptation.
- **Mathlib leverage.** Lifts an existing Mathlib generalization (`fourierCoeff` already E-valued)
  one step further into the qualitative RL pipeline. If a Hilbert-E version of
  `hasSum_sq_fourierCoeff` doesn't yet exist in Mathlib, this gallery proof could either
  (a) build it locally as a stepping stone, or (b) eventually upstream to Mathlib.
- **Tractability.** Estimate: Hilbert-E branch ≤ 150 LOC if Mathlib's `HilbertBasis` machinery
  generalizes; ≥ 300 LOC if we need to rebuild Parseval for E. See `knowledge.md` §4.

---

## Acceptance Criteria

Bootstrap session (this PR) acceptance:
- [x] `research/problems/<slug>/{problem.md,knowledge.md,state.md,sessions/<date>-...md}` created.
- [x] Mathlib bearer pins recorded with file paths + line numbers + commit SHA `2df2f0150c…`.
- [x] Multi-cycle phase plan written (≥ 6 phases through to ACT / VERIFY / COMPLETED).
- [x] Decision recorded: which branch (Hilbert E vs Banach E) is the primary target.

Future-cycle acceptance (out of scope for S1):
- Hilbert E theorem proved with 0 sorries / 0 axioms.
- Gallery entry `src/data/proofs/fourier-series-oq-02-oq-01-oq-02/` with meta.json, annotations.
- Lean file `proofs/Proofs/FourierSeriesOQ02OQ01OQ02.lean`.

---

> _Phase note: this skill maps "S1 OBSERVE" to canonical "ORIENT" phase
> (the slug had zero prior `research/problems/` content; this PR seeds it)._
