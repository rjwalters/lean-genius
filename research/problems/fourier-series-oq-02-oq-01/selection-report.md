# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 84 available, 1257 in-progress, 589 completed, 7 graduated

## Selected Problem

- **ID**: fourier-series-oq-02-oq-01
- **Name**: Alternative Mathlib Proof of riemannLebesgue_of_holder
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 7/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Highly specific and tractable (tract=7)**: The problem has an exact proof strategy already laid out: use the Mathlib chain Hölder → Continuous → L¹ → Riemann-Lebesgue. All intermediate lemmas exist in Mathlib. This is a proof engineering problem, not a discovery problem — very amenable to autonomous research.
2. **Theory-level value**: Replacing a quantitative decay argument with a qualitative Riemann-Lebesgue application demonstrates composability of Mathlib's analysis library. The resulting proof would be significantly shorter and more readable, with Mathlib PR potential.
3. **Domain diversity**: Fourier analysis / real analysis — not covered in recent seeker batches. Complements the Ptolemy (geometry) and Lebesgue (measure theory) selections in this cycle.

## Quality Gate

- Near-duplicate? **No** — the existing `riemannLebesgue_of_holder` proof is quantitative (decay rate); this asks for a qualitative alternative. Different proof technique, potentially shorter.
- Shallow specialization? **No** — proves an important direction in the theory of Fourier series: Hölder continuity → Fourier coefficient decay.
- One-off example? **No** — applies to all Hölder continuous functions on `AddCircle T`.
- Significance ≥ 3? **Yes** (7/10).
- Domain repeated last 3? **No** — Fourier analysis is fresh.

## Rejection Summary

- **Candidates considered**: 84
- **Confidence**: high — score 77, clearly ahead of all rejected candidates

## Related Gallery Proofs

- `fourier-series-oq-02`: Parent gallery proof of `FourierHolderDecay` with existing `riemannLebesgue_of_holder`.
- `fourier-series`: Base Fourier series gallery entry — `fourierCoeff` definitions used here.

## Suggested First Steps

1. **OBSERVE**: Read `FourierHolderDecay.lean` source. Identify exactly what `riemannLebesgue_of_holder` currently proves and how. Find the quantitative bound it uses.
2. **ORIENT**: Search Mathlib for `MeasureTheory.Integrable.tendsto_set_integral`, `ContinuousOn.integrable`, and `MeasureTheory.riemannLebesgue` (or `tendsto_integral_exp_mul_atTop`). Verify the chain `IsHolderOnCircle → Continuous → Integrable → riemannLebesgue`.
3. **DECIDE**: Draft the alternative proof:
   ```lean
   theorem riemannLebesgue_of_holder' (C : ℝ≥0) (α : ℝ≥0) (f : AddCircle T → ℂ)
       (hf : IsHolderOnCircle C α f) (hα : 0 < α) :
       Tendsto (fun n : ℤ => fourierCoeff f n) cofinite (𝓝 0) := by
     have hcont : Continuous f := hf.continuous  -- Hölder → continuous
     have hint : Integrable f := hcont.integrable  -- continuous → L¹
     exact MeasureTheory.fourier_integral_tendsto_zero hint  -- L¹ → RL
   ```
   Then verify each step has the right Mathlib lemma names.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 84 |
| In Progress | 1257 |
| Completed | 589 |
| Graduated | 7 |
| Blocked | 2 |

## Candidate Pool Health

- Pool depth: **adequate** (84 >> threshold 15)
- Recommendation: Pool healthy
- Next refresh recommended: 30 minutes

## Initialized

- [x] Research workspace exists at `research/problems/fourier-series-oq-02-oq-01/`
- [x] problem.md populated with formal statement and proof strategy
- [x] Registered in `research/db/knowledge.db` with status 'available'
- [x] Ready for /researcher
