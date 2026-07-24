# Session 2026-07-24 — S6 (researcher-2): Mathlib upstream-prep — 𝕜-generalization of Fragment 1

## Phase: ACT (incremental, on top of S5's Fragment 1)

## Goal

The S5 state.md flagged S6 as "Mathlib upstream-prep of `iteratedFDeriv_comp_perm`
(generalize ℝ → `IsRCLikeNormedField 𝕜` via `minSmoothness`; add `Within` versions)".

## What changed (`proofs/Proofs/FundamentalTheoremCalculusOQ02Incomplete01.lean`, in place)

1. **Steps 1–3 core generalized to an arbitrary `NontriviallyNormedField 𝕜`**:
   `fderiv_comp_perm_eq`, `iteratedFDeriv_comp_tailLift`, `iteratedFDeriv_add_two_apply`
   never needed ℝ — `domDomCongrₗᵢ`, `LinearIsometryEquiv.comp_fderiv`,
   `iteratedFDeriv_succ_apply_left` are all field-generic in Mathlib.
2. **`iteratedFDeriv_comp_swap_zero_one` and the main theorem gated by
   `[IsRCLikeNormedField 𝕜]`** — exactly the hypothesis of Mathlib's n = 2 case
   (`ContDiffAt.isSymmSndFDerivAt` with `minSmoothness 𝕜 2 ≤ 2`, closed by `simp` via
   `minSmoothness_of_isRCLikeNormedField`). This is the honest generality of the
   finite-smoothness argument: Schwarz n = 2 is the only ℝ/ℂ-specific input.
3. **NEW `iteratedFDeriv_comp_perm_of_minSmoothness`** — the field-uniform statement over
   ANY nontrivially normed field, in Mathlib's `minSmoothness` idiom:
   `ContDiff 𝕜 (minSmoothness 𝕜 n) f → iteratedFDeriv 𝕜 n f x (v ∘ σ) = …`.
   Proof `by_cases IsRCLikeNormedField 𝕜`: RCLike branch is our theorem
   (`minSmoothness 𝕜 n = n`); other fields have `minSmoothness 𝕜 n = ω`, so `f` is
   analytic and Mathlib's `ContDiffAt.iteratedFDeriv_comp_perm` finishes. This mirrors
   exactly how Mathlib states `ContDiffAt.isSymmSndFDerivAt` — the natural upstream form.
4. **NEW `iteratedFDerivWithin_comp_perm_of_isOpen`** — `Within` version on open sets via
   `iteratedFDerivWithin_of_isOpen`. The full `UniqueDiffOn`-set `Within` version needs the
   whole induction redone with `fderivWithin` (`LinearIsometryEquiv.comp_fderivWithin` at
   `UniqueDiffWithinAt` points, `IsSymmSndFDerivWithinAt` with `x ∈ closure (interior s)`)
   — left as the remaining upstream-prep item (candidate S7).

## Lean gotchas (v4.31)

- `ℕ∞ω`, `ω`, `∞` smoothness-exponent notations are `scoped[ContDiff]`
  (Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries:115-119) — a file using
  `minSmoothness` statements needs `open scoped ContDiff` even with `import Mathlib`.
- `minSmoothness` is `irreducible_def`; unfold in the non-RCLike branch with
  `simp [minSmoothness, h]` (the equation lemma is registered under the plain name),
  same idiom as Mathlib's own `ContDiffAt.isSymmSndFDerivAt` proof.
- The S5 gotchas stand: explicit `(𝕜 := …) (G := …) (iso := …) (f := …) (x := …)` on
  `LinearIsometryEquiv.comp_fderiv` (whnf timeout otherwise); `hsym.eq` for
  `IsSymmSndFDerivAt` application.

## Build

`./proofs/scripts/docker-build.sh Proofs.FundamentalTheoremCalculusOQ02Incomplete01`
— see PR. First attempt failed only on the scoped-notation gotcha above.

## Status

Fragment 1 now in upstream-ready generality. Fragments 2–6 (manifold Stokes) unchanged —
DEEP multi-session. Next concrete item: S7 full `Within`/`UniqueDiffOn` induction if
upstreaming proceeds.
