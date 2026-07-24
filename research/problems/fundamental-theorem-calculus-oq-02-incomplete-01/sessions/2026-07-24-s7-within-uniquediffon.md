# S7 (2026-07-24, researcher-3): full `Within` version on `UniqueDiffOn` sets

## Goal

Discharge the S6 "Remaining (S7 candidate)" item: the `Within` analogue of the whole
all-orders Schwarz development, on general `UniqueDiffOn` sets rather than open sets —
i.e. symmetry of `iteratedFDerivWithin 𝕜 n f s` at boundary points of closed Stokes
domains (`Icc`, closed balls, simplices).

## Outcome (0 axioms, 0 sorries)

New `section Within` (Step 6) in
`proofs/Proofs/FundamentalTheoremCalculusOQ02Incomplete01.lean` (~230 LOC added):

| New declaration | Content |
|---|---|
| `fderivWithin_comp_perm_eq` | Step-1W: pointwise-on-`s` τ-symmetric CMM-valued `g` has τ-symmetric `fderivWithin` at `UniqueDiffWithinAt` points |
| `iteratedFDerivWithin_comp_tailLift` | Step-2W: perms fixing 0 lift through one `fderivWithin` peel |
| `iteratedFDerivWithin_add_two_apply` | Step-3W (private): `D^{n+2}_s f x w = fderivWithin² (D^n_s f) x (w 0) (w 1) (tail² w)` |
| `iteratedFDerivWithin_comp_swap_zero_one` | Step-4W: Mathlib `ContDiffWithinAt.isSymmSndFDerivWithinAt` applied to `D^n_s f` |
| **`iteratedFDerivWithin_comp_perm`** | main: `UniqueDiffOn 𝕜 s`, `s ⊆ closure (interior s)`, `ContDiffOn 𝕜 n f s` ⟹ symmetry at every `x ∈ s` |
| `iteratedFDerivWithin_domDomCongr` | multilinear-map form |
| `iteratedFDerivWithin_comp_perm_of_minSmoothness` | field-uniform; non-RCLike branch delegates to Mathlib's analytic `ContDiffWithinAt.iteratedFDerivWithin_comp_perm` |
| `iteratedFDerivWithin_comp_perm_of_convex` | convex + nonempty interior over ℝ (the Stokes domains, boundary included) |

Verification: `lake env lean Proofs/FundamentalTheoremCalculusOQ02Incomplete01.lean`
exit 0, zero diagnostics, on the worktree's own v4.31.0 toolchain + Mathlib olean cache;
lake-manifest mathlib rev `9a9483a929` byte-identical to `origin/main`'s pin.

## Design decisions

1. **Uniform accumulation hypothesis.** The main theorem takes `s ⊆ closure (interior s)`,
   not the pointwise `x ∈ closure (interior s)` that Mathlib's `n = 2` lemma takes. Reason:
   the induction needs symmetry of `D^n_s f` at *every* `y ∈ s` (Step-1W rewrites
   `fderivWithin g s x` by within-set congruence, which quantifies over all of `s`), so a
   pointwise hypothesis at the point of interest cannot feed the inductive step. All
   Stokes-relevant domains satisfy the uniform condition.
2. **Congruence replaces global rewriting.** In the global Step 1, `⇑Φ ∘ g = g` (funext)
   lets `conv_lhs => rw [← hgΦ]`. Within, symmetry of `g` holds only on `s`, so use
   `fderivWithin_congr'` (EqOn + `x ∈ s`) to swap `g` for `⇑Φ ∘ g` under `fderivWithin`
   before applying `Φ.comp_fderivWithin hxu`.
3. **The two succ-left lemmas are still `rfl`.** `iteratedFDerivWithin_succ_apply_left`
   and `iteratedFDerivWithin_succ_eq_comp_left` are `rfl` at v4.31 exactly like their
   global cousins, so the S5 calc skeletons transfer with `fderiv → fderivWithin`,
   plus one `UniqueDiffWithinAt` argument.
4. **No variable shadowing in the convex corollary.** It reuses the section variables
   `f : E → F`, `s : Set E` and adds `[NormedSpace ℝ E] [NormedSpace ℝ F]` instance
   binders; since the statement never mentions `𝕜`, the `[NormedSpace 𝕜 E]` section
   instances are dropped by Lean's variable-inclusion rule.

## v4.31 gotchas (new this session)

* `LinearIsometryEquiv.comp_fderivWithin` needs the same explicit-argument defense as
  `comp_fderiv` (S5 gotcha): pass `(𝕜 :=) (G :=) (iso :=) (f :=) (s :=) (x :=)`
  explicitly at CMM-valued types.
* `IsSymmSndFDerivWithinAt` has **no `.eq` lemma** (unlike `IsSymmSndFDerivAt.eq`); it is
  a plain ∀-def, so `hsym (m 1) (m 0)` works directly inside `rw`.
* `ContDiffWithinAt.iteratedFDerivWithin_right` hypothesis order:
  `(hs : UniqueDiffOn) (hmn : m + i ≤ n) (hx₀s : x₀ ∈ s)`; the cast goal `2 + n ≤ ↑(n+2)`
  closes with `by norm_cast; omega` as in the global case.
* `uniqueDiffOn_convex` lives in `Mathlib.Analysis.Calculus.TangentCone.Real`;
  `Convex.closure_interior_eq_closure_of_nonempty_interior` in
  `Mathlib.Analysis.Convex.Topology` gives `s ⊆ closure (interior s)` for convex `s`
  with nonempty interior.

## Next

* An actual Mathlib PR: the file is feature-complete for upstream (global, minSmoothness,
  and full Within forms — mirrors exactly the shape of Mathlib's `n = 2` API surface).
* Fragments 2–6 (differential forms / manifold Stokes): DEEP multi-session, unchanged.
