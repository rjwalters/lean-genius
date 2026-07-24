# S8 (2026-07-24, researcher-3) — nested directional-derivative bridge + classical Clairaut form

## Outcome

New "Step 7 (S8)" section in `proofs/Proofs/FundamentalTheoremCalculusOQ02Incomplete01.lean`
(~130 LOC, 0 axioms, 0 sorries, host-verified `lake env lean` exit 0, zero diagnostics,
pinned v4.31.0 toolchain, lake-manifest mathlib rev identical to origin/main).

Everything shipped in S5–S7 is phrased through `iteratedFDeriv` — the multilinear-map
packaging. Classical texts state Clairaut/Schwarz as *nested* directional derivatives
commuting: `∂_{v₀} ∂_{v₁} … f` order-independent, where `∂_w g = fun y => fderiv 𝕜 g y w`.
Mathlib (v4.31) bridges the two forms only at `n = 2` (`iteratedFDeriv_two_apply`); the
general-`n` bridge did not exist. S8 adds it and derives the classical nested statements:

* `nestedFDeriv 𝕜 n v f` — the `n`-fold nested directional derivative
  `∂_{v 0} (∂_{v 1} (… (∂_{v (n-1)} f)))`, direction `v 0` outermost (matches the design of
  Mathlib's abstract `LineDeriv.iteratedLineDerivOp`, which has NO instance for plain
  functions and NO `iteratedFDeriv` relation — checked `Analysis/Distribution/DerivNotation.lean`).
* `nestedFDeriv_eq_iteratedFDeriv` — **the general-`n` bridge**: for `C^n` `f` (any
  nontrivially normed field), `nestedFDeriv 𝕜 n v f x = iteratedFDeriv 𝕜 n f x v`.
  Induction: IH turns the inner nest into `y ↦ D^n f y (tail v)` = the CMM-valued map
  `iteratedFDeriv 𝕜 n f` applied to the CONSTANT tuple `tail v`;
  `fderiv_continuousMultilinear_apply_const_apply` (Mathlib, `FDeriv/CompCLM.lean`) commutes
  the constant application past `fderiv`; differentiability of `D^n f` from
  `ContDiff.differentiable_iteratedFDeriv (n < n+1)`; reassemble with
  `iteratedFDeriv_succ_apply_left` (rfl at v4.31).
* `nestedFDeriv_comp_perm` — classical all-orders Clairaut, nested form, over ℝ/ℂ:
  `nestedFDeriv 𝕜 n (v ∘ σ) f x = nestedFDeriv 𝕜 n v f x` for `C^n` `f`. Two bridge
  rewrites + `iteratedFDeriv_comp_perm`.
* `nestedFDeriv_comp_perm_of_minSmoothness` — field-uniform version; the bridge itself only
  needs `C^n`, extracted from the `minSmoothness` hypothesis via `le_minSmoothness`.
* `fderiv_fderiv_comm` — the `C²` special case spelled out:
  `fderiv 𝕜 (fun y => fderiv 𝕜 f y b) x a = fderiv 𝕜 (fun y => fderiv 𝕜 f y a) x b`.
  This is genuinely different from Mathlib's `IsSymmSndFDerivAt` (there the evaluation is
  OUTSIDE the outer derivative: `fderiv 𝕜 (fderiv 𝕜 f) x v w`); the nested spelling is the
  one in which `∂²f/∂x∂y = ∂²f/∂y∂x` is classically written, and Mathlib has no
  `fderiv_fderiv`-commutation lemma of this shape (grepped).

## Lean notes (v4.31)

* `nestedFDeriv` defined by structural recursion on `n` with `variable (𝕜) in`; recursive
  call inside the equations takes only the varying args (`nestedFDeriv n (Fin.tail v) f`) —
  fixed section params are auto-applied. All three unfolding lemmas (`_zero`, `_succ_apply`,
  `_one_apply`) are `rfl`.
* `nestedFDeriv 𝕜 2 ![a,b] f x = fderiv 𝕜 (fun y => fderiv 𝕜 f y b) x a` is `rfl` after
  `rw [nestedFDeriv_succ_apply, (Fin.tail ![a,b] = ![b])]` — `![b] 0` and `![a,b] 0` reduce
  definitionally, and `rw` matched the `2 = ?n + 1` literal without a `show`.
* `fin_cases i` on `i : Fin 1` leaves ONE goal — `fin_cases i <;> rfl` trips the
  `unnecessarySeqFocus` linter; use `fin_cases i` then `rfl` on separate lines.
* Compiled clean on first verification pass (only the two linter warnings above).

## Remaining

* An actual Mathlib upstream PR — Fragment 1 (now including the nested/classical API layer,
  which is precisely what an upstream reviewer would ask for as the "user-facing" form).
  No mathlib4 checkout exists on this host; a submission session needs a clone + cache
  (~several GB) and a port to current master (this file is pinned at v4.31 idioms).
* S9 candidates (session-sized): `Within` version of the nested bridge
  (`nestedFDerivWithin` via `fderivWithin_continuousMultilinear_apply_const_apply`, which
  exists at the same place in Mathlib); `lineDeriv`-flavored corollaries via
  `DifferentiableAt.lineDeriv_eq_fderiv` (each intermediate nest is differentiable by the
  bridge, since it equals a CMM-application of `D^k f`).
* Fragments 2–6 (manifold Stokes) — DEEP multi-session, unchanged.
