import Mathlib

/-
# Symmetry of the n-th iterated Fréchet derivative for C^n functions (all orders Schwarz/Clairaut)

Research slug: fundamental-theorem-calculus-oq-02-incomplete-01 (Fragment 1 of the
generalized-Stokes decomposition; parent gallery entry `fundamental-theorem-calculus-oq-02`).

## What This Formalizes

If `f : E → F` is `C^n` over `𝕜 = ℝ` or `ℂ` (finite smoothness — analyticity NOT required),
then its `n`-th iterated Fréchet derivative at every point is a *symmetric* multilinear map:

  `iteratedFDeriv 𝕜 n f x (v ∘ σ) = iteratedFDeriv 𝕜 n f x v`  for every `σ : Perm (Fin n)`.

This is the all-orders Schwarz/Clairaut theorem. It is the analytic backbone of `d ∘ d = 0`
for differential forms, hence of the generalized Stokes theorem (Fragment 1 of this slug's
decomposition, designed in the S3/S4 session memos of 2026-06).

S6 (2026-07-24) generalized the original ℝ-only development (S5) for Mathlib upstream-prep:

* the combinatorial core (Steps 1–3 below) is now stated over an arbitrary
  `NontriviallyNormedField 𝕜`;
* the main theorem `iteratedFDeriv_comp_perm` holds over any `IsRCLikeNormedField 𝕜`
  (i.e. `𝕜` isomorphic to `ℝ` or `ℂ` — exactly the hypothesis of Mathlib's `n = 2` case);
* `iteratedFDeriv_comp_perm_of_minSmoothness` is the field-uniform statement in Mathlib's
  `minSmoothness` idiom: over `ℝ`/`ℂ` it requires `C^n`, over any other field it requires
  `C^ω` and delegates to Mathlib's analytic version — this is the natural upstream statement;
* `iteratedFDerivWithin_comp_perm_of_isOpen` is the `Within` version on open sets.

S7 (2026-07-24) added the full `Within` development on `UniqueDiffOn` sets (Step 6 below):
the whole induction redone with `fderivWithin`, giving

* `iteratedFDerivWithin_comp_perm` — on any `UniqueDiffOn` set `s` with
  `s ⊆ closure (interior s)`, the `n`-th derivative within `s` of a `C^n`-on-`s` function
  is symmetric at every point of `s` (boundary points included);
* `iteratedFDerivWithin_comp_perm_of_convex` — the concrete form on convex sets with
  nonempty interior over `ℝ` (closed balls, `Icc`, simplices — the Stokes domains);
* `iteratedFDerivWithin_comp_perm_of_minSmoothness` — the field-uniform `Within` form.

## Relation to Mathlib (v4.31 pin)

Mathlib currently has:
* `second_derivative_symmetric` / `ContDiffAt.isSymmSndFDerivAt` — the `n = 2` case for
  `C^2` functions over `ℝ` or `ℂ`;
* `ContDiffAt.iteratedFDeriv_comp_perm` (in `Mathlib.Analysis.Analytic.IteratedFDeriv`) —
  the general-`n` statement, but only for *analytic* (`C^ω`) functions.

The general-`n`, finite-smoothness statement proved here is (as of the v4.31 pin) NOT in
Mathlib. It strictly strengthens the analytic version over `ℝ`/`ℂ` since `C^ω ⊊ C^n` as
function classes (`C^n` contains many non-analytic functions).

## Proof structure (elementary, no group-closure machinery)

Induction on `n`, using `Equiv.Perm.decomposeFin` to factor any permutation of `Fin (n+1)`
as `swap 0 p * (tail lift of τ)`:

1. `fderiv_comp_perm_eq` — if every value of a multilinear-map-valued function `g` is
   invariant under precomposition by `τ`, so is every value of `fderiv 𝕜 g x`
   (postcompose with the linear isometry `ContinuousMultilinearMap.domDomCongrₗᵢ`).
2. `iteratedFDeriv_comp_tailLift` — symmetry of `D^n f` everywhere lifts to symmetry of
   `D^(n+1) f` under permutations fixing position 0 (peel one derivative with
   `iteratedFDeriv_succ_apply_left`).
3. `iteratedFDeriv_comp_swap_zero_one` — swapping the two outermost directions is the
   Mathlib `n = 2` case `ContDiffAt.isSymmSndFDerivAt` applied to `g := iteratedFDeriv 𝕜 n f`
   (which is `C^2` by `ContDiff.iteratedFDeriv_right`), after rewriting `D^(n+2) f x m` as
   `fderiv 𝕜 (fderiv 𝕜 (D^n f)) x (m 0) (m 1) (tail (tail m))`. This is the one step that
   needs `IsRCLikeNormedField 𝕜`.
4. `swap 0 p` for general `p` is conjugate to `swap 0 1` by a tail lift
   (`Equiv.symm_trans_swap_trans`), so no `Subgroup.closure` argument is needed.

0 axioms, 0 sorries.
-/

open Function Equiv
open scoped ContDiff

namespace FTCOQ02Incomplete01

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F}

/-! ### Step 1: derivatives of pointwise-symmetric multilinear-map-valued functions -/

/-- If every value of `g : E → (E [×n]→L[𝕜] F)` is invariant under precomposition with the
permutation `τ`, then so is every value of its derivative. The proof postcomposes `g` with
the linear isometry `domDomCongrₗᵢ τ` and uses that `fderiv` commutes with linear
isometries. Holds over any nontrivially normed field. -/
theorem fderiv_comp_perm_eq {n : ℕ}
    {g : E → ContinuousMultilinearMap 𝕜 (fun _ : Fin n => E) F} {τ : Equiv.Perm (Fin n)}
    (hg : ∀ y (w : Fin n → E), g y (w ∘ τ) = g y w) (x u : E) (w : Fin n → E) :
    fderiv 𝕜 g x u (w ∘ τ) = fderiv 𝕜 g x u w := by
  set Φ := ContinuousMultilinearMap.domDomCongrₗᵢ 𝕜 E F τ with hΦ
  have hgΦ : ⇑Φ ∘ g = g := by
    funext y
    exact ContinuousMultilinearMap.ext fun v => hg y v
  have hfd : fderiv 𝕜 g x = (Φ : (ContinuousMultilinearMap 𝕜 (fun _ : Fin n => E) F) →L[𝕜]
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin n => E) F)).comp (fderiv 𝕜 g x) := by
    conv_lhs => rw [← hgΦ]
    exact Φ.comp_fderiv
  have happ : fderiv 𝕜 g x u = (fderiv 𝕜 g x u).domDomCongr τ := by
    conv_lhs => rw [hfd]
    rfl
  conv_rhs => rw [happ]
  simp [ContinuousMultilinearMap.domDomCongr_apply, Function.comp_def]

/-! ### Step 2: tail lift — permutations fixing position 0 -/

/-- If the `n`-th derivative of `f` is `τ`-symmetric at every point, then the `(n+1)`-th
derivative is symmetric under the tail lift `decomposeFin.symm (0, τ)` of `τ` (the
permutation of `Fin (n+1)` fixing `0` and acting by `τ` on the tail). Holds over any
nontrivially normed field. -/
theorem iteratedFDeriv_comp_tailLift {n : ℕ} {τ : Equiv.Perm (Fin n)}
    (hτ : ∀ y (w : Fin n → E), iteratedFDeriv 𝕜 n f y (w ∘ τ) = iteratedFDeriv 𝕜 n f y w)
    (x : E) (v : Fin (n + 1) → E) :
    iteratedFDeriv 𝕜 (n + 1) f x (v ∘ (Equiv.Perm.decomposeFin.symm (0, τ))) =
      iteratedFDeriv 𝕜 (n + 1) f x v := by
  have h0 : (v ∘ (Equiv.Perm.decomposeFin.symm (0, τ))) 0 = v 0 := by simp
  have ht : Fin.tail (v ∘ (Equiv.Perm.decomposeFin.symm (0, τ))) = Fin.tail v ∘ τ := by
    funext i
    simp [Fin.tail, Equiv.Perm.decomposeFin_symm_apply_succ]
  calc iteratedFDeriv 𝕜 (n + 1) f x (v ∘ (Equiv.Perm.decomposeFin.symm (0, τ)))
      = fderiv 𝕜 (iteratedFDeriv 𝕜 n f) x ((v ∘ (Equiv.Perm.decomposeFin.symm (0, τ))) 0)
          (Fin.tail (v ∘ (Equiv.Perm.decomposeFin.symm (0, τ)))) :=
        iteratedFDeriv_succ_apply_left _
    _ = fderiv 𝕜 (iteratedFDeriv 𝕜 n f) x (v 0) (Fin.tail v ∘ τ) := by rw [h0, ht]
    _ = fderiv 𝕜 (iteratedFDeriv 𝕜 n f) x (v 0) (Fin.tail v) :=
        fderiv_comp_perm_eq hτ x (v 0) (Fin.tail v)
    _ = iteratedFDeriv 𝕜 (n + 1) f x v := (iteratedFDeriv_succ_apply_left _).symm

/-! ### Step 3: the two outermost directions commute (Mathlib's `n = 2` Schwarz) -/

/-- Expand the `(n+2)`-th derivative as the second derivative of the `n`-th derivative,
applied to the two leading directions. Holds over any nontrivially normed field. -/
private theorem iteratedFDeriv_add_two_apply {n : ℕ} (f : E → F) (x : E)
    (w : Fin (n + 2) → E) :
    iteratedFDeriv 𝕜 (n + 2) f x w =
      fderiv 𝕜 (fderiv 𝕜 (iteratedFDeriv 𝕜 n f)) x (w 0) (w 1)
        (Fin.tail (Fin.tail w)) := by
  have h2 := LinearIsometryEquiv.comp_fderiv
    (𝕜 := 𝕜) (G := E)
    (iso := (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F).symm)
    (f := fderiv 𝕜 (iteratedFDeriv 𝕜 n f)) (x := x)
  have htw : Fin.tail w 0 = w 1 := by
    simp [Fin.tail]
  calc iteratedFDeriv 𝕜 (n + 2) f x w
      = fderiv 𝕜 (iteratedFDeriv 𝕜 (n + 1) f) x (w 0) (Fin.tail w) :=
        iteratedFDeriv_succ_apply_left w
    _ = fderiv 𝕜 (⇑(continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F).symm ∘
          fderiv 𝕜 (iteratedFDeriv 𝕜 n f)) x (w 0) (Fin.tail w) := by
        rw [← iteratedFDeriv_succ_eq_comp_left]
    _ = (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F).symm
          (fderiv 𝕜 (fderiv 𝕜 (iteratedFDeriv 𝕜 n f)) x (w 0)) (Fin.tail w) := by
        rw [h2]; rfl
    _ = fderiv 𝕜 (fderiv 𝕜 (iteratedFDeriv 𝕜 n f)) x (w 0) (Fin.tail w 0)
          (Fin.tail (Fin.tail w)) := rfl
    _ = fderiv 𝕜 (fderiv 𝕜 (iteratedFDeriv 𝕜 n f)) x (w 0) (w 1)
          (Fin.tail (Fin.tail w)) := by rw [htw]

/-- Swapping the two outermost differentiation directions: the `n = 2` Schwarz theorem
(`ContDiffAt.isSymmSndFDerivAt`, which needs only `C^2` over `ℝ` or `ℂ`) applied to the
multilinear-map-valued function `iteratedFDeriv 𝕜 n f`. This is the single step that
requires `IsRCLikeNormedField 𝕜`. -/
theorem iteratedFDeriv_comp_swap_zero_one [IsRCLikeNormedField 𝕜] {n : ℕ}
    (hf : ContDiff 𝕜 (n + 2 : ℕ) f) (x : E) (m : Fin (n + 2) → E) :
    iteratedFDeriv 𝕜 (n + 2) f x (m ∘ Equiv.swap 0 1) = iteratedFDeriv 𝕜 (n + 2) f x m := by
  have hg : ContDiff 𝕜 2 (iteratedFDeriv 𝕜 n f) :=
    hf.iteratedFDeriv_right (by norm_cast; omega)
  have hsym : IsSymmSndFDerivAt 𝕜 (iteratedFDeriv 𝕜 n f) x :=
    hg.contDiffAt.isSymmSndFDerivAt (by simp)
  have h0 : (m ∘ Equiv.swap 0 1) 0 = m 1 := by simp
  have h1 : (m ∘ Equiv.swap 0 1) 1 = m 0 := by simp
  have ht : Fin.tail (Fin.tail (m ∘ Equiv.swap 0 1)) = Fin.tail (Fin.tail m) := by
    funext i
    simp only [Fin.tail, Function.comp_apply]
    congr 1
  rw [iteratedFDeriv_add_two_apply, iteratedFDeriv_add_two_apply, h0, h1, ht,
    hsym.eq (m 1) (m 0)]

/-! ### Step 4: the main theorem -/

/-- **Symmetry of the `n`-th iterated Fréchet derivative of a `C^n` function** (all-orders
Schwarz/Clairaut over `ℝ` or `ℂ`, finite smoothness — no analyticity required).

Mathlib (v4.31) has this only for `n = 2` (`ContDiffAt.isSymmSndFDerivAt`) or for
analytic `f` (`ContDiffAt.iteratedFDeriv_comp_perm`). -/
theorem iteratedFDeriv_comp_perm [IsRCLikeNormedField 𝕜] :
    ∀ {n : ℕ}, ContDiff 𝕜 (n : ℕ) f → ∀ (x : E) (v : Fin n → E) (σ : Equiv.Perm (Fin n)),
      iteratedFDeriv 𝕜 n f x (v ∘ σ) = iteratedFDeriv 𝕜 n f x v := by
  intro n
  induction n with
  | zero =>
    intro _ x v σ
    rw [Subsingleton.elim (v ∘ ⇑σ) v]
  | succ n IH =>
    intro hf x v σ
    -- the `n`-th derivative is symmetric at every point, by the induction hypothesis
    have hsymm : ∀ (τ : Equiv.Perm (Fin n)) (y : E) (w : Fin n → E),
        iteratedFDeriv 𝕜 n f y (w ∘ τ) = iteratedFDeriv 𝕜 n f y w :=
      fun τ y w => IH (hf.of_le (by exact_mod_cast Nat.le_succ n)) y w τ
    -- factor σ = swap 0 p * (tail lift of τ) via `decomposeFin`
    set p : Fin (n + 1) := (Equiv.Perm.decomposeFin σ).1 with hp
    set τ : Equiv.Perm (Fin n) := (Equiv.Perm.decomposeFin σ).2 with hτdef
    have hσ : σ = Equiv.Perm.decomposeFin.symm (p, τ) := by
      rw [hp, hτdef]
      exact (Equiv.symm_apply_apply Equiv.Perm.decomposeFin σ).symm
    have hfact : σ = Equiv.swap 0 p * Equiv.Perm.decomposeFin.symm (0, τ) := by
      rw [hσ]
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [Equiv.Perm.mul_apply, Equiv.Perm.decomposeFin_symm_apply_succ]
    have hcomp : v ∘ σ = (v ∘ Equiv.swap 0 p) ∘ ⇑(Equiv.Perm.decomposeFin.symm (0, τ)) := by
      rw [hfact]
      funext i
      simp
    rw [hcomp,
      iteratedFDeriv_comp_tailLift (fun y w => hsymm τ y w) x (v ∘ Equiv.swap 0 p)]
    -- it remains to handle `swap 0 p`; split on `p`
    clear hcomp hfact hσ hp hτdef
    refine Fin.cases ?_ (fun j => ?_) p
    · -- `p = 0`: the swap is the identity
      have : v ∘ ⇑(Equiv.swap (0 : Fin (n + 1)) 0) = v := by
        funext i; simp
      rw [this]
    · -- `p = j.succ`: conjugate `swap 0 j.succ` into `swap 0 1` by a tail lift
      cases n with
      | zero => exact j.elim0
      | succ k =>
        set ρ : Equiv.Perm (Fin (k + 1)) := Equiv.swap 0 j with hρ
        set ρhat : Equiv.Perm (Fin (k + 2)) := Equiv.Perm.decomposeFin.symm (0, ρ) with hρhat
        have hρ0 : ρhat 0 = 0 := by simp [hρhat]
        have hρ1 : ρhat 1 = j.succ := by
          have h01 : (1 : Fin (k + 2)) = (0 : Fin (k + 1)).succ := by
            simp [Fin.succ_zero_eq_one]
          rw [h01]
          simp [hρhat, hρ]
        have hρinv : ρhat⁻¹ = Equiv.Perm.decomposeFin.symm (0, ρ⁻¹) := by
          rw [inv_eq_iff_mul_eq_one]
          ext i
          refine Fin.cases ?_ (fun i => ?_) i <;>
            simp [hρhat, Equiv.Perm.mul_apply, Equiv.Perm.decomposeFin_symm_apply_succ]
        have hconj : Equiv.swap (0 : Fin (k + 2)) j.succ = ρhat * Equiv.swap 0 1 * ρhat⁻¹ := by
          have h := Equiv.symm_trans_swap_trans (0 : Fin (k + 2)) 1 ρhat
          rw [hρ0, hρ1] at h
          rw [← h]
          rfl
        have hv : v ∘ ⇑(Equiv.swap (0 : Fin (k + 2)) j.succ) =
            ((v ∘ ⇑ρhat) ∘ ⇑(Equiv.swap (0 : Fin (k + 2)) 1)) ∘ ⇑ρhat⁻¹ := by
          rw [hconj]
          funext i
          simp
        calc iteratedFDeriv 𝕜 (k + 2) f x (v ∘ ⇑(Equiv.swap 0 j.succ))
            = iteratedFDeriv 𝕜 (k + 2) f x
                (((v ∘ ⇑ρhat) ∘ ⇑(Equiv.swap 0 1)) ∘ ⇑ρhat⁻¹) := by rw [hv]
          _ = iteratedFDeriv 𝕜 (k + 2) f x ((v ∘ ⇑ρhat) ∘ ⇑(Equiv.swap 0 1)) := by
              rw [hρinv]
              exact iteratedFDeriv_comp_tailLift (fun y w => hsymm ρ⁻¹ y w) x _
          _ = iteratedFDeriv 𝕜 (k + 2) f x (v ∘ ⇑ρhat) :=
              iteratedFDeriv_comp_swap_zero_one hf x (v ∘ ⇑ρhat)
          _ = iteratedFDeriv 𝕜 (k + 2) f x v :=
              iteratedFDeriv_comp_tailLift (fun y w => hsymm ρ y w) x v

/-- The `n`-th iterated derivative of a `C^n` function, as a multilinear map, is fixed by
`domDomCongr` along any permutation. -/
theorem iteratedFDeriv_domDomCongr [IsRCLikeNormedField 𝕜] {n : ℕ}
    (hf : ContDiff 𝕜 (n : ℕ) f) (x : E) (σ : Equiv.Perm (Fin n)) :
    (iteratedFDeriv 𝕜 n f x).domDomCongr σ = iteratedFDeriv 𝕜 n f x := by
  refine ContinuousMultilinearMap.ext fun v => ?_
  simpa [ContinuousMultilinearMap.domDomCongr_apply, Function.comp_def] using
    iteratedFDeriv_comp_perm hf x v σ

/-- Specialization to `C^∞` functions: every iterated derivative is symmetric. This is
strictly stronger over `ℝ`/`ℂ` than Mathlib's analytic version, since smooth functions
need not be analytic. -/
theorem iteratedFDeriv_comp_perm_of_contDiff_infty [IsRCLikeNormedField 𝕜]
    (hf : ContDiff 𝕜 (⊤ : ℕ∞) f) {n : ℕ}
    (x : E) (v : Fin n → E) (σ : Equiv.Perm (Fin n)) :
    iteratedFDeriv 𝕜 n f x (v ∘ σ) = iteratedFDeriv 𝕜 n f x v :=
  iteratedFDeriv_comp_perm (hf.of_le (by exact_mod_cast le_top)) x v σ

/-! ### Step 5 (S6): field-uniform `minSmoothness` version and `Within` version -/

/-- **Field-uniform version, in Mathlib's `minSmoothness` idiom.** Over any nontrivially
normed field `𝕜`, if `f` is `C^(minSmoothness 𝕜 n)` — that is, `C^n` when `𝕜` is `ℝ` or
`ℂ`, and `C^ω` (analytic) otherwise — then the `n`-th iterated derivative is symmetric.

Over `ℝ`/`ℂ` this is the finite-smoothness theorem above; over any other field the
requirement degrades to analyticity, where Mathlib's
`ContDiffAt.iteratedFDeriv_comp_perm` applies. This mirrors exactly how Mathlib states
`ContDiffAt.isSymmSndFDerivAt`, making it the natural upstream form. -/
theorem iteratedFDeriv_comp_perm_of_minSmoothness {n : ℕ}
    (hf : ContDiff 𝕜 (minSmoothness 𝕜 n) f) (x : E) (v : Fin n → E)
    (σ : Equiv.Perm (Fin n)) :
    iteratedFDeriv 𝕜 n f x (v ∘ σ) = iteratedFDeriv 𝕜 n f x v := by
  by_cases h : IsRCLikeNormedField 𝕜
  · haveI := h
    rw [minSmoothness_of_isRCLikeNormedField] at hf
    exact iteratedFDeriv_comp_perm hf x v σ
  · have hω : minSmoothness 𝕜 (n : ℕ∞ω) = ω := by
      simp [minSmoothness, h]
    rw [hω] at hf
    exact hf.contDiffAt.iteratedFDeriv_comp_perm v σ

/-- `Within` version on **open** sets: on an open set the iterated derivative within the
set agrees with the global one (`iteratedFDerivWithin_of_isOpen`), so symmetry transfers.
See `iteratedFDerivWithin_comp_perm` below (S7) for the general `UniqueDiffOn` version,
which needs only `s ⊆ closure (interior s)` and `ContDiffOn` — this open-set version is
kept because its hypotheses (global `ContDiff`, no unique-differentiability data) are
incomparable. -/
theorem iteratedFDerivWithin_comp_perm_of_isOpen [IsRCLikeNormedField 𝕜] {n : ℕ}
    (hf : ContDiff 𝕜 (n : ℕ) f) {s : Set E} (hs : IsOpen s) {x : E} (hx : x ∈ s)
    (v : Fin n → E) (σ : Equiv.Perm (Fin n)) :
    iteratedFDerivWithin 𝕜 n f s x (v ∘ σ) = iteratedFDerivWithin 𝕜 n f s x v := by
  rw [iteratedFDerivWithin_of_isOpen n hs hx]
  exact iteratedFDeriv_comp_perm hf x v σ

/-! ### Step 6 (S7): the full `Within` version on `UniqueDiffOn` sets

The `Within` analogue of the entire development: on a set `s` of unique differentiability
every point of which is accumulated by interior points (`s ⊆ closure (interior s)` — true
for every convex set with nonempty interior, hence for closed balls, `Icc`, simplices, …),
the `n`-th iterated derivative *within `s`* of a function that is `C^n` *on `s`* is
symmetric at every point of `s`. Steps 1–4 are redone with `fderivWithin`; the `n = 2`
input is Mathlib's `ContDiffWithinAt.isSymmSndFDerivWithinAt`, whose closure-of-interior
hypothesis is why the accumulation condition must hold at every point of `s` (the
induction consumes symmetry of the previous derivative at *all* points of `s`, so a
pointwise hypothesis at the single point of interest would not suffice for the inductive
step). -/

section Within

variable {s : Set E}

/-- `Within` version of `fderiv_comp_perm_eq`: if every value of `g` *on `s`* is invariant
under precomposition with `τ`, then so is every value of `fderivWithin 𝕜 g s` at any point
of `s` where `s` is uniquely differentiable. Holds over any nontrivially normed field. -/
theorem fderivWithin_comp_perm_eq {n : ℕ}
    {g : E → ContinuousMultilinearMap 𝕜 (fun _ : Fin n => E) F} {τ : Equiv.Perm (Fin n)}
    (hg : ∀ y ∈ s, ∀ (w : Fin n → E), g y (w ∘ τ) = g y w)
    {x : E} (hxu : UniqueDiffWithinAt 𝕜 s x) (hxs : x ∈ s) (u : E) (w : Fin n → E) :
    fderivWithin 𝕜 g s x u (w ∘ τ) = fderivWithin 𝕜 g s x u w := by
  set Φ := ContinuousMultilinearMap.domDomCongrₗᵢ 𝕜 E F τ with hΦ
  have hcongr : fderivWithin 𝕜 g s x = fderivWithin 𝕜 (⇑Φ ∘ g) s x :=
    (fderivWithin_congr' (fun y hy => ContinuousMultilinearMap.ext fun v => hg y hy v)
      hxs).symm
  have hfd : fderivWithin 𝕜 g s x =
      (Φ : (ContinuousMultilinearMap 𝕜 (fun _ : Fin n => E) F) →L[𝕜]
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin n => E) F)).comp (fderivWithin 𝕜 g s x) := by
    conv_lhs => rw [hcongr]
    exact Φ.comp_fderivWithin hxu
  have happ : fderivWithin 𝕜 g s x u = (fderivWithin 𝕜 g s x u).domDomCongr τ := by
    conv_lhs => rw [hfd]
    rfl
  conv_rhs => rw [happ]
  simp [ContinuousMultilinearMap.domDomCongr_apply, Function.comp_def]

/-- `Within` version of `iteratedFDeriv_comp_tailLift`: if the `n`-th derivative within
`s` is `τ`-symmetric at every point of `s`, the `(n+1)`-th derivative within `s` is
symmetric under the tail lift of `τ` at any uniquely-differentiable point of `s`. Holds
over any nontrivially normed field. -/
theorem iteratedFDerivWithin_comp_tailLift {n : ℕ} {τ : Equiv.Perm (Fin n)}
    (hτ : ∀ y ∈ s, ∀ (w : Fin n → E),
      iteratedFDerivWithin 𝕜 n f s y (w ∘ τ) = iteratedFDerivWithin 𝕜 n f s y w)
    {x : E} (hxu : UniqueDiffWithinAt 𝕜 s x) (hxs : x ∈ s) (v : Fin (n + 1) → E) :
    iteratedFDerivWithin 𝕜 (n + 1) f s x (v ∘ (Equiv.Perm.decomposeFin.symm (0, τ))) =
      iteratedFDerivWithin 𝕜 (n + 1) f s x v := by
  have h0 : (v ∘ (Equiv.Perm.decomposeFin.symm (0, τ))) 0 = v 0 := by simp
  have ht : Fin.tail (v ∘ (Equiv.Perm.decomposeFin.symm (0, τ))) = Fin.tail v ∘ τ := by
    funext i
    simp [Fin.tail, Equiv.Perm.decomposeFin_symm_apply_succ]
  calc iteratedFDerivWithin 𝕜 (n + 1) f s x (v ∘ (Equiv.Perm.decomposeFin.symm (0, τ)))
      = fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n f s) s x
          ((v ∘ (Equiv.Perm.decomposeFin.symm (0, τ))) 0)
          (Fin.tail (v ∘ (Equiv.Perm.decomposeFin.symm (0, τ)))) :=
        iteratedFDerivWithin_succ_apply_left _
    _ = fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n f s) s x (v 0) (Fin.tail v ∘ τ) := by
        rw [h0, ht]
    _ = fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n f s) s x (v 0) (Fin.tail v) :=
        fderivWithin_comp_perm_eq hτ hxu hxs (v 0) (Fin.tail v)
    _ = iteratedFDerivWithin 𝕜 (n + 1) f s x v :=
        (iteratedFDerivWithin_succ_apply_left _).symm

/-- Expand the `(n+2)`-th derivative within `s` as the second derivative within `s` of
the `n`-th derivative within `s`, applied to the two leading directions. Holds over any
nontrivially normed field, at any uniquely-differentiable point. -/
private theorem iteratedFDerivWithin_add_two_apply {n : ℕ} (f : E → F) {x : E}
    (hxu : UniqueDiffWithinAt 𝕜 s x) (w : Fin (n + 2) → E) :
    iteratedFDerivWithin 𝕜 (n + 2) f s x w =
      fderivWithin 𝕜 (fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n f s) s) s x (w 0) (w 1)
        (Fin.tail (Fin.tail w)) := by
  have h2 := LinearIsometryEquiv.comp_fderivWithin
    (𝕜 := 𝕜) (G := E)
    (iso := (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F).symm)
    (f := fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n f s) s) (s := s) (x := x) hxu
  have htw : Fin.tail w 0 = w 1 := by
    simp [Fin.tail]
  calc iteratedFDerivWithin 𝕜 (n + 2) f s x w
      = fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 (n + 1) f s) s x (w 0) (Fin.tail w) :=
        iteratedFDerivWithin_succ_apply_left w
    _ = fderivWithin 𝕜
          (⇑(continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F).symm ∘
            fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n f s) s) s x (w 0) (Fin.tail w) := by
        rw [← iteratedFDerivWithin_succ_eq_comp_left]
    _ = (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F).symm
          (fderivWithin 𝕜 (fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n f s) s) s x (w 0))
          (Fin.tail w) := by
        rw [h2]; rfl
    _ = fderivWithin 𝕜 (fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n f s) s) s x (w 0)
          (Fin.tail w 0) (Fin.tail (Fin.tail w)) := rfl
    _ = fderivWithin 𝕜 (fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n f s) s) s x (w 0) (w 1)
          (Fin.tail (Fin.tail w)) := by rw [htw]

/-- `Within` version of the outermost-swap step: Mathlib's within-set `n = 2` Schwarz
theorem (`ContDiffWithinAt.isSymmSndFDerivWithinAt`) applied to
`iteratedFDerivWithin 𝕜 n f s`. This is the single step requiring `IsRCLikeNormedField 𝕜`
and the closure-of-interior accumulation hypothesis at `x`. -/
theorem iteratedFDerivWithin_comp_swap_zero_one [IsRCLikeNormedField 𝕜] {n : ℕ}
    (hf : ContDiffOn 𝕜 (n + 2 : ℕ) f s) (hs : UniqueDiffOn 𝕜 s) {x : E}
    (hxcl : x ∈ closure (interior s)) (hxs : x ∈ s) (m : Fin (n + 2) → E) :
    iteratedFDerivWithin 𝕜 (n + 2) f s x (m ∘ Equiv.swap 0 1) =
      iteratedFDerivWithin 𝕜 (n + 2) f s x m := by
  have hg : ContDiffWithinAt 𝕜 2 (iteratedFDerivWithin 𝕜 n f s) s x :=
    (hf x hxs).iteratedFDerivWithin_right hs (by norm_cast; omega) hxs
  have hsym : IsSymmSndFDerivWithinAt 𝕜 (iteratedFDerivWithin 𝕜 n f s) s x :=
    hg.isSymmSndFDerivWithinAt (by simp) hs hxcl hxs
  have h0 : (m ∘ Equiv.swap 0 1) 0 = m 1 := by simp
  have h1 : (m ∘ Equiv.swap 0 1) 1 = m 0 := by simp
  have ht : Fin.tail (Fin.tail (m ∘ Equiv.swap 0 1)) = Fin.tail (Fin.tail m) := by
    funext i
    simp only [Fin.tail, Function.comp_apply]
    congr 1
  rw [iteratedFDerivWithin_add_two_apply f (hs x hxs),
    iteratedFDerivWithin_add_two_apply f (hs x hxs), h0, h1, ht, hsym (m 1) (m 0)]

/-- **`Within` version of the main theorem.** On a set `s` of unique differentiability
with `s ⊆ closure (interior s)` (every convex set with nonempty interior qualifies — see
`iteratedFDerivWithin_comp_perm_of_convex`), the `n`-th iterated derivative within `s` of
a function that is `C^n` on `s` is symmetric at every point of `s`:

  `iteratedFDerivWithin 𝕜 n f s x (v ∘ σ) = iteratedFDerivWithin 𝕜 n f s x v`.

Mathlib (v4.31) has this only for `n = 2` (`ContDiffWithinAt.isSymmSndFDerivWithinAt`)
or for analytic `f` (`ContDiffWithinAt.iteratedFDerivWithin_comp_perm`). -/
theorem iteratedFDerivWithin_comp_perm [IsRCLikeNormedField 𝕜]
    (hs : UniqueDiffOn 𝕜 s) (h's : s ⊆ closure (interior s)) :
    ∀ {n : ℕ}, ContDiffOn 𝕜 (n : ℕ) f s → ∀ {x : E}, x ∈ s →
      ∀ (v : Fin n → E) (σ : Equiv.Perm (Fin n)),
      iteratedFDerivWithin 𝕜 n f s x (v ∘ σ) = iteratedFDerivWithin 𝕜 n f s x v := by
  intro n
  induction n with
  | zero =>
    intro _ x hxs v σ
    rw [Subsingleton.elim (v ∘ ⇑σ) v]
  | succ n IH =>
    intro hf x hxs v σ
    -- the `n`-th derivative within `s` is symmetric at every point of `s`, by the IH
    have hsymm : ∀ (τ : Equiv.Perm (Fin n)), ∀ y ∈ s, ∀ (w : Fin n → E),
        iteratedFDerivWithin 𝕜 n f s y (w ∘ τ) = iteratedFDerivWithin 𝕜 n f s y w :=
      fun τ y hy w => IH (hf.of_le (by exact_mod_cast Nat.le_succ n)) hy w τ
    -- factor σ = swap 0 p * (tail lift of τ) via `decomposeFin`
    set p : Fin (n + 1) := (Equiv.Perm.decomposeFin σ).1 with hp
    set τ : Equiv.Perm (Fin n) := (Equiv.Perm.decomposeFin σ).2 with hτdef
    have hσ : σ = Equiv.Perm.decomposeFin.symm (p, τ) := by
      rw [hp, hτdef]
      exact (Equiv.symm_apply_apply Equiv.Perm.decomposeFin σ).symm
    have hfact : σ = Equiv.swap 0 p * Equiv.Perm.decomposeFin.symm (0, τ) := by
      rw [hσ]
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [Equiv.Perm.mul_apply, Equiv.Perm.decomposeFin_symm_apply_succ]
    have hcomp : v ∘ σ = (v ∘ Equiv.swap 0 p) ∘ ⇑(Equiv.Perm.decomposeFin.symm (0, τ)) := by
      rw [hfact]
      funext i
      simp
    rw [hcomp,
      iteratedFDerivWithin_comp_tailLift (fun y hy w => hsymm τ y hy w) (hs x hxs) hxs
        (v ∘ Equiv.swap 0 p)]
    -- it remains to handle `swap 0 p`; split on `p`
    clear hcomp hfact hσ hp hτdef
    refine Fin.cases ?_ (fun j => ?_) p
    · -- `p = 0`: the swap is the identity
      have : v ∘ ⇑(Equiv.swap (0 : Fin (n + 1)) 0) = v := by
        funext i; simp
      rw [this]
    · -- `p = j.succ`: conjugate `swap 0 j.succ` into `swap 0 1` by a tail lift
      cases n with
      | zero => exact j.elim0
      | succ k =>
        set ρ : Equiv.Perm (Fin (k + 1)) := Equiv.swap 0 j with hρ
        set ρhat : Equiv.Perm (Fin (k + 2)) := Equiv.Perm.decomposeFin.symm (0, ρ) with hρhat
        have hρ0 : ρhat 0 = 0 := by simp [hρhat]
        have hρ1 : ρhat 1 = j.succ := by
          have h01 : (1 : Fin (k + 2)) = (0 : Fin (k + 1)).succ := by
            simp [Fin.succ_zero_eq_one]
          rw [h01]
          simp [hρhat, hρ]
        have hρinv : ρhat⁻¹ = Equiv.Perm.decomposeFin.symm (0, ρ⁻¹) := by
          rw [inv_eq_iff_mul_eq_one]
          ext i
          refine Fin.cases ?_ (fun i => ?_) i <;>
            simp [hρhat, Equiv.Perm.mul_apply, Equiv.Perm.decomposeFin_symm_apply_succ]
        have hconj : Equiv.swap (0 : Fin (k + 2)) j.succ = ρhat * Equiv.swap 0 1 * ρhat⁻¹ := by
          have h := Equiv.symm_trans_swap_trans (0 : Fin (k + 2)) 1 ρhat
          rw [hρ0, hρ1] at h
          rw [← h]
          rfl
        have hv : v ∘ ⇑(Equiv.swap (0 : Fin (k + 2)) j.succ) =
            ((v ∘ ⇑ρhat) ∘ ⇑(Equiv.swap (0 : Fin (k + 2)) 1)) ∘ ⇑ρhat⁻¹ := by
          rw [hconj]
          funext i
          simp
        calc iteratedFDerivWithin 𝕜 (k + 2) f s x (v ∘ ⇑(Equiv.swap 0 j.succ))
            = iteratedFDerivWithin 𝕜 (k + 2) f s x
                (((v ∘ ⇑ρhat) ∘ ⇑(Equiv.swap 0 1)) ∘ ⇑ρhat⁻¹) := by rw [hv]
          _ = iteratedFDerivWithin 𝕜 (k + 2) f s x ((v ∘ ⇑ρhat) ∘ ⇑(Equiv.swap 0 1)) := by
              rw [hρinv]
              exact iteratedFDerivWithin_comp_tailLift (fun y hy w => hsymm ρ⁻¹ y hy w)
                (hs x hxs) hxs _
          _ = iteratedFDerivWithin 𝕜 (k + 2) f s x (v ∘ ⇑ρhat) :=
              iteratedFDerivWithin_comp_swap_zero_one hf hs (h's hxs) hxs (v ∘ ⇑ρhat)
          _ = iteratedFDerivWithin 𝕜 (k + 2) f s x v :=
              iteratedFDerivWithin_comp_tailLift (fun y hy w => hsymm ρ y hy w)
                (hs x hxs) hxs v

/-- `Within` version of `iteratedFDeriv_domDomCongr`: on a `UniqueDiffOn` set accumulated
by its interior, the `n`-th derivative within the set, as a multilinear map, is fixed by
`domDomCongr` along any permutation. -/
theorem iteratedFDerivWithin_domDomCongr [IsRCLikeNormedField 𝕜] {n : ℕ}
    (hs : UniqueDiffOn 𝕜 s) (h's : s ⊆ closure (interior s))
    (hf : ContDiffOn 𝕜 (n : ℕ) f s) {x : E} (hxs : x ∈ s) (σ : Equiv.Perm (Fin n)) :
    (iteratedFDerivWithin 𝕜 n f s x).domDomCongr σ = iteratedFDerivWithin 𝕜 n f s x := by
  refine ContinuousMultilinearMap.ext fun v => ?_
  simpa [ContinuousMultilinearMap.domDomCongr_apply, Function.comp_def] using
    iteratedFDerivWithin_comp_perm hs h's hf hxs v σ

/-- Field-uniform `minSmoothness` form of the `Within` theorem, mirroring
`iteratedFDeriv_comp_perm_of_minSmoothness`: over `ℝ`/`ℂ` it requires `C^n` on `s`; over
any other nontrivially normed field the hypothesis degrades to analyticity, where
Mathlib's `ContDiffWithinAt.iteratedFDerivWithin_comp_perm` applies (and the
closure-of-interior hypothesis is not needed on that branch). -/
theorem iteratedFDerivWithin_comp_perm_of_minSmoothness {n : ℕ}
    (hs : UniqueDiffOn 𝕜 s) (h's : s ⊆ closure (interior s))
    (hf : ContDiffOn 𝕜 (minSmoothness 𝕜 n) f s) {x : E} (hxs : x ∈ s) (v : Fin n → E)
    (σ : Equiv.Perm (Fin n)) :
    iteratedFDerivWithin 𝕜 n f s x (v ∘ σ) = iteratedFDerivWithin 𝕜 n f s x v := by
  by_cases h : IsRCLikeNormedField 𝕜
  · haveI := h
    rw [minSmoothness_of_isRCLikeNormedField] at hf
    exact iteratedFDerivWithin_comp_perm hs h's hf hxs v σ
  · have hω : minSmoothness 𝕜 (n : ℕ∞ω) = ω := by
      simp [minSmoothness, h]
    rw [hω] at hf
    exact (hf x hxs).iteratedFDerivWithin_comp_perm hs hxs v σ

/-- On a **convex** set with nonempty interior over `ℝ` (a closed ball, an `Icc`, a
simplex, …): the `n`-th iterated derivative within the set of a `C^n`-on-the-set function
is symmetric at every point — including boundary points. Convex bodies are exactly the
domains of integration in the classical Stokes theorem, which is what this fragment
decomposition is building towards. -/
theorem iteratedFDerivWithin_comp_perm_of_convex [NormedSpace ℝ E] [NormedSpace ℝ F]
    (hconv : Convex ℝ s) (hne : (interior s).Nonempty) {n : ℕ}
    (hf : ContDiffOn ℝ (n : ℕ) f s) {x : E} (hxs : x ∈ s) (v : Fin n → E)
    (σ : Equiv.Perm (Fin n)) :
    iteratedFDerivWithin ℝ n f s x (v ∘ σ) = iteratedFDerivWithin ℝ n f s x v := by
  have hs : UniqueDiffOn ℝ s := uniqueDiffOn_convex hconv hne
  have h's : s ⊆ closure (interior s) := by
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior hne]
    exact subset_closure
  exact iteratedFDerivWithin_comp_perm hs h's hf hxs v σ

end Within

/-! ### Step 7 (S8): the classical nested form — iterated directional derivatives

Everything above is phrased through `iteratedFDeriv`, the multilinear-map packaging of the
`n`-th derivative. Classical texts state Clairaut/Schwarz differently: *nested* directional
derivatives commute,

  `∂_{v₀} (∂_{v₁} (… (∂_{vₙ₋₁} f))) = ∂_{v_{σ(0)}} (∂_{v_{σ(1)}} (… (∂_{v_{σ(n-1)}} f)))`,

where `∂_w g = fun y => fderiv 𝕜 g y w`. Mathlib (v4.31) has the bridge between the two
forms only at `n = 2` (`iteratedFDeriv_two_apply`); the general-`n` bridge — nested
directional derivatives of a `C^n` function compute the `n`-th iterated derivative applied
to the direction vector — is proved here (`nestedFDeriv_eq_iteratedFDeriv`), and the
classical nested Clairaut theorem follows from `iteratedFDeriv_comp_perm`.

(`Mathlib.Analysis.Distribution.DerivNotation` defines an abstract iterated
line-derivative operator `∂^{v}` via the `LineDeriv` notation typeclass, but provides no
instance for plain functions `E → F` and no relation to `iteratedFDeriv` — the concrete
bridge below is not there.) -/

variable (𝕜) in
/-- The `n`-fold nested directional derivative:
`nestedFDeriv 𝕜 n v f = ∂_{v 0} (∂_{v 1} (… (∂_{v (n-1)} f)))` where
`∂_w g = fun y => fderiv 𝕜 g y w` — direction `v 0` is applied *outermost*, matching the
left-to-right reading of `∂_{v₀} ∂_{v₁} … f`. -/
noncomputable def nestedFDeriv : (n : ℕ) → (Fin n → E) → (E → F) → E → F
  | 0, _, f => f
  | n + 1, v, f => fun x => fderiv 𝕜 (nestedFDeriv n (Fin.tail v) f) x (v 0)

@[simp]
theorem nestedFDeriv_zero (v : Fin 0 → E) (f : E → F) : nestedFDeriv 𝕜 0 v f = f :=
  rfl

theorem nestedFDeriv_succ_apply {n : ℕ} (v : Fin (n + 1) → E) (f : E → F) (x : E) :
    nestedFDeriv 𝕜 (n + 1) v f x = fderiv 𝕜 (nestedFDeriv 𝕜 n (Fin.tail v) f) x (v 0) :=
  rfl

@[simp]
theorem nestedFDeriv_one_apply (v : Fin 1 → E) (f : E → F) (x : E) :
    nestedFDeriv 𝕜 1 v f x = fderiv 𝕜 f x (v 0) :=
  rfl

/-- **The general-`n` nested/multilinear bridge.** For a `C^n` function, the `n`-fold
nested directional derivative along `v 0, …, v (n-1)` equals the `n`-th iterated Fréchet
derivative applied to `v`. Mathlib (v4.31) has this only at `n = 2`
(`iteratedFDeriv_two_apply`). Holds over any nontrivially normed field.

Inductive step: by the IH the inner `n`-fold nest is `y ↦ iteratedFDeriv 𝕜 n f y (tail v)`,
i.e. the multilinear-map-valued function `iteratedFDeriv 𝕜 n f` applied to the *constant*
tuple `tail v`; `fderiv_continuousMultilinear_apply_const_apply` commutes the constant
application past `fderiv` (differentiability of `iteratedFDeriv 𝕜 n f` comes from
`ContDiff.differentiable_iteratedFDeriv`), and `iteratedFDeriv_succ_apply_left` reassembles
the `(n+1)`-st derivative. -/
theorem nestedFDeriv_eq_iteratedFDeriv :
    ∀ {n : ℕ}, ContDiff 𝕜 (n : ℕ) f → ∀ (v : Fin n → E) (x : E),
      nestedFDeriv 𝕜 n v f x = iteratedFDeriv 𝕜 n f x v := by
  intro n
  induction n with
  | zero =>
    intro _ v x
    exact (iteratedFDeriv_zero_apply v).symm
  | succ n IH =>
    intro hf v x
    have hfn : ContDiff 𝕜 (n : ℕ) f := hf.of_le (by exact_mod_cast Nat.le_succ n)
    have hfun : nestedFDeriv 𝕜 n (Fin.tail v) f =
        fun y => iteratedFDeriv 𝕜 n f y (Fin.tail v) :=
      funext fun y => IH hfn (Fin.tail v) y
    have hdiff : DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 n f) x :=
      (hf.differentiable_iteratedFDeriv (by norm_cast; omega)).differentiableAt
    calc nestedFDeriv 𝕜 (n + 1) v f x
        = fderiv 𝕜 (nestedFDeriv 𝕜 n (Fin.tail v) f) x (v 0) := rfl
      _ = fderiv 𝕜 (fun y => iteratedFDeriv 𝕜 n f y (Fin.tail v)) x (v 0) := by
          rw [hfun]
      _ = fderiv 𝕜 (iteratedFDeriv 𝕜 n f) x (v 0) (Fin.tail v) :=
          fderiv_continuousMultilinear_apply_const_apply hdiff (Fin.tail v) (v 0)
      _ = iteratedFDeriv 𝕜 (n + 1) f x v := (iteratedFDeriv_succ_apply_left v).symm

/-- **Classical all-orders Clairaut/Schwarz, nested form.** For a `C^n` function over `ℝ`
or `ℂ`, nested directional derivatives may be taken in any order:

  `∂_{v_{σ(0)}} (∂_{v_{σ(1)}} (… f)) = ∂_{v_0} (∂_{v_1} (… f))`  at every point. -/
theorem nestedFDeriv_comp_perm [IsRCLikeNormedField 𝕜] {n : ℕ}
    (hf : ContDiff 𝕜 (n : ℕ) f) (v : Fin n → E) (σ : Equiv.Perm (Fin n)) (x : E) :
    nestedFDeriv 𝕜 n (v ∘ σ) f x = nestedFDeriv 𝕜 n v f x := by
  rw [nestedFDeriv_eq_iteratedFDeriv hf (v ∘ σ) x, nestedFDeriv_eq_iteratedFDeriv hf v x,
    iteratedFDeriv_comp_perm hf x v σ]

/-- Field-uniform `minSmoothness` form of the nested Clairaut theorem: over `ℝ`/`ℂ` the
hypothesis is `C^n`; over any other nontrivially normed field it degrades to analyticity.
The bridge itself only ever needs `C^n`, which `le_minSmoothness` extracts. -/
theorem nestedFDeriv_comp_perm_of_minSmoothness {n : ℕ}
    (hf : ContDiff 𝕜 (minSmoothness 𝕜 n) f) (v : Fin n → E) (σ : Equiv.Perm (Fin n))
    (x : E) :
    nestedFDeriv 𝕜 n (v ∘ σ) f x = nestedFDeriv 𝕜 n v f x := by
  have hfn : ContDiff 𝕜 (n : ℕ) f := hf.of_le le_minSmoothness
  rw [nestedFDeriv_eq_iteratedFDeriv hfn (v ∘ σ) x, nestedFDeriv_eq_iteratedFDeriv hfn v x,
    iteratedFDeriv_comp_perm_of_minSmoothness hf x v σ]

/-- **Second derivatives commute, nested classical form**: for a `C²` function over `ℝ` or
`ℂ`,

  `∂_a (∂_b f) = ∂_b (∂_a f)`,  i.e.
  `fderiv 𝕜 (fun y => fderiv 𝕜 f y b) x a = fderiv 𝕜 (fun y => fderiv 𝕜 f y a) x b`.

This differs from Mathlib's `IsSymmSndFDerivAt` (which swaps the two arguments of
`fderiv 𝕜 (fderiv 𝕜 f) x`, evaluation *outside* the outer derivative) precisely by the
bridge `nestedFDeriv_eq_iteratedFDeriv`; the nested spelling is the one in which the
classical `∂²f/∂x∂y = ∂²f/∂y∂x` is usually written. -/
theorem fderiv_fderiv_comm [IsRCLikeNormedField 𝕜] (hf : ContDiff 𝕜 2 f) (a b x : E) :
    fderiv 𝕜 (fun y => fderiv 𝕜 f y b) x a = fderiv 𝕜 (fun y => fderiv 𝕜 f y a) x b := by
  have h2 : ContDiff 𝕜 ((2 : ℕ) : ℕ∞ω) f := by exact_mod_cast hf
  have hab : (![b, a] : Fin 2 → E) ∘ ⇑(Equiv.swap 0 1) = ![a, b] := by
    funext i
    fin_cases i <;> simp
  have ha : Fin.tail (![a, b] : Fin 2 → E) = ![b] := by
    funext i
    fin_cases i
    rfl
  have hb : Fin.tail (![b, a] : Fin 2 → E) = ![a] := by
    funext i
    fin_cases i
    rfl
  have key := nestedFDeriv_comp_perm h2 (![b, a] : Fin 2 → E) (Equiv.swap 0 1) x
  rw [hab] at key
  calc fderiv 𝕜 (fun y => fderiv 𝕜 f y b) x a
      = nestedFDeriv 𝕜 2 ![a, b] f x := by
        rw [nestedFDeriv_succ_apply, ha]
        rfl
    _ = nestedFDeriv 𝕜 2 ![b, a] f x := key
    _ = fderiv 𝕜 (fun y => fderiv 𝕜 f y a) x b := by
        rw [nestedFDeriv_succ_apply, hb]
        rfl

/-! ### Step 8 (S9): the nested layer within a set, and line-derivative corollaries

The nested directional-derivative development of Step 7 (S8), transported to the
`Within` world (derivatives relative to a set `s`, boundary points included), plus the
honest *Gateaux* (line-derivative) form of the classical commutation statement.
`nestedFDerivWithin` is the `n`-fold `∂_{v}` built from `fderivWithin`; on a set with
unique derivatives (`UniqueDiffOn`) it computes `iteratedFDerivWithin` applied to the
direction tuple (`nestedFDerivWithin_eq_iteratedFDerivWithin`), and therefore inherits
the full permutation symmetry of Step 6 (S7) — including at boundary points of convex
bodies, the domains of the classical Stokes theorem.  The line-derivative corollary
closes the loop with the most classical spelling of Clairaut/Schwarz: mixed *Gateaux*
directional derivatives of a `C²` function commute, `∂_a ∂_b f = ∂_b ∂_a f`, where each
`∂` is a genuine one-dimensional limit `d/dt g(x + t w)|₀` (`lineDeriv`). -/

section WithinNested

variable {s : Set E}

variable (𝕜) in
/-- The `n`-fold nested directional derivative *within* `s`:
`nestedFDerivWithin 𝕜 n v f s = ∂_{v 0} (∂_{v 1} (… (∂_{v (n-1)} f)))` where
`∂_w g = fun y => fderivWithin 𝕜 g s y w` — the `Within` counterpart of
`nestedFDeriv`. -/
noncomputable def nestedFDerivWithin : (n : ℕ) → (Fin n → E) → (E → F) → Set E → E → F
  | 0, _, f, _ => f
  | n + 1, v, f, s => fun x =>
      fderivWithin 𝕜 (nestedFDerivWithin n (Fin.tail v) f s) s x (v 0)

@[simp]
theorem nestedFDerivWithin_zero (v : Fin 0 → E) (f : E → F) (s : Set E) :
    nestedFDerivWithin 𝕜 0 v f s = f :=
  rfl

theorem nestedFDerivWithin_succ_apply {n : ℕ} (v : Fin (n + 1) → E) (f : E → F)
    (s : Set E) (x : E) :
    nestedFDerivWithin 𝕜 (n + 1) v f s x
      = fderivWithin 𝕜 (nestedFDerivWithin 𝕜 n (Fin.tail v) f s) s x (v 0) :=
  rfl

@[simp]
theorem nestedFDerivWithin_one_apply (v : Fin 1 → E) (f : E → F) (s : Set E) (x : E) :
    nestedFDerivWithin 𝕜 1 v f s x = fderivWithin 𝕜 f s x (v 0) :=
  rfl

/-- On the whole space the `Within` nest is the plain nest. -/
theorem nestedFDerivWithin_univ :
    ∀ {n : ℕ} (v : Fin n → E) (f : E → F),
      nestedFDerivWithin 𝕜 n v f Set.univ = nestedFDeriv 𝕜 n v f := by
  intro n
  induction n with
  | zero => intro v f; rfl
  | succ n IH =>
    intro v f
    funext x
    rw [nestedFDerivWithin_succ_apply, nestedFDeriv_succ_apply, IH, fderivWithin_univ]

/-- **The `Within` nested/multilinear bridge**: for a `C^n`-on-`s` function and a set
with unique derivatives, the `n`-fold nested directional derivative within `s` computes
the `n`-th iterated derivative within `s` applied to the direction tuple, at every point
of `s` (boundary points included).  The inner nest agrees with the multilinear
application only *on* `s` — exactly what `fderivWithin_congr'` transports — and
`fderivWithin_continuousMultilinear_apply_const_apply` commutes the constant application
past `fderivWithin`. -/
theorem nestedFDerivWithin_eq_iteratedFDerivWithin (hs : UniqueDiffOn 𝕜 s) :
    ∀ {n : ℕ}, ContDiffOn 𝕜 (n : ℕ) f s → ∀ (v : Fin n → E), ∀ x ∈ s,
      nestedFDerivWithin 𝕜 n v f s x = iteratedFDerivWithin 𝕜 n f s x v := by
  intro n
  induction n with
  | zero =>
    intro _ v x _
    exact (iteratedFDerivWithin_zero_apply v).symm
  | succ n IH =>
    intro hf v x hx
    have hfn : ContDiffOn 𝕜 (n : ℕ) f s := hf.of_le (by exact_mod_cast Nat.le_succ n)
    have heq : Set.EqOn (nestedFDerivWithin 𝕜 n (Fin.tail v) f s)
        (fun y => iteratedFDerivWithin 𝕜 n f s y (Fin.tail v)) s :=
      fun y hy => IH hfn (Fin.tail v) y hy
    have hdiff : DifferentiableWithinAt 𝕜 (iteratedFDerivWithin 𝕜 n f s) s x :=
      hf.differentiableOn_iteratedFDerivWithin (by norm_cast; omega) hs x hx
    calc nestedFDerivWithin 𝕜 (n + 1) v f s x
        = fderivWithin 𝕜 (nestedFDerivWithin 𝕜 n (Fin.tail v) f s) s x (v 0) := rfl
      _ = fderivWithin 𝕜 (fun y => iteratedFDerivWithin 𝕜 n f s y (Fin.tail v)) s x
            (v 0) := by
          rw [fderivWithin_congr' heq hx]
      _ = fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n f s) s x (v 0) (Fin.tail v) :=
          fderivWithin_continuousMultilinear_apply_const_apply (hs x hx) hdiff
            (Fin.tail v) (v 0)
      _ = iteratedFDerivWithin 𝕜 (n + 1) f s x v :=
          (iteratedFDerivWithin_succ_apply_left v).symm

/-- **Classical nested Clairaut/Schwarz within a set**: on a set with unique derivatives
whose interior is dense in it, nested directional derivatives within the set of a
`C^n`-on-the-set function may be taken in any order — at every point of the set,
boundary included. -/
theorem nestedFDerivWithin_comp_perm [IsRCLikeNormedField 𝕜] {n : ℕ}
    (hs : UniqueDiffOn 𝕜 s) (h's : s ⊆ closure (interior s))
    (hf : ContDiffOn 𝕜 (n : ℕ) f s) {x : E} (hxs : x ∈ s) (v : Fin n → E)
    (σ : Equiv.Perm (Fin n)) :
    nestedFDerivWithin 𝕜 n (v ∘ σ) f s x = nestedFDerivWithin 𝕜 n v f s x := by
  rw [nestedFDerivWithin_eq_iteratedFDerivWithin hs hf (v ∘ σ) x hxs,
      nestedFDerivWithin_eq_iteratedFDerivWithin hs hf v x hxs,
      iteratedFDerivWithin_comp_perm hs h's hf hxs v σ]

/-- Field-uniform `minSmoothness` form of the nested `Within` Clairaut theorem. -/
theorem nestedFDerivWithin_comp_perm_of_minSmoothness {n : ℕ}
    (hs : UniqueDiffOn 𝕜 s) (h's : s ⊆ closure (interior s))
    (hf : ContDiffOn 𝕜 (minSmoothness 𝕜 n) f s) {x : E} (hxs : x ∈ s) (v : Fin n → E)
    (σ : Equiv.Perm (Fin n)) :
    nestedFDerivWithin 𝕜 n (v ∘ σ) f s x = nestedFDerivWithin 𝕜 n v f s x := by
  have hfn : ContDiffOn 𝕜 (n : ℕ) f s := hf.of_le le_minSmoothness
  rw [nestedFDerivWithin_eq_iteratedFDerivWithin hs hfn (v ∘ σ) x hxs,
      nestedFDerivWithin_eq_iteratedFDerivWithin hs hfn v x hxs,
      iteratedFDerivWithin_comp_perm_of_minSmoothness hs h's hf hxs v σ]

/-- Nested `Within` Clairaut on a **convex** set with nonempty interior over `ℝ` (closed
balls, `Icc`, simplices, …): nested directional derivatives within the set commute at
every point, including boundary points. -/
theorem nestedFDerivWithin_comp_perm_of_convex [NormedSpace ℝ E] [NormedSpace ℝ F]
    (hconv : Convex ℝ s) (hne : (interior s).Nonempty) {n : ℕ}
    (hf : ContDiffOn ℝ (n : ℕ) f s) {x : E} (hxs : x ∈ s) (v : Fin n → E)
    (σ : Equiv.Perm (Fin n)) :
    nestedFDerivWithin ℝ n (v ∘ σ) f s x = nestedFDerivWithin ℝ n v f s x := by
  have hs : UniqueDiffOn ℝ s := uniqueDiffOn_convex hconv hne
  have h's : s ⊆ closure (interior s) := by
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior hne]
    exact subset_closure
  exact nestedFDerivWithin_comp_perm hs h's hf hxs v σ

/-- **Second derivatives within a set commute, nested classical form**: the `Within`
counterpart of `fderiv_fderiv_comm` — for a `C²`-on-`s` function,
`∂_a (∂_b f) = ∂_b (∂_a f)` at every point of `s` with both `∂`'s taken within `s`. -/
theorem fderivWithin_fderivWithin_comm [IsRCLikeNormedField 𝕜]
    (hs : UniqueDiffOn 𝕜 s) (h's : s ⊆ closure (interior s))
    (hf : ContDiffOn 𝕜 2 f s) (a b : E) {x : E} (hxs : x ∈ s) :
    fderivWithin 𝕜 (fun y => fderivWithin 𝕜 f s y b) s x a
      = fderivWithin 𝕜 (fun y => fderivWithin 𝕜 f s y a) s x b := by
  have h2 : ContDiffOn 𝕜 ((2 : ℕ) : ℕ∞ω) f s := by exact_mod_cast hf
  have hab : (![b, a] : Fin 2 → E) ∘ ⇑(Equiv.swap 0 1) = ![a, b] := by
    funext i
    fin_cases i <;> simp
  have ha : Fin.tail (![a, b] : Fin 2 → E) = ![b] := by
    funext i
    fin_cases i
    rfl
  have hb : Fin.tail (![b, a] : Fin 2 → E) = ![a] := by
    funext i
    fin_cases i
    rfl
  have key := nestedFDerivWithin_comp_perm hs h's h2 hxs (![b, a] : Fin 2 → E)
    (Equiv.swap 0 1)
  rw [hab] at key
  calc fderivWithin 𝕜 (fun y => fderivWithin 𝕜 f s y b) s x a
      = nestedFDerivWithin 𝕜 2 ![a, b] f s x := by
        rw [nestedFDerivWithin_succ_apply, ha]
        rfl
    _ = nestedFDerivWithin 𝕜 2 ![b, a] f s x := key
    _ = fderivWithin 𝕜 (fun y => fderivWithin 𝕜 f s y a) s x b := by
        rw [nestedFDerivWithin_succ_apply, hb]
        rfl

end WithinNested

/-- **Mixed Gateaux (line) derivatives commute** for `C²` functions over `ℝ` or `ℂ`:
`∂_a (∂_b f) = ∂_b (∂_a f)` where `∂_w g x = lineDeriv 𝕜 g x w` is the genuine
one-dimensional directional derivative `d/dt g(x + t·w)|_{t=0}`.  For `f : ℝ² → ℝ` and
`a, b` the standard basis vectors this is literally the textbook
`∂²f/∂x∂y = ∂²f/∂y∂x`.  Follows from `fderiv_fderiv_comm` once both nests are
identified with Fréchet nests: the inner identification is
`DifferentiableAt.lineDeriv_eq_fderiv` for `f` itself, the outer one applies to
`y ↦ fderiv 𝕜 f y w`, which is differentiable because `fderiv 𝕜 f` is `C¹`
(`ContDiff.fderiv_right`) and constant evaluation is a continuous linear map
(`DifferentiableAt.clm_apply`). -/
theorem lineDeriv_lineDeriv_comm [IsRCLikeNormedField 𝕜] (hf : ContDiff 𝕜 2 f)
    (a b x : E) :
    lineDeriv 𝕜 (fun y => lineDeriv 𝕜 f y b) x a
      = lineDeriv 𝕜 (fun y => lineDeriv 𝕜 f y a) x b := by
  have hdiff : Differentiable 𝕜 f := hf.differentiable (by norm_num)
  have hinner : ∀ w : E, (fun y => lineDeriv 𝕜 f y w) = fun y => fderiv 𝕜 f y w := by
    intro w
    funext y
    exact (hdiff y).lineDeriv_eq_fderiv
  have hfd : Differentiable 𝕜 (fderiv 𝕜 f) := by
    have h1 : ContDiff 𝕜 1 (fderiv 𝕜 f) := hf.fderiv_right (m := 1) (by norm_num)
    exact h1.differentiable (by norm_num)
  have houter : ∀ (w : E) (y : E), DifferentiableAt 𝕜 (fun z => fderiv 𝕜 f z w) y :=
    fun w y => (hfd y).clm_apply (differentiableAt_const w)
  rw [hinner a, hinner b, (houter b x).lineDeriv_eq_fderiv,
      (houter a x).lineDeriv_eq_fderiv]
  exact fderiv_fderiv_comm hf a b x

/-! ### Step 9 (S10): the general-`n` Gateaux nest — `nestedLineDeriv`

The last classical spelling: `n`-fold nested *Gateaux* (line) derivatives.
Step 8's `lineDeriv_lineDeriv_comm` treats `n = 2`; here the full tower is
built — `nestedLineDeriv 𝕜 n v f = ∂_{v 0} (∂_{v 1} (… f))` with each `∂_w g x`
the genuine one-dimensional limit `d/dt g(x + t·w)|₀` (`lineDeriv`), no Fréchet
structure in the *statement* at all.  For a `C^n` function every level of the
nest is in fact Fréchet differentiable, so the Gateaux nest coincides with the
Fréchet nest (`nestedLineDeriv_eq_nestedFDeriv`, level-by-level via
`DifferentiableAt.lineDeriv_eq_fderiv`), hence computes the `n`-th iterated
derivative applied to the direction tuple and inherits the all-orders
permutation symmetry.  This is Clairaut/Schwarz in its weakest-primitive form:
only iterated one-dimensional limits appear. -/

section GateauxNested

variable (𝕜) in
/-- The `n`-fold nested Gateaux (line) derivative:
`nestedLineDeriv 𝕜 n v f = ∂_{v 0} (∂_{v 1} (… (∂_{v (n-1)} f)))` where
`∂_w g x = lineDeriv 𝕜 g x w = d/dt g(x + t·w)|_{t=0}` — direction `v 0`
outermost, matching `nestedFDeriv`. -/
noncomputable def nestedLineDeriv : (n : ℕ) → (Fin n → E) → (E → F) → E → F
  | 0, _, f => f
  | n + 1, v, f => fun x => lineDeriv 𝕜 (nestedLineDeriv n (Fin.tail v) f) x (v 0)

@[simp]
theorem nestedLineDeriv_zero (v : Fin 0 → E) (f : E → F) :
    nestedLineDeriv 𝕜 0 v f = f :=
  rfl

theorem nestedLineDeriv_succ_apply {n : ℕ} (v : Fin (n + 1) → E) (f : E → F) (x : E) :
    nestedLineDeriv 𝕜 (n + 1) v f x
      = lineDeriv 𝕜 (nestedLineDeriv 𝕜 n (Fin.tail v) f) x (v 0) :=
  rfl

@[simp]
theorem nestedLineDeriv_one_apply (v : Fin 1 → E) (f : E → F) (x : E) :
    nestedLineDeriv 𝕜 1 v f x = lineDeriv 𝕜 f x (v 0) :=
  rfl

/-- **The Gateaux/Fréchet nest bridge.** For a `C^n` function the `n`-fold nested
line derivative agrees with the `n`-fold nested Fréchet derivative: at each level
the inner nest is (by the S8 bridge) the constant-tuple evaluation of the
`C^{n-k}` multilinear derivative, hence Fréchet differentiable, and
`DifferentiableAt.lineDeriv_eq_fderiv` upgrades the Gateaux level to Fréchet.
Holds over any nontrivially normed field. -/
theorem nestedLineDeriv_eq_nestedFDeriv :
    ∀ {n : ℕ}, ContDiff 𝕜 (n : ℕ) f → ∀ (v : Fin n → E) (x : E),
      nestedLineDeriv 𝕜 n v f x = nestedFDeriv 𝕜 n v f x := by
  intro n
  induction n with
  | zero => intro _ v x; rfl
  | succ n IH =>
    intro hf v x
    have hfn : ContDiff 𝕜 (n : ℕ) f := hf.of_le (by exact_mod_cast Nat.le_succ n)
    have hfun : nestedLineDeriv 𝕜 n (Fin.tail v) f
        = nestedFDeriv 𝕜 n (Fin.tail v) f :=
      funext fun y => IH hfn (Fin.tail v) y
    have hfun2 : nestedFDeriv 𝕜 n (Fin.tail v) f
        = fun y => iteratedFDeriv 𝕜 n f y (Fin.tail v) :=
      funext fun y => nestedFDeriv_eq_iteratedFDeriv hfn (Fin.tail v) y
    have hdiff : DifferentiableAt 𝕜
        (fun y => iteratedFDeriv 𝕜 n f y (Fin.tail v)) x := by
      have h1 : DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 n f) x :=
        (hf.differentiable_iteratedFDeriv (by norm_cast; omega)).differentiableAt
      exact h1.continuousMultilinear_apply_const _
    calc nestedLineDeriv 𝕜 (n + 1) v f x
        = lineDeriv 𝕜 (nestedLineDeriv 𝕜 n (Fin.tail v) f) x (v 0) := rfl
      _ = lineDeriv 𝕜 (fun y => iteratedFDeriv 𝕜 n f y (Fin.tail v)) x (v 0) := by
          rw [hfun, hfun2]
      _ = fderiv 𝕜 (fun y => iteratedFDeriv 𝕜 n f y (Fin.tail v)) x (v 0) :=
          hdiff.lineDeriv_eq_fderiv
      _ = fderiv 𝕜 (nestedFDeriv 𝕜 n (Fin.tail v) f) x (v 0) := by rw [← hfun2]
      _ = nestedFDeriv 𝕜 (n + 1) v f x := rfl

/-- The Gateaux nest of a `C^n` function computes the `n`-th iterated Fréchet
derivative applied to the direction tuple — the two S8/S10 bridges composed. -/
theorem nestedLineDeriv_eq_iteratedFDeriv {n : ℕ} (hf : ContDiff 𝕜 (n : ℕ) f)
    (v : Fin n → E) (x : E) :
    nestedLineDeriv 𝕜 n v f x = iteratedFDeriv 𝕜 n f x v := by
  rw [nestedLineDeriv_eq_nestedFDeriv hf v x, nestedFDeriv_eq_iteratedFDeriv hf v x]

/-- **Classical all-orders Clairaut/Schwarz, Gateaux form.** For a `C^n` function
over `ℝ` or `ℂ`, nested one-dimensional directional derivatives may be taken in
any order — the weakest-primitive spelling of the theorem: only iterated limits
`d/dt g(x + t·w)|₀` appear in the statement. -/
theorem nestedLineDeriv_comp_perm [IsRCLikeNormedField 𝕜] {n : ℕ}
    (hf : ContDiff 𝕜 (n : ℕ) f) (v : Fin n → E) (σ : Equiv.Perm (Fin n)) (x : E) :
    nestedLineDeriv 𝕜 n (v ∘ σ) f x = nestedLineDeriv 𝕜 n v f x := by
  rw [nestedLineDeriv_eq_nestedFDeriv hf (v ∘ σ) x,
    nestedLineDeriv_eq_nestedFDeriv hf v x, nestedFDeriv_comp_perm hf v σ x]

/-- Field-uniform `minSmoothness` form of the Gateaux nested Clairaut theorem. -/
theorem nestedLineDeriv_comp_perm_of_minSmoothness {n : ℕ}
    (hf : ContDiff 𝕜 (minSmoothness 𝕜 n) f) (v : Fin n → E) (σ : Equiv.Perm (Fin n))
    (x : E) :
    nestedLineDeriv 𝕜 n (v ∘ σ) f x = nestedLineDeriv 𝕜 n v f x := by
  have hfn : ContDiff 𝕜 (n : ℕ) f := hf.of_le le_minSmoothness
  rw [nestedLineDeriv_eq_nestedFDeriv hfn (v ∘ σ) x,
    nestedLineDeriv_eq_nestedFDeriv hfn v x,
    nestedFDeriv_comp_perm_of_minSmoothness hf v σ x]

/-- Sanity: the `n = 2` Gateaux nest is literally the Step-8 double line
derivative, so `nestedLineDeriv_comp_perm` at `n = 2` recovers
`lineDeriv_lineDeriv_comm`. -/
theorem nestedLineDeriv_two_apply (a b : E) (f : E → F) (x : E) :
    nestedLineDeriv 𝕜 2 ![a, b] f x
      = lineDeriv 𝕜 (fun y => lineDeriv 𝕜 f y b) x a := by
  have ha : Fin.tail (![a, b] : Fin 2 → E) = ![b] := by
    funext i
    fin_cases i
    rfl
  rw [nestedLineDeriv_succ_apply, ha]
  rfl

end GateauxNested

end FTCOQ02Incomplete01
