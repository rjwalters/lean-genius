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
* `iteratedFDerivWithin_comp_perm_of_isOpen` is the `Within` version on open sets. (The full
  `UniqueDiffOn`-set `Within` version needs the whole induction redone with `fderivWithin`
  and is left as further upstream work — see the state.md S6 notes.)

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
(The general `UniqueDiffOn` version requires redoing the induction with `fderivWithin`
and is left as further upstream work.) -/
theorem iteratedFDerivWithin_comp_perm_of_isOpen [IsRCLikeNormedField 𝕜] {n : ℕ}
    (hf : ContDiff 𝕜 (n : ℕ) f) {s : Set E} (hs : IsOpen s) {x : E} (hx : x ∈ s)
    (v : Fin n → E) (σ : Equiv.Perm (Fin n)) :
    iteratedFDerivWithin 𝕜 n f s x (v ∘ σ) = iteratedFDerivWithin 𝕜 n f s x v := by
  rw [iteratedFDerivWithin_of_isOpen n hs hx]
  exact iteratedFDeriv_comp_perm hf x v σ

end FTCOQ02Incomplete01
