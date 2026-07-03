/-
# Hilbert's 13th Problem — OQ-03
## What are the minimal requirements on the inner functions?

Hilbert #13 / OQ-03 asks: in the Kolmogorov–Arnold superposition

  f(x₁,…,xₙ) = Σ_q Φ_q( Σ_p coeff_{p,q} · φ_p(x_p) ),

what are the **minimal requirements on the inner functions** `φ_p` (and the coefficients)
for such a representation to be possible for *every* continuous `f`? The full sufficiency
question is genuinely deep — the precise characterisation of admissible inner families is the
content of Sternfeld's "basic embedding" theory (1985) and remains subtle. This file does NOT
resolve sufficiency. Instead it isolates and **fully verifies (0 axioms, 0 sorries)** the
*necessary* core that any admissible inner family must satisfy:

> **Point separation is mandatory.** Bundle the inner data into a single "feature map"
> `Ψ : domain → ℝ^Q`, `Ψ(x)_q = Σ_p coeff_{p,q} · φ_p(x_p)`. The outer functions `Φ_q` see `x`
> *only through* `Ψ(x)`. Therefore if `Ψ` collapses two distinct points (`Ψ x = Ψ y`, `x ≠ y`),
> then **every** representable function is forced to agree on them: `f x = f y`. Since continuous
> functions on the cube separate points, a universal inner family must make `Ψ` **injective**.
>
> As a concrete consequence on the individual inner functions: each `φ_p` must itself be
> **injective**. (Take two cube points differing only in coordinate `p`; `Ψ` distinguishes them
> only if `φ_p` does.)

This is the unconditional, provable kernel of "minimal requirements on the inner functions":
injectivity (point separation) is *necessary*. It is not sufficient — Sternfeld showed the
requirement is strictly stronger (a uniform "α-separation" / measure-separation condition) — and
we make no claim to the contrary; see the closing remark.

## Results (0 axioms, 0 sorries)
* `OuterRepresentable` — `f = Σ_q Φ_q ∘ (Ψ · _q)` for some outer functions `Φ`.
* `eq_of_feature_eq` — outer functions cannot separate points the feature map merges:
  `Ψ x = Ψ y → f x = f y` for any representable `f`.
* `feature_injective_of_universal` — if every point-separating (continuous) function is
  representable through `Ψ`, then `Ψ` is injective.
* `kaFeature` — the Kolmogorov–Arnold inner feature map on the product domain.
* `inner_injective_of_feature_injective` — an injective KA feature map forces each inner
  function `φ_p` to be injective.
* `inner_functions_must_be_injective` — the headline necessary condition: a single inner family
  `(φ, coeff)` that represents *every* continuous function on `ℝⁿ` must have every `φ_p` injective.

## References
- Kolmogorov, A.N. (1957). "On the representation of continuous functions of several variables
  by superpositions of continuous functions of one variable and addition."
- Arnold, V.I. (1957). "On functions of three variables."
- Sternfeld, Y. (1985). "Dimension, superposition of functions and separation of points, in
  compact metric spaces." Israel J. Math. (the sharp characterisation of admissible inner families)
- Ostrand, P.A. (1965). "Dimension of metric spaces and Hilbert's problem 13."
-/

import Mathlib

namespace Hilbert13OQ03

/-! ## The feature map abstraction

Whatever the inner functions are, the outer functions only ever see the domain point `x`
through the `Q`-tuple of inner sums. We call that tuple the *feature map* `Ψ x : Fin Q → ℝ`. -/

/-- `f` is representable by outer univariate functions composed with the feature map `Ψ`:
    `f x = Σ_q Φ_q (Ψ x q)` for some family of outer functions `Φ`. This is exactly the shape
    of a Kolmogorov–Arnold superposition once the inner sums are bundled into `Ψ`. -/
def OuterRepresentable {X : Type*} {Q : ℕ} (Ψ : X → (Fin Q → ℝ)) (f : X → ℝ) : Prop :=
  ∃ Φ : Fin Q → (ℝ → ℝ), ∀ x, f x = ∑ q, Φ q (Ψ x q)

/-- **Outer functions cannot separate what the feature map merges.**
    If the feature map sends `x` and `y` to the same tuple, every representable function agrees
    on them. This is the structural obstruction at the heart of the inner-function requirements:
    the burden of *separating points* falls entirely on the inner data `Ψ`. -/
theorem eq_of_feature_eq {X : Type*} {Q : ℕ} {Ψ : X → (Fin Q → ℝ)} {f : X → ℝ}
    (hf : OuterRepresentable Ψ f) {x y : X} (h : Ψ x = Ψ y) : f x = f y := by
  obtain ⟨Φ, hΦ⟩ := hf
  calc f x = ∑ q, Φ q (Ψ x q) := hΦ x
    _ = ∑ q, Φ q (Ψ y q) := by rw [h]
    _ = f y := (hΦ y).symm

/-- **Converse: the feature map is the *only* obstruction.**
    If the feature map already distinguishes `x` and `y`, then some representable function does
    too — namely the feature coordinate `q` on which they differ, realised by the outer family
    `Φ_q = id`, `Φ_{q'} = 0` for `q' ≠ q`. So the outer layer *can* recover any separation the
    inner layer provides; it is powerless only against merges. -/
theorem exists_representable_of_feature_ne {X : Type*} {Q : ℕ} (Ψ : X → (Fin Q → ℝ))
    {x y : X} (h : Ψ x ≠ Ψ y) :
    ∃ f : X → ℝ, OuterRepresentable Ψ f ∧ f x ≠ f y := by
  obtain ⟨q, hq⟩ := Function.ne_iff.mp h
  refine ⟨fun z => Ψ z q, ⟨fun q' => if q' = q then id else 0, fun z => ?_⟩, hq⟩
  rw [Finset.sum_eq_single_of_mem q (Finset.mem_univ q)]
  · simp
  · intro q' _ hq'; simp [hq']

/-- **Fibers of the feature map = indistinguishability classes.**
    The representable functions separate `x` and `y` *iff* the feature map does. Combining the
    collapse lemma (`eq_of_feature_eq`) with its converse, the equivalence relation "every
    representable function agrees on `x` and `y`" is *exactly* `Ψ x = Ψ y`: the feature map's
    fibers are precisely the classes of points no Kolmogorov–Arnold superposition can tell apart.
    This sharpens "point separation is necessary" into "point separation is exactly what the
    outer layer cannot recover". -/
theorem representable_separates_iff_feature_ne {X : Type*} {Q : ℕ} (Ψ : X → (Fin Q → ℝ))
    (x y : X) :
    (∃ f : X → ℝ, OuterRepresentable Ψ f ∧ f x ≠ f y) ↔ Ψ x ≠ Ψ y := by
  constructor
  · rintro ⟨f, hf, hfxy⟩ h
    exact hfxy (eq_of_feature_eq hf h)
  · exact fun h => exists_representable_of_feature_ne Ψ h

/-- **Necessity of point separation.**
    Suppose every function that *some* continuous function distinguishes is representable through
    `Ψ` (the "universal inner family" situation), and that continuous functions separate the
    points of `X`. Then `Ψ` must be injective: it cannot afford to merge any two distinct points,
    because some continuous (hence representable) function tells them apart. -/
theorem feature_injective_of_universal {X : Type*} [TopologicalSpace X] {Q : ℕ}
    {Ψ : X → (Fin Q → ℝ)}
    (huniv : ∀ f : X → ℝ, Continuous f → OuterRepresentable Ψ f)
    (hsep : ∀ x y : X, x ≠ y → ∃ f : X → ℝ, Continuous f ∧ f x ≠ f y) :
    Function.Injective Ψ := by
  intro x y h
  by_contra hxy
  obtain ⟨f, hcont, hfxy⟩ := hsep x y hxy
  exact hfxy (eq_of_feature_eq (huniv f hcont) h)

/-! ## The Kolmogorov–Arnold inner feature map

Now specialise `Ψ` to the actual Kolmogorov–Arnold shape on the product domain `Fin n → ℝ`:
each feature coordinate `q` is the inner sum `Σ_p coeff_{p,q} · φ_p(x_p)`. -/

/-- The Kolmogorov–Arnold inner feature map: `kaFeature φ coeff x q = Σ_p coeff_{p,q} · φ_p(x_p)`. -/
def kaFeature {n Q : ℕ} (φ : Fin n → (ℝ → ℝ)) (coeff : Fin n → Fin Q → ℝ) :
    (Fin n → ℝ) → (Fin Q → ℝ) :=
  fun x q => ∑ p, coeff p q * φ p (x p)

/-- **An injective KA feature map forces every inner function to be injective.**
    If `φ_p(a) = φ_p(b)` for some `a ≠ b`, then the two cube points that differ only in
    coordinate `p` (values `a` vs `b`, all other coordinates `0`) have identical feature tuples,
    so the feature map could not be injective. Contrapositive: injectivity of the bundled feature
    map descends to each individual inner function. -/
theorem inner_injective_of_feature_injective {n Q : ℕ}
    {φ : Fin n → (ℝ → ℝ)} {coeff : Fin n → Fin Q → ℝ}
    (hinj : Function.Injective (kaFeature φ coeff)) (p : Fin n) :
    Function.Injective (φ p) := by
  intro a b hab
  -- Two points differing only in coordinate `p`.
  have key : (fun i => if i = p then a else 0) = (fun i => if i = p then b else 0) := by
    apply hinj
    funext q
    show ∑ p', coeff p' q * φ p' (if p' = p then a else 0)
       = ∑ p', coeff p' q * φ p' (if p' = p then b else 0)
    apply Finset.sum_congr rfl
    intro p' _
    rcases eq_or_ne p' p with hp | hp
    · subst hp; simp [hab]
    · simp [hp]
  have := congrFun key p
  simpa using this

/-! ## Point separation on the cube domain

On the product domain `Fin n → ℝ` (with its product topology) continuous functions separate
points: the coordinate projections already do. -/

/-- Continuous functions separate points of `Fin n → ℝ`: distinct points differ in some
    coordinate, and that coordinate projection is continuous. -/
theorem separates_of_pi {n : ℕ} (x y : Fin n → ℝ) (h : x ≠ y) :
    ∃ f : (Fin n → ℝ) → ℝ, Continuous f ∧ f x ≠ f y := by
  obtain ⟨p, hp⟩ := Function.ne_iff.mp h
  exact ⟨fun z => z p, continuous_apply p, hp⟩

/-- **The minimal requirement, made explicit.**
    If one fixed inner family `(φ, coeff)` yields a Kolmogorov–Arnold superposition for *every*
    continuous function on `ℝⁿ`, then every inner function `φ_p` must be injective. Injectivity
    (point separation) is therefore a *necessary* condition on the inner functions — the
    unconditional core of "what are the minimal requirements on the inner functions". -/
theorem inner_functions_must_be_injective {n Q : ℕ}
    (φ : Fin n → (ℝ → ℝ)) (coeff : Fin n → Fin Q → ℝ)
    (huniv : ∀ f : (Fin n → ℝ) → ℝ, Continuous f →
        OuterRepresentable (kaFeature φ coeff) f)
    (p : Fin n) :
    Function.Injective (φ p) :=
  inner_injective_of_feature_injective
    (feature_injective_of_universal huniv separates_of_pi) p

/-- **The bundled form.** The same hypotheses force the whole inner feature map to be injective —
    i.e. the inner family must *separate the points of the cube*. This is the strongest
    necessary statement available at this level of generality. -/
theorem feature_must_separate_points {n Q : ℕ}
    (φ : Fin n → (ℝ → ℝ)) (coeff : Fin n → Fin Q → ℝ)
    (huniv : ∀ f : (Fin n → ℝ) → ℝ, Continuous f →
        OuterRepresentable (kaFeature φ coeff) f) :
    Function.Injective (kaFeature φ coeff) :=
  feature_injective_of_universal huniv separates_of_pi

/-!
## Closing remark: necessity vs. sufficiency

Injectivity of the inner feature map (equivalently, each `φ_p` being injective together with the
coefficient combination separating points) is **necessary** but **not sufficient**. Sternfeld
(1985) proved that an inner family admits a continuous outer reconstruction for *all* continuous
`f` only under a strictly stronger, *uniform* separation condition (no two distinct points may be
"asymptotically merged"); mere injectivity allows the outer functions to require unbounded
oscillation and fail continuity. So the present result pins down the *floor* of the requirements —
point separation — while the *exact* admissibility threshold is the deeper Sternfeld criterion,
which we do not formalise here.
-/

#check @eq_of_feature_eq
#check @exists_representable_of_feature_ne
#check @representable_separates_iff_feature_ne
#check @feature_injective_of_universal
#check @inner_injective_of_feature_injective
#check @inner_functions_must_be_injective
#check @feature_must_separate_points

end Hilbert13OQ03
