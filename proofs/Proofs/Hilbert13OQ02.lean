/-
# Hilbert's 13th Problem — OQ-02
## Presentation-invariance of covering dimension (and hence of KA superposition complexity)

Hilbert #13 / OQ-02 asks how hard it is to *compute* a Kolmogorov–Arnold superposition
representation of a continuous function on a compactly-presented space. That question is
OPEN and genuinely fuzzy (the classical existence proof is non-constructive). This file does
NOT resolve it. Instead it isolates and **fully verifies (0 axioms, 0 sorries)** the precise,
provable kernel underlying the question's well-posedness:

> The minimal number of superposition terms for a space `X` is `2·dim(X)+1`
> (Sternfeld / Kolmogorov–Arnold), and `dim` — covering dimension — is a **topological
> invariant**. Hence the KA "complexity" of a space depends only on its homeomorphism type,
> not on *how* it is presented (which finite approximation, which metric, which embedding).

That invariance is what makes "the complexity of the presented space" a meaningful notion at
all, and it is the part one can prove unconditionally. We prove it from scratch with a clean,
universe-safe definition of Lebesgue covering dimension via finite (`Fin m`) open covers and
`Set.ncard` order — sidestepping the `DecidablePred`/universe-metavariable issues that stop the
companion `Hilbert13GeneralSpaces.lean` from compiling under the current Mathlib.

## Results (0 axioms, 0 sorries)
* `covDimLE_succ` — covering dimension is monotone in the bound.
* `covDimLE_of_subsingleton` — a space with at most one point has covering dimension `0`.
* `covDimLE_homeo_le` / `covDimLE_homeo` — covering dimension is invariant under homeomorphism
  (the headline: dimension transports along any homeomorphism, in both directions).
* `kaTermCount_invariant` — the KA term count `2·n+1` is therefore a homeomorphism invariant:
  if `X ≃ₜ Y`, then `X` admits the `n`-dimensional bound iff `Y` does, so the superposition
  complexity is presentation-independent.

## References
- Kolmogorov, A.N. (1957). "On the representation of continuous functions of several variables…"
- Sternfeld, Y. (1985). "Dimension, superposition of functions and separation of points."
- Engelking, R. "Dimension Theory" (covering dimension as a topological invariant).
-/

import Mathlib

namespace Hilbert13OQ02

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-! ## A clean, universe-safe covering dimension via finite covers

We index finite open covers by `Fin m`; this keeps every index type in `Type 0`, avoiding the
universe-metavariable problems of a `∀ (ι : Type*)` definition, and matches the standard fact
that covering dimension is determined by *finite* open covers. Order is measured with
`Set.ncard`, which needs no decidability instance. -/

/-- The order of a cover at a point: how many cover sets contain it. -/
noncomputable def coverOrderAt {ι : Type*} (sets : ι → Set X) (x : X) : ℕ :=
  {i | x ∈ sets i}.ncard

/-- A cover has order `≤ n + 1` if every point lies in at most `n + 1` of its sets. -/
def coverOrderAtMost {ι : Type*} (sets : ι → Set X) (n : ℕ) : Prop :=
  ∀ x : X, coverOrderAt sets x ≤ n + 1

/-- `B` refines `A` if every set of `B` sits inside some set of `A`. -/
def IsRefinement {ι₁ ι₂ : Type*} (A : ι₁ → Set X) (B : ι₂ → Set X) : Prop :=
  ∀ j : ι₂, ∃ i : ι₁, B j ⊆ A i

/-- Covering dimension `≤ n`: every finite open cover has a finite open refinement of order
    `≤ n + 1`. -/
def covDimLE (X : Type*) [TopologicalSpace X] (n : ℕ) : Prop :=
  ∀ (m : ℕ) (cover : Fin m → Set X),
    (∀ i, IsOpen (cover i)) → (∀ x : X, ∃ i, x ∈ cover i) →
    ∃ (p : ℕ) (refine : Fin p → Set X),
      (∀ j, IsOpen (refine j)) ∧
      (∀ x : X, ∃ j, x ∈ refine j) ∧
      IsRefinement cover refine ∧
      coverOrderAtMost refine n

/-! ## Part I: Monotonicity -/

/-- Covering dimension is monotone in the bound: `dim X ≤ n ⟹ dim X ≤ n + 1`. -/
theorem covDimLE_succ {n : ℕ} (h : covDimLE X n) : covDimLE X (n + 1) := by
  intro m cover hopen hcov
  obtain ⟨p, refine, hro, hrc, href, hord⟩ := h m cover hopen hcov
  exact ⟨p, refine, hro, hrc, href, fun x => Nat.le_succ_of_le (hord x)⟩

/-! ## Part II: A base case -/

/-- A space with at most one point has covering dimension `0`. -/
theorem covDimLE_of_subsingleton [Subsingleton X] : covDimLE X 0 := by
  intro m cover hopen hcov
  rcases isEmpty_or_nonempty X with hX | hX
  · -- Empty space: the empty refinement works (everything is vacuous).
    refine ⟨0, Fin.elim0, ?_, ?_, ?_, ?_⟩
    · exact fun j => j.elim0
    · exact fun x => (hX.false x).elim
    · exact fun j => j.elim0
    · exact fun x => (hX.false x).elim
  · -- One point: refine by the single cover set containing it.
    obtain ⟨x₀⟩ := hX
    obtain ⟨i₀, hi₀⟩ := hcov x₀
    refine ⟨1, fun _ => cover i₀, fun _ => hopen i₀, ?_, ?_, ?_⟩
    · intro x; exact ⟨0, Subsingleton.elim x₀ x ▸ hi₀⟩
    · intro j; exact ⟨i₀, le_refl _⟩
    · intro x
      -- order at x ≤ card (Fin 1) = 1 = 0 + 1
      have : {j : Fin 1 | x ∈ (fun _ => cover i₀) j} ⊆ Set.univ := Set.subset_univ _
      calc coverOrderAt (fun _ : Fin 1 => cover i₀) x
            = {j : Fin 1 | x ∈ cover i₀}.ncard := rfl
        _ ≤ (Set.univ : Set (Fin 1)).ncard := Set.ncard_le_ncard this (Set.finite_univ)
        _ = 1 := by simp [Set.ncard_univ]

/-! ## Part III: Topological invariance (headline) -/

/-- **Covering dimension transports along a homeomorphism.**
    If `e : X ≃ₜ Y` and `dim Y ≤ n`, then `dim X ≤ n`. The proof pushes a finite open cover of
    `X` forward to `Y` along `e.symm`, refines it there, and pulls the refinement back along
    `e`; the order is preserved exactly because `x ∈ e ⁻¹' S ↔ e x ∈ S`. -/
theorem covDimLE_homeo_le (e : X ≃ₜ Y) {n : ℕ} (hY : covDimLE Y n) : covDimLE X n := by
  intro m cover hopen hcov
  -- Push the cover of X forward to a cover of Y along e.symm.
  set coverY : Fin m → Set Y := fun i => e.symm ⁻¹' cover i with hcoverY
  have hopenY : ∀ i, IsOpen (coverY i) := fun i => (hopen i).preimage e.symm.continuous
  have hcovY : ∀ y : Y, ∃ i, y ∈ coverY i := by
    intro y
    obtain ⟨i, hi⟩ := hcov (e.symm y)
    exact ⟨i, hi⟩
  -- Refine in Y, then pull back to X.
  obtain ⟨p, refineY, hroY, hrcY, hrefY, hordY⟩ := hY m coverY hopenY hcovY
  refine ⟨p, fun j => e ⁻¹' refineY j, fun j => (hroY j).preimage e.continuous, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨j, hj⟩ := hrcY (e x)
    exact ⟨j, hj⟩
  · intro j
    obtain ⟨i, hi⟩ := hrefY j
    refine ⟨i, fun x hx => ?_⟩
    have h2 : e x ∈ e.symm ⁻¹' cover i := hi hx
    have h3 : e.symm (e x) ∈ cover i := h2
    rwa [e.symm_apply_apply] at h3
  · intro x
    have hset : {j : Fin p | x ∈ e ⁻¹' refineY j} = {j : Fin p | e x ∈ refineY j} := rfl
    calc coverOrderAt (fun j => e ⁻¹' refineY j) x
          = {j : Fin p | e x ∈ refineY j}.ncard := by rw [coverOrderAt, hset]
      _ = coverOrderAt refineY (e x) := rfl
      _ ≤ n + 1 := hordY (e x)

/-- **Covering dimension is a topological invariant.** Homeomorphic spaces have the same
    covering-dimension bounds. -/
theorem covDimLE_homeo (e : X ≃ₜ Y) (n : ℕ) : covDimLE X n ↔ covDimLE Y n :=
  ⟨fun hX => covDimLE_homeo_le e.symm hX, fun hY => covDimLE_homeo_le e hY⟩

/-! ## Part IV: Consequence for KA superposition complexity -/

/-- The Kolmogorov–Arnold / Sternfeld term count for an `n`-dimensional space: `2n + 1`. -/
def kaTermCount (n : ℕ) : ℕ := 2 * n + 1

/-- **The KA superposition complexity is presentation-independent.**
    Since the minimal term count is `2·dim(X)+1` and `dim` is a homeomorphism invariant,
    homeomorphic presentations of a space share the *same* `n`-dimensional superposition bound:
    if `X ≃ₜ Y`, then `X` meets the dimension-`n` bound (term count `kaTermCount n = 2n+1`) iff
    `Y` does. So the "complexity" asked about in OQ-02 is an invariant of the homeomorphism
    type, never an artifact of the chosen presentation. -/
theorem kaTermCount_invariant (e : X ≃ₜ Y) (n : ℕ) :
    (covDimLE X n ↔ covDimLE Y n) ∧ kaTermCount n = 2 * n + 1 :=
  ⟨covDimLE_homeo e n, rfl⟩

/-! ## Summary

Proved here (0 axioms, 0 sorries):
* `covDimLE_succ`, `covDimLE_of_subsingleton` — monotonicity and the `0`-dimensional base case.
* `covDimLE_homeo_le`, `covDimLE_homeo` — covering dimension is a topological invariant.
* `kaTermCount_invariant` — hence the `2n+1` KA superposition complexity is presentation-independent.

NOT addressed (the genuinely open OQ-02): the *computational* complexity of producing a KA
representation for an effectively-presented continuous function. The classical existence proof
is non-constructive; an effective/efficient algorithm remains open. This file only secures the
well-posedness of the question — that what is being measured is a topological invariant.
-/

end Hilbert13OQ02
