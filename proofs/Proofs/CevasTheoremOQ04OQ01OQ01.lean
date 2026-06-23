import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Proofs.CevasTheoremOQ04OQ01

/-
# N-Dimensional Mass-Point Ceva: Constructive Converse (Mass from Ratios)

## Research Question (cevas-theorem-oq-04-oq-01, S3 follow-up)

The parent file `CevasTheoremOQ04OQ01.lean` proves the *forward* direction of the
n-dimensional mass-point Ceva identity: a `MassPoint n` (n+1 positive vertex
masses on an n-simplex) yields complement fractions

  ratio i = (Σ_{j ≠ i} mass j) / total = 1 - mass i / total

that satisfy the **dimensional Ceva identity** `Σ_i ratio i = n` with each
`ratio i ∈ (0, 1)`.

This file proves the **converse / realisation** direction (listed as S3
candidate #2 in the parent's "Next iteration" section), the n-dimensional
analogue of the triangle file's `masses_from_ceva`:

> Given a *ratio profile* `r : Fin (n+1) → ℝ` with each `r i < 1` and
> `Σ_i r i = n`, there exist positive masses realising it, i.e. a
> `MassPoint n` whose complement fractions are exactly `r`.

The construction is the canonical normalised one: take `mass i = 1 - r i`.
Positivity is exactly `r i < 1`; the sum constraint `Σ r i = n` forces
`total = (n+1) - n = 1`, hence `mass i / total = 1 - r i` and
`ratio i = 1 - (1 - r i) = r i`.

We also record the **normalised uniqueness** statement: among mass points of
total mass `1`, the ratio profile determines the masses (so the realisation
above is the unique normalised representative of its ratio class).

## What this file does

* `massesFromRatio` — the canonical `MassPoint n` with `mass i = 1 - r i`
* `massesFromRatio_total` — its total mass is `1`
* `massesFromRatio_ratio` — its complement fractions are exactly `r`
* `exists_massPoint_of_ratioProfile` — the realisation theorem (∃ form)
* `massPoint_normalized_unique` — total-`1` mass points are determined by ratios
* `massesFromRatio_pos` — restated positivity of the constructed masses
* n = 2 (triangle) specialisation as a sanity check

## What this file does NOT do (still deferred)

* `AffineSpace`/`AffineCombination` geometric concurrency (S3 candidate #3).
* The triangle bridge to `MassPointCeva.MassPoint` edge-split parameters
  (S3 candidate #1).

## References

* Parent: `proofs/Proofs/CevasTheoremOQ04OQ01.lean`
* Grandparent: `proofs/Proofs/CevasTheoremOQ04.lean` (`masses_from_ceva`)
* Mathlib: `Mathlib.LinearAlgebra.AffineSpace.Ceva` (Joseph Myers 2025)
-/

namespace NDimMassPoint

variable {n : ℕ}

/-- The canonical **mass-from-ratios** construction: given a ratio profile
    `r` with each `r i < 1`, the masses `mass i = 1 - r i` are positive.
    (The sum constraint `Σ r i = n` is not needed for positivity, only for
    the total to normalise to `1`.) -/
noncomputable def massesFromRatio (r : Fin (n + 1) → ℝ) (hr1 : ∀ i, r i < 1) :
    MassPoint n where
  mass := fun i => 1 - r i
  pos  := fun i => by have := hr1 i; linarith

@[simp] lemma massesFromRatio_mass (r : Fin (n + 1) → ℝ) (hr1 : ∀ i, r i < 1)
    (i : Fin (n + 1)) : (massesFromRatio r hr1).mass i = 1 - r i := rfl

/-- Restated positivity of the constructed masses. -/
lemma massesFromRatio_pos (r : Fin (n + 1) → ℝ) (hr1 : ∀ i, r i < 1)
    (i : Fin (n + 1)) : 0 < (massesFromRatio r hr1).mass i :=
  (massesFromRatio r hr1).pos i

/-- The constraint `Σ r i = n` forces the constructed total mass to be `1`. -/
lemma massesFromRatio_total (r : Fin (n + 1) → ℝ) (hr1 : ∀ i, r i < 1)
    (hsum : (∑ i, r i) = (n : ℝ)) : (massesFromRatio r hr1).total = 1 := by
  unfold MassPoint.total
  have hone : (∑ _i : Fin (n + 1), (1 : ℝ)) = (n + 1 : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp
  simp only [massesFromRatio_mass]
  rw [Finset.sum_sub_distrib, hone, hsum]
  ring

/-- **Realisation, explicit form**: the constructed mass point has complement
    fractions exactly equal to the given ratio profile `r`. -/
lemma massesFromRatio_ratio (r : Fin (n + 1) → ℝ) (hr1 : ∀ i, r i < 1)
    (hsum : (∑ i, r i) = (n : ℝ)) (i : Fin (n + 1)) :
    (massesFromRatio r hr1).ratio i = r i := by
  rw [MassPoint.ratio_eq_one_sub, massesFromRatio_total r hr1 hsum,
      massesFromRatio_mass, div_one]
  ring

/-- **N-dim Mass-Point Ceva, converse / realisation theorem.**

    Every ratio profile `r : Fin (n+1) → ℝ` that satisfies the necessary
    conditions — each `r i < 1` and `Σ_i r i = n` — is realised by an actual
    positive-mass assignment on the n-simplex.  This is the n-dimensional
    analogue of the triangle file's `masses_from_ceva`. -/
theorem exists_massPoint_of_ratioProfile (r : Fin (n + 1) → ℝ)
    (hr1 : ∀ i, r i < 1) (hsum : (∑ i, r i) = (n : ℝ)) :
    ∃ mp : MassPoint n, ∀ i, mp.ratio i = r i :=
  ⟨massesFromRatio r hr1, massesFromRatio_ratio r hr1 hsum⟩

/-- **Normalised uniqueness**: among mass points whose total mass is `1`,
    the complement-fraction profile determines the masses uniquely.  Combined
    with `massesFromRatio_total`, this says `massesFromRatio` is *the* unique
    total-`1` representative of each realisable ratio class. -/
theorem massPoint_normalized_unique (mp₁ mp₂ : MassPoint n)
    (h₁ : mp₁.total = 1) (h₂ : mp₂.total = 1)
    (hr : ∀ i, mp₁.ratio i = mp₂.ratio i) :
    ∀ i, mp₁.mass i = mp₂.mass i := by
  intro i
  have e₁ := mp₁.ratio_eq_one_sub i
  have e₂ := mp₂.ratio_eq_one_sub i
  rw [h₁, div_one] at e₁
  rw [h₂, div_one] at e₂
  have key := hr i
  rw [e₁, e₂] at key
  linarith

/- ## Specialisation to n = 2 (triangle): sanity check -/

/-- For a triangle ratio profile `(r₀, r₁, r₂)` with each `rᵢ < 1` and
    `r₀ + r₁ + r₂ = 2`, there is a positive-mass triangle realising it. -/
example (r : Fin 3 → ℝ) (hr1 : ∀ i, r i < 1)
    (hsum : r 0 + r 1 + r 2 = 2) :
    ∃ mp : MassPoint 2, ∀ i, mp.ratio i = r i := by
  refine exists_massPoint_of_ratioProfile r hr1 ?_
  rw [Fin.sum_univ_three]
  exact_mod_cast hsum

end NDimMassPoint

/-
## Summary

* `massesFromRatio r hr1` — canonical realising masses `mass i = 1 - r i`
* `massesFromRatio_total` — total normalises to `1` under `Σ r i = n`
* `massesFromRatio_ratio` — complement fractions recover `r` exactly
* `exists_massPoint_of_ratioProfile` — realisation theorem (n-dim converse)
* `massPoint_normalized_unique` — total-`1` masses determined by ratios
* n = 2 triangle specialisation verified

**Sorry count**: 0
**Axiom count**: 0
-/
