/-
  Knight's Tour Oblique Angles: The Order-16 Group Acts on Level Sets (OQ-02)

  `KnightsTourObliqueOQ02Order16.lean` fused the order-8 dihedral board group
  `D4` and the order-2 time reversal `C2` into the full order-16 symmetry group
  `D4xC2 := D4 × C2` acting on `ClosedTour` (`MulAction D4xC2 ClosedTour`), and
  proved every orbit has cardinality dividing 16 (`fullOrbit_card_dvd_sixteen`).

  What remained implicit there: that this order-16 action *restricts to each
  histogram level set* `levelSet k`. The two pointwise count-invariances were
  already established separately —

    * `oblique_count_invariant`  (board group `D4`, `KnightsTourOblique.lean`),
    * `obliqueCount_reverseTour` (time reversal, `…OQ02ReverseCount.lean`) —

  but they had only been lifted to level sets *one factor at a time*
  (`levelSet_image_applyD4Tour_eq`, `levelSet_image_reverseTour_eq`). This file
  fuses them at the group level.

  ## What this file proves (0 sorries, 0 axioms)

  * `obliqueCount_revBool` / `obliqueCount_smul` — the full order-16 group
    preserves the oblique count: `obliqueCount (g • t) = obliqueCount t`.
  * `full_smul_mem_levelSet` — every group element keeps a tour inside its
    level set.
  * `smul_injective` / `levelSet_image_smul_eq` — each `g : D4xC2` induces a
    *bijection* of `levelSet k` onto itself, the order-16 analogue of the
    single-factor results `levelSet_image_applyD4Tour_eq` and
    `levelSet_image_reverseTour_eq`.
  * `fullOrbit_subset_levelSet` — each order-16 orbit lies inside a *single*
    level set (`fullOrbit t ⊆ levelSet (obliqueCount t)`).

  Together these are exactly the prerequisite that legitimizes decomposing
  `levelSet k` into order-16 orbits: the group acts on the finite set
  `levelSet k`, so `obliqueDistribution k = (levelSet k).card` is a sum of
  orbit sizes, each dividing 16 (`fullOrbit_card_dvd_sixteen`). This is the
  structural foundation for the sole remaining open direction of OQ-02 — a
  mod-16 congruence on `obliqueDistribution k` in terms of the self-symmetric
  tour count.

  Parent: `KnightsTourOblique.lean`.
  Siblings: `…OQ02.lean`, `…OQ02Reverse.lean`, `…OQ02ReverseCount.lean`,
  `…OQ02Order16.lean`.
-/

import Mathlib
import Proofs.KnightsTourObliqueOQ02Order16

namespace KnightsTourOblique

open List

/-! ## The full order-16 group preserves the oblique count -/

/-- Time reversal selected by a `Bool` flag preserves the oblique count. The
    `false` branch is the identity (`rfl`); the `true` branch is
    `obliqueCount_reverseTour`. -/
theorem obliqueCount_revBool (b : Bool) (t : ClosedTour) :
    obliqueCount (revBool b t) = obliqueCount t := by
  cases b with
  | false => rfl
  | true => exact obliqueCount_reverseTour t

/-- **The full order-16 group preserves the oblique count.** For every
    `g : D4xC2` and tour `t`, `obliqueCount (g • t) = obliqueCount t`. This
    fuses the two independent invariances `oblique_count_invariant` (board
    group) and `obliqueCount_reverseTour` (time reversal) into a single
    statement for the combined direct-product action. -/
theorem obliqueCount_smul (g : D4xC2) (t : ClosedTour) :
    obliqueCount (g • t) = obliqueCount t := by
  rw [d4xc2_smul_def, oblique_count_invariant]
  exact obliqueCount_revBool g.2 t

/-! ## The action restricts to each level set -/

/-- Every order-16 group element keeps a tour inside its level set: if
    `t ∈ levelSet k` then `g • t ∈ levelSet k`, by `obliqueCount_smul`. -/
theorem full_smul_mem_levelSet {k : ℕ} {t : ClosedTour} (g : D4xC2)
    (ht : t ∈ levelSet k) : g • t ∈ levelSet k := by
  simp only [levelSet, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
  rw [obliqueCount_smul]
  exact ht

/-- The full group acts on `levelSet k`: its image under `g • ·` is contained
    in `levelSet k`. -/
theorem levelSet_image_smul_subset (g : D4xC2) (k : ℕ) :
    (levelSet k).image (g • ·) ⊆ levelSet k := by
  intro u hu
  simp only [Finset.mem_image] at hu
  obtain ⟨t, ht, rfl⟩ := hu
  exact full_smul_mem_levelSet g ht

/-- Acting by a group element is injective on tours: `g • ·` has left inverse
    `g⁻¹ • ·` via `inv_smul_smul`. -/
theorem smul_injective (g : D4xC2) :
    Function.Injective (g • · : ClosedTour → ClosedTour) := by
  intro a b hab
  have h := congrArg (fun t => g⁻¹ • t) hab
  simpa only [inv_smul_smul] using h

/-- Acting by a group element preserves the cardinality of a level set
    (injectivity of the action). -/
theorem levelSet_image_smul_card (g : D4xC2) (k : ℕ) :
    ((levelSet k).image (g • ·)).card = (levelSet k).card :=
  Finset.card_image_of_injective _ (smul_injective g)

/-- **The order-16 group acts by bijections on each level set.** Every
    `g : D4xC2` induces a bijection of `levelSet k` onto itself. This is the
    order-16 fusion of the single-factor results
    `levelSet_image_applyD4Tour_eq` (board group) and
    `levelSet_image_reverseTour_eq` (time reversal). -/
theorem levelSet_image_smul_eq (g : D4xC2) (k : ℕ) :
    (levelSet k).image (g • ·) = levelSet k := by
  apply Finset.eq_of_subset_of_card_le (levelSet_image_smul_subset g k)
  rw [levelSet_image_smul_card]

/-! ## Each orbit lives in a single level set -/

/-- **Every order-16 orbit lies inside a single level set.** The full symmetry
    orbit of `t` is contained in `levelSet (obliqueCount t)`, since every group
    element preserves the oblique count (`obliqueCount_smul`). Hence the level
    sets are unions of order-16 orbits — combined with
    `fullOrbit_card_dvd_sixteen` this is the structural basis for a mod-16
    congruence on `obliqueDistribution k = (levelSet k).card`. -/
theorem fullOrbit_subset_levelSet (t : ClosedTour) :
    fullOrbit t ⊆ levelSet (obliqueCount t) := by
  intro u hu
  simp only [fullOrbit, Finset.mem_image, Finset.mem_univ, true_and] at hu
  obtain ⟨g, rfl⟩ := hu
  have ht : t ∈ levelSet (obliqueCount t) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ t, rfl⟩
  exact full_smul_mem_levelSet g ht

end KnightsTourOblique
