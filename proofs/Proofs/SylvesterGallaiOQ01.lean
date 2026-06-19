import Mathlib
import Proofs.Erdos606OQ03OQ03

/-!
# Sylvester–Gallai theorem (sylvester-gallai-theorem-oq-01)

**Statement.** Every finite set of points in the Euclidean plane that is *not* all
collinear determines an *ordinary line* — a line passing through exactly two of the
points.

## Strategy — REDUCTION to the already-verified gallery proof

A complete, machine-checked proof of Sylvester–Gallai by Kelly's 1948 metric
argument **already exists in this gallery**: `Proofs/Erdos606OQ03OQ03.lean`,
namespace `SylvesterGallai`, theorem `SylvesterGallai.sylvester_gallai`
(508 lines, 0 sorries, 0 axioms, registered in `Proofs.lean`). That proof is
stated over the *concrete coordinate plane* `Point := ℝ × ℝ` with a custom
cross-product collinearity predicate

  `SylvesterGallai.Collinear a b c := ∃ t, c.1-a.1 = t*(b.1-a.1) ∧ c.2-a.2 = t*(b.2-a.2)`.

This file restates the theorem in the **canonical Mathlib formulation** —
`EuclideanSpace ℝ (Fin 2)` with `Collinear ℝ` — and obtains it as a corollary of
the verified proof, transporting along the coordinate isomorphism

  `φ : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ,  φ x := (x 0, x 1)`.

This replaces re-proving Kelly's delicate 6-case geometric kernel (~500–900 lines)
with a small, purely mechanical **type/predicate bridge**: three lemmas relating
`Collinear ℝ {a,b,c}` to `SylvesterGallai.Collinear (φ a) (φ b) (φ c)`, the
injectivity of `φ`, and the not-all-collinear / cardinality transport. The hard
mathematics is done; what remains is bookkeeping along an isomorphism.

### Remaining obligations (the four `sorry`s below)

* `phi_injective` — `φ` is injective (a point of the plane is determined by its two
  coordinates). Routine `funext`/`Fin`-case.
* `three_le_card_of_not_collinear` — a non-collinear finite set has ≥ 3 points
  (any set of ≤ 2 points is collinear: `Set.Subsingleton.collinear` / `collinear_pair`).
* `collinear_iff_sg` — for `a ≠ b`, Mathlib `Collinear ℝ {a,b,c}` is equivalent to
  the cross-product predicate `SylvesterGallai.Collinear (φ a) (φ b) (φ c)`.
  (`collinear_iff_of_mem` unfolds Mathlib collinearity to `∃ r, c = r • (b - a) + a`;
  reading off the two `Fin 2` coordinates gives exactly the cross-product form.)
* `not_allCollinear_image` — `¬ Collinear ℝ ↑S` transports to
  `¬ SylvesterGallai.AllCollinear (S.image φ)` (contrapositive of `collinear_iff_sg`
  plus `φ` injective on `S`).

These four are independent, statement-fixed, and good **Aristotle** targets.

**Status.** `formalized` — the main theorem is reduced to the four bridge lemmas
above; no open *geometric* content remains. Build-pending (host saturated at
authoring time; standalone + unregistered keeps it fleet-safe).
-/

namespace SylvesterGallaiOQ01

open SylvesterGallai (Point)

/-- The Euclidean plane `ℝ²` in its canonical Mathlib form. -/
abbrev E := EuclideanSpace ℝ (Fin 2)

/-- Coordinate isomorphism to the concrete plane `ℝ × ℝ` used by the verified
gallery proof `Proofs/Erdos606OQ03OQ03.lean`. -/
noncomputable def φ (x : E) : ℝ × ℝ := (x 0, x 1)

/-- A pair `(a, b)` of points of `S` spans an **ordinary line**: every point of `S`
collinear with `a` and `b` is already one of `a`, `b`. -/
def IsOrdinary (S : Finset E) (a b : E) : Prop :=
  ∀ c ∈ S, Collinear ℝ ({a, b, c} : Set E) → c = a ∨ c = b

-- ============================================================
-- Bridge lemmas (the only remaining obligations — all mechanical)
-- ============================================================

/-- `φ` is injective: a planar point is determined by its two coordinates. -/
theorem phi_injective : Function.Injective φ := by
  sorry

/-- A finite non-collinear point set has at least three points. -/
theorem three_le_card_of_not_collinear (S : Finset E)
    (hS : ¬ Collinear ℝ (↑S : Set E)) : 3 ≤ S.card := by
  sorry

/-- **Predicate bridge.** For distinct `a b`, Mathlib collinearity of `{a,b,c}`
agrees with the cross-product collinearity of `Proofs/Erdos606OQ03OQ03.lean`
under the coordinate map `φ`. -/
theorem collinear_iff_sg (a b c : E) (hab : a ≠ b) :
    Collinear ℝ ({a, b, c} : Set E) ↔
      SylvesterGallai.Collinear (φ a) (φ b) (φ c) := by
  sorry

/-- **Hypothesis transport.** A non-collinear set maps to a not-all-collinear image. -/
theorem not_allCollinear_image (S : Finset E)
    (hS : ¬ Collinear ℝ (↑S : Set E)) :
    ¬ SylvesterGallai.AllCollinear (S.image φ) := by
  sorry

-- ============================================================
-- Main theorem — reduction to the verified proof
-- ============================================================

/-- **Sylvester–Gallai theorem** (canonical Mathlib formulation). Every finite
non-collinear set of points in the Euclidean plane determines an ordinary line.

Proof: transport `S` to `S.image φ ⊆ ℝ × ℝ`, invoke the verified
`SylvesterGallai.sylvester_gallai`, and pull the ordinary line back along the
injective coordinate map `φ`. -/
theorem sylvester_gallai (S : Finset E)
    (hS : ¬ Collinear ℝ (↑S : Set E)) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ IsOrdinary S a b := by
  classical
  -- Transport the hypotheses to the concrete plane.
  have hcard : 3 ≤ (S.image φ).card := by
    have := three_le_card_of_not_collinear S hS
    calc 3 ≤ S.card := this
      _ = (S.image φ).card := (Finset.card_image_of_injective S phi_injective).symm
  have hnot := not_allCollinear_image S hS
  -- Invoke the verified Kelly proof over ℝ × ℝ.
  obtain ⟨A, B, hAmem, hBmem, hAB, hord⟩ :=
    SylvesterGallai.sylvester_gallai (S.image φ) hcard hnot
  -- Pull the witnesses back along φ.
  obtain ⟨a, haS, rfl⟩ := Finset.mem_image.mp hAmem
  obtain ⟨b, hbS, rfl⟩ := Finset.mem_image.mp hBmem
  have hab : a ≠ b := fun h => hAB (by rw [h])
  refine ⟨a, haS, b, hbS, hab, ?_⟩
  intro c hcS hcol
  -- Carry collinearity across the bridge and apply ordinariness of (φ a, φ b).
  have hsg : SylvesterGallai.Collinear (φ a) (φ b) (φ c) :=
    (collinear_iff_sg a b c hab).mp hcol
  rcases hord (φ c) (Finset.mem_image_of_mem φ hcS) hsg with h | h
  · exact Or.inl (phi_injective h)
  · exact Or.inr (phi_injective h)

end SylvesterGallaiOQ01
