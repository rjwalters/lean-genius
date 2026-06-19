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
with a small, purely mechanical **type/predicate bridge**: a lemma relating
`Collinear ℝ {a,b,c}` to `SylvesterGallai.Collinear (φ a) (φ b) (φ c)`, the
injectivity of `φ`, and the not-all-collinear / cardinality transport. The hard
mathematics is done; what remains is bookkeeping along an isomorphism.

### The four bridge lemmas (all discharged below, 0 sorries)

* `phi_injective` — `φ` is injective (a point of the plane is determined by its two
  coordinates). `PiLp.ext` + `Fin.forall_fin_two`.
* `three_le_card_of_not_collinear` — a non-collinear finite set has ≥ 3 points
  (any set of ≤ 2 points is collinear: `collinear_empty` / `collinear_singleton` /
  `collinear_pair`).
* `collinear_iff_sg` — for `a ≠ b`, Mathlib `Collinear ℝ {a,b,c}` is equivalent to
  the cross-product predicate `SylvesterGallai.Collinear (φ a) (φ b) (φ c)`.
  (`collinear_iff_of_mem` unfolds Mathlib collinearity to `∃ r, p = r • v +ᵥ p₀`;
  reading off the two `Fin 2` coordinates gives exactly the cross-product form.)
* `not_allCollinear_image` — `¬ Collinear ℝ ↑S` transports to
  `¬ SylvesterGallai.AllCollinear (S.image φ)`.

**Key subtlety** (documented in-file): the custom predicate matches Mathlib's
`Collinear ℝ {a,b,c}` only when `a ≠ b`, so `collinear_iff_sg` carries that
hypothesis (always available in the ordinary-line context). Only the *forward*
map `φ` is needed — no inverse — sidestepping `PiLp`/`EuclideanSpace` element
construction.

**Status.** `verified` — the geometric content lives in the verified
`Erdos606OQ03OQ03`; this file closes the four bridge lemmas with 0 sorries and
0 nonstandard axioms, yielding the theorem in the canonical Mathlib formulation.
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
  intro x y h
  simp only [φ, Prod.mk.injEq] at h
  apply PiLp.ext
  rw [Fin.forall_fin_two]
  exact h

/-- A finite non-collinear point set has at least three points. -/
theorem three_le_card_of_not_collinear (S : Finset E)
    (hS : ¬ Collinear ℝ (↑S : Set E)) : 3 ≤ S.card := by
  by_contra h
  push_neg at h
  apply hS
  rcases (by omega : S.card = 0 ∨ S.card = 1 ∨ S.card = 2) with h0 | h1 | h2
  · rw [Finset.card_eq_zero] at h0
    subst h0
    rw [Finset.coe_empty]
    exact collinear_empty ℝ E
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
    subst hx
    rw [Finset.coe_singleton]
    exact collinear_singleton ℝ x
  · obtain ⟨x, y, hxy, hS2⟩ := Finset.card_eq_two.mp h2
    subst hS2
    rw [Finset.coe_insert, Finset.coe_singleton]
    exact collinear_pair ℝ x y

/-- **Helper.** The cross-product collinearity `SylvesterGallai.Collinear (φa)(φb)(φc)`
exhibits `c` as an affine combination `c = t • (b - a) +ᵥ a` on the line through
`a, b`. This is the algebraic core of the predicate bridge. -/
private theorem sg_to_smul {a b c : E}
    (h : SylvesterGallai.Collinear (φ a) (φ b) (φ c)) :
    ∃ t : ℝ, c = t • (b - a) +ᵥ a := by
  obtain ⟨t, ht0, ht1⟩ := h
  -- `φ _` projections are definitionally the coordinates; rewrite ht0/ht1 to that form.
  change c 0 - a 0 = t * (b 0 - a 0) at ht0
  change c 1 - a 1 = t * (b 1 - a 1) at ht1
  refine ⟨t, ?_⟩
  rw [vadd_eq_add]
  apply PiLp.ext
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    linarith
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    linarith

/-- **Predicate bridge.** For distinct `a b`, Mathlib collinearity of `{a,b,c}`
agrees with the cross-product collinearity of `Proofs/Erdos606OQ03OQ03.lean`
under the coordinate map `φ`. -/
theorem collinear_iff_sg (a b c : E) (hab : a ≠ b) :
    Collinear ℝ ({a, b, c} : Set E) ↔
      SylvesterGallai.Collinear (φ a) (φ b) (φ c) := by
  constructor
  · -- Mathlib collinearity → cross-product predicate
    intro hcol
    rw [collinear_iff_of_mem (Set.mem_insert a _)] at hcol
    obtain ⟨v, hv⟩ := hcol
    obtain ⟨rb, hb⟩ := hv b (by simp)
    obtain ⟨rc, hc⟩ := hv c (by simp)
    rw [vadd_eq_add] at hb hc
    have hbv : b - a = rb • v := by rw [hb]; abel
    have hcv : c - a = rc • v := by rw [hc]; abel
    have hrb : rb ≠ 0 := by
      intro h0
      apply hab
      rw [h0, zero_smul, sub_eq_zero] at hbv
      exact hbv.symm
    have key : c - a = (rc * rb⁻¹) • (b - a) := by
      rw [hcv, hbv, smul_smul, mul_assoc, inv_mul_cancel₀ hrb, mul_one]
    refine ⟨rc * rb⁻¹, ?_, ?_⟩
    · show c 0 - a 0 = (rc * rb⁻¹) * (b 0 - a 0)
      have h0 := congrArg (fun w => w 0) key
      simpa using h0
    · show c 1 - a 1 = (rc * rb⁻¹) * (b 1 - a 1)
      have h1 := congrArg (fun w => w 1) key
      simpa using h1
  · -- cross-product predicate → Mathlib collinearity
    intro hsg
    obtain ⟨t, hc⟩ := sg_to_smul hsg
    rw [collinear_iff_of_mem (Set.mem_insert a _)]
    refine ⟨b - a, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by rw [zero_smul, vadd_eq_add]; abel⟩
    · exact ⟨1, by rw [one_smul, vadd_eq_add]; abel⟩
    · exact ⟨t, hc⟩

/-- **Hypothesis transport.** A non-collinear set maps to a not-all-collinear image. -/
theorem not_allCollinear_image (S : Finset E)
    (hS : ¬ Collinear ℝ (↑S : Set E)) :
    ¬ SylvesterGallai.AllCollinear (S.image φ) := by
  intro hAC
  apply hS
  obtain ⟨A, hA, B, hB, hAB, hall⟩ := hAC
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hB
  rw [collinear_iff_of_mem (Finset.mem_coe.mpr ha)]
  refine ⟨b - a, ?_⟩
  intro p hp
  rw [Finset.mem_coe] at hp
  have hsg : SylvesterGallai.Collinear (φ a) (φ b) (φ p) :=
    hall (φ p) (Finset.mem_image_of_mem φ hp)
  exact sg_to_smul hsg

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
    have h3 := three_le_card_of_not_collinear S hS
    calc 3 ≤ S.card := h3
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
