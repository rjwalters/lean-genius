import Proofs.Erdos85C4FreeTrianglePartnerInvolution
import Proofs.Erdos85PrescribedPairInvolution
import Proofs.Erdos85EvenFinsetInvolutionPairing

/-!
# Assembly of canonical and broken-fiber pairings

The local Baer mate is canonical on the triangle-partner domain and chosen
separately on the disjoint broken-edge domain.  This file combines two such
partial involutions into the single total mate expected by the relay graph.
-/

namespace Erdos85

noncomputable section

/-- Use `leftMate` on the left fiber and `rightMate` everywhere else. -/
def disjointFiberMate {V : Type*} (left : V → Prop)
    (leftMate rightMate : V → V) (v : V) : V :=
  by
    classical
    exact if left v then leftMate v else rightMate v

/-- Two disjoint fixed-point-free involutions assemble to one on their union. -/
theorem disjointFiberMate_properties
    {V : Type*} (left right : V → Prop) (leftMate rightMate : V → V)
    (hdisjoint : ∀ v, left v → ¬ right v)
    (hleftClosed : ∀ v, left v → left (leftMate v))
    (hleftInvol : ∀ v, left v → leftMate (leftMate v) = v)
    (hleftFixed : ∀ v, left v → leftMate v ≠ v)
    (hrightClosed : ∀ v, right v → right (rightMate v))
    (hrightInvol : ∀ v, right v → rightMate (rightMate v) = v)
    (hrightFixed : ∀ v, right v → rightMate v ≠ v) :
    (∀ v, left v ∨ right v →
      left (disjointFiberMate left leftMate rightMate v) ∨
        right (disjointFiberMate left leftMate rightMate v)) ∧
    (∀ v, left v ∨ right v →
      disjointFiberMate left leftMate rightMate
        (disjointFiberMate left leftMate rightMate v) = v) ∧
    (∀ v, left v ∨ right v →
      disjointFiberMate left leftMate rightMate v ≠ v) := by
  have hrightNotLeft : ∀ v, right v → ¬ left v := by
    intro v hright hleft
    exact hdisjoint v hleft hright
  constructor
  · intro v hv
    by_cases hl : left v
    · left
      simpa [disjointFiberMate, hl] using hleftClosed v hl
    · right
      have hr : right v := hv.resolve_left hl
      simpa [disjointFiberMate, hl] using hrightClosed v hr
  constructor
  · intro v hv
    by_cases hl : left v
    · have hl' : left (leftMate v) := hleftClosed v hl
      simp [disjointFiberMate, hl, hl', hleftInvol v hl]
    · have hr : right v := hv.resolve_left hl
      have hr' : right (rightMate v) := hrightClosed v hr
      have hl' : ¬ left (rightMate v) := hrightNotLeft _ hr'
      simp [disjointFiberMate, hl, hl', hrightInvol v hr]
  · intro v hv
    by_cases hl : left v
    · simpa [disjointFiberMate, hl] using hleftFixed v hl
    · have hr : right v := hv.resolve_left hl
      simpa [disjointFiberMate, hl] using hrightFixed v hr

/-- Complete the canonical triangle-partner involution by arbitrarily pairing
the even broken-edge fiber at every witness.  The resulting local mates pair
the entire neighbor star and retain the canonical mate wherever it exists. -/
theorem exists_baerCompletedMate_of_even_brokenFibers
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (heven : ∀ p, Even ((Finset.univ.filter fun x =>
      (triangleFreeEdgeGraph G).Adj p x).card)) :
    ∃ mate : V → V → V,
      (∀ p x, G.Adj p x → G.Adj p (mate p x)) ∧
      (∀ p x, G.Adj p x → mate p (mate p x) = x) ∧
      (∀ p x, G.Adj p x → mate p x ≠ x) ∧
      (∀ p x, trianglePartnerEligible G p x →
        mate p x = trianglePartner G p x) := by
  obtain ⟨brokenMate, hbrokenClosed, hbrokenInvol, hbrokenFixed, _⟩ :=
    exists_witnessMate_of_even_fibers
      (fun p x => (triangleFreeEdgeGraph G).Adj p x) heven
  let mate : V → V → V := fun p =>
    disjointFiberMate (trianglePartnerEligible G p)
      (trianglePartner G p) (brokenMate p)
  have hcover : ∀ p x, G.Adj p x →
      trianglePartnerEligible G p x ∨
        (triangleFreeEdgeGraph G).Adj p x := by
    intro p x hpx
    by_cases helig : trianglePartnerEligible G p x
    · exact Or.inl helig
    · right
      by_contra hbroken
      exact helig ((trianglePartnerEligible_iff_not_triangleFreeEdge G p x).2
        ⟨hpx, hbroken⟩)
  have hprops : ∀ p,
      (∀ x, trianglePartnerEligible G p x ∨
          (triangleFreeEdgeGraph G).Adj p x →
        trianglePartnerEligible G p (mate p x) ∨
          (triangleFreeEdgeGraph G).Adj p (mate p x)) ∧
      (∀ x, trianglePartnerEligible G p x ∨
          (triangleFreeEdgeGraph G).Adj p x → mate p (mate p x) = x) ∧
      (∀ x, trianglePartnerEligible G p x ∨
          (triangleFreeEdgeGraph G).Adj p x → mate p x ≠ x) := by
    intro p
    apply disjointFiberMate_properties
    · intro x helig
      exact ((trianglePartnerEligible_iff_not_triangleFreeEdge G p x).1 helig).2
    · exact fun x hx => trianglePartner_closed hx
    · exact fun x hx => trianglePartner_involutive hfree hx
    · exact fun x hx => trianglePartner_fixedPointFree hx
    · exact hbrokenClosed p
    · exact hbrokenInvol p
    · exact hbrokenFixed p
  refine ⟨mate, ?_, ?_, ?_, ?_⟩
  · intro p x hpx
    rcases (hprops p).1 x (hcover p x hpx) with helig | hbroken
    · exact ((trianglePartnerEligible_iff_not_triangleFreeEdge G p (mate p x)).1
        helig).1
    · exact ((mem_triangleFreeNeighbors G p (mate p x)).mp
        ((triangleFreeEdgeGraph_adj G p (mate p x)).mp hbroken)).1
  · intro p x hpx
    exact (hprops p).2.1 x (hcover p x hpx)
  · intro p x hpx
    exact (hprops p).2.2 x (hcover p x hpx)
  · intro p x helig
    simp [mate, disjointFiberMate, helig]

end

end Erdos85

#print axioms Erdos85.disjointFiberMate_properties
#print axioms Erdos85.exists_baerCompletedMate_of_even_brokenFibers
