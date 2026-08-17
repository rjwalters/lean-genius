import Proofs.Erdos85ThreeOrbitColorPacking

/-! # Owner pattern forced by a collision-color rainbow -/

namespace Erdos85

/-- If the three edges of a triangle have pairwise distinct row-collision
colors, equality of the collided rows forces the actual edge-owner pattern to
be monochromatic in the fourth color or `2+1`, with the doubled owner equal
to the collision color on the opposite edge. -/
theorem fourColor_collisionRainbow_ownerPattern
    {C : Type*}
    (α β γ δ p q r : C)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hαδ : α ≠ δ) (hβδ : β ≠ δ) (hγδ : γ ≠ δ)
    (hall : ∀ x : C, x = α ∨ x = β ∨ x = γ ∨ x = δ)
    (hpα : p ≠ α) (hqβ : q ≠ β) (hrγ : r ≠ γ)
    (hα : q = α ↔ r = α)
    (hβ : p = β ↔ r = β)
    (hγ : p = γ ↔ q = γ) :
    (p = δ ∧ q = δ ∧ r = δ) ∨
      (p = δ ∧ q = α ∧ r = α) ∨
      (p = β ∧ q = δ ∧ r = β) ∨
      (p = γ ∧ q = γ ∧ r = δ) := by
  rcases hall p with hp | hp | hp | hp <;>
    rcases hall q with hq | hq | hq | hq <;>
    rcases hall r with hr | hr | hr | hr <;>
    simp_all

end Erdos85
