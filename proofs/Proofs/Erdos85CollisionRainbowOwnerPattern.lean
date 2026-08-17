import Proofs.Erdos85ThreeOrbitColorPacking

/-! # Owner pattern forced by a collision-color rainbow -/

namespace Erdos85

open SimpleGraph

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

/-- Graph interface to the preceding enumeration.  Equal adjacency rows in
three distinct factor colors supply all three owner-pattern equivalences. -/
theorem fourColor_equalRows_triangle_ownerPattern
    {V C : Type*} [Fintype V] [DecidableEq V]
    (O : C → SimpleGraph V) [∀ color, DecidableRel (O color).Adj]
    {a b c : V} {α β γ δ p q r : C}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hαδ : α ≠ δ) (hβδ : β ≠ δ) (hγδ : γ ≠ δ)
    (hall : ∀ x : C, x = α ∨ x = β ∨ x = γ ∨ x = δ)
    (hAB : ∀ color, (O color).Adj a b ↔ color = p)
    (hAC : ∀ color, (O color).Adj a c ↔ color = q)
    (hBC : ∀ color, (O color).Adj b c ↔ color = r)
    (habRows : ∀ z, (O α).adjMatrix ℤ a z = (O α).adjMatrix ℤ b z)
    (hacRows : ∀ z, (O β).adjMatrix ℤ a z = (O β).adjMatrix ℤ c z)
    (hbcRows : ∀ z, (O γ).adjMatrix ℤ b z = (O γ).adjMatrix ℤ c z) :
    (p = δ ∧ q = δ ∧ r = δ) ∨
      (p = δ ∧ q = α ∧ r = α) ∨
      (p = β ∧ q = δ ∧ r = β) ∨
      (p = γ ∧ q = γ ∧ r = δ) := by
  have rowAdj (color : C) {x y : V}
      (hrows : ∀ z, (O color).adjMatrix ℤ x z =
        (O color).adjMatrix ℤ y z) (z : V) :
      (O color).Adj x z ↔ (O color).Adj y z := by
    have h := hrows z
    simp only [SimpleGraph.adjMatrix_apply] at h
    by_cases hxz : (O color).Adj x z <;>
      by_cases hyz : (O color).Adj y z <;> simp_all
  have hpα : p ≠ α := by
    intro hp
    have hab : (O α).Adj a b := (hAB α).mpr hp.symm
    exact (O α).loopless.irrefl b ((rowAdj α habRows b).mp hab)
  have hqβ : q ≠ β := by
    intro hq
    have hac : (O β).Adj a c := (hAC β).mpr hq.symm
    exact (O β).loopless.irrefl c ((rowAdj β hacRows c).mp hac)
  have hrγ : r ≠ γ := by
    intro hr
    have hbc : (O γ).Adj b c := (hBC γ).mpr hr.symm
    exact (O γ).loopless.irrefl c ((rowAdj γ hbcRows c).mp hbc)
  have hα : q = α ↔ r = α := by
    constructor
    · intro hq
      have hac : (O α).Adj a c := (hAC α).mpr hq.symm
      exact ((hBC α).mp ((rowAdj α habRows c).mp hac)).symm
    · intro hr
      have hbc : (O α).Adj b c := (hBC α).mpr hr.symm
      exact ((hAC α).mp ((rowAdj α habRows c).mpr hbc)).symm
  have hβ : p = β ↔ r = β := by
    constructor
    · intro hp
      have hab : (O β).Adj a b := (hAB β).mpr hp.symm
      exact ((hBC β).mp ((rowAdj β hacRows b).mp hab |>.symm)).symm
    · intro hr
      have hbc : (O β).Adj b c := (hBC β).mpr hr.symm
      have hab : (O β).Adj a b :=
        (rowAdj β hacRows b).mpr hbc.symm
      exact ((hAB β).mp hab).symm
  have hγ : p = γ ↔ q = γ := by
    constructor
    · intro hp
      have hab : (O γ).Adj a b := (hAB γ).mpr hp.symm
      have hac : (O γ).Adj a c :=
        ((rowAdj γ hbcRows a).mp hab.symm).symm
      exact ((hAC γ).mp hac).symm
    · intro hq
      have hac : (O γ).Adj a c := (hAC γ).mpr hq.symm
      have hab : (O γ).Adj a b :=
        ((rowAdj γ hbcRows a).mpr hac.symm).symm
      exact ((hAB γ).mp hab).symm
  exact fourColor_collisionRainbow_ownerPattern α β γ δ p q r
    hαβ hαγ hβγ hαδ hβδ hγδ hall hpα hqβ hrγ hα hβ hγ

end Erdos85
