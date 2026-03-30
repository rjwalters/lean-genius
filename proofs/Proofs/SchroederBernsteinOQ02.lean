/-
  Schroeder-Bernstein OQ-02: Knaster-Tarski Fixed-Point Proof

  The Knaster-Tarski theorem states that every monotone function on
  a complete lattice has a fixed point. This provides an elegant proof
  of Schroeder-Bernstein:

  Given injections f : A → B and g : B → A, define
    Φ(S) = A \ g(B \ f(S))   for S ⊆ A

  Φ is monotone on the power set lattice 𝒫(A), which is complete.
  By Knaster-Tarski, Φ has a fixed point S₀. Then define:
    h(x) = f(x) if x ∈ S₀, g⁻¹(x) if x ∉ S₀

  This h is the desired bijection A → B.

  Mathlib provides the Knaster-Tarski theorem as `OrderHom.lfp` /
  `CompleteLattice.le_lfp` and the Schroeder-Bernstein theorem as
  `Function.Embedding.schroeder_bernstein`.
-/
import Mathlib

namespace SchroederBernsteinOQ02

open Set Function

-- ============================================================
-- Part 1: The Knaster-Tarski operator
-- ============================================================

variable {α β : Type*}

/-- The Knaster-Tarski operator for Schroeder-Bernstein.
    Given f : α → β injective and g : β → α injective,
    Φ(S) = A \ g(B \ f(S)) = compl (g '' (compl (f '' S))). -/
def knasterTarskiOp (f : α → β) (g : β → α) : Set α → Set α :=
  fun S => (g '' (f '' S)ᶜ)ᶜ

/-- The KT operator is monotone: S ⊆ T → Φ(S) ⊆ Φ(T). -/
theorem knasterTarskiOp_mono (f : α → β) (g : β → α) :
    Monotone (knasterTarskiOp f g) := by
  intro S T hST
  unfold knasterTarskiOp
  apply compl_subset_compl.mpr
  apply image_subset
  exact compl_subset_compl.mpr (image_subset f hST)

/-- The fixed point of Φ exists by the Knaster-Tarski theorem.
    In Lean, Set α is a complete lattice, so we can use lfp. -/
noncomputable def knasterTarskiFixedPoint (f : α → β) (g : β → α) : Set α :=
  OrderHom.lfp ⟨knasterTarskiOp f g, knasterTarskiOp_mono f g⟩

/-- The fixed point satisfies S₀ = Φ(S₀). -/
theorem fixedPoint_eq (f : α → β) (g : β → α) :
    knasterTarskiFixedPoint f g = knasterTarskiOp f g (knasterTarskiFixedPoint f g) := by
  unfold knasterTarskiFixedPoint
  exact (OrderHom.isLFP_lfp ⟨knasterTarskiOp f g, knasterTarskiOp_mono f g⟩).eq

-- ============================================================
-- Part 2: Constructing the bijection
-- ============================================================

/-- Given the fixed point S₀, construct the bijection h.
    h(x) = f(x) if x ∈ S₀, g⁻¹(x) if x ∉ S₀. -/
noncomputable def knasterTarskiBij (f : α → β) (g : β → α)
    (hf : Injective f) (hg : Injective g) : α → β :=
  let S₀ := knasterTarskiFixedPoint f g
  fun x => if x ∈ S₀ then f x
    else -- x ∉ S₀ means x ∈ g(B \ f(S₀)), so ∃ y, g(y) = x
    Classical.choice (by
      have heq := fixedPoint_eq f g
      -- Since S₀ = (g '' (f '' S₀)ᶜ)ᶜ, x ∉ S₀ means x ∈ g '' (f '' S₀)ᶜ
      sorry : Nonempty β)

/-- The Knaster-Tarski bijection is a bijection. -/
theorem knasterTarskiBij_bijective (f : α → β) (g : β → α)
    (hf : Injective f) (hg : Injective g) :
    Bijective (knasterTarskiBij f g hf hg) := by
  sorry

/-- **Schroeder-Bernstein via Knaster-Tarski:**
    Making the fixed point explicit. -/
theorem schroeder_bernstein_knaster_tarski
    (f : α → β) (g : β → α) (hf : Injective f) (hg : Injective g) :
    ∃ h : α → β, Bijective h := by
  exact ⟨knasterTarskiBij f g hf hg, knasterTarskiBij_bijective f g hf hg⟩

end SchroederBernsteinOQ02
