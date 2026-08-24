import Proofs.Erdos85ThreeSeparatorUniformYWingFiberSizes

/-!
# The complementary P-fiber injects into its K-wing

Each ordinary point of the complementary P-fiber has a second K-neighbor
in the complementary K-wing.  Two distinct points cannot have the same
second center: that center and the fixed P-center would then have two
common A-neighbors.  This C4-free injection, composed with B44, gives the
uniform lower bound `b-2 ≤ |K_w|` in (B45).
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- C4-free injectivity of the second-center map. -/
theorem commonNeighbor_secondCenter_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (G K : Finset V) (p : V) (φ : V → V)
    (hφK : ∀ y ∈ G, φ y ∈ K)
    (hpφ : ∀ y ∈ G, p ≠ φ y)
    (hpy : ∀ y ∈ G, A.Adj p y)
    (hφy : ∀ y ∈ G, A.Adj (φ y) y) :
    G.card ≤ K.card := by
  apply Finset.card_le_card_of_injOn φ
  · intro y hy
    exact hφK y hy
  · intro y hy y' hy' hφeq
    have hφy'common : A.Adj (φ y) y' := by
      rw [hφeq]
      exact hφy y' hy'
    exact commonNeighbor_unique_of_c4Free hfree (hpφ y hy)
      (hpy y hy) (hφy y hy)
      (hpy y' hy') hφy'common

/-- B45: the ordinary complementary P-fiber injects into `K_w`, so the
wing contains at least `b-2` K-centers. -/
theorem complementary_Pfiber_injection_forces_Kwing_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (G H K : Finset V) (p : V) (φ : V → V) (b : ℕ)
    (hordinary : b - 2 ≤ (G \ H).card)
    (hφK : ∀ y ∈ G \ H, φ y ∈ K)
    (hpφ : ∀ y ∈ G \ H, p ≠ φ y)
    (hpy : ∀ y ∈ G \ H, A.Adj p y)
    (hφy : ∀ y ∈ G \ H, A.Adj (φ y) y) :
    b - 2 ≤ K.card := by
  have hcard := commonNeighbor_secondCenter_card_le
    A hfree (G \ H) K p φ hφK hpφ hpy hφy
  omega

/-- Full B44-to-B45 composition from a `(b-1)`-point fiber and an
at-most-one exceptional subset. -/
theorem c4Free_complementary_Pfiber_Kwing_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (G H K : Finset V) (p : V) (φ : V → V) (b : ℕ)
    (hHG : H ⊆ G)
    (hGcard : G.card = b - 1)
    (hHcard : H.card ≤ 1)
    (hφK : ∀ y ∈ G \ H, φ y ∈ K)
    (hpφ : ∀ y ∈ G \ H, p ≠ φ y)
    (hpy : ∀ y ∈ G \ H, A.Adj p y)
    (hφy : ∀ y ∈ G \ H, A.Adj (φ y) y) :
    b - 2 ≤ K.card := by
  have hordinary := complementary_Pfiber_ordinary_card_ge_b_sub_two
    G H b hHG hGcard hHcard
  exact complementary_Pfiber_injection_forces_Kwing_lower
    A hfree G H K p φ b hordinary hφK hpφ hpy hφy

end


end Erdos85

#print axioms Erdos85.commonNeighbor_secondCenter_card_le
#print axioms Erdos85.complementary_Pfiber_injection_forces_Kwing_lower
#print axioms Erdos85.c4Free_complementary_Pfiber_Kwing_lower
