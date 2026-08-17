import Mathlib

/-! # Complements of three balanced bipartite factors -/

namespace Erdos85

/-- The neighbors of a left vertex in a finite bipartite edge set. -/
def bipartiteFstFiber
    {A B : Type*} [Fintype B] [DecidableEq A] [DecidableEq B]
    (S : Finset (A × B)) (a : A) : Finset B :=
  (Finset.univ : Finset B).filter fun b => (a, b) ∈ S

/-- The neighbors of a right vertex in a finite bipartite edge set. -/
def bipartiteSndFiber
    {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
    (S : Finset (A × B)) (b : B) : Finset A :=
  (Finset.univ : Finset A).filter fun a => (a, b) ∈ S

private theorem bipartiteFstFiber_disjoint
    {A B : Type*} [Fintype B] [DecidableEq A] [DecidableEq B]
    {S T : Finset (A × B)} (hST : Disjoint S T) (a : A) :
    Disjoint (bipartiteFstFiber S a) (bipartiteFstFiber T a) := by
  rw [Finset.disjoint_left] at hST ⊢
  intro b hbS hbT
  exact hST (by simpa [bipartiteFstFiber] using hbS)
    (by simpa [bipartiteFstFiber] using hbT)

private theorem bipartiteSndFiber_disjoint
    {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
    {S T : Finset (A × B)} (hST : Disjoint S T) (b : B) :
    Disjoint (bipartiteSndFiber S b) (bipartiteSndFiber T b) := by
  rw [Finset.disjoint_left] at hST ⊢
  intro a haS haT
  exact hST (by simpa [bipartiteSndFiber] using haS)
    (by simpa [bipartiteSndFiber] using haT)

/-- Three pairwise edge-disjoint left-degree-two factors on an `8 × 8`
grid leave a left-degree-two complement. -/
theorem three_bipartite_degreeTwo_factors_complement_fstFiber_card_eq_two
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (hB : Fintype.card B = 8)
    (S T U : Finset (A × B))
    (hST : Disjoint S T) (hSU : Disjoint S U) (hTU : Disjoint T U)
    (hS : ∀ a, (bipartiteFstFiber S a).card = 2)
    (hT : ∀ a, (bipartiteFstFiber T a).card = 2)
    (hU : ∀ a, (bipartiteFstFiber U a).card = 2)
    (a : A) :
    (bipartiteFstFiber
      ((Finset.univ : Finset A) ×ˢ (Finset.univ : Finset B) \
        ((S ∪ T) ∪ U)) a).card = 2 := by
  classical
  have hSTa := bipartiteFstFiber_disjoint hST a
  have hSUa := bipartiteFstFiber_disjoint hSU a
  have hTUa := bipartiteFstFiber_disjoint hTU a
  have hUTa : Disjoint
      (bipartiteFstFiber S a ∪ bipartiteFstFiber T a)
      (bipartiteFstFiber U a) :=
    Finset.disjoint_union_left.mpr ⟨hSUa, hTUa⟩
  have hUnion :
      bipartiteFstFiber ((S ∪ T) ∪ U) a =
        (bipartiteFstFiber S a ∪ bipartiteFstFiber T a) ∪
          bipartiteFstFiber U a := by
    ext b
    simp [bipartiteFstFiber]
  have hUnionCard : (bipartiteFstFiber ((S ∪ T) ∪ U) a).card = 6 := by
    rw [hUnion, Finset.card_union_of_disjoint hUTa,
      Finset.card_union_of_disjoint hSTa, hS a, hT a, hU a]
  have hComplement :
      bipartiteFstFiber
        ((Finset.univ : Finset A) ×ˢ (Finset.univ : Finset B) \
          ((S ∪ T) ∪ U)) a =
        (Finset.univ : Finset B) \
          bipartiteFstFiber ((S ∪ T) ∪ U) a := by
    ext b
    simp [bipartiteFstFiber]
  rw [hComplement, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, hB, hUnionCard]

/-- Three pairwise edge-disjoint right-degree-two factors on an `8 × 8`
grid leave a right-degree-two complement. -/
theorem three_bipartite_degreeTwo_factors_complement_sndFiber_card_eq_two
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (hA : Fintype.card A = 8)
    (S T U : Finset (A × B))
    (hST : Disjoint S T) (hSU : Disjoint S U) (hTU : Disjoint T U)
    (hS : ∀ b, (bipartiteSndFiber S b).card = 2)
    (hT : ∀ b, (bipartiteSndFiber T b).card = 2)
    (hU : ∀ b, (bipartiteSndFiber U b).card = 2)
    (b : B) :
    (bipartiteSndFiber
      ((Finset.univ : Finset A) ×ˢ (Finset.univ : Finset B) \
        ((S ∪ T) ∪ U)) b).card = 2 := by
  classical
  have hSTb := bipartiteSndFiber_disjoint hST b
  have hSUb := bipartiteSndFiber_disjoint hSU b
  have hTUb := bipartiteSndFiber_disjoint hTU b
  have hUTb : Disjoint
      (bipartiteSndFiber S b ∪ bipartiteSndFiber T b)
      (bipartiteSndFiber U b) :=
    Finset.disjoint_union_left.mpr ⟨hSUb, hTUb⟩
  have hUnion :
      bipartiteSndFiber ((S ∪ T) ∪ U) b =
        (bipartiteSndFiber S b ∪ bipartiteSndFiber T b) ∪
          bipartiteSndFiber U b := by
    ext a
    simp [bipartiteSndFiber]
  have hUnionCard : (bipartiteSndFiber ((S ∪ T) ∪ U) b).card = 6 := by
    rw [hUnion, Finset.card_union_of_disjoint hUTb,
      Finset.card_union_of_disjoint hSTb, hS b, hT b, hU b]
  have hComplement :
      bipartiteSndFiber
        ((Finset.univ : Finset A) ×ˢ (Finset.univ : Finset B) \
          ((S ∪ T) ∪ U)) b =
        (Finset.univ : Finset A) \
          bipartiteSndFiber ((S ∪ T) ∪ U) b := by
    ext a
    simp [bipartiteSndFiber]
  rw [hComplement, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, hA, hUnionCard]

end Erdos85
