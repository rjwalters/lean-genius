import Proofs.Erdos85LocalGramPackingTuttePointCover

/-!
# Optional-star assembly for the B.3 Tutte cover

This file transports the pair groups supplied by Tutte on an induced residual
subtype back to the ambient row type, then adjoins a common-point star and
singleton leftovers.  The remaining outer-design lemma only has to construct
the three residual pieces and verify Tutte's condition and the strict budget.
-/

namespace Erdos85

variable {V P : Type*}

/-- No Tutte violator on a residual subtype gives ambient pair groups covering
that residual, with group count at most half its cardinality. -/
theorem exists_ambientPairGroups_of_residual_noTutteViolator
    [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
    (B : V → Finset P) (E : Finset V)
    (hTutte : ∀ u : Set {x // x ∈ E},
      ¬(blockCollisionGraph (fun x : {x // x ∈ E} => B x.1)).IsTutteViolator u) :
    ∃ groups : Finset (Finset V),
      groups.card ≤ E.card / 2 ∧
      (∀ S ∈ groups, ∃ p, ∀ x ∈ S, p ∈ B x) ∧
      ∀ x ∈ E, ∃ S ∈ groups, x ∈ S := by
  classical
  obtain ⟨subgroups, hsubgroupsCard, hsubgroupsPoint, hsubgroupsCover⟩ :=
    exists_pairGroups_of_collisionGraph_of_noTutteViolator
      (fun x : {x // x ∈ E} => B x.1) hTutte
  let lift : Finset {x // x ∈ E} → Finset V := fun S =>
    S.map (Function.Embedding.subtype _)
  let groups : Finset (Finset V) := subgroups.image lift
  refine ⟨groups, ?_, ?_, ?_⟩
  · calc
      groups.card ≤ subgroups.card := Finset.card_image_le
      _ ≤ E.card / 2 := by
        rw [Nat.le_div_iff_mul_le Nat.two_pos, Nat.mul_comm]
        simpa using hsubgroupsCard
  · intro S hS
    rcases Finset.mem_image.mp hS with ⟨T, hT, rfl⟩
    obtain ⟨p, hp⟩ := hsubgroupsPoint T hT
    refine ⟨p, ?_⟩
    intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hp y hy
  · intro x hxE
    obtain ⟨T, hT, hxT⟩ := hsubgroupsCover ⟨x, hxE⟩
    refine ⟨lift T, Finset.mem_image.mpr ⟨T, hT, rfl⟩, ?_⟩
    exact Finset.mem_map.mpr ⟨⟨x, hxE⟩, hxT, rfl⟩

#print axioms exists_ambientPairGroups_of_residual_noTutteViolator

/-- Assemble the exact `(13bi)` residual certificate: an optional three-row
common-point star, singleton leftovers, and a Tutte-perfect residual.  The
resulting ambient groups have the closed-form `(13bj)` budget. -/
theorem exists_groups_of_optionalStar_residual_noTutteViolator
    [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
    (B : V → Finset P) (R Q L E : Finset V) (sigma : ℕ)
    (hsigma : sigma ≤ 1)
    (hQcard : Q.card = 3 * sigma)
    (hQcommon : Q.Nonempty → ∃ p, ∀ x ∈ Q, p ∈ B x)
    (hLblocks : ∀ x ∈ L, (B x).Nonempty)
    (hpartition : R ⊆ Q ∪ L ∪ E)
    (hTutte : ∀ u : Set {x // x ∈ E},
      ¬(blockCollisionGraph (fun x : {x // x ∈ E} => B x.1)).IsTutteViolator u) :
    ∃ groups : Finset (Finset V),
      groups.card ≤ sigma + L.card + E.card / 2 ∧
      (∀ S ∈ groups, ∃ p, ∀ x ∈ S, p ∈ B x) ∧
      ∀ x ∈ R, ∃ S ∈ groups, x ∈ S := by
  classical
  obtain ⟨pairGroups, hpairCard, hpairPoint, hpairCover⟩ :=
    exists_ambientPairGroups_of_residual_noTutteViolator B E hTutte
  let starGroups : Finset (Finset V) := if Q = ∅ then ∅ else {Q}
  let singletonGroups : Finset (Finset V) := L.image fun x => {x}
  let groups := pairGroups ∪ starGroups ∪ singletonGroups
  have hstarCard : starGroups.card ≤ sigma := by
    interval_cases sigma
    · have hQempty : Q = ∅ := Finset.card_eq_zero.mp (by simpa using hQcard)
      simp [starGroups, hQempty]
    · by_cases hQempty : Q = ∅
      · simp [starGroups, hQempty]
      · simp [starGroups, hQempty]
  have hsingletonCard : singletonGroups.card ≤ L.card := Finset.card_image_le
  refine ⟨groups, ?_, ?_, ?_⟩
  · calc
      groups.card ≤ pairGroups.card + starGroups.card + singletonGroups.card := by
        exact (Finset.card_union_le _ _).trans <|
          Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ E.card / 2 + sigma + L.card := by omega
      _ = sigma + L.card + E.card / 2 := by omega
  · intro S hS
    simp only [groups, Finset.mem_union] at hS
    rcases hS with (hS | hS) | hS
    · exact hpairPoint S hS
    · have hQne : Q ≠ ∅ := by
        intro hQ
        simp [starGroups, hQ] at hS
      have hSQ : S = Q := by simpa [starGroups, hQne] using hS
      subst S
      exact hQcommon (Finset.nonempty_iff_ne_empty.mpr hQne)
    · rcases Finset.mem_image.mp hS with ⟨x, hxL, rfl⟩
      obtain ⟨p, hp⟩ := hLblocks x hxL
      exact ⟨p, by simpa using hp⟩
  · intro x hxR
    have hx := hpartition hxR
    simp only [Finset.mem_union] at hx
    rcases hx with (hxQ | hxL) | hxE
    · have hQne : Q ≠ ∅ := fun h => by simp [h] at hxQ
      refine ⟨Q, ?_, hxQ⟩
      exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_union.mpr <| Or.inr <| by simp [starGroups, hQne]
    · refine ⟨{x}, ?_, by simp⟩
      exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_image.mpr ⟨x, hxL, rfl⟩
    · obtain ⟨S, hS, hxS⟩ := hpairCover x hxE
      exact ⟨S, Finset.mem_union.mpr (Or.inl <|
        Finset.mem_union.mpr <| Or.inl hS), hxS⟩

#print axioms exists_groups_of_optionalStar_residual_noTutteViolator

/-- Final graph-facing `(13bi)`--`(13bj)` consumer.  Once the outer design
supplies the optional star, leftovers, Tutte condition, and strict numerical
budget, the local Gram-packing contradiction is automatic. -/
theorem false_of_localGramPacking_optionalStar_tuttePointCover
    [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
    (A H W : V → V → Prop) [DecidableRel A]
    (d : V → ℕ) (u : V) (B : V → Finset P)
    (R Q L E : Finset V) (sigma : ℕ)
    (hsymm : Std.Symm A)
    (hdegree : ∀ v, (relationNeighborFinset A v).card = d v)
    (hsupport : ∀ v w, A v w → H v w)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hshared : ∀ x y, x ≠ y → ¬ Disjoint (B x) (B y) → W x y)
    (hresidual : ∀ x, H u x →
      x ∉ reverseForcedLocalGramNeighborFinset H W d u →
      x ∉ reverseImpossibleLocalGramNeighborFinset H W d u →
      (∀ f ∈ reverseForcedLocalGramNeighborFinset H W d u,
        f ≠ x → ¬ W f x) → x ∈ R)
    (hsigma : sigma ≤ 1)
    (hQcard : Q.card = 3 * sigma)
    (hQcommon : Q.Nonempty → ∃ p, ∀ x ∈ Q, p ∈ B x)
    (hLblocks : ∀ x ∈ L, (B x).Nonempty)
    (hpartition : R ⊆ Q ∪ L ∪ E)
    (hTutte : ∀ t : Set {x // x ∈ E},
      ¬(blockCollisionGraph (fun x : {x // x ∈ E} => B x.1)).IsTutteViolator t)
    (hbudget :
      (reverseForcedLocalGramNeighborFinset H W d u).card +
        sigma + L.card + E.card / 2 < d u) :
    False := by
  obtain ⟨groups, hgroupsCard, hgroupsPoint, hgroupsCover⟩ :=
    exists_groups_of_optionalStar_residual_noTutteViolator
      B R Q L E sigma hsigma hQcard hQcommon hLblocks hpartition hTutte
  apply false_of_localGramPackingGroupedPointCover
      A H W d u B groups hsymm hdegree hsupport hgram hshared hgroupsPoint
  · intro x hxH hxF hxI hxcompat
    exact hgroupsCover x (hresidual x hxH hxF hxI hxcompat)
  · omega

#print axioms false_of_localGramPacking_optionalStar_tuttePointCover

end Erdos85
