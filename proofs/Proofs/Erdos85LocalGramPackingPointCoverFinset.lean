import Proofs.Erdos85LocalGramPacking

/-!
# Scale-one finite point covers for reverse local-packing intervals

This is the direct consumer needed by the q=9 B.3 collision-star matching
certificate.  Once the collision data constructs a finite set of points
meeting every contracted residual block, no explicit weight function or
rational arithmetic remains at the call site.
-/

namespace Erdos85

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- Choose one common point from each named group of rows.  The image of
those choices covers every row belonging to a group and has at most as many
points as there are groups. -/
theorem exists_pointCoverFinset_of_grouped_commonPoint
    {P : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (B : V → Finset P) (groups : Finset (Finset V))
    (hcommon : ∀ S ∈ groups, ∃ p, ∀ x ∈ S, p ∈ B x) :
    ∃ C : Finset P,
      C.card ≤ groups.card ∧
      ∀ S ∈ groups, ∀ x ∈ S, ¬ Disjoint C (B x) := by
  classical
  let pick : {S // S ∈ groups} → P := fun S =>
    Classical.choose (hcommon S.1 S.2)
  let C : Finset P := groups.attach.image pick
  refine ⟨C, ?_, ?_⟩
  · calc
      C.card ≤ groups.attach.card := Finset.card_image_le
      _ = groups.card := Finset.card_attach
  · intro S hS x hx
    have hpickB : pick ⟨S, hS⟩ ∈ B x :=
      (Classical.choose_spec (hcommon S hS)) x hx
    have hpickC : pick ⟨S, hS⟩ ∈ C := by
      apply Finset.mem_image.mpr
      exact ⟨⟨S, hS⟩, by simp, rfl⟩
    rw [Finset.not_disjoint_iff]
    exact ⟨pick ⟨S, hS⟩, hpickC, hpickB⟩

/-- A strict finite point cover of all candidates left after the forced and
impossible reverse-interval contractions gives a rank deficit at that row. -/
theorem reverseIntervalRankDeficit_of_pointCoverFinset
    {P : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (H W : V → V → Prop) (d : V → ℕ) (u : V)
    (B : V → Finset P) (C : Finset P)
    (hshared : ∀ x y, x ≠ y → ¬ Disjoint (B x) (B y) → W x y)
    (hcover : ∀ x, H u x →
      x ∉ reverseForcedLocalGramNeighborFinset H W d u →
      x ∉ reverseImpossibleLocalGramNeighborFinset H W d u →
      (∀ f ∈ reverseForcedLocalGramNeighborFinset H W d u,
        f ≠ x → ¬ W f x) →
      ¬ Disjoint C (B x))
    (htotal :
      (reverseForcedLocalGramNeighborFinset H W d u).card + C.card < d u) :
    HasReverseIntervalRankDeficitAt H W d u := by
  classical
  let weight : P → ℕ := fun p => if p ∈ C then 1 else 0
  apply reverseIntervalRankDeficit_of_scaledPointCover
      H W d u B weight 1 (by decide) hshared
  · intro x hxH hxF hxI hxcompat
    rcases Finset.not_disjoint_iff.mp
        (hcover x hxH hxF hxI hxcompat) with ⟨p, hpC, hpB⟩
    calc
      1 = weight p := by simp [weight, hpC]
      _ ≤ ∑ q ∈ B x, weight q := by
        exact Finset.single_le_sum
          (fun q _hq => Nat.zero_le (weight q)) hpB
  · simpa [weight] using htotal

/-- Grouped collision certificates (pairs, singletons, and optionally one
triple-star) produce the strict point cover required by the reverse interval
consumer. -/
theorem reverseIntervalRankDeficit_of_groupedPointCover
    {P : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (H W : V → V → Prop) (d : V → ℕ) (u : V)
    (B : V → Finset P) (groups : Finset (Finset V))
    (hshared : ∀ x y, x ≠ y → ¬ Disjoint (B x) (B y) → W x y)
    (hcommon : ∀ S ∈ groups, ∃ p, ∀ x ∈ S, p ∈ B x)
    (hgroup : ∀ x, H u x →
      x ∉ reverseForcedLocalGramNeighborFinset H W d u →
      x ∉ reverseImpossibleLocalGramNeighborFinset H W d u →
      (∀ f ∈ reverseForcedLocalGramNeighborFinset H W d u,
        f ≠ x → ¬ W f x) →
      ∃ S ∈ groups, x ∈ S)
    (htotal :
      (reverseForcedLocalGramNeighborFinset H W d u).card +
        groups.card < d u) :
    HasReverseIntervalRankDeficitAt H W d u := by
  obtain ⟨C, hCcard, hCcover⟩ :=
    exists_pointCoverFinset_of_grouped_commonPoint B groups hcommon
  apply reverseIntervalRankDeficit_of_pointCoverFinset
      H W d u B C hshared
  · intro x hxH hxF hxI hxcompat
    obtain ⟨S, hS, hxS⟩ := hgroup x hxH hxF hxI hxcompat
    exact hCcover S hS x hxS
  · exact lt_of_le_of_lt (Nat.add_le_add_left hCcard _) htotal

/-- Direct graph-facing consumer for a strict scale-one contracted point
cover.  This is the final interface a collision-star certificate needs. -/
theorem false_of_localGramPackingPointCoverFinset
    {P : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (A H W : V → V → Prop) [DecidableRel A]
    (d : V → ℕ) (u : V) (B : V → Finset P) (C : Finset P)
    (hsymm : Std.Symm A)
    (hdegree : ∀ v, (relationNeighborFinset A v).card = d v)
    (hsupport : ∀ v w, A v w → H v w)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hshared : ∀ x y, x ≠ y → ¬ Disjoint (B x) (B y) → W x y)
    (hcover : ∀ x, H u x →
      x ∉ reverseForcedLocalGramNeighborFinset H W d u →
      x ∉ reverseImpossibleLocalGramNeighborFinset H W d u →
      (∀ f ∈ reverseForcedLocalGramNeighborFinset H W d u,
        f ≠ x → ¬ W f x) →
      ¬ Disjoint C (B x))
    (htotal :
      (reverseForcedLocalGramNeighborFinset H W d u).card + C.card < d u) :
    False := by
  apply false_of_localGramPackingReverseIntervalRankDeficit
      A H W d hsymm hdegree hsupport hgram
  exact ⟨u, reverseIntervalRankDeficit_of_pointCoverFinset
    H W d u B C hshared hcover htotal⟩

#print axioms reverseIntervalRankDeficit_of_pointCoverFinset
#print axioms exists_pointCoverFinset_of_grouped_commonPoint
#print axioms reverseIntervalRankDeficit_of_groupedPointCover
#print axioms false_of_localGramPackingPointCoverFinset

end Erdos85
