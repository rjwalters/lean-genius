import Proofs.Erdos85SizeTwoEigenlineCyclicSelectedOrbitReciprocity
import Proofs.Erdos85SizeTwoEigenlineCyclicMatchingCounts

/-!
# Full-orbit regularity of the cyclic matching design

Node: `SIZE-TWO-EIGENLINE(q)` (outline F.3).

Reciprocity alone makes the full matching incidence design regular on both
sides.  Every absolute source-cell is contained in exactly `q - 2` source
matchings, without using looplessness or reconstructing the exterior graph.
-/

namespace Erdos85

noncomputable section

/-- Every edge in a source matching is itself the absolute cell of a unique
matching source. -/
theorem exists_unique_sourceCell_eq_of_mem_matching
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (target : SizeTwoCyclicMatchingSource q a)
    (e : SizeTwoCyclicAbsoluteGridEdge q)
    (he : e ∈ sizeTwoCyclicSourceMatching code target) :
    ∃! source : SizeTwoCyclicMatchingSource q a,
      sizeTwoCyclicMatchingSourceCell source = e := by
  obtain ⟨s, hs, _⟩ :=
    sizeTwoCyclicSourceMatching_mem_reverse_exists_eq_difference
      code target.1 target.2 e he
  let source : SizeTwoCyclicMatchingSource q a := (e.1, s)
  have hsource : sizeTwoCyclicMatchingSourceCell source = e := by
    apply Prod.ext
    · rfl
    · dsimp [source, sizeTwoCyclicMatchingSourceCell]
      rw [hs]
      abel
  refine ⟨source, hsource, ?_⟩
  intro source' hsource'
  exact sizeTwoCyclicMatchingSourceCell_injective
    (hsource'.trans hsource.symm)

/-- Sources incident with a fixed source are equivalent to the edges in its
matching.  Reciprocity supplies incidence of the inverse source. -/
def sizeTwoCyclicIncidentSourcesEquivMatching
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (target : SizeTwoCyclicMatchingSource q a) :
    {source : SizeTwoCyclicMatchingSource q a //
      sizeTwoCyclicMatchingSourceCell source ∈
        sizeTwoCyclicSourceMatching code target} ≃
      {e : SizeTwoCyclicAbsoluteGridEdge q //
        e ∈ sizeTwoCyclicSourceMatching code target} := by
  let f : {source : SizeTwoCyclicMatchingSource q a //
      sizeTwoCyclicMatchingSourceCell source ∈
        sizeTwoCyclicSourceMatching code target} →
      {e : SizeTwoCyclicAbsoluteGridEdge q //
        e ∈ sizeTwoCyclicSourceMatching code target} :=
    fun source => ⟨sizeTwoCyclicMatchingSourceCell source.1, source.2⟩
  exact Equiv.ofBijective f ⟨by
    intro x y hxy
    apply Subtype.ext
    exact sizeTwoCyclicMatchingSourceCell_injective (congrArg Subtype.val hxy), by
    intro e
    obtain ⟨source, hsource, _⟩ :=
      exists_unique_sourceCell_eq_of_mem_matching code target e.1 e.2
    refine ⟨⟨source, ?_⟩, ?_⟩
    · simpa [hsource] using e.2
    · apply Subtype.ext
      exact hsource⟩

/-- The intrinsic incident-source fiber has the same cardinality `q - 2` as
each source matching. -/
theorem sizeTwoCyclicIncidentSources_card_eq_sub_two
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hq1 : (1 : ZMod q) ≠ 0)
    (target : SizeTwoCyclicMatchingSource q a) :
    Fintype.card {source : SizeTwoCyclicMatchingSource q a //
      sizeTwoCyclicMatchingSourceCell source ∈
        sizeTwoCyclicSourceMatching code target} = q - 2 := by
  rw [Fintype.card_congr
    (sizeTwoCyclicIncidentSourcesEquivMatching code target)]
  rw [Fintype.card_coe]
  exact sizeTwoCyclicSourceMatching_card_eq_sub_two code hq1 target

/-- With every difference fiber selected, the multiplicity at every source
cell is exactly `q - 2`.  This strengthens graph-derived point replication:
only reciprocity and the matching size are needed. -/
theorem sizeTwoCyclicFullOrbitMultiplicity_sourceCell_eq_sub_two
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hq1 : (1 : ZMod q) ≠ 0)
    (target : SizeTwoCyclicMatchingSource q a) :
    sizeTwoCyclicSelectedOrbitMultiplicity code Finset.univ
        (sizeTwoCyclicMatchingSourceCell target) = q - 2 := by
  rw [sizeTwoCyclicSelectedOrbitMultiplicity_sourceCell]
  rw [← sizeTwoCyclicIncidentSources_card_eq_sub_two code hq1 target]
  rw [Fintype.card_subtype]
  simp_rw [Finset.card_filter]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- Coordinate form: every absolute cell whose difference avoids the two
reflection holes has full-orbit multiplicity exactly `q - 2`. -/
theorem sizeTwoCyclicFullOrbitMultiplicity_eq_sub_two_of_allowed
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (hq1 : (1 : ZMod q) ≠ 0)
    (e : SizeTwoCyclicAbsoluteGridEdge q)
    (he : e.2 - e.1 ≠ a ∧ e.2 - e.1 ≠ -1 - a) :
    sizeTwoCyclicSelectedOrbitMultiplicity code Finset.univ e = q - 2 := by
  let target : SizeTwoCyclicMatchingSource q a :=
    (e.1, ⟨e.2 - e.1, he⟩)
  have hcell : sizeTwoCyclicMatchingSourceCell target = e := by
    apply Prod.ext
    · rfl
    · dsimp [target, sizeTwoCyclicMatchingSourceCell]
      abel
  rw [← hcell]
  exact sizeTwoCyclicFullOrbitMultiplicity_sourceCell_eq_sub_two
    code hq1 target

end

end Erdos85

#print axioms Erdos85.exists_unique_sourceCell_eq_of_mem_matching
#print axioms Erdos85.sizeTwoCyclicIncidentSources_card_eq_sub_two
#print axioms Erdos85.sizeTwoCyclicFullOrbitMultiplicity_sourceCell_eq_sub_two
#print axioms Erdos85.sizeTwoCyclicFullOrbitMultiplicity_eq_sub_two_of_allowed
