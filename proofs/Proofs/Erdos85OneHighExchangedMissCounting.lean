import Proofs.Erdos85OneHighInternalEdgeSameMiss

/-! # Counting exchanged miss-label pairs -/

namespace Erdos85

noncomputable section

/-- Choose one endpoint of every matching edge using the ambient finite
linear order, and retain only edges on which the labels differ. -/
def nonconstantMatchingEdgeSources
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [DecidableEq L]
    (mate : X → X) (label : X → L) : Finset X :=
  Finset.univ.filter fun x => x < mate x ∧ label x ≠ label (mate x)

/-- The unordered label pair carried by an oriented matching edge, represented
canonically as an ordered pair using the label order. -/
def exchangedMissPairKey
    {X L : Type*} [LinearOrder L]
    (mate : X → X) (label : X → L) (x : X) : L × L :=
  (min (label x) (label (mate x)), max (label x) (label (mate x)))

/-- Multiplicity of an unordered exchanged label pair among the nonconstant
matching edges. -/
def exchangedMissPairMultiplicity
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [Fintype L] [DecidableEq L] [LinearOrder L]
    (mate : X → X) (label : X → L) (key : L × L) : ℕ :=
  ((nonconstantMatchingEdgeSources mate label).filter fun x =>
    exchangedMissPairKey mate label x = key).card

/-- The finite set of genuine unordered label-pair keys. -/
def exchangedMissPairKeys (L : Type*) [Fintype L] [DecidableEq L]
    [LinearOrder L] : Finset (L × L) :=
  (Finset.univ.product Finset.univ).filter fun key => key.1 < key.2

/-- Exact fiber accounting: summing exchanged-pair multiplicities counts
precisely the nonconstant matching edges. -/
theorem sum_exchangedMissPairMultiplicity
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [Fintype L] [DecidableEq L] [LinearOrder L]
    (mate : X → X) (label : X → L) :
    (∑ key : L × L, exchangedMissPairMultiplicity mate label key) =
      (nonconstantMatchingEdgeSources mate label).card := by
  simpa [exchangedMissPairMultiplicity] using
    Finset.sum_card_fiberwise_eq_card_filter
      (nonconstantMatchingEdgeSources mate label)
      (Finset.univ : Finset (L × L))
      (exchangedMissPairKey mate label)

/-- Pigeonhole interface for the next obstruction: if there are more
nonconstant matching edges than possible unordered keys (the present bound
uses the ambient ordered-pair type), two distinct matching edges carry the
same exchanged label pair. -/
theorem exists_repeated_exchangedMissPair_of_card_lt
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [Fintype L] [DecidableEq L] [LinearOrder L]
    (mate : X → X) (label : X → L)
    (hcard : Fintype.card (L × L) <
      (nonconstantMatchingEdgeSources mate label).card) :
    ∃ x ∈ nonconstantMatchingEdgeSources mate label,
      ∃ y ∈ nonconstantMatchingEdgeSources mate label,
        x ≠ y ∧ exchangedMissPairKey mate label x =
          exchangedMissPairKey mate label y := by
  let S := nonconstantMatchingEdgeSources mate label
  let key : {x // x ∈ S} → L × L := fun x =>
    exchangedMissPairKey mate label x.1
  have hcard' : Fintype.card (L × L) < Fintype.card {x // x ∈ S} := by
    simpa [S] using hcard
  obtain ⟨x, y, hxy, hkey⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt key hcard'
  exact ⟨x.1, x.2, y.1, y.2, fun h => hxy (Subtype.ext h), hkey⟩

/-- Every key occurring on a nonconstant edge is genuinely off-diagonal. -/
theorem exchangedMissPairKey_lt_of_mem
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [DecidableEq L] [LinearOrder L]
    {mate : X → X} {label : X → L} {x : X}
    (hx : x ∈ nonconstantMatchingEdgeSources mate label) :
    (exchangedMissPairKey mate label x).1 <
      (exchangedMissPairKey mate label x).2 := by
  have hne : label x ≠ label (mate x) := (Finset.mem_filter.mp hx).2.2
  simp only [exchangedMissPairKey]
  exact min_lt_max.mpr hne

/-- Sharpened exact accounting over only genuine unordered label pairs. -/
theorem sum_exchangedMissPairMultiplicity_over_keys
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [Fintype L] [DecidableEq L] [LinearOrder L]
    (mate : X → X) (label : X → L) :
    (∑ key ∈ exchangedMissPairKeys L,
      exchangedMissPairMultiplicity mate label key) =
      (nonconstantMatchingEdgeSources mate label).card := by
  let S := nonconstantMatchingEdgeSources mate label
  let key := exchangedMissPairKey mate label
  have hmaps : ∀ x ∈ S, key x ∈ exchangedMissPairKeys L := by
    intro x hx
    refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
    exact exchangedMissPairKey_lt_of_mem hx
  have hsum := Finset.sum_card_fiberwise_eq_card_filter
    S (exchangedMissPairKeys L) key
  have hfilter : S.filter (fun x => key x ∈ exchangedMissPairKeys L) = S :=
    Finset.filter_eq_self.mpr hmaps
  rw [hfilter] at hsum
  simpa [S, key, exchangedMissPairMultiplicity] using hsum

/-- Sharp pigeonhole form using only off-diagonal unordered keys. -/
theorem exists_repeated_exchangedMissPair_of_keys_card_lt
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [Fintype L] [DecidableEq L] [LinearOrder L]
    (mate : X → X) (label : X → L)
    (hcard : (exchangedMissPairKeys L).card <
      (nonconstantMatchingEdgeSources mate label).card) :
    ∃ x ∈ nonconstantMatchingEdgeSources mate label,
      ∃ y ∈ nonconstantMatchingEdgeSources mate label,
        x ≠ y ∧ exchangedMissPairKey mate label x =
          exchangedMissPairKey mate label y := by
  let S := nonconstantMatchingEdgeSources mate label
  let key := exchangedMissPairKey mate label
  have hmaps : ∀ x ∈ S, key x ∈ exchangedMissPairKeys L := by
    intro x hx
    refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
    exact exchangedMissPairKey_lt_of_mem hx
  obtain ⟨x, hx, y, hy, hxy, hkey⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  exact ⟨x, hx, y, hy, hxy, hkey⟩

end

end Erdos85
