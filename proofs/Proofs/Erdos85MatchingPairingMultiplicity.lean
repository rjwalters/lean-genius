import Proofs.Erdos85MatchingPairingRefinement

/-! # Multiplicity transport for matching-induced pairing lists -/

namespace Erdos85

noncomputable section

/-- On a genuine off-diagonal key, counting the key in the canonical list of
matching edges is exactly the exchanged-key multiplicity used by the graph
parity argument. -/
theorem matchingPairingListSorted_count_eq_exchangedMissPairMultiplicity_of_lt
    {X : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    (mate : X → X) (label : X → Fin 8) (key : OneHighLabelPair)
    (hkey : key.1 < key.2) :
    (matchingPairingListSorted mate label).count key =
      exchangedMissPairMultiplicity mate label key := by
  exact matchingPairingListSorted_count_eq_exchangedMissPairMultiplicity
    mate label key hkey

/-- Singleton-refinement form consumed directly by the pairing-sector API. -/
theorem matchingPairingRefinementMultiplicity_eq_exchangedMissPairMultiplicity
    {X : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    (mate : X → X) (label : X → Fin 8) (key : OneHighLabelPair)
    (hkey : key.1 < key.2) :
    oneHighPairingRefinementMultiplicity
        [matchingPairingListSorted mate label] key =
      exchangedMissPairMultiplicity mate label key := by
  simpa [oneHighPairingRefinementMultiplicity] using
    matchingPairingListSorted_count_eq_exchangedMissPairMultiplicity_of_lt
      mate label key hkey

/-- Orientation-free form of exchanged-key multiplicity: both endpoints of
each matching edge carrying an off-diagonal key are counted on the right. -/
theorem two_mul_exchangedMissPairMultiplicity_eq_endpoint_card
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [Fintype L] [LinearOrder L]
    (mate : X → X) (label : X → L) (key : L × L)
    (hinv : Function.Involutive mate) (hfree : ∀ x, mate x ≠ x)
    (hkey : key.1 < key.2) :
    2 * exchangedMissPairMultiplicity mate label key =
      ((Finset.univ : Finset X).filter fun x =>
        exchangedMissPairKey mate label x = key).card := by
  classical
  let S := matchingEdgeSources mate
  let P : X → Prop := fun x => exchangedMissPairKey mate label x = key
  have hPmate (x : X) : P (mate x) ↔ P x := by
    simp only [P, exchangedMissPairKey, hinv x]
    constructor <;> intro h
    · simpa [min_comm, max_comm] using h
    · simpa [min_comm, max_comm] using h
  have hu := matchingEdgeSources_union_mateImage mate hinv hfree
  have hd := matchingEdgeSources_disjoint_mateImage mate hinv
  have himage : (S.image mate).filter P = (S.filter P).image mate := by
    ext x
    simp only [S, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hpy⟩
      exact ⟨y, ⟨hy, (hPmate y).mp hpy⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hpy⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, (hPmate y).mpr hpy⟩
  have hfilteredDisjoint :
      Disjoint (S.filter P) ((S.image mate).filter P) :=
    Finset.disjoint_filter_filter hd
  have hcard :
      ((Finset.univ : Finset X).filter P).card =
        2 * (S.filter P).card := by
    rw [← hu, Finset.filter_union, Finset.card_union_of_disjoint hfilteredDisjoint,
      himage, Finset.card_image_of_injective _ hinv.injective]
    omega
  rw [hcard]
  congr 1
  unfold exchangedMissPairMultiplicity nonconstantMatchingEdgeSources
  congr 1
  ext x
  simp only [S, P, matchingEdgeSources, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨⟨hx, hne⟩, hp⟩
    exact ⟨hx, hp⟩
  · rintro ⟨hx, hp⟩
    refine ⟨⟨hx, ?_⟩, hp⟩
    intro heq
    have : key.1 = key.2 := by
      rw [← hp]
      simp [exchangedMissPairKey, heq]
    exact (ne_of_lt hkey) this

/-- Exchanged-key multiplicity of a fiber-preserving matching on a sigma type
is the sum of the multiplicities of its fiber matchings.  The proof uses the
orientation-free endpoint count, so it is independent of the unrelated
linear orders chosen on the sigma type and on each fiber. -/
theorem sum_exchangedMissPairMultiplicity_eq_sigma
    {I L : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, LinearOrder (X i)] [LinearOrder (Sigma X)]
    [Fintype L] [LinearOrder L]
    (mate : ∀ i, X i → X i) (label : ∀ i, X i → L)
    (key : L × L) (hinv : ∀ i, Function.Involutive (mate i))
    (hfree : ∀ i x, mate i x ≠ x) (hkey : key.1 < key.2) :
    (∑ i, exchangedMissPairMultiplicity (mate i) (label i) key) =
      exchangedMissPairMultiplicity
        (fun z : Sigma X => ⟨z.1, mate z.1 z.2⟩)
        (fun z : Sigma X => label z.1 z.2) key := by
  classical
  let globalMate : Sigma X → Sigma X := fun z => ⟨z.1, mate z.1 z.2⟩
  let globalLabel : Sigma X → L := fun z => label z.1 z.2
  have hglobalInv : Function.Involutive globalMate := by
    rintro ⟨i, x⟩
    simp only [globalMate]
    congr 1
    exact hinv i x
  have hglobalFree : ∀ z, globalMate z ≠ z := by
    rintro ⟨i, x⟩ h
    simp only [globalMate] at h
    injection h with _ hx
    exact hfree i x hx
  have hg := two_mul_exchangedMissPairMultiplicity_eq_endpoint_card
    globalMate globalLabel key hglobalInv hglobalFree hkey
  have hl (i : I) := two_mul_exchangedMissPairMultiplicity_eq_endpoint_card
    (mate i) (label i) key (hinv i) (hfree i) hkey
  have hendpoints :
      ((Finset.univ : Finset (Sigma X)).filter fun z =>
        exchangedMissPairKey globalMate globalLabel z = key).card =
      ∑ i, ((Finset.univ : Finset (X i)).filter fun x =>
        exchangedMissPairKey (mate i) (label i) x = key).card := by
    rw [← Finset.univ_sigma_univ, Finset.filter_sigma, Finset.card_sigma]
    rfl
  have htwice :
      2 * (∑ i, exchangedMissPairMultiplicity (mate i) (label i) key) =
        2 * exchangedMissPairMultiplicity globalMate globalLabel key := by
    rw [hg, hendpoints]
    simp_rw [← hl]
    rw [Finset.mul_sum]
  simpa [globalMate, globalLabel] using
    (Nat.eq_of_mul_eq_mul_left (by omega) htwice)

end

end Erdos85
