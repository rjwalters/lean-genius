import Proofs.Erdos85OneHighPairingRefinement
import Proofs.Erdos85MatchingLabelParity

/-! # Canonical pairing lists induced by a free involution -/

namespace Erdos85

noncomputable section

def matchingEdgeSources
    {X : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    (mate : X → X) : Finset X :=
  Finset.univ.filter fun x => x < mate x

def matchingPairingList
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [LinearOrder L]
    (mate : X → X) (label : X → L) : List (L × L) :=
  (matchingEdgeSources mate).toList.map fun x =>
    (min (label x) (label (mate x)), max (label x) (label (mate x)))

@[simp] theorem matchingPairingList_length
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [LinearOrder L]
    (mate : X → X) (label : X → L) :
    (matchingPairingList mate label).length = (matchingEdgeSources mate).card := by
  simp [matchingPairingList]

theorem matchingEdgeSources_union_mateImage
    {X : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    (mate : X → X) (hinv : Function.Involutive mate)
    (hfree : ∀ x, mate x ≠ x) :
    matchingEdgeSources mate ∪ (matchingEdgeSources mate).image mate = Finset.univ := by
  ext x
  simp only [matchingEdgeSources, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro _
    trivial
  · intro _
    rcases lt_or_gt_of_ne (hfree x).symm with hlt | hgt
    · exact Or.inl hlt
    · right
      refine ⟨mate x, ?_, hinv x⟩
      simpa [hinv x] using hgt

theorem matchingEdgeSources_disjoint_mateImage
    {X : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    (mate : X → X) (hinv : Function.Involutive mate) :
    Disjoint (matchingEdgeSources mate) ((matchingEdgeSources mate).image mate) := by
  apply Finset.disjoint_left.mpr
  intro x hx hxim
  have hxlt : x < mate x := (Finset.mem_filter.mp hx).2
  rcases Finset.mem_image.mp hxim with ⟨y, hy, hyx⟩
  have hylt : y < mate y := (Finset.mem_filter.mp hy).2
  subst x
  rw [hinv y] at hxlt
  exact (lt_asymm hxlt hylt).elim

theorem two_mul_matchingEdgeSources_card
    {X : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    (mate : X → X) (hinv : Function.Involutive mate)
    (hfree : ∀ x, mate x ≠ x) :
    2 * (matchingEdgeSources mate).card = Fintype.card X := by
  have hu := matchingEdgeSources_union_mateImage mate hinv hfree
  have hd := matchingEdgeSources_disjoint_mateImage mate hinv
  have hc := Finset.card_union_of_disjoint hd
  rw [hu, Finset.card_univ,
    Finset.card_image_of_injective _ hinv.injective] at hc
  omega

theorem two_mul_matchingPairingList_length
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [LinearOrder L]
    (mate : X → X) (label : X → L)
    (hinv : Function.Involutive mate) (hfree : ∀ x, mate x ≠ x) :
    2 * (matchingPairingList mate label).length = Fintype.card X := by
  rw [matchingPairingList_length]
  exact two_mul_matchingEdgeSources_card mate hinv hfree

theorem canonicalFinPair_endpointCount
    (a b label : Fin 8) :
    oneHighLabelPairEndpointCount (min a b, max a b) label =
      (if a = label then 1 else 0) + (if b = label then 1 else 0) := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_right hab]
    rfl
  · rw [min_eq_right hba, max_eq_left hba, add_comm]
    rfl

theorem matchingPairingList_endpointCount
    {X : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    (mate : X → X) (label : X → Fin 8) (l : Fin 8)
    (hinv : Function.Involutive mate) (hfree : ∀ x, mate x ≠ x) :
    oneHighPairingEndpointCount (matchingPairingList mate label) l =
      (matchingLabelFiber label l).card := by
  classical
  let S := matchingEdgeSources mate
  have hu := matchingEdgeSources_union_mateImage mate hinv hfree
  have hd := matchingEdgeSources_disjoint_mateImage mate hinv
  have himage :
      (∑ x ∈ S.image mate, if label x = l then 1 else 0) =
        ∑ x ∈ S, if label (mate x) = l then 1 else 0 := by
    rw [Finset.sum_image]
    exact hinv.injective.injOn
  have huniv :
      (∑ x ∈ (Finset.univ : Finset X), if label x = l then 1 else 0) =
        (∑ x ∈ S, if label x = l then 1 else 0) +
          ∑ x ∈ S, if label (mate x) = l then 1 else 0 := by
    rw [← hu, Finset.sum_union hd, himage]
  have hfiber : (matchingLabelFiber label l).card =
      ∑ x ∈ (Finset.univ : Finset X),
        if label x = l then (1 : Nat) else 0 := by
    unfold matchingLabelFiber
    exact (Finset.sum_boole (R := Nat)
      (fun x => label x = l) Finset.univ).symm
  rw [hfiber, huniv]
  simp [oneHighPairingEndpointCount, matchingPairingList, S,
    canonicalFinPair_endpointCount,
    Finset.sum_add_distrib]

/-- Sorted form used by the executable source-shape enumeration. -/
def matchingPairingListSorted
    {X : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    (mate : X → X) (label : X → Fin 8) : List OneHighLabelPair :=
  (matchingPairingList mate label).mergeSort fun a b => decide (a ≤ b)

@[simp] theorem matchingPairingListSorted_length
    {X : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    (mate : X → X) (label : X → Fin 8) :
    (matchingPairingListSorted mate label).length =
      (matchingPairingList mate label).length := by
  exact List.Perm.length_eq (List.mergeSort_perm _ _)

theorem matchingPairingListSorted_endpointCount
    {X : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    (mate : X → X) (label : X → Fin 8) (l : Fin 8)
    (hinv : Function.Involutive mate) (hfree : ∀ x, mate x ≠ x) :
    oneHighPairingEndpointCount (matchingPairingListSorted mate label) l =
      (matchingLabelFiber label l).card := by
  rw [oneHighPairingEndpointCount]
  unfold matchingPairingListSorted
  have hp := (List.mergeSort_perm (matchingPairingList mate label)
    (fun a b => decide (a ≤ b))).map
    (fun pair => oneHighLabelPairEndpointCount pair l)
  rw [hp.sum_eq]
  exact matchingPairingList_endpointCount mate label l hinv hfree

theorem list_countP_eq_toFinset_filter_card_of_nodup
    {A : Type*} [DecidableEq A] (l : List A) (p : A → Bool)
    (h : l.Nodup) :
    l.countP p = (l.toFinset.filter fun x => p x = true).card := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha := (List.nodup_cons.mp h).1
      have hl := (List.nodup_cons.mp h).2
      have hat : a ∉ l.toFinset := by simpa using ha
      by_cases hp : p a = true
      · rw [List.countP_cons_of_pos hp, ih hl, List.toFinset_cons,
          Finset.filter_insert]
        simp [hp, hat]
      · rw [List.countP_cons_of_neg hp, ih hl, List.toFinset_cons,
          Finset.filter_insert]
        simp [hp]

/-- On an off-diagonal key, counting the full pairing list agrees exactly
with the pre-existing nonconstant exchanged-key multiplicity. -/
theorem matchingPairingList_count_eq_exchangedMissPairMultiplicity
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [Fintype L] [LinearOrder L]
    (mate : X → X) (label : X → L) (key : L × L)
    (hkey : key.1 < key.2) :
    (matchingPairingList mate label).count key =
      exchangedMissPairMultiplicity mate label key := by
  classical
  unfold matchingPairingList exchangedMissPairMultiplicity
    matchingEdgeSources nonconstantMatchingEdgeSources
    exchangedMissPairKey
  rw [List.count_eq_countP, List.countP_map,
    list_countP_eq_toFinset_filter_card_of_nodup _ _
      (Finset.nodup_toList _)]
  simp only [Finset.toList_toFinset]
  simp only [Finset.filter_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Function.comp_apply, beq_iff_eq]
  constructor
  · rintro ⟨hxlt, hpair⟩
    refine ⟨⟨hxlt, ?_⟩, hpair⟩
    intro heq
    have hkdiag : key.1 = key.2 := by
      rw [← hpair]
      simp [heq]
    exact (ne_of_lt hkey) hkdiag
  · rintro ⟨⟨hxlt, _⟩, hpair⟩
    exact ⟨hxlt, hpair⟩

theorem matchingPairingListSorted_count_eq_exchangedMissPairMultiplicity
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [Fintype L] [LinearOrder L]
    (mate : X → X) (label : X → L) (key : L × L)
    (hkey : key.1 < key.2) :
    ((matchingPairingList mate label).mergeSort fun a b =>
        decide (a ≤ b)).count key =
      exchangedMissPairMultiplicity mate label key := by
  rw [(List.mergeSort_perm (matchingPairingList mate label)
    (fun a b => decide (a ≤ b))).count_eq]
  exact matchingPairingList_count_eq_exchangedMissPairMultiplicity
    mate label key hkey

end

end Erdos85
