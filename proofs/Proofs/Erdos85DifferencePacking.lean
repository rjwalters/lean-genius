import Proofs.Erdos85UniqueSidonFactor
import Proofs.Erdos85SecondOrderQuotient

/-!
# Packing difference sets from a common defect cycle

For a fixed cyclic source component, every circulant block into another
component has a Sidon connection set.  More importantly, the nonzero ordered
difference sets belonging to *different* target components are disjoint: a
shared difference would give two source vertices two common neighbours, one
in each target component.  Thus all block difference sets pack together into
the `r - 1` nonzero residues.  This is the aggregate form needed for the
minimum-layer argument; it does not enumerate quotient parameters.
-/

namespace Erdos85

noncomputable section

/-- Reflection of a finite connection set. -/
def negFinset {Z : Type*} [DecidableEq Z] [Neg Z] (A : Finset Z) : Finset Z :=
  A.image (fun z ↦ -z)

@[simp] theorem mem_negFinset_iff
    {Z : Type*} [DecidableEq Z] [AddCommGroup Z]
    (A : Finset Z) (z : Z) :
    z ∈ negFinset A ↔ -z ∈ A := by
  constructor
  · intro hz
    obtain ⟨a, ha, hza⟩ := Finset.mem_image.mp hz
    rw [← hza]
    simpa using ha
  · intro hz
    exact Finset.mem_image.mpr ⟨-z, by simpa using hz, by simp⟩

/-- Negating a connection set does not change its set of ordered
differences.  This is why the difference array is independent of coordinate
reflections and block transposition. -/
theorem orderedDifferenceSet_negFinset
    {Z : Type*} [Fintype Z] [DecidableEq Z] [AddCommGroup Z]
    (A : Finset Z) :
    orderedDifferenceSet (negFinset A) = orderedDifferenceSet A := by
  ext z
  constructor
  · intro hz
    simp only [orderedDifferenceSet, Finset.mem_image] at hz ⊢
    obtain ⟨p, hp, hpz⟩ := hz
    obtain ⟨hp1, hp2, hpne⟩ := mem_orderedDistinctPairs_iff.mp hp
    refine ⟨⟨-p.2, -p.1⟩, mem_orderedDistinctPairs_iff.mpr ?_, ?_⟩
    · exact ⟨(mem_negFinset_iff A p.2).mp hp2,
          (mem_negFinset_iff A p.1).mp hp1, by
            intro h
            apply hpne.symm
            exact neg_injective h⟩
    · calc
        -p.2 - -p.1 = p.1 - p.2 := by abel
        _ = z := hpz
  · intro hz
    simp only [orderedDifferenceSet, Finset.mem_image] at hz ⊢
    obtain ⟨p, hp, hpz⟩ := hz
    obtain ⟨hp1, hp2, hpne⟩ := mem_orderedDistinctPairs_iff.mp hp
    refine ⟨⟨-p.2, -p.1⟩, mem_orderedDistinctPairs_iff.mpr ?_, ?_⟩
    · exact ⟨(mem_negFinset_iff A (-p.2)).mpr (by simpa using hp2),
          (mem_negFinset_iff A (-p.1)).mpr (by simpa using hp1), by
            intro h
            apply hpne.symm
            exact neg_injective h⟩
    · calc
        -p.2 - -p.1 = p.1 - p.2 := by abel
        _ = z := hpz

/-- Reflection preserves the ordered Sidon property. -/
theorem isOrderedSidon_negFinset_iff
    {Z : Type*} [Fintype Z] [DecidableEq Z] [AddCommGroup Z]
    (A : Finset Z) :
    IsOrderedSidon (negFinset A) ↔ IsOrderedSidon A := by
  let flipNeg : Z × Z → Z × Z := fun p ↦ (-p.2, -p.1)
  have hmem : ∀ {p : Z × Z}, p ∈ orderedDistinctPairs A →
      flipNeg p ∈ orderedDistinctPairs (negFinset A) := by
    intro p hp
    obtain ⟨hp1, hp2, hpne⟩ := mem_orderedDistinctPairs_iff.mp hp
    apply mem_orderedDistinctPairs_iff.mpr
    refine ⟨(mem_negFinset_iff A (-p.2)).mpr (by simpa using hp2),
      (mem_negFinset_iff A (-p.1)).mpr (by simpa using hp1), ?_⟩
    intro h
    apply hpne.symm
    exact neg_injective h
  have hdiff : ∀ p : Z × Z,
      (flipNeg p).1 - (flipNeg p).2 = p.1 - p.2 := by
    intro p
    dsimp [flipNeg]
    abel
  constructor
  · intro h p hp q hq heq
    have heq' : (flipNeg p).1 - (flipNeg p).2 =
        (flipNeg q).1 - (flipNeg q).2 := by simpa [hdiff] using heq
    have hfg := h (by simpa using hmem hp) (by simpa using hmem hq) heq'
    apply Prod.ext
    · have := congrArg (fun x : Z × Z ↦ -x.2) hfg
      simpa [flipNeg] using this
    · have := congrArg (fun x : Z × Z ↦ -x.1) hfg
      simpa [flipNeg] using this
  · intro h
    intro p hp q hq heq
    have hpdata := mem_orderedDistinctPairs_iff.mp hp
    have hqdata := mem_orderedDistinctPairs_iff.mp hq
    have hp' : flipNeg p ∈ orderedDistinctPairs A := by
      apply mem_orderedDistinctPairs_iff.mpr
      refine ⟨(mem_negFinset_iff A p.2).mp hpdata.2.1,
        (mem_negFinset_iff A p.1).mp hpdata.1, ?_⟩
      intro hne
      apply hpdata.2.2.symm
      exact neg_injective hne
    have hq' : flipNeg q ∈ orderedDistinctPairs A := by
      apply mem_orderedDistinctPairs_iff.mpr
      refine ⟨(mem_negFinset_iff A q.2).mp hqdata.2.1,
        (mem_negFinset_iff A q.1).mp hqdata.1, ?_⟩
      intro hne
      apply hqdata.2.2.symm
      exact neg_injective hne
    have heq' : (flipNeg p).1 - (flipNeg p).2 =
        (flipNeg q).1 - (flipNeg q).2 := by simpa [hdiff] using heq
    have hfg := h (by simpa using hp') (by simpa using hq') heq'
    apply Prod.ext
    · have := congrArg (fun x : Z × Z ↦ -x.2) hfg
      simpa [flipNeg] using this
    · have := congrArg (fun x : Z × Z ↦ -x.1) hfg
      simpa [flipNeg] using this
variable {Z K V : Type*}
  [Fintype Z] [DecidableEq Z] [AddCommGroup Z]
  [Fintype K] [DecidableEq K]
  [Fintype V] [DecidableEq V]

/-- Ordered differences are closed under negation, by reversing the ordered
pair. -/
theorem neg_mem_orderedDifferenceSet_iff (A : Finset Z) (z : Z) :
    -z ∈ orderedDifferenceSet A ↔ z ∈ orderedDifferenceSet A := by
  have hneg (t : Z) (ht : t ∈ orderedDifferenceSet A) :
      -t ∈ orderedDifferenceSet A := by
    simp only [orderedDifferenceSet, Finset.mem_image] at ht ⊢
    obtain ⟨p, hp, hpt⟩ := ht
    have hpdata := mem_orderedDistinctPairs_iff.mp hp
    refine ⟨(p.2, p.1), ?_, ?_⟩
    · exact mem_orderedDistinctPairs_iff.mpr
        ⟨hpdata.2.1, hpdata.1, hpdata.2.2.symm⟩
    · calc
        p.2 - p.1 = -(p.1 - p.2) := by abel
        _ = -t := congrArg Neg.neg hpt
  constructor
  · intro hz
    simpa using hneg (-z) hz
  · exact hneg z

/-- The residues not used by any ordered-difference set in a family. -/
def unusedOrderedDifferences (A : K → Finset Z) : Finset Z :=
  (Finset.univ.erase (0 : Z)) \
    (Finset.univ.biUnion fun k ↦ orderedDifferenceSet (A k))

theorem neg_mem_unusedOrderedDifferences_iff (A : K → Finset Z) (z : Z) :
    -z ∈ unusedOrderedDifferences A ↔ z ∈ unusedOrderedDifferences A := by
  simp only [unusedOrderedDifferences, Finset.mem_sdiff, Finset.mem_erase,
    Finset.mem_univ, and_true, Finset.mem_biUnion]
  constructor <;> intro h
  · refine ⟨?_, ?_⟩
    · simpa using h.1
    · rintro ⟨k, hk, hzk⟩
      apply h.2
      exact ⟨k, trivial,
        (neg_mem_orderedDifferenceSet_iff (A k) z).mpr hzk⟩
  · refine ⟨?_, ?_⟩
    · simpa using h.1
    · rintro ⟨k, hk, hzk⟩
      apply h.2
      exact ⟨k, trivial,
        (neg_mem_orderedDifferenceSet_iff (A k) z).mp hzk⟩

/-- Pure finite-difference form of the two-hole count. -/
theorem card_unusedOrderedDifferences_eq_two_of_packing
    (A : K → Finset Z)
    (hpair : ∀ {k l : K}, k ≠ l →
      Disjoint (orderedDifferenceSet (A k))
        (orderedDifferenceSet (A l)))
    (hsidon : ∀ k, IsOrderedSidon (A k))
    (hcard : 3 ≤ Fintype.card Z)
    (hexcess : ∑ k, (A k).card * ((A k).card - 1) =
      Fintype.card Z - 3) :
    (unusedOrderedDifferences A).card = 2 := by
  let U : Finset Z := Finset.univ.biUnion
    (fun k ↦ orderedDifferenceSet (A k))
  have hpair' : (↑(Finset.univ : Finset K) : Set K).PairwiseDisjoint
      (fun k ↦ orderedDifferenceSet (A k)) := by
    intro k hk l hl hkl
    exact hpair hkl
  have hcardU : U.card = Fintype.card Z - 3 := by
    rw [Finset.card_biUnion hpair']
    calc
      ∑ k, (orderedDifferenceSet (A k)).card =
          ∑ k, (A k).card * ((A k).card - 1) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact card_orderedDifferenceSet_of_sidon (hsidon k)
      _ = Fintype.card Z - 3 := hexcess
  have hsub : U ⊆ Finset.univ.erase (0 : Z) := by
    intro z hz
    obtain ⟨k, hk, hzk⟩ := Finset.mem_biUnion.mp hz
    exact Finset.mem_erase.mpr ⟨
      fun hz0 ↦ zero_not_mem_orderedDifferenceSet (A k) (hz0 ▸ hzk),
      Finset.mem_univ z⟩
  change ((Finset.univ.erase (0 : Z)) \ U).card = 2
  rw [Finset.card_sdiff_of_subset hsub,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : Z)),
    Finset.card_univ, hcardU]
  omega

/-- Pure packing criterion for the canonical leave `{1,-1}`. -/
theorem unusedOrderedDifferences_eq_one_negOne_of_packing
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r)
    (A : K → Finset (ZMod r))
    (hpair : ∀ {k l : K}, k ≠ l →
      Disjoint (orderedDifferenceSet (A k))
        (orderedDifferenceSet (A l)))
    (hsidon : ∀ k, IsOrderedSidon (A k))
    (hexcess : ∑ k, (A k).card * ((A k).card - 1) =
      r - 3)
    (hone : ∀ k, (1 : ZMod r) ∉ orderedDifferenceSet (A k)) :
    unusedOrderedDifferences A = {1, -1} := by
  have hone0 : (1 : ZMod r) ≠ 0 := by
    intro h
    have hr1 : r = 1 := ZMod.one_eq_zero_iff.mp h
    omega
  have hminus : (-1 : ZMod r) ≠ 1 := by
    simpa using zmod_sub_one_ne_add_one_of_three_le hr3 (0 : ZMod r)
  have htwo := card_unusedOrderedDifferences_eq_two_of_packing
    A hpair hsidon (by simpa using hr3) (by simpa using hexcess)
  have honeMem : (1 : ZMod r) ∈ unusedOrderedDifferences A := by
    simp only [unusedOrderedDifferences, Finset.mem_sdiff, Finset.mem_erase,
      Finset.mem_univ, and_true, Finset.mem_biUnion]
    exact ⟨hone0, by rintro ⟨k, hk, hmem⟩; exact hone k hmem⟩
  have hnegMem : (-1 : ZMod r) ∈ unusedOrderedDifferences A :=
    (neg_mem_unusedOrderedDifferences_iff A 1).mpr honeMem
  have hdistinct : (1 : ZMod r) ≠ -1 := hminus.symm
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact honeMem
    · exact hnegMem
  · rw [htwo]
    simp [hdistinct, hminus]

/-- A Sidon set closed under negation contains at most one inverse pair. -/
theorem card_le_two_of_neg_closed_isOrderedSidon
    (A : Finset Z) (hneg : ∀ a ∈ A, -a ∈ A)
    (hSidon : IsOrderedSidon A) : A.card ≤ 2 := by
  by_cases hA : A = ∅
  · simp [hA]
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hA
  apply (Finset.card_le_card (s := A) (t := {a, -a}) ?_).trans
    Finset.card_le_two
  intro b hb
  by_cases hba : b = a
  · simp [hba]
  have hp : (a, b) ∈ orderedDistinctPairs A :=
    mem_orderedDistinctPairs_iff.mpr ⟨ha, hb, Ne.symm hba⟩
  have hq : (-b, -a) ∈ orderedDistinctPairs A :=
    mem_orderedDistinctPairs_iff.mpr
      ⟨hneg b hb, hneg a ha, neg_injective.ne hba⟩
  have hpq : (a, b) = (-b, -a) := by
    apply hSidon hp hq
    change a - b = -b - -a
    abel
  have hbneg : b = -a := congrArg Prod.snd hpq
  simp [hba, hbneg]

/-- Consequently, a `C4`-free undirected circulant block from a cyclic part
to itself has degree at most two. -/
theorem card_connectionSet_le_two_of_c4Free_self_circulantBlock
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (u : Z → V) (hu : Function.Injective u)
    (A : Finset Z)
    (hblock : ∀ x z, G.Adj (u x) (u z) ↔ z - x ∈ A) :
    A.card ≤ 2 := by
  apply card_le_two_of_neg_closed_isOrderedSidon A
  · intro a ha
    have h0a : G.Adj (u 0) (u a) := by
      rw [hblock]
      simpa using ha
    have ha0 : G.Adj (u a) (u 0) := h0a.symm
    rw [hblock] at ha0
    simpa using ha0
  · exact isOrderedSidon_of_c4Free_circulantBlock
      G hfree u u hu hu A hblock

/-- Distinct target blocks from the same cyclic source have disjoint ordered
difference sets.  The only graph input is `C4`-freeness and separation of the
target parametrizations. -/
theorem orderedDifferenceSet_disjoint_of_c4Free_circulantBlocks
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (u : Z → V) (w : K → Z → V)
    (hu : Function.Injective u)
    (hwsep : ∀ {k l : K}, k ≠ l → ∀ x y, w k x ≠ w l y)
    (A : K → Finset Z)
    (hblock : ∀ k x z, G.Adj (u x) (w k z) ↔ z - x ∈ A k)
    {k l : K} (hkl : k ≠ l) :
    Disjoint (orderedDifferenceSet (A k)) (orderedDifferenceSet (A l)) := by
  rw [Finset.disjoint_left]
  intro delta hk hl
  simp only [orderedDifferenceSet, Finset.mem_image] at hk hl
  obtain ⟨p, hp, hpdelta⟩ := hk
  obtain ⟨q, hq, hqdelta⟩ := hl
  obtain ⟨hp1, hp2, hpne⟩ := mem_orderedDistinctPairs_iff.mp hp
  obtain ⟨hq1, hq2, hqne⟩ := mem_orderedDistinctPairs_iff.mp hq
  have hdiff : p.1 - p.2 = q.1 - q.2 := hpdelta.trans hqdelta.symm
  let s : Z := p.1 - p.2
  have hs : s ≠ 0 := by
    intro hs0
    exact hpne (sub_eq_zero.mp hs0)
  have hu0s : u 0 ≠ u s := by
    intro hus
    exact hs (hu hus.symm)
  have hwne : w k p.1 ≠ w l q.1 := hwsep hkl p.1 q.1
  have hkp0 : G.Adj (w k p.1) (u 0) := by
    rw [G.adj_comm, hblock]
    simpa using hp1
  have hlq0 : G.Adj (w l q.1) (u 0) := by
    rw [G.adj_comm, hblock]
    simpa using hq1
  have hkps : G.Adj (w k p.1) (u s) := by
    rw [G.adj_comm, hblock]
    have heq : p.1 - s = p.2 := by dsimp [s]; abel
    rw [heq]
    exact hp2
  have hlqs : G.Adj (w l q.1) (u s) := by
    rw [G.adj_comm, hblock]
    have heq : q.1 - s = q.2 := by
      dsimp [s]
      rw [hdiff]
      abel
    rw [heq]
    exact hq2
  exact (hfree (containsC4_of_two_common hu0s hwne
    hkp0 hkps hlq0 hlqs)).elim

/-- Pairwise form of the preceding packing lemma, convenient when the two
targets have been reflected independently to normalize their orientations. -/
theorem orderedDifferenceSet_disjoint_of_c4Free_two_circulantBlocks
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (u w₁ w₂ : Z → V) (hu : Function.Injective u)
    (hwsep : ∀ x y, w₁ x ≠ w₂ y)
    (A B : Finset Z)
    (hA : ∀ x z, G.Adj (u x) (w₁ z) ↔ z - x ∈ A)
    (hB : ∀ x z, G.Adj (u x) (w₂ z) ↔ z - x ∈ B) :
    Disjoint (orderedDifferenceSet A) (orderedDifferenceSet B) := by
  rw [Finset.disjoint_left]
  intro delta hAd hBd
  simp only [orderedDifferenceSet, Finset.mem_image] at hAd hBd
  obtain ⟨p, hp, hpdelta⟩ := hAd
  obtain ⟨q, hq, hqdelta⟩ := hBd
  obtain ⟨hp1, hp2, hpne⟩ := mem_orderedDistinctPairs_iff.mp hp
  obtain ⟨hq1, hq2, hqne⟩ := mem_orderedDistinctPairs_iff.mp hq
  have hdiff : p.1 - p.2 = q.1 - q.2 := hpdelta.trans hqdelta.symm
  let s : Z := p.1 - p.2
  have hs : s ≠ 0 := by
    intro hs0
    exact hpne (sub_eq_zero.mp hs0)
  have hu0s : u 0 ≠ u s := by
    intro hus
    exact hs (hu hus.symm)
  have hwne : w₁ p.1 ≠ w₂ q.1 := hwsep p.1 q.1
  have h₁p0 : G.Adj (w₁ p.1) (u 0) := by
    rw [G.adj_comm, hA]
    simpa using hp1
  have h₂q0 : G.Adj (w₂ q.1) (u 0) := by
    rw [G.adj_comm, hB]
    simpa using hq1
  have h₁ps : G.Adj (w₁ p.1) (u s) := by
    rw [G.adj_comm, hA]
    have heq : p.1 - s = p.2 := by dsimp [s]; abel
    rw [heq]
    exact hp2
  have h₂qs : G.Adj (w₂ q.1) (u s) := by
    rw [G.adj_comm, hB]
    have heq : q.1 - s = q.2 := by
      dsimp [s]
      rw [hdiff]
      abel
    rw [heq]
    exact hq2
  exact (hfree (containsC4_of_two_common hu0s hwne
    h₁p0 h₁ps h₂q0 h₂qs)).elim

/-- Aggregate ordered-difference packing for every target block out of a
fixed cyclic source. -/
theorem sum_card_orderedDifferenceSet_le_card_sub_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (u : Z → V) (w : K → Z → V)
    (hu : Function.Injective u)
    (hwsep : ∀ {k l : K}, k ≠ l → ∀ x y, w k x ≠ w l y)
    (A : K → Finset Z)
    (hblock : ∀ k x z, G.Adj (u x) (w k z) ↔ z - x ∈ A k) :
    (∑ k, (orderedDifferenceSet (A k)).card) ≤ Fintype.card Z - 1 := by
  let U : Finset Z := Finset.univ.biUnion fun k ↦ orderedDifferenceSet (A k)
  have hpair : (↑(Finset.univ : Finset K) : Set K).PairwiseDisjoint
      (fun k ↦ orderedDifferenceSet (A k)) := by
    intro k hk l hl hkl
    exact orderedDifferenceSet_disjoint_of_c4Free_circulantBlocks
      G hfree u w hu hwsep A hblock hkl
  have hcardU : U.card = ∑ k, (orderedDifferenceSet (A k)).card := by
    simpa only [U, Finset.sum_filter, Finset.mem_univ, if_true] using
      (Finset.card_biUnion hpair)
  have hsub : U ⊆ Finset.univ.erase (0 : Z) := by
    intro z hz
    obtain ⟨k, hk, hzk⟩ := Finset.mem_biUnion.mp hz
    exact Finset.mem_erase.mpr ⟨
      fun hz0 ↦ zero_not_mem_orderedDifferenceSet (A k) (hz0 ▸ hzk),
      Finset.mem_univ z⟩
  have hle := Finset.card_le_card hsub
  rw [hcardU, Finset.card_erase_of_mem (Finset.mem_univ (0 : Z)),
    Finset.card_univ] at hle
  exact hle

/-- Sidon cardinalities turn aggregate difference packing into the quadratic
quotient inequality used at the minimum layer. -/
theorem sum_card_mul_pred_le_card_sub_one_of_c4Free_circulantBlocks
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (u : Z → V) (w : K → Z → V)
    (hu : Function.Injective u)
    (hw : ∀ k, Function.Injective (w k))
    (hwsep : ∀ {k l : K}, k ≠ l → ∀ x y, w k x ≠ w l y)
    (A : K → Finset Z)
    (hblock : ∀ k x z, G.Adj (u x) (w k z) ↔ z - x ∈ A k) :
    (∑ k, (A k).card * ((A k).card - 1)) ≤ Fintype.card Z - 1 := by
  calc
    (∑ k, (A k).card * ((A k).card - 1)) =
        ∑ k, (orderedDifferenceSet (A k)).card := by
      apply Finset.sum_congr rfl
      intro k hk
      symm
      exact card_orderedDifferenceSet_of_sidon
        (isOrderedSidon_of_c4Free_circulantBlock
          G hfree u (w k) hu (hw k) (A k) (hblock k))
    _ ≤ Fintype.card Z - 1 :=
      sum_card_orderedDifferenceSet_le_card_sub_one
        G hfree u w hu hwsep A hblock

/-- When the minimum-layer excess identity makes the quadratic sum exactly
`|Z|-3`, precisely two nonzero residues are unused by all target-block
difference sets.  This is the invariant two-hole conclusion, independent of
the number or sizes of the blocks. -/
theorem card_unused_orderedDifferences_eq_two
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (u : Z → V) (w : K → Z → V)
    (hu : Function.Injective u)
    (hw : ∀ k, Function.Injective (w k))
    (hwsep : ∀ {k l : K}, k ≠ l → ∀ x y, w k x ≠ w l y)
    (A : K → Finset Z)
    (hblock : ∀ k x z, G.Adj (u x) (w k z) ↔ z - x ∈ A k)
    (hcard : 3 ≤ Fintype.card Z)
    (hexcess : (∑ k, (A k).card * ((A k).card - 1)) =
      Fintype.card Z - 3) :
    (unusedOrderedDifferences A).card = 2 := by
  let U : Finset Z := Finset.univ.biUnion fun k ↦ orderedDifferenceSet (A k)
  have hpair : (↑(Finset.univ : Finset K) : Set K).PairwiseDisjoint
      (fun k ↦ orderedDifferenceSet (A k)) := by
    intro k hk l hl hkl
    exact orderedDifferenceSet_disjoint_of_c4Free_circulantBlocks
      G hfree u w hu hwsep A hblock hkl
  have hcardU : U.card = Fintype.card Z - 3 := by
    rw [Finset.card_biUnion hpair]
    calc
      (∑ k, (orderedDifferenceSet (A k)).card) =
          ∑ k, (A k).card * ((A k).card - 1) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact card_orderedDifferenceSet_of_sidon
          (isOrderedSidon_of_c4Free_circulantBlock
            G hfree u (w k) hu (hw k) (A k) (hblock k))
      _ = Fintype.card Z - 3 := hexcess
  have hsub : U ⊆ Finset.univ.erase (0 : Z) := by
    intro z hz
    obtain ⟨k, hk, hzk⟩ := Finset.mem_biUnion.mp hz
    exact Finset.mem_erase.mpr ⟨
      fun hz0 ↦ zero_not_mem_orderedDifferenceSet (A k) (hz0 ▸ hzk),
      Finset.mem_univ z⟩
  change ((Finset.univ.erase (0 : Z)) \ U).card = 2
  rw [Finset.card_sdiff_of_subset hsub,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : Z)),
    Finset.card_univ, hcardU]
  omega

/-- A connection set from a parametrized second-order defect cycle cannot
use displacement `1` as an ordered difference: such a difference would give
the two consecutive defect vertices a common `G`-neighbour, whereas the
boundary square identity says that they have none. -/
theorem one_not_mem_orderedDifferenceSet_of_secondOrder_cycleBlock
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr3 : 3 ≤ r)
    (u w : ZMod r → V) (hu : Function.Injective u)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)})
    (A : Finset (ZMod r))
    (hblock : ∀ x z, G.Adj (u x) (w z) ↔ z - x ∈ A) :
    (1 : ZMod r) ∉ orderedDifferenceSet A := by
  intro hone
  simp only [orderedDifferenceSet, Finset.mem_image] at hone
  obtain ⟨p, hp, hpone⟩ := hone
  obtain ⟨hp1, hp2, hpne⟩ := mem_orderedDistinctPairs_iff.mp hp
  have hone0 : (1 : ZMod r) ≠ 0 := by
    intro h
    have hr1 : r = 1 := ZMod.one_eq_zero_iff.mp h
    omega
  have hu01 : u 0 ≠ u 1 := hu.ne hone0.symm
  have hD01 : u 1 ∈
      (secondOrderDefectGraph G).neighborFinset (u 0) := by
    rw [huD]
    simp
  have hcommon := card_common_eq_if_secondOrderDefect_of_even
    G hfree hd heven hmin hcard (u 0) (u 1) hu01
  rw [if_pos hD01] at hcommon
  have h0p : G.Adj (u 0) (w p.1) := by
    rw [hblock]
    simpa using hp1
  have h1p : G.Adj (u 1) (w p.1) := by
    rw [hblock]
    have heq : p.1 - 1 = p.2 := by
      apply sub_eq_iff_eq_add.mpr
      have heq' := sub_eq_iff_eq_add.mp hpone
      simpa [add_comm] using heq'
    rw [heq]
    exact hp2
  have hpcommon : w p.1 ∈
      G.neighborFinset (u 0) ∩ G.neighborFinset (u 1) := by
    simp [h0p, h1p]
  have hempty := Finset.card_eq_zero.mp hcommon
  rw [hempty] at hpcommon
  simp at hpcommon

/-- At the minimum-layer equality, the anonymous two-hole set is canonically
the pair of defect-cycle steps `{1,-1}`. -/
theorem unusedOrderedDifferences_eq_one_negOne_of_secondOrder_cycleBlocks
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr3 : 3 ≤ r)
    (u : ZMod r → V) (w : K → ZMod r → V)
    (hu : Function.Injective u)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)})
    (hw : ∀ k, Function.Injective (w k))
    (hwsep : ∀ {k l : K}, k ≠ l → ∀ x y, w k x ≠ w l y)
    (A : K → Finset (ZMod r))
    (hblock : ∀ k x z, G.Adj (u x) (w k z) ↔ z - x ∈ A k)
    (hexcess : (∑ k, (A k).card * ((A k).card - 1)) = r - 3) :
    unusedOrderedDifferences A = {1, -1} := by
  have htwo : (unusedOrderedDifferences A).card = 2 := by
    apply card_unused_orderedDifferences_eq_two
      G hfree u w hu hw hwsep A hblock
    · simpa using hr3
    · simpa using hexcess
  have hone0 : (1 : ZMod r) ≠ 0 := by
    intro h
    have hr1 : r = 1 := ZMod.one_eq_zero_iff.mp h
    omega
  have hone : (1 : ZMod r) ∈ unusedOrderedDifferences A := by
    simp only [unusedOrderedDifferences, Finset.mem_sdiff, Finset.mem_erase,
      Finset.mem_univ, and_true, Finset.mem_biUnion]
    refine ⟨hone0, ?_⟩
    rintro ⟨k, hk, hkone⟩
    exact one_not_mem_orderedDifferenceSet_of_secondOrder_cycleBlock
      G hfree hd heven hmin hcard hr3 u (w k) hu huD (A k) (hblock k) hkone
  have hnegone : (-1 : ZMod r) ∈ unusedOrderedDifferences A :=
    (neg_mem_unusedOrderedDifferences_iff A 1).mpr hone
  have hminus : (-1 : ZMod r) ≠ 1 := by
    simpa using zmod_sub_one_ne_add_one_of_three_le hr3 (0 : ZMod r)
  have hdistinct : (1 : ZMod r) ≠ -1 := by
    exact hminus.symm
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hone
    · exact hnegone
  · rw [htwo]
    simp [hdistinct, hminus]

/-- Every diagonal quotient entry of an equal odd-cycle terminal layer is at
most two.  In the circulant branch this is the inverse-pair Sidon bound; in
the reverse-circulant branch looplessness forces the entire self-block to
vanish. -/
theorem secondOrder_equalOddCycleComponent_diagonal_le_two
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr3 : 3 ≤ r) (hrOdd : Odd r)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (u : ZMod r → V) (hu : Function.Injective u)
    (huRange : Set.range u = c.supp)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)}) :
    componentQuotientMatrix G (secondOrderDefectGraph G) c c ≤ 2 := by
  let D := secondOrderDefectGraph G
  let B : Matrix (ZMod r) (ZMod r) ℤ :=
    fun x y ↦ G.adjMatrix ℤ (u x) (u y)
  have hcommZ := adjMatrix_comm_secondOrderDefect_of_even
    G hfree hd heven hmin hcard
  have hOrient := graph_equalOddCycleBlock_orientation
    hr3 hrOdd G D u u hu hu hcommZ huD huD
  have hu0c : u 0 ∈ c.supp := by
    rw [← huRange]
    exact ⟨0, rfl⟩
  have hQ := componentQuotientMatrix_apply_eq G D 2
    (secondOrderDefectGraph_degree_eq_two G hfree hd heven hmin hcard)
    (adjMatrix_comm_secondOrderDefect_of_even_real
      G hfree hd heven hmin hcard) c c hu0c
  rcases hOrient with htrans | hreverse
  · obtain ⟨A, hA⟩ :=
      exists_connectionSet_of_translationInvariantBlock G u u htrans
    have hAle : A.card ≤ 2 :=
      card_connectionSet_le_two_of_c4Free_self_circulantBlock
        G hfree u hu A hA
    rw [hQ]
    have heq : componentNeighborFinset G D c (u 0) = A.image u := by
      ext y
      constructor
      · intro hy
        have hydata : G.Adj (u 0) y ∧ y ∈ c.supp := by
          simpa [componentNeighborFinset, SimpleGraph.mem_neighborFinset,
            and_comm] using hy
        have hyrange : y ∈ Set.range u := by simpa [huRange] using hydata.2
        obtain ⟨z, rfl⟩ := hyrange
        have hzA : z ∈ A := by
          simpa using (hA 0 z).mp hydata.1
        exact Finset.mem_image.mpr ⟨z, hzA, rfl⟩
      · intro hy
        obtain ⟨z, hzA, rfl⟩ := Finset.mem_image.mp hy
        have hzc : u z ∈ c.supp := by
          rw [← huRange]
          exact ⟨z, rfl⟩
        have hAdj : G.Adj (u 0) (u z) := by
          rw [hA]
          simpa using hzA
        have hzmk : D.connectedComponentMk (u z) = c :=
          (SimpleGraph.ConnectedComponent.mem_supp_iff c (u z)).mp hzc
        simp [componentNeighborFinset, hAdj, hzmk]
    rw [heq, Finset.card_image_iff.mpr]
    · exact hAle
    · intro x hx y hy hxy
      exact hu hxy
  · have hzero : ∀ x y, B x y = 0 :=
      oddCycle_reverseTranslationInvariant_zero_of_diagonal_zero
        hrOdd B (by simpa only [B] using hreverse) (by
          intro z
          simp [B, SimpleGraph.adjMatrix_apply])
    rw [hQ]
    have hempty : componentNeighborFinset G D c (u 0) = ∅ := by
      ext y
      simp only [Finset.notMem_empty, iff_false]
      intro hy
      have hydata : G.Adj (u 0) y ∧ y ∈ c.supp := by
        simpa [componentNeighborFinset, SimpleGraph.mem_neighborFinset,
          and_comm] using hy
      have hyrange : y ∈ Set.range u := by simpa [huRange] using hydata.2
      obtain ⟨z, rfl⟩ := hyrange
      have hz := hzero 0 z
      simp [B, SimpleGraph.adjMatrix_apply, hydata.1] at hz
    simp [hempty]

end

end Erdos85
