import Proofs.Erdos85BinaryCycleIntertwiner

/-!
# The unique-intermediate Sidon obstruction

This file supplies the additive-combinatorial bridge behind the
unique-intermediate obstruction.  If two finite connection sets uniquely
factor a finite additive group, their nonzero ordered-difference sets are
disjoint.  If both connection sets are Sidon, counting these differences
contradicts the arithmetic lemma in `Erdos85BinaryCycleIntertwiner`.
-/

namespace Erdos85

section

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [AddCommGroup Z]

/-- Extract the finite connection set of a translation-invariant graph
block. -/
theorem exists_connectionSet_of_translationInvariantBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} [NeZero r]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (u w : ZMod r → V)
    (htrans : ∀ x z,
      G.adjMatrix ℤ (u (x + 1)) (w (z + 1)) =
        G.adjMatrix ℤ (u x) (w z)) :
    ∃ A : Finset (ZMod r), ∀ x z, G.Adj (u x) (w z) ↔ z - x ∈ A := by
  let B : Matrix (ZMod r) (ZMod r) ℤ := fun x z ↦ G.adjMatrix ℤ (u x) (w z)
  let A : Finset (ZMod r) := Finset.univ.filter fun a ↦ G.Adj (u 0) (w a)
  refine ⟨A, ?_⟩
  intro x z
  have heq : B x z = B 0 (z - x) :=
    translationInvariant_eq_of_sub_eq B (by simpa only [B] using htrans) (by ring)
  simp only [B, SimpleGraph.adjMatrix_apply] at heq
  dsimp only [A]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hxz : G.Adj (u x) (w z) <;>
    by_cases h0 : G.Adj (u 0) (w (z - x)) <;> simp_all

/-- Ordered pairs of distinct elements of a finite connection set. -/
def orderedDistinctPairs (A : Finset Z) : Finset (Z × Z) :=
  (A ×ˢ A).filter fun p ↦ p.1 ≠ p.2

/-- The ordered nonzero differences made by a finite connection set. -/
def orderedDifferenceSet (A : Finset Z) : Finset Z :=
  (orderedDistinctPairs A).image fun p ↦ p.1 - p.2

theorem mem_orderedDistinctPairs_iff {A : Finset Z} {p : Z × Z} :
    p ∈ orderedDistinctPairs A ↔ p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≠ p.2 := by
  simp [orderedDistinctPairs, and_assoc]

theorem zero_not_mem_orderedDifferenceSet (A : Finset Z) :
    0 ∉ orderedDifferenceSet A := by
  simp only [orderedDifferenceSet, Finset.mem_image]
  rintro ⟨p, hp, hzero⟩
  have hpne : p.1 ≠ p.2 := (mem_orderedDistinctPairs_iff.mp hp).2.2
  exact hpne (sub_eq_zero.mp hzero)

/-- A convenient formulation of the Sidon property: the ordered difference
map is injective away from the diagonal. -/
def IsOrderedSidon (A : Finset Z) : Prop :=
  Set.InjOn (fun p : Z × Z ↦ p.1 - p.2) ↑(orderedDistinctPairs A)

theorem card_orderedDistinctPairs (A : Finset Z) :
    (orderedDistinctPairs A).card = A.card * (A.card - 1) := by
  classical
  unfold orderedDistinctPairs
  have hcount : ((A ×ˢ A).filter fun p : Z × Z ↦ p.1 = p.2).card = A.card := by
    have hdiag : ((A ×ˢ A).filter fun p : Z × Z ↦ p.1 = p.2) =
        A.image fun a ↦ (a, a) := by
      ext p
      constructor
      · intro hp
        have hp' : p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 = p.2 := by
          have ht : (p.1 ∈ A ∧ p.2 ∈ A) ∧ p.1 = p.2 := by simpa using hp
          exact ⟨ht.1.1, ht.1.2, ht.2⟩
        apply Finset.mem_image.mpr
        exact ⟨p.1, hp'.1, Prod.ext rfl hp'.2.2⟩
      · rintro hp
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
        simp [ha]
    rw [hdiag, Finset.card_image_iff.mpr]
    intro a _ b _ hab
    exact congrArg Prod.fst hab
  have hpartition :
      (A ×ˢ A).filter (fun p : Z × Z ↦ p.1 ≠ p.2) =
        (A ×ˢ A) \ ((A ×ˢ A).filter fun p : Z × Z ↦ p.1 = p.2) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff, not_and, not_not]
    tauto
  rw [hpartition,
    Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
    Finset.card_product, hcount]
  rw [Nat.mul_sub_left_distrib]
  simp

theorem card_orderedDifferenceSet_of_sidon {A : Finset Z}
    (hA : IsOrderedSidon A) :
    (orderedDifferenceSet A).card = A.card * (A.card - 1) := by
  rw [orderedDifferenceSet, Finset.card_image_iff.mpr]
  · exact card_orderedDistinctPairs A
  · intro p hp q hq hpq
    exact hA (by simpa using hp) (by simpa using hq) hpq

/-- A translation-invariant binary block of a `C4`-free graph has Sidon
connection support.  This is the graph-facing source of the Sidon hypotheses
used below. -/
theorem isOrderedSidon_of_c4Free_circulantBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (u w : Z → V) (hu : Function.Injective u) (hw : Function.Injective w)
    (A : Finset Z)
    (hblock : ∀ x z, G.Adj (u x) (w z) ↔ z - x ∈ A) :
    IsOrderedSidon A := by
  intro p hp q hq hdiff
  change p.1 - p.2 = q.1 - q.2 at hdiff
  have hp' := mem_orderedDistinctPairs_iff.mp hp
  have hq' := mem_orderedDistinctPairs_iff.mp hq
  by_cases hfirst : p.1 = q.1
  · have hsecond : p.2 = q.2 := by
      rw [hfirst] at hdiff
      exact sub_right_injective hdiff
    exact Prod.ext hfirst hsecond
  let δ : Z := p.1 - q.1
  have hδ : δ ≠ 0 := by
    intro hz
    apply hfirst
    exact sub_eq_zero.mp hz
  have hδsecond : δ = p.2 - q.2 := by
    dsimp [δ]
    apply sub_eq_sub_iff_add_eq_add.mpr
    have hs := sub_eq_sub_iff_add_eq_add.mp hdiff
    simpa [add_comm] using hs
  have hu0δ : u 0 ≠ u δ := by
    intro heq
    exact hδ (hu heq.symm)
  have hw12 : w p.1 ≠ w p.2 := hw.ne hp'.2.2
  have hp10 : G.Adj (w p.1) (u 0) := by
    rw [G.adj_comm, hblock]
    simpa using hp'.1
  have hp20 : G.Adj (w p.2) (u 0) := by
    rw [G.adj_comm, hblock]
    simpa using hp'.2.1
  have hp1δ : G.Adj (w p.1) (u δ) := by
    rw [G.adj_comm, hblock]
    have heq : p.1 - δ = q.1 := by dsimp [δ]; abel
    rw [heq]
    exact hq'.1
  have hp2δ : G.Adj (w p.2) (u δ) := by
    rw [G.adj_comm, hblock]
    have heq : p.2 - δ = q.2 := by rw [hδsecond]; abel
    rw [heq]
    exact hq'.2.1
  exact (hfree (containsC4_of_two_common hu0δ hw12
    hp10 hp1δ hp20 hp2δ)).elim

/-- Uniqueness of all `A+B` representations separates the nonzero ordered
differences of `A` from those of `B`. -/
theorem orderedDifferenceSet_disjoint_of_unique_add
    {A B : Finset Z}
    (hunique : ∀ a₁ ∈ A, ∀ b₂ ∈ B, ∀ a₂ ∈ A, ∀ b₁ ∈ B,
      a₁ + b₂ = a₂ + b₁ → a₁ = a₂ ∧ b₂ = b₁) :
    Disjoint (orderedDifferenceSet A) (orderedDifferenceSet B) := by
  rw [Finset.disjoint_left]
  intro z hzA hzB
  simp only [orderedDifferenceSet, Finset.mem_image] at hzA hzB
  obtain ⟨p, hp, hpz⟩ := hzA
  obtain ⟨q, hq, hqz⟩ := hzB
  obtain ⟨hpA, hpB, hpne⟩ := mem_orderedDistinctPairs_iff.mp hp
  obtain ⟨hqA, hqB, hqne⟩ := mem_orderedDistinctPairs_iff.mp hq
  have hsum : p.1 + q.2 = p.2 + q.1 := by
    have hdiff : p.1 - p.2 = q.1 - q.2 := hpz.trans hqz.symm
    rw [sub_eq_sub_iff_add_eq_add] at hdiff
    simpa [add_comm] using hdiff
  have heq := hunique p.1 hpA q.2 hqB p.2 hpB q.1 hqA hsum
  exact hpne heq.1

/-- Two Sidon connection sets that uniquely factor every element of a finite
additive group cannot exist once the group has order at least three. -/
theorem no_unique_sidon_factor
    {A B : Finset Z}
    (hApos : 0 < A.card) (hBpos : 0 < B.card)
    (hZ : 3 ≤ Fintype.card Z)
    (hprod : A.card * B.card = Fintype.card Z)
    (hAsidon : IsOrderedSidon A) (hBsidon : IsOrderedSidon B)
    (hunique : ∀ a₁ ∈ A, ∀ b₂ ∈ B, ∀ a₂ ∈ A, ∀ b₁ ∈ B,
      a₁ + b₂ = a₂ + b₁ → a₁ = a₂ ∧ b₂ = b₁) : False := by
  have hdisj := orderedDifferenceSet_disjoint_of_unique_add hunique
  have hsub : orderedDifferenceSet A ∪ orderedDifferenceSet B ⊆
      Finset.univ.erase (0 : Z) := by
    intro z hz
    have hz' : z ∈ orderedDifferenceSet A ∨ z ∈ orderedDifferenceSet B := by
      simpa using hz
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ z⟩
    rcases hz' with hzA | hzB
    · exact fun hzero ↦ zero_not_mem_orderedDifferenceSet A (hzero ▸ hzA)
    · exact fun hzero ↦ zero_not_mem_orderedDifferenceSet B (hzero ▸ hzB)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj,
    card_orderedDifferenceSet_of_sidon hAsidon,
    card_orderedDifferenceSet_of_sidon hBsidon,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : Z)), Finset.card_univ] at hcard
  exact no_unique_sidon_factor_degrees hApos hBpos hZ hprod hcard

/-- Representation-level form used by a block product equal to the all-ones
matrix: if every group element has a unique expression `a+b`, the cardinal
product and collision-uniqueness hypotheses of `no_unique_sidon_factor`
follow automatically. -/
theorem no_unique_sidon_factor_of_unique_pair_sums
    {A B : Finset Z}
    (hZ : 3 ≤ Fintype.card Z)
    (hAsidon : IsOrderedSidon A) (hBsidon : IsOrderedSidon B)
    (hrep : ∀ t : Z, ∃! p : A × B, (p.1.1 : Z) + p.2.1 = t) : False := by
  let f : A × B → Z := fun p ↦ (p.1.1 : Z) + p.2.1
  have hfbij : Function.Bijective f := by
    constructor
    · intro p q hpq
      have hu := hrep (f p)
      exact hu.unique (by rfl) (by simpa [f] using hpq.symm)
    · intro t
      obtain ⟨p, hp, _⟩ := hrep t
      exact ⟨p, hp⟩
  let e : (A × B) ≃ Z := Equiv.ofBijective f hfbij
  have hprod : A.card * B.card = Fintype.card Z := by
    have hc := Fintype.card_congr e
    simpa only [Fintype.card_prod, Fintype.card_coe] using hc
  have hApos : 0 < A.card := by
    obtain ⟨p, _, _⟩ := hrep 0
    exact Finset.card_pos.mpr ⟨p.1.1, p.1.2⟩
  have hBpos : 0 < B.card := by
    obtain ⟨p, _, _⟩ := hrep 0
    exact Finset.card_pos.mpr ⟨p.2.1, p.2.2⟩
  apply no_unique_sidon_factor hApos hBpos hZ hprod hAsidon hBsidon
  intro a₁ ha₁ b₂ hb₂ a₂ ha₂ b₁ hb₁ hsum
  let p : A × B := (⟨a₁, ha₁⟩, ⟨b₂, hb₂⟩)
  let q : A × B := (⟨a₂, ha₂⟩, ⟨b₁, hb₁⟩)
  have hu := hrep (a₁ + b₂)
  have hp : (p.1.1 : Z) + p.2.1 = a₁ + b₂ := by rfl
  have hq : (q.1.1 : Z) + q.2.1 = a₁ + b₂ := by simpa [q] using hsum.symm
  have hpq : p = q := hu.unique hp hq
  exact ⟨congrArg (fun x : A × B ↦ x.1.1) hpq,
    congrArg (fun x : A × B ↦ x.2.1) hpq⟩

/-- A convolution count equal to one is exactly unique additive
representation.  Matrix multiplication of binary circulant blocks supplies
the displayed filtered-cardinality hypothesis entrywise. -/
theorem unique_pair_sums_of_convolution_card_eq_one
    {A B : Finset Z}
    (hconv : ∀ t : Z,
      ((A ×ˢ B).filter fun p : Z × Z ↦ p.1 + p.2 = t).card = 1) :
    ∀ t : Z, ∃! p : A × B, (p.1.1 : Z) + p.2.1 = t := by
  intro t
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp (hconv t)
  have hqmem : q ∈ (A ×ˢ B).filter fun p : Z × Z ↦ p.1 + p.2 = t := by
    rw [hq]
    simp
  have hqdata : q.1 ∈ A ∧ q.2 ∈ B ∧ q.1 + q.2 = t := by
    have ht : (q.1 ∈ A ∧ q.2 ∈ B) ∧ q.1 + q.2 = t := by simpa using hqmem
    exact ⟨ht.1.1, ht.1.2, ht.2⟩
  let qq : A × B := (⟨q.1, hqdata.1⟩, ⟨q.2, hqdata.2.1⟩)
  refine ⟨qq, hqdata.2.2, ?_⟩
  intro p hp
  apply Prod.ext <;> apply Subtype.ext
  · have hpmem : ((p.1.1 : Z), (p.2.1 : Z)) ∈
        (A ×ˢ B).filter fun s : Z × Z ↦ s.1 + s.2 = t := by
      simp [p.1.2, p.2.2, hp]
    rw [hq] at hpmem
    simpa [qq] using congrArg Prod.fst (Finset.mem_singleton.mp hpmem)
  · have hpmem : ((p.1.1 : Z), (p.2.1 : Z)) ∈
        (A ×ˢ B).filter fun s : Z × Z ↦ s.1 + s.2 = t := by
      simp [p.1.2, p.2.2, hp]
    rw [hq] at hpmem
    simpa [qq] using congrArg Prod.snd (Finset.mem_singleton.mp hpmem)

/-- Graph-facing unique-intermediate obstruction for two circulant blocks.
The two block supports cannot compose with a unique intermediate coordinate
for every source--target displacement in a `C4`-free graph. -/
theorem no_unique_intermediate_circulant_blocks
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (u w v : Z → V)
    (hu : Function.Injective u) (hw : Function.Injective w)
    (hv : Function.Injective v)
    (A B : Finset Z)
    (hAblock : ∀ x z, G.Adj (u x) (w z) ↔ z - x ∈ A)
    (hBblock : ∀ x z, G.Adj (w x) (v z) ↔ z - x ∈ B)
    (hZ : 3 ≤ Fintype.card Z)
    (hrep : ∀ t : Z, ∃! p : A × B, (p.1.1 : Z) + p.2.1 = t) : False := by
  exact no_unique_sidon_factor_of_unique_pair_sums hZ
    (isOrderedSidon_of_c4Free_circulantBlock G hfree u w hu hw A hAblock)
    (isOrderedSidon_of_c4Free_circulantBlock G hfree w v hw hv B hBblock)
    hrep

/-- Vertex-level form: two circulant blocks in a `C4`-free graph cannot give
exactly one middle coordinate for every ordered source--target pair.  This is
the form produced directly by the off-diagonal square identity. -/
theorem no_unique_middle_circulant_blocks
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (u w v : Z → V)
    (hu : Function.Injective u) (hw : Function.Injective w)
    (hv : Function.Injective v)
    (A B : Finset Z)
    (hAblock : ∀ x z, G.Adj (u x) (w z) ↔ z - x ∈ A)
    (hBblock : ∀ x z, G.Adj (w x) (v z) ↔ z - x ∈ B)
    (hZ : 3 ≤ Fintype.card Z)
    (hmiddle : ∀ x y : Z, ∃! z : Z,
      G.Adj (u x) (w z) ∧ G.Adj (w z) (v y)) : False := by
  apply no_unique_intermediate_circulant_blocks G hfree u w v hu hw hv
    A B hAblock hBblock hZ
  intro t
  obtain ⟨z, hz, hzuniq⟩ := hmiddle 0 t
  have hzA : z ∈ A := by simpa using (hAblock 0 z).mp hz.1
  have htzB : t - z ∈ B := (hBblock z t).mp hz.2
  let p : A × B := (⟨z, hzA⟩, ⟨t - z, htzB⟩)
  refine ⟨p, ?_, ?_⟩
  · dsimp [p]
    abel
  · intro q hq
    have hqa : G.Adj (u 0) (w q.1.1) := by
      rw [hAblock]
      simpa using q.1.2
    have hqb : G.Adj (w q.1.1) (v t) := by
      rw [hBblock]
      have heq : t - q.1.1 = q.2.1 := by
        have := hq
        change (q.1.1 : Z) + q.2.1 = t at this
        apply sub_eq_iff_eq_add.mpr
        simpa [add_comm] using this.symm
      rw [heq]
      exact q.2.2
    have hqz : q.1.1 = z := hzuniq q.1.1 ⟨hqa, hqb⟩
    apply Prod.ext <;> apply Subtype.ext
    · exact hqz
    · dsimp [p]
      have := hq
      change (q.1.1 : Z) + q.2.1 = t at this
      rw [hqz] at this
      apply eq_sub_iff_add_eq.mpr
      simpa [add_comm] using this

/-- Counted-convolution version of the graph-facing obstruction, matching
the entrywise statement that the product of the two binary blocks is `J`. -/
theorem no_circulant_block_convolution_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (u w v : Z → V)
    (hu : Function.Injective u) (hw : Function.Injective w)
    (hv : Function.Injective v)
    (A B : Finset Z)
    (hAblock : ∀ x z, G.Adj (u x) (w z) ↔ z - x ∈ A)
    (hBblock : ∀ x z, G.Adj (w x) (v z) ↔ z - x ∈ B)
    (hZ : 3 ≤ Fintype.card Z)
    (hconv : ∀ t : Z,
      ((A ×ˢ B).filter fun p : Z × Z ↦ p.1 + p.2 = t).card = 1) : False := by
  apply no_unique_intermediate_circulant_blocks G hfree u w v hu hw hv
    A B hAblock hBblock hZ
  exact unique_pair_sums_of_convolution_card_eq_one hconv

end

end Erdos85
