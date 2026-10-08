import Mathlib.Order.PiLex
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalHighSymmetry

/-! # Row keys and the lex-minimal completion under the high-side symmetry

The *row* of an empty vertex `e` in a canonical H7/T0 completion `H` is its
set of singleton/pair neighbours.  This file proves the graph-level facts
behind the `hsb` symmetry-breaking clauses:

* the high-side action moves the row of every empty vertex by one fixed
  permutation of the 35 outside indices (`sevenHighT0RowSet_highRelabel`);
* an empty vertex has exactly `7 - (empty degree)` outside neighbours
  (`emptyNbr_add_row_card`), with the empty degree read off the semantic mask;
* among all completions with a given mask there is one whose vector of row
  keys is lexicographically minimal (`exists_rowKeyMinimal`); no high-side
  relabeling lowers it.  No group law is needed: the minimum is taken over
  *all* completions of the cube, and relabelings stay inside that set;
* hence a group element that fixes the keys of rows `0..k-1` and strictly
  lowers the key of row `k` refutes "rows `0..k` are exactly these lists" for
  the minimal completion (`sevenHighT0HsbWitness_excludes`).

The weight function is arbitrary here; `...HsbSound` instantiates it with the
DIMACS-order weight of the generator.
-/

namespace Erdos85

open SimpleGraph

/-- The 35 singleton/pair low indices. -/
abbrev SevenHighT0OutsideIndex := (Fin 7 × Fin 2) ⊕ SevenHighT0PairIndex

abbrev sevenHighT0EmptyVertex (e : Fin 7) : SevenHighT0CanonicalIndex :=
  Sum.inr (Sum.inl e)

abbrev sevenHighT0OutsideVertex (x : SevenHighT0OutsideIndex) :
    SevenHighT0CanonicalIndex :=
  Sum.inr (Sum.inr x)

noncomputable section

/-- The high-side action on the outside indices. -/
def sevenHighT0OutsideHighPerm (σ : Equiv.Perm (Fin 7))
    (flip : Fin 7 → Equiv.Perm (Fin 2)) :
    SevenHighT0OutsideIndex ≃ SevenHighT0OutsideIndex :=
  Equiv.sumCongr (Equiv.prodShear σ flip) (sevenHighT0PairIndexPerm σ)

theorem sevenHighT0CanonicalHighRelabel_empty_outside_adj
    (σ : Equiv.Perm (Fin 7)) (flip : Fin 7 → Equiv.Perm (Fin 2))
    (H : SimpleGraph SevenHighT0CanonicalIndex) (e : Fin 7)
    (x : SevenHighT0OutsideIndex) :
    (sevenHighT0CanonicalHighRelabel σ flip H).Adj
        (sevenHighT0EmptyVertex e)
        (sevenHighT0OutsideVertex (sevenHighT0OutsideHighPerm σ flip x)) ↔
      H.Adj (sevenHighT0EmptyVertex e) (sevenHighT0OutsideVertex x) := by
  have hsymm : (sevenHighT0OutsideHighPerm σ flip).symm
      (sevenHighT0OutsideHighPerm σ flip x) = x :=
    Equiv.symm_apply_apply _ _
  have hadj : (sevenHighT0CanonicalHighRelabel σ flip H).Adj
        (sevenHighT0EmptyVertex e)
        (sevenHighT0OutsideVertex (sevenHighT0OutsideHighPerm σ flip x)) ↔
      H.Adj (Sum.inr (Sum.inl e))
        (Sum.inr (Sum.inr ((sevenHighT0OutsideHighPerm σ flip).symm
          (sevenHighT0OutsideHighPerm σ flip x)))) := Iff.rfl
  rw [hadj, hsymm]

open Classical in
/-- Outside neighbours of an empty vertex. -/
def sevenHighT0RowSet (H : SimpleGraph SevenHighT0CanonicalIndex)
    (e : Fin 7) : Finset SevenHighT0OutsideIndex :=
  Finset.univ.filter fun x =>
    H.Adj (sevenHighT0EmptyVertex e) (sevenHighT0OutsideVertex x)

open Classical in
/-- Empty neighbours of an empty vertex. -/
def sevenHighT0EmptyNbrSet (H : SimpleGraph SevenHighT0CanonicalIndex)
    (e : Fin 7) : Finset (Fin 7) :=
  Finset.univ.filter fun f =>
    H.Adj (sevenHighT0EmptyVertex e) (sevenHighT0EmptyVertex f)

/-- Weighted key of a row. -/
def sevenHighT0RowKey (w : SevenHighT0OutsideIndex → ℕ)
    (H : SimpleGraph SevenHighT0CanonicalIndex) (e : Fin 7) : ℕ :=
  ∑ x ∈ sevenHighT0RowSet H e, w x

theorem sevenHighT0RowSet_highRelabel
    (σ : Equiv.Perm (Fin 7)) (flip : Fin 7 → Equiv.Perm (Fin 2))
    (H : SimpleGraph SevenHighT0CanonicalIndex) (e : Fin 7) :
    sevenHighT0RowSet (sevenHighT0CanonicalHighRelabel σ flip H) e =
      (sevenHighT0RowSet H e).map
        (sevenHighT0OutsideHighPerm σ flip).toEmbedding := by
  ext y
  rw [Finset.mem_map_equiv]
  have h := sevenHighT0CanonicalHighRelabel_empty_outside_adj σ flip H e
    ((sevenHighT0OutsideHighPerm σ flip).symm y)
  rw [Equiv.apply_symm_apply] at h
  unfold sevenHighT0RowSet
  rw [Finset.mem_filter, Finset.mem_filter]
  exact ⟨fun hy => ⟨Finset.mem_univ _, h.mp hy.2⟩,
    fun hy => ⟨Finset.mem_univ _, h.mpr hy.2⟩⟩

theorem sevenHighT0RowKey_highRelabel
    (w : SevenHighT0OutsideIndex → ℕ)
    (σ : Equiv.Perm (Fin 7)) (flip : Fin 7 → Equiv.Perm (Fin 2))
    (H : SimpleGraph SevenHighT0CanonicalIndex) (e : Fin 7) :
    sevenHighT0RowKey w (sevenHighT0CanonicalHighRelabel σ flip H) e =
      sevenHighT0RowKey
        (fun x => w (sevenHighT0OutsideHighPerm σ flip x)) H e := by
  unfold sevenHighT0RowKey
  rw [sevenHighT0RowSet_highRelabel]
  exact Finset.sum_map _ _ _

open Classical in
theorem sevenHighT0LowNbr_card_split
    (H : SimpleGraph SevenHighT0CanonicalIndex) (e : Fin 7) :
    (Finset.univ.filter fun i : SevenHighT0LowIndex =>
        H.Adj (sevenHighT0EmptyVertex e) (Sum.inr i)).card =
      (sevenHighT0EmptyNbrSet H e).card + (sevenHighT0RowSet H e).card := by
  unfold sevenHighT0EmptyNbrSet sevenHighT0RowSet
  simp only [Finset.card_filter, Fintype.sum_sum_type]

/-- Row cardinality: the low-degree equation of an empty vertex splits into
empty neighbours and outside neighbours. -/
theorem SevenHighT0CanonicalCompletionSemantics.emptyNbr_add_row_card
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (hH : SevenHighT0CanonicalCompletionSemantics H) (e : Fin 7) :
    (sevenHighT0EmptyNbrSet H e).card + (sevenHighT0RowSet H e).card = 7 := by
  have hdeg : ((H.comap Sum.inr).neighborFinset (Sum.inl e)).card + 0 = 7 :=
    hH.low_degree (Sum.inl e)
  have hcard : ((H.comap Sum.inr).neighborFinset (Sum.inl e)).card =
      (sevenHighT0EmptyNbrSet H e).card + (sevenHighT0RowSet H e).card := by
    rw [← sevenHighT0LowNbr_card_split]
    congr 1
    ext i
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
    exact ⟨fun h => ⟨Finset.mem_univ _, h⟩, fun h => h.2⟩
  omega

/-- The empty neighbours are read off the semantic mask. -/
theorem sevenHighT0EmptyNbrSet_eq_mask
    (H : SimpleGraph SevenHighT0CanonicalIndex) [DecidableRel H.Adj]
    (e : Fin 7) :
    sevenHighT0EmptyNbrSet H e =
      Finset.univ.filter fun f : Fin 7 =>
        sevenHighT0CanonicalEmptySemanticMaskAdj
          (sevenHighT0CanonicalEmptySemanticMask H) e.1 f.1 = true := by
  ext f
  have h := sevenHighT0CanonicalEmptySemanticMaskAdj_eq H e f
  unfold sevenHighT0EmptyNbrSet
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · intro hadj
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [h]
    exact decide_eq_true hadj.2
  · intro hm
    refine ⟨Finset.mem_univ _, ?_⟩
    have hm2 := hm.2
    rw [h] at hm2
    exact of_decide_eq_true hm2

/-- Among the completions with the mask of `H` there is one that no
high-side relabeling makes lexicographically smaller in its row keys. -/
theorem SevenHighT0CanonicalCompletionSemantics.exists_rowKeyMinimal
    (w : SevenHighT0OutsideIndex → ℕ)
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (hH : SevenHighT0CanonicalCompletionSemantics H) :
    ∃ (H' : SimpleGraph SevenHighT0CanonicalIndex)
      (inst : DecidableRel H'.Adj),
      @SevenHighT0CanonicalCompletionSemantics H' inst ∧
      @sevenHighT0CanonicalEmptySemanticMask H' inst =
        sevenHighT0CanonicalEmptySemanticMask H ∧
      ∀ (σ : Equiv.Perm (Fin 7)) (flip : Fin 7 → Equiv.Perm (Fin 2))
        (k : Fin 7),
        (∀ j, j < k →
          sevenHighT0RowKey w (sevenHighT0CanonicalHighRelabel σ flip H') j =
            sevenHighT0RowKey w H' j) →
        ¬ sevenHighT0RowKey w (sevenHighT0CanonicalHighRelabel σ flip H') k <
            sevenHighT0RowKey w H' k := by
  let S : Set (SimpleGraph SevenHighT0CanonicalIndex) :=
    {G | ∃ inst : DecidableRel G.Adj,
      @SevenHighT0CanonicalCompletionSemantics G inst ∧
      @sevenHighT0CanonicalEmptySemanticMask G inst =
        sevenHighT0CanonicalEmptySemanticMask H}
  have hS : S.Nonempty := ⟨H, ‹DecidableRel H.Adj›, hH, rfl⟩
  let f : SimpleGraph SevenHighT0CanonicalIndex → Lex (Fin 7 → ℕ) :=
    fun G => toLex (fun e => sevenHighT0RowKey w G e)
  obtain ⟨H', ⟨inst, h1, h2⟩, hmin⟩ :=
    Set.exists_min_image S f (Set.toFinite S) hS
  refine ⟨H', inst, h1, h2, ?_⟩
  intro σ flip k hfix hlt
  have hmem : sevenHighT0CanonicalHighRelabel σ flip H' ∈ S :=
    ⟨@sevenHighT0CanonicalHighRelabel_adj_decidable σ flip H' inst,
      @SevenHighT0CanonicalCompletionSemantics.highRelabel H' inst h1 σ flip,
      (@sevenHighT0CanonicalEmptySemanticMask_highRelabel
        H' inst σ flip).trans h2⟩
  have hle : f H' ≤ f (sevenHighT0CanonicalHighRelabel σ flip H') :=
    hmin _ hmem
  have hlex : f (sevenHighT0CanonicalHighRelabel σ flip H') < f H' :=
    Exists.intro k ⟨hfix, hlt⟩
  exact not_le.mpr hlex hle

/-- A group element that fixes the keys of the rows before `k` and strictly
lowers the key of row `k` shows that the minimal completion does not have
exactly the rows `L 0, …, L k`. -/
theorem sevenHighT0HsbWitness_excludes
    (w : SevenHighT0OutsideIndex → ℕ) (mask : ℕ)
    {H' : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H'.Adj]
    (hH' : SevenHighT0CanonicalCompletionSemantics H')
    (hmask : sevenHighT0CanonicalEmptySemanticMask H' = mask)
    (σ : Equiv.Perm (Fin 7)) (flip : Fin 7 → Equiv.Perm (Fin 2))
    (hmin : ∀ k : Fin 7,
      (∀ j, j < k →
        sevenHighT0RowKey w (sevenHighT0CanonicalHighRelabel σ flip H') j =
          sevenHighT0RowKey w H' j) →
      ¬ sevenHighT0RowKey w (sevenHighT0CanonicalHighRelabel σ flip H') k <
          sevenHighT0RowKey w H' k)
    (k : Fin 7) (L : Fin 7 → List SevenHighT0OutsideIndex)
    (hnodup : ∀ j, j ≤ k → (L j).Nodup)
    (hlen : ∀ j, j ≤ k →
      (Finset.univ.filter fun f : Fin 7 =>
        sevenHighT0CanonicalEmptySemanticMaskAdj mask j.1 f.1 = true).card +
          (L j).length = 7)
    (hfix : ∀ j, j < k →
      ((L j).map fun x => w (sevenHighT0OutsideHighPerm σ flip x)).sum =
        ((L j).map w).sum)
    (hlt : ((L k).map fun x => w (sevenHighT0OutsideHighPerm σ flip x)).sum <
        ((L k).map w).sum) :
    ∃ j, j ≤ k ∧ ∃ x ∈ L j,
      ¬ H'.Adj (sevenHighT0EmptyVertex j) (sevenHighT0OutsideVertex x) := by
  by_contra hcon
  have hall : ∀ j, j ≤ k → ∀ x ∈ L j,
      H'.Adj (sevenHighT0EmptyVertex j) (sevenHighT0OutsideVertex x) := by
    intro j hj x hx
    by_contra hx'
    exact hcon ⟨j, hj, x, hx, hx'⟩
  have hrow : ∀ j, j ≤ k → sevenHighT0RowSet H' j = (L j).toFinset := by
    intro j hj
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [List.mem_toFinset] at hx
      unfold sevenHighT0RowSet
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hall j hj x hx⟩
    · rw [List.toFinset_card_of_nodup (hnodup j hj)]
      have h1 := hH'.emptyNbr_add_row_card j
      have h2 := congrArg Finset.card (sevenHighT0EmptyNbrSet_eq_mask H' j)
      rw [hmask] at h2
      have h3 := hlen j hj
      omega
  have hkey : ∀ (w' : SevenHighT0OutsideIndex → ℕ) (j : Fin 7), j ≤ k →
      sevenHighT0RowKey w' H' j = ((L j).map w').sum := by
    intro w' j hj
    unfold sevenHighT0RowKey
    rw [hrow j hj]
    exact List.sum_toFinset w' (hnodup j hj)
  apply hmin k
  · intro j hj
    rw [sevenHighT0RowKey_highRelabel,
      hkey (fun x => w (sevenHighT0OutsideHighPerm σ flip x)) j
        (le_of_lt hj),
      hkey w j (le_of_lt hj)]
    exact hfix j hj
  · rw [sevenHighT0RowKey_highRelabel,
      hkey (fun x => w (sevenHighT0OutsideHighPerm σ flip x)) k (le_refl k),
      hkey w k (le_refl k)]
    exact hlt

end

end Erdos85

#print axioms Erdos85.sevenHighT0RowKey_highRelabel
#print axioms Erdos85.SevenHighT0CanonicalCompletionSemantics.emptyNbr_add_row_card
#print axioms Erdos85.SevenHighT0CanonicalCompletionSemantics.exists_rowKeyMinimal
#print axioms Erdos85.sevenHighT0HsbWitness_excludes
