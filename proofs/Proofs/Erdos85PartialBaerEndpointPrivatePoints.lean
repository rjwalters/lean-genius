import Proofs.Erdos85BinarySquareDyadicSignedTerminal

/-!
# Private points in the endpoint partial-Baer design

At the pure endpoint `c = q`, the scalar identities say that `q` exceptional
lines have no triple point and every pair meets once.  This file turns those
counts into a pointwise structure theorem: every exceptional line has one
and only one point belonging to no other exceptional line.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- Points of line `i` which do not occur in its intersection with any other
line of the family. -/
def partialBaerPrivatePoints
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]
    (L : ι → Finset V) (i : ι) : Finset V :=
  L i \ ((Finset.univ.erase i).biUnion fun j => L i ∩ L j)

/-- Pairwise-one intersections and absence of triple points force exactly
one private point on every line when the number and size of the lines are
both `q`. -/
theorem partialBaer_privatePoints_card_eq_one
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]
    {q : ℕ} (L : ι → Finset V)
    (hindex : Fintype.card ι = q)
    (hline : ∀ i, (L i).card = q)
    (hpair : ∀ i j, i ≠ j → (L i ∩ L j).card = 1)
    (htriple : ∀ x i j k, x ∈ L i → x ∈ L j → x ∈ L k →
      i = j ∨ i = k ∨ j = k)
    (i : ι) :
    (partialBaerPrivatePoints L i).card = 1 := by
  let J : Finset ι := Finset.univ.erase i
  let B : ι → Finset V := fun j => L i ∩ L j
  have hdisj : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → Disjoint (B j) (B k) := by
    intro j hj k hk hjk
    rw [Finset.disjoint_left]
    intro x hxj hxk
    have hxj' := Finset.mem_inter.mp hxj
    have hxk' := Finset.mem_inter.mp hxk
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    rcases htriple x i j k hxj'.1 hxj'.2 hxk'.2 with hij | hik | hjkeq
    · exact hji hij.symm
    · exact hki hik.symm
    · exact hjk hjkeq
  have hJcard : J.card = q - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      hindex]
  have hBcard : (J.biUnion B).card = q - 1 := by
    rw [Finset.card_biUnion hdisj]
    calc
      ∑ j ∈ J, (B j).card = ∑ _j ∈ J, 1 := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hpair i j (fun hij => (Finset.mem_erase.mp hj).1 hij.symm)
      _ = J.card := by simp
      _ = q - 1 := hJcard
  have hBsub : J.biUnion B ⊆ L i := by
    apply Finset.biUnion_subset.mpr
    intro j hj
    exact Finset.inter_subset_left
  have hqpos : 0 < q := by
    rw [← hindex]
    exact Fintype.card_pos_iff.mpr ⟨i⟩
  change (L i \ J.biUnion B).card = 1
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hBsub, hline i, hBcard]
  omega

/-- The unique private points form a canonical-size transversal: one may
choose one point from every line, the choices are pairwise distinct, and the
point chosen for a line lies on no other line of the family. -/
theorem exists_injective_partialBaer_privatePoint
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]
    {q : ℕ} (L : ι → Finset V)
    (hindex : Fintype.card ι = q)
    (hline : ∀ i, (L i).card = q)
    (hpair : ∀ i j, i ≠ j → (L i ∩ L j).card = 1)
    (htriple : ∀ x i j k, x ∈ L i → x ∈ L j → x ∈ L k →
      i = j ∨ i = k ∨ j = k) :
    ∃ p : ι → V, Function.Injective p ∧
      ∀ i, p i ∈ L i ∧ ∀ j, j ≠ i → p i ∉ L j := by
  classical
  have hprivate : ∀ i, (partialBaerPrivatePoints L i).card = 1 :=
    partialBaer_privatePoints_card_eq_one L hindex hline hpair htriple
  let p : ι → V := fun i =>
    (Finset.card_pos.mp (by rw [hprivate i]; norm_num)).choose
  have hpPrivate : ∀ i, p i ∈ partialBaerPrivatePoints L i := by
    intro i
    exact (Finset.card_pos.mp (by rw [hprivate i]; norm_num)).choose_spec
  have hp : ∀ i, p i ∈ L i ∧ ∀ j, j ≠ i → p i ∉ L j := by
    intro i
    have hpi := Finset.mem_sdiff.mp (hpPrivate i)
    refine ⟨hpi.1, ?_⟩
    intro j hji hpj
    apply hpi.2
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩, ?_⟩
    exact Finset.mem_inter.mpr ⟨hpi.1, hpj⟩
  refine ⟨p, ?_, hp⟩
  intro i j hpij
  by_contra hij
  exact (hp i).2 j (fun hji => hij hji.symm) (hpij ▸ (hp j).1)

/-- Graph-facing endpoint form.  A family `E` of `q` vertices whose
neighborhood lines have size `q`, meet pairwise once, and have point
replication at most two admits an injective private-neighbor matching.
Moreover the matched point of `i` has `i` as its unique neighbor in `E`. -/
theorem exists_injective_privateNeighbor_of_endpointProfile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (E : Finset V) (hEcard : E.card = q)
    (hline : ∀ i ∈ E, G.degree i = q)
    (hpair : ∀ i ∈ E, ∀ j ∈ E, i ≠ j →
      (G.neighborFinset i ∩ G.neighborFinset j).card = 1)
    (hcap : ∀ x, (G.neighborFinset x ∩ E).card ≤ 2) :
    ∃ p : {i // i ∈ E} → V, Function.Injective p ∧
      ∀ i, G.Adj i.1 (p i) ∧ G.neighborFinset (p i) ∩ E = {i.1} := by
  classical
  let I := {i // i ∈ E}
  let L : I → Finset V := fun i => G.neighborFinset i.1
  have hindex : Fintype.card I = q := by
    simpa [I] using hEcard
  have hline' : ∀ i, (L i).card = q := by
    intro i
    rw [show L i = G.neighborFinset i.1 by rfl,
      G.card_neighborFinset_eq_degree, hline i.1 i.2]
  have hpair' : ∀ i j, i ≠ j → (L i ∩ L j).card = 1 := by
    intro i j hij
    exact hpair i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h))
  have htriple : ∀ x i j k, x ∈ L i → x ∈ L j → x ∈ L k →
      i = j ∨ i = k ∨ j = k := by
    intro x i j k hxi hxj hxk
    by_contra h
    push Not at h
    have hsub : ({i.1, j.1, k.1} : Finset V) ⊆
        G.neighborFinset x ∩ E := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact Finset.mem_inter.mpr ⟨by
          simpa [L, SimpleGraph.mem_neighborFinset, G.adj_comm] using hxi, i.2⟩
      · exact Finset.mem_inter.mpr ⟨by
          simpa [L, SimpleGraph.mem_neighborFinset, G.adj_comm] using hxj, j.2⟩
      · exact Finset.mem_inter.mpr ⟨by
          simpa [L, SimpleGraph.mem_neighborFinset, G.adj_comm] using hxk, k.2⟩
    have hdistinct : i.1 ≠ j.1 ∧ i.1 ≠ k.1 ∧ j.1 ≠ k.1 := by
      exact ⟨fun hij => h.1 (Subtype.ext hij),
        fun hik => h.2.1 (Subtype.ext hik),
        fun hjk => h.2.2 (Subtype.ext hjk)⟩
    have hthree : ({i.1, j.1, k.1} : Finset V).card = 3 := by
      simp [hdistinct.1, hdistinct.2.1, hdistinct.2.2]
    have := Finset.card_le_card hsub
    rw [hthree] at this
    have hcapx := hcap x
    omega
  obtain ⟨p, hpInjective, hp⟩ :=
    exists_injective_partialBaer_privatePoint L hindex hline' hpair' htriple
  refine ⟨p, hpInjective, ?_⟩
  intro i
  have hpi := hp i
  constructor
  · simpa [L, SimpleGraph.mem_neighborFinset] using hpi.1
  · apply Finset.eq_singleton_iff_unique_mem.mpr
    constructor
    · exact Finset.mem_inter.mpr ⟨by
        simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using
          (show G.Adj i.1 (p i) by
            simpa [L, SimpleGraph.mem_neighborFinset] using hpi.1), i.2⟩
    · intro y hy
      have hyE := (Finset.mem_inter.mp hy).2
      by_contra hyi
      have hpNot := hpi.2 ⟨y, hyE⟩ (fun h => hyi (congrArg Subtype.val h))
      apply hpNot
      have hyp := (Finset.mem_inter.mp hy).1
      simpa [L, SimpleGraph.mem_neighborFinset, G.adj_comm] using hyp

/-- Zero-mass form of the graph-facing endpoint theorem.  In a C4-free
graph, absence of defect edges inside `E` makes every two neighborhood lines
meet exactly once.  Vanishing total triple-incidence mass makes every point
lie on at most two of those lines.  These are precisely the two pointwise
hypotheses needed for the private-neighbor matching. -/
theorem exists_injective_privateNeighbor_of_noDefectEdges_noTripleMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {q : ℕ} (E : Finset V) (hEcard : E.card = q)
    (hline : ∀ i ∈ E, G.degree i = q)
    (hDindependent : ∀ i ∈ E, ∀ j ∈ E, i ≠ j →
      ¬(secondOrderDefectGraph G).Adj i j)
    (htripleMass :
      (∑ x : V, ((G.neighborFinset x ∩ E).card).choose 3) = 0) :
    ∃ p : {i // i ∈ E} → V, Function.Injective p ∧
      ∀ i, G.Adj i.1 (p i) ∧ G.neighborFinset (p i) ∩ E = {i.1} := by
  classical
  have hpair : ∀ i ∈ E, ∀ j ∈ E, i ≠ j →
      (G.neighborFinset i ∩ G.neighborFinset j).card = 1 := by
    intro i hi j hj hij
    have hnotMem : j ∉ (secondOrderDefectGraph G).neighborFinset i := by
      simpa [SimpleGraph.mem_neighborFinset] using hDindependent i hi j hj hij
    have hcommon := card_common_eq_if_secondOrderDefect G hfree i j hij
    rw [if_neg hnotMem] at hcommon
    exact hcommon
  have hcap : ∀ x, (G.neighborFinset x ∩ E).card ≤ 2 := by
    intro x
    have hterm : ((G.neighborFinset x ∩ E).card).choose 3 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp
        htripleMass x (Finset.mem_univ x)
    by_contra h
    have hthree : 3 ≤ (G.neighborFinset x ∩ E).card := by omega
    have hpos : 0 < ((G.neighborFinset x ∩ E).card).choose 3 :=
      Nat.choose_pos hthree
    omega
  exact exists_injective_privateNeighbor_of_endpointProfile
    G E hEcard hline hpair hcap

end

end Erdos85

#print axioms Erdos85.partialBaer_privatePoints_card_eq_one
#print axioms Erdos85.exists_injective_partialBaer_privatePoint
#print axioms Erdos85.exists_injective_privateNeighbor_of_endpointProfile
#print axioms Erdos85.exists_injective_privateNeighbor_of_noDefectEdges_noTripleMass
