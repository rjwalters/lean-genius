import Proofs.Erdos85OrderFortyNineOrdinaryCodePartitionIntersection

/-!
# The two `(2,1^6)` bipartite zero-pattern types

The pairwise open-code intersection grid has a bipartite zero graph with one
degree-two vertex on each shore and every other vertex of degree one.  Its
isomorphism type is decided by one bit: whether the two exceptional vertices
are adjacent.  The adjacent case has a distinguished `P4`; the nonadjacent
case has two distinguished `P3`s.  The remaining vertices have degree one,
so form isolated matching edges.
-/

namespace Erdos85

noncomputable section

def bipartiteRow {L R : Type*} [Fintype R] [DecidableEq R]
    (Z : L → R → Prop) [DecidableRel Z] (a : L) : Finset R :=
  Finset.univ.filter (Z a)

def bipartiteColumn {L R : Type*} [Fintype L] [DecidableEq L]
    (Z : L → R → Prop) [DecidableRel Z] (b : R) : Finset L :=
  Finset.univ.filter (fun a => Z a b)

private theorem finset_eq_singleton_of_card_eq_one_of_mem
    {α : Type*} [DecidableEq α] {S : Finset α} {x : α}
    (hcard : S.card = 1) (hx : x ∈ S) : S = {x} := by
  obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp hcard
  have hxy : x = y := by simpa using hx
  exact Finset.singleton_inj.mpr hxy.symm

private theorem mem_bipartiteRow_iff
    {L R : Type*} [Fintype R] [DecidableEq R]
    (Z : L → R → Prop) [DecidableRel Z] (a : L) (b : R) :
    b ∈ bipartiteRow Z a ↔ Z a b := by simp [bipartiteRow]

private theorem mem_bipartiteColumn_iff
    {L R : Type*} [Fintype L] [DecidableEq L]
    (Z : L → R → Prop) [DecidableRel Z] (a : L) (b : R) :
    a ∈ bipartiteColumn Z b ↔ Z a b := by simp [bipartiteColumn]

/-- Exact two-type classification of a bipartite relation having one
degree-two vertex on either shore and degree one everywhere else. -/
theorem bipartite_degree_two_one_pattern_dichotomy
    {L R : Type*} [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    (Z : L → R → Prop) [DecidableRel Z]
    (a0 : L) (b0 : R)
    (hrow0 : (bipartiteRow Z a0).card = 2)
    (hrow1 : ∀ a, a ≠ a0 → (bipartiteRow Z a).card = 1)
    (hcol0 : (bipartiteColumn Z b0).card = 2)
    (hcol1 : ∀ b, b ≠ b0 → (bipartiteColumn Z b).card = 1) :
    (Z a0 b0 ∧
      ∃ a1 b1,
        a1 ≠ a0 ∧ b1 ≠ b0 ∧
        bipartiteRow Z a0 = {b0, b1} ∧
        bipartiteColumn Z b0 = {a0, a1} ∧
        bipartiteRow Z a1 = {b0} ∧
        bipartiteColumn Z b1 = {a0}) ∨
    (¬ Z a0 b0 ∧
      ∃ a1 a2 b1 b2,
        a1 ≠ a2 ∧ b1 ≠ b2 ∧
        a1 ≠ a0 ∧ a2 ≠ a0 ∧ b1 ≠ b0 ∧ b2 ≠ b0 ∧
        bipartiteRow Z a0 = {b1, b2} ∧
        bipartiteColumn Z b0 = {a1, a2} ∧
        bipartiteRow Z a1 = {b0} ∧
        bipartiteRow Z a2 = {b0} ∧
        bipartiteColumn Z b1 = {a0} ∧
        bipartiteColumn Z b2 = {a0}) := by
  classical
  by_cases hz : Z a0 b0
  · left
    refine ⟨hz, ?_⟩
    obtain ⟨x, y, hxy, hrowPair⟩ := Finset.card_eq_two.mp hrow0
    have hb0 : b0 ∈ bipartiteRow Z a0 := by
      simp [bipartiteRow, hz]
    rw [hrowPair] at hb0
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb0
    rcases hb0 with rfl | rfl
    · obtain ⟨u, v, huv, hcolPair⟩ := Finset.card_eq_two.mp hcol0
      have ha0 : a0 ∈ bipartiteColumn Z b0 := by
        simp [bipartiteColumn, hz]
      rw [hcolPair] at ha0
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha0
      rcases ha0 with rfl | rfl
      · refine ⟨v, y, huv.symm, hxy.symm, hrowPair, hcolPair, ?_, ?_⟩
        · apply finset_eq_singleton_of_card_eq_one_of_mem (hrow1 v huv.symm)
          apply (mem_bipartiteRow_iff Z v b0).mpr
          apply (mem_bipartiteColumn_iff Z v b0).mp
          rw [hcolPair]
          simp
        · apply finset_eq_singleton_of_card_eq_one_of_mem (hcol1 y hxy.symm)
          apply (mem_bipartiteColumn_iff Z a0 y).mpr
          apply (mem_bipartiteRow_iff Z a0 y).mp
          rw [hrowPair]
          simp
      · refine ⟨u, y, huv, hxy.symm, hrowPair, ?_, ?_, ?_⟩
        · simpa [Finset.pair_comm] using hcolPair
        · apply finset_eq_singleton_of_card_eq_one_of_mem (hrow1 u huv)
          apply (mem_bipartiteRow_iff Z u b0).mpr
          apply (mem_bipartiteColumn_iff Z u b0).mp
          rw [hcolPair]
          simp
        · apply finset_eq_singleton_of_card_eq_one_of_mem (hcol1 y hxy.symm)
          apply (mem_bipartiteColumn_iff Z a0 y).mpr
          apply (mem_bipartiteRow_iff Z a0 y).mp
          rw [hrowPair]
          simp
    · obtain ⟨u, v, huv, hcolPair⟩ := Finset.card_eq_two.mp hcol0
      have ha0 : a0 ∈ bipartiteColumn Z b0 := by
        simp [bipartiteColumn, hz]
      rw [hcolPair] at ha0
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha0
      rcases ha0 with rfl | rfl
      · refine ⟨v, x, huv.symm, hxy, ?_, hcolPair, ?_, ?_⟩
        · simpa [Finset.pair_comm] using hrowPair
        · apply finset_eq_singleton_of_card_eq_one_of_mem (hrow1 v huv.symm)
          apply (mem_bipartiteRow_iff Z v b0).mpr
          apply (mem_bipartiteColumn_iff Z v b0).mp
          rw [hcolPair]
          simp
        · apply finset_eq_singleton_of_card_eq_one_of_mem (hcol1 x hxy)
          apply (mem_bipartiteColumn_iff Z a0 x).mpr
          apply (mem_bipartiteRow_iff Z a0 x).mp
          rw [hrowPair]
          simp
      · refine ⟨u, x, huv, hxy, ?_, ?_, ?_, ?_⟩
        · simpa [Finset.pair_comm] using hrowPair
        · simpa [Finset.pair_comm] using hcolPair
        · apply finset_eq_singleton_of_card_eq_one_of_mem (hrow1 u huv)
          apply (mem_bipartiteRow_iff Z u b0).mpr
          apply (mem_bipartiteColumn_iff Z u b0).mp
          rw [hcolPair]
          simp
        · apply finset_eq_singleton_of_card_eq_one_of_mem (hcol1 x hxy)
          apply (mem_bipartiteColumn_iff Z a0 x).mpr
          apply (mem_bipartiteRow_iff Z a0 x).mp
          rw [hrowPair]
          simp
  · right
    refine ⟨hz, ?_⟩
    obtain ⟨b1, b2, hb12, hrowPair⟩ := Finset.card_eq_two.mp hrow0
    obtain ⟨a1, a2, ha12, hcolPair⟩ := Finset.card_eq_two.mp hcol0
    have hb1 : b1 ≠ b0 := by
      intro h
      subst b1
      have : b0 ∈ bipartiteRow Z a0 := by simp [hrowPair]
      simpa [bipartiteRow, hz] using this
    have hb2 : b2 ≠ b0 := by
      intro h
      subst b2
      have : b0 ∈ bipartiteRow Z a0 := by simp [hrowPair]
      simpa [bipartiteRow, hz] using this
    have ha1 : a1 ≠ a0 := by
      intro h
      subst a1
      have : a0 ∈ bipartiteColumn Z b0 := by simp [hcolPair]
      simpa [bipartiteColumn, hz] using this
    have ha2 : a2 ≠ a0 := by
      intro h
      subst a2
      have : a0 ∈ bipartiteColumn Z b0 := by simp [hcolPair]
      simpa [bipartiteColumn, hz] using this
    refine ⟨a1, a2, b1, b2, ha12, hb12, ha1, ha2, hb1, hb2,
      hrowPair, hcolPair, ?_, ?_, ?_, ?_⟩
    · apply finset_eq_singleton_of_card_eq_one_of_mem (hrow1 a1 ha1)
      apply (mem_bipartiteRow_iff Z a1 b0).mpr
      apply (mem_bipartiteColumn_iff Z a1 b0).mp
      rw [hcolPair]
      simp
    · apply finset_eq_singleton_of_card_eq_one_of_mem (hrow1 a2 ha2)
      apply (mem_bipartiteRow_iff Z a2 b0).mpr
      apply (mem_bipartiteColumn_iff Z a2 b0).mp
      rw [hcolPair]
      simp
    · apply finset_eq_singleton_of_card_eq_one_of_mem (hcol1 b1 hb1)
      apply (mem_bipartiteColumn_iff Z a0 b1).mpr
      apply (mem_bipartiteRow_iff Z a0 b1).mp
      rw [hrowPair]
      simp
    · apply finset_eq_singleton_of_card_eq_one_of_mem (hcol1 b2 hb2)
      apply (mem_bipartiteColumn_iff Z a0 b2).mpr
      apply (mem_bipartiteRow_iff Z a0 b2).mp
      rw [hrowPair]
      simp

/-- In the three-code geometry, the two nonshared pairpoints belonging to the
third code have disjoint open neighborhoods.  This is the structural reason
the distinguished entry of every pairwise zero-pattern is present. -/
theorem thirdOpenCode_nonshared_pairpoint_cells_disjoint
    {V : Type*} {H : SimpleGraph V} {C : Set V}
    (hC : IsOpenCode H C) {p q : V}
    (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q) :
    Disjoint (H.neighborSet p) (H.neighborSet q) :=
  hC.disjoint_neighborSet hp hq hpq

/-- Once the distinguished zero is supplied by the third-code lemma, only
the `P4` branch of the `(2,1^6)` classification remains. -/
theorem bipartite_degree_two_one_pattern_forced_P4
    {L R : Type*} [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    (Z : L → R → Prop) [DecidableRel Z]
    (a0 : L) (b0 : R)
    (hrow0 : (bipartiteRow Z a0).card = 2)
    (hrow1 : ∀ a, a ≠ a0 → (bipartiteRow Z a).card = 1)
    (hcol0 : (bipartiteColumn Z b0).card = 2)
    (hcol1 : ∀ b, b ≠ b0 → (bipartiteColumn Z b).card = 1)
    (hz : Z a0 b0) :
    ∃ a1 b1,
      a1 ≠ a0 ∧ b1 ≠ b0 ∧
      bipartiteRow Z a0 = {b0, b1} ∧
      bipartiteColumn Z b0 = {a0, a1} ∧
      bipartiteRow Z a1 = {b0} ∧
      bipartiteColumn Z b1 = {a0} := by
  rcases bipartite_degree_two_one_pattern_dichotomy
    Z a0 b0 hrow0 hrow1 hcol0 hcol1 with hP4 | hP3
  · exact hP4.2
  · exact (hP3.1 hz).elim

end

end Erdos85

#print axioms Erdos85.bipartite_degree_two_one_pattern_dichotomy
#print axioms Erdos85.thirdOpenCode_nonshared_pairpoint_cells_disjoint
#print axioms Erdos85.bipartite_degree_two_one_pattern_forced_P4
