import Proofs.Erdos85ClosedNeighborhoodCutTriangleIdentity

/-!
# Comparing a minimum cut with a one-vertex deletion

Deleting a vertex from a shore replaces its outward boundary edges by its
inward edges.  In a regular graph this gives the exact identity used to cap
every boundary degree of a minimum-cut shore.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Exact change in a regular graph cut after erasing one shore vertex. -/
theorem finsetGraphCutSize_erase_add_two_mul_outDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] {r : ℕ}
    (hreg : ∀ v, D.degree v = r) (S : Finset V) {x : V} (hxS : x ∈ S) :
    finsetGraphCutSize D (S.erase x) +
        2 * (D.neighborFinset x \ S).card =
      finsetGraphCutSize D S + r := by
  classical
  let i := (D.neighborFinset x ∩ S).card
  let o := (D.neighborFinset x \ S).card
  have hdegree : i + o = r := by
    dsimp only [i, o]
    rw [Finset.card_inter_add_card_sdiff,
      D.card_neighborFinset_eq_degree, hreg x]
  have hS : insert x (S.erase x) = S := Finset.insert_erase hxS
  have hpoint : ∀ u ∈ S.erase x,
      (D.neighborFinset u ∩ S).card =
        (D.neighborFinset u ∩ (S.erase x)).card +
          if D.Adj u x then 1 else 0 := by
    intro u hu
    have hrewrite : D.neighborFinset u ∩ S =
        D.neighborFinset u ∩ insert x (S.erase x) := by rw [hS]
    rw [hrewrite, Finset.insert_inter]
    by_cases hux : D.Adj u x
    · have hxN : x ∈ D.neighborFinset u :=
        (D.mem_neighborFinset u x).mpr hux
      simp only [hxN, if_pos]
      have hxnot : x ∉ D.neighborFinset u ∩ S.erase x := by simp
      rw [Finset.card_insert_of_notMem hxnot]
      simp [hux]
    · have hxN : x ∉ D.neighborFinset u := by
        simpa [SimpleGraph.mem_neighborFinset] using hux
      simp [hxN, hux]
  have hindicator :
      (∑ u ∈ S.erase x, if D.Adj u x then 1 else 0) = i := by
    dsimp only [i]
    have hxN : x ∉ D.neighborFinset x := by simp
    calc
      (∑ u ∈ S.erase x, if D.Adj u x then 1 else 0) =
          ((S.erase x).filter fun u => D.Adj u x).card := by
        rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
      _ = (D.neighborFinset x ∩ (S.erase x)).card := by
        congr 1
        ext u
        simp [SimpleGraph.mem_neighborFinset, D.adj_comm, and_comm]
      _ = (D.neighborFinset x ∩ S).card := by
        have hi := Finset.inter_insert_of_notMem
          (s₁ := D.neighborFinset x) (s₂ := S.erase x) hxN
        calc
          _ = (D.neighborFinset x ∩ insert x (S.erase x)).card :=
            congrArg Finset.card hi.symm
          _ = _ := by rw [hS]
  have hinternal :
      (∑ u ∈ S, (D.neighborFinset u ∩ S).card) =
        (∑ u ∈ S.erase x,
          (D.neighborFinset u ∩ (S.erase x)).card) + 2 * i := by
    have hsplit := Finset.sum_erase_add S
      (fun u => (D.neighborFinset u ∩ S).card) hxS
    calc
      (∑ u ∈ S, (D.neighborFinset u ∩ S).card) =
          (D.neighborFinset x ∩ S).card +
            ∑ u ∈ S.erase x, (D.neighborFinset u ∩ S).card := by
        omega
      _ = i + ∑ u ∈ S.erase x,
          ((D.neighborFinset u ∩ (S.erase x)).card +
            if D.Adj u x then 1 else 0) := by
        dsimp only [i]
        congr 1
        apply Finset.sum_congr rfl
        exact hpoint
      _ = (∑ u ∈ S.erase x,
          (D.neighborFinset u ∩ (S.erase x)).card) + 2 * i := by
        rw [Finset.sum_add_distrib, hindicator]
        omega
  have hcutS := finsetGraphCutSize_add_sum_internal_eq_card_mul_of_regular
    D hreg S
  have hcutErase := finsetGraphCutSize_add_sum_internal_eq_card_mul_of_regular
    D hreg (S.erase x)
  have hcardErase : (S.erase x).card + 1 = S.card := by
    rw [Finset.card_erase_of_mem hxS]
    exact Nat.sub_add_cancel (Finset.one_le_card.mpr ⟨x, hxS⟩)
  have hcardMul : (S.erase x).card * r + r = S.card * r := by
    calc
      (S.erase x).card * r + r = ((S.erase x).card + 1) * r := by ring
      _ = S.card * r := by rw [hcardErase]
  dsimp only [i, o] at hdegree
  rw [hinternal] at hcutS
  omega

/-- A minimum-cut shore has outward degree at most half the regular degree,
provided deleting the vertex leaves another shore to which the same lower
cut bound applies. -/
theorem two_mul_outDegree_le_of_minCut_erase
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] {r : ℕ}
    (hreg : ∀ v, D.degree v = r) (S : Finset V) {x : V} (hxS : x ∈ S)
    (hcut : finsetGraphCutSize D S = r)
    (hlowerErase : r ≤ finsetGraphCutSize D (S.erase x)) :
    2 * (D.neighborFinset x \ S).card ≤ r := by
  have hid := finsetGraphCutSize_erase_add_two_mul_outDegree
    D hreg S hxS
  omega

/-- Even-parameter form used by the binary-square minimum-cut argument. -/
theorem outDegree_le_even_sub_two_half_of_minCut_erase
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] {q : ℕ} (hq : 2 ≤ q)
    (hqEven : Even q) (hreg : ∀ v, D.degree v = q - 1)
    (S : Finset V) {x : V} (hxS : x ∈ S)
    (hcut : finsetGraphCutSize D S = q - 1)
    (hlowerErase : q - 1 ≤ finsetGraphCutSize D (S.erase x)) :
    (D.neighborFinset x \ S).card ≤ (q - 2) / 2 := by
  have htwo := two_mul_outDegree_le_of_minCut_erase
    D hreg S hxS hcut hlowerErase
  obtain ⟨m, hm⟩ := hqEven
  omega

#print axioms finsetGraphCutSize_erase_add_two_mul_outDegree
#print axioms two_mul_outDegree_le_of_minCut_erase
#print axioms outDegree_le_even_sub_two_half_of_minCut_erase

end

end Erdos85
