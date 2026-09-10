import Proofs.Erdos85SevenVertexSubcubicBound

/-! The degree profile in the nine-edge equality case, without enumeration. -/
namespace Erdos85
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sevenVertex_subcubic_nine_edges_degree_ge_two
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 7)
    (hmax : ∀ x, G.degree x ≤ 3) (hedges : G.edgeFinset.card = 9) :
    ∀ x, 2 ≤ G.degree x := by
  classical
  let f := fun x => 3 - G.degree x
  let L := Finset.univ.filter (fun x => G.degree x < 3)
  have hsdeg := G.sum_degrees_eq_twice_card_edges
  rw [hedges] at hsdeg
  have heach : ∀ x, f x + G.degree x = 3 := by
    intro x
    have := hmax x
    dsimp [f]
    omega
  have hs : ∑ x : V, f x = 3 := by
    have hsum : (∑ x : V, f x) + ∑ x : V, G.degree x = 21 := by
      rw [← Finset.sum_add_distrib]
      simp_rw [heach]
      simp [hcard]
    omega
  have hsL : ∑ x ∈ L, f x = 3 := by
    have heq : ∑ x ∈ L, f x = ∑ x : V, f x := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro x _ hx
      have hx3 : G.degree x = 3 := by
        have := hmax x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        omega
      simp [f, hx3]
    omega
  intro v
  by_contra hv
  have hvL : v ∈ L := by simp [L]; omega
  have hvf : 2 ≤ f v := by dsimp [f]; omega
  have hL : L.card ≤ 2 := by
    have hones : (L.erase v).card ≤ ∑ x ∈ L.erase v, f x := by
      calc
        _ = ∑ _x ∈ L.erase v, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum (by
          intro x hx
          have hxL := (Finset.mem_erase.mp hx).2
          have hxdeg : G.degree x < 3 := (Finset.mem_filter.mp hxL).2
          dsimp [f]
          omega)
    have hsum := Finset.sum_erase_add (s := L) f hvL
    have hcardErase := Finset.card_erase_add_one hvL
    omega
  have hLdeg : (∑ x ∈ L, G.degree x) + 3 = 3 * L.card := by
    calc
      _ = (∑ x ∈ L, G.degree x) + ∑ x ∈ L, f x := by rw [hsL]
      _ = ∑ x ∈ L, (f x + G.degree x) := by rw [Finset.sum_add_distrib]; omega
      _ = 3 * L.card := by simp_rw [heach]; simp [Nat.mul_comm]
  let S := L ∪ L.biUnion (fun x => G.neighborFinset x)
  have hScard : S.card ≤ 5 := by
    have h1 := Finset.card_union_le L (L.biUnion (fun x => G.neighborFinset x))
    have h2 := Finset.card_biUnion_le (s := L) (t := fun x => G.neighborFinset x)
    simp only [G.card_neighborFinset_eq_degree] at h2
    dsimp [S]
    omega
  have hsmall : S.card < (Finset.univ : Finset V).card := by simp [hcard]; omega
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  have hxL : x ∉ L := fun hh => hx (Finset.mem_union_left _ hh)
  have hx3 : G.degree x = 3 := by
    have := hmax x
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hxL
    omega
  apply sevenVertex_not_cubic_root_with_cubic_neighbors G hfree hcard x hx3
  intro y hxy
  have hyL : y ∉ L := by
    intro hy
    apply hx
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨y, hy, by simpa using hxy.symm⟩)
  have := hmax y
  simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hyL
  omega

/-- Equality forces three degree-two vertices and four degree-three vertices. -/
theorem sevenVertex_subcubic_nine_edges_degree_counts
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 7)
    (hmax : ∀ x, G.degree x ≤ 3) (hedges : G.edgeFinset.card = 9) :
    (Finset.univ.filter (fun x => G.degree x = 2)).card = 3 ∧
      (Finset.univ.filter (fun x => G.degree x = 3)).card = 4 := by
  classical
  have hmin := sevenVertex_subcubic_nine_edges_degree_ge_two G hfree hcard hmax hedges
  have hcases : ∀ x, G.degree x = 2 ∨ G.degree x = 3 := by
    intro x
    have := hmin x
    have := hmax x
    omega
  have hsum := G.sum_degrees_eq_twice_card_edges
  rw [hedges] at hsum
  have ht : ∀ x, (if G.degree x = 2 then 1 else 0) + G.degree x = 3 := by
    intro x
    rcases hcases x with h | h <;> simp [h]
  have htSum : (Finset.univ.filter (fun x => G.degree x = 2)).card +
      (∑ x : V, G.degree x) = 21 := by
    have hh := congrArg (fun f : V → ℕ => ∑ x, f x) (funext ht)
    simpa [Finset.sum_add_distrib, hcard] using hh
  have hboth : ∀ x, (if G.degree x = 2 then 1 else 0) +
      (if G.degree x = 3 then 1 else 0) = 1 := by
    intro x
    rcases hcases x with h | h <;> simp [h]
  have hcards : (Finset.univ.filter (fun x => G.degree x = 2)).card +
      (Finset.univ.filter (fun x => G.degree x = 3)).card = 7 := by
    have hh := congrArg (fun f : V → ℕ => ∑ x, f x) (funext hboth)
    simpa [Finset.sum_add_distrib, hcard] using hh
  omega
end Erdos85
#print axioms Erdos85.sevenVertex_subcubic_nine_edges_degree_ge_two
#print axioms Erdos85.sevenVertex_subcubic_nine_edges_degree_counts
