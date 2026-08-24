import Proofs.Erdos85DefectCutLaplacianSupport

/-!
# Excluding the dual negative-spike three-separator profile

The signed profile `L_D 1_Y = 1 - A 1_R - A 1_c` with `c ∈ R`
forces every ambient neighbor of `c` out of both separator shores.  A
three-vertex separator then cannot contain all `q ≥ 4` neighbors of `c`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The negative-spike dual pattern-B profile is incompatible with a
q-regular ambient graph when the separator has three vertices. -/
theorem false_of_threeSeparator_negativeSpike_laplacianProfile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    {q : ℕ} (hq : 4 ≤ q) (hreg : ∀ v, G.degree v = q)
    (X Y W R : Finset V) (c : V)
    (hcover : X ∪ Y ∪ W = Finset.univ)
    (hXY : Disjoint X Y)
    (hno : ∀ x ∈ X, ∀ y ∈ Y, ¬ D.Adj x y)
    (hWcard : W.card = 3) (hcR : c ∈ R)
    (hprofile : ∀ v,
      finsetGraphLaplacianIndicator D Y v =
        1 - ((G.neighborFinset v ∩ R).card : ℤ) -
          (if G.Adj v c then 1 else 0)) : False := by
  have hnoX : ∀ v ∈ X, ¬ G.Adj v c := by
    intro v hvX hvc
    have hvY : v ∉ Y := fun hvY =>
      Finset.disjoint_left.mp hXY hvX hvY
    have hDzero : (D.neighborFinset v ∩ Y).card = 0 := by
      apply Finset.card_eq_zero.mpr
      ext y
      constructor
      · intro hy
        obtain ⟨hvy, hyY⟩ := Finset.mem_inter.mp hy
        exact (hno v hvX y hyY
          ((SimpleGraph.mem_neighborFinset D v y).mp hvy)).elim
      · intro hy
        simpa using hy
    have hcMem : c ∈ G.neighborFinset v ∩ R :=
      Finset.mem_inter.mpr ⟨
        (SimpleGraph.mem_neighborFinset G v c).mpr hvc, hcR⟩
    have hcardOne : 1 ≤ (G.neighborFinset v ∩ R).card :=
      Finset.one_le_card.mpr ⟨c, hcMem⟩
    have hcardOneZ : (1 : ℤ) ≤ (G.neighborFinset v ∩ R).card := by
      exact_mod_cast hcardOne
    have hp := hprofile v
    simp only [finsetGraphLaplacianIndicator, hvY, if_false, hDzero,
      Nat.cast_zero, sub_zero, mul_zero, hvc, if_pos] at hp
    omega
  have hnoY : ∀ v ∈ Y, ¬ G.Adj v c := by
    intro v hvY hvc
    have hinterLe : (D.neighborFinset v ∩ Y).card ≤ D.degree v := by
      rw [← D.card_neighborFinset_eq_degree]
      exact Finset.card_le_card Finset.inter_subset_left
    have hcMem : c ∈ G.neighborFinset v ∩ R :=
      Finset.mem_inter.mpr ⟨
        (SimpleGraph.mem_neighborFinset G v c).mpr hvc, hcR⟩
    have hcardOne : 1 ≤ (G.neighborFinset v ∩ R).card :=
      Finset.one_le_card.mpr ⟨c, hcMem⟩
    have hp := hprofile v
    simp only [finsetGraphLaplacianIndicator, hvY, if_true, hvc] at hp
    have hinterCast : ((D.neighborFinset v ∩ Y).card : ℤ) ≤ D.degree v := by
      exact_mod_cast hinterLe
    omega
  have hsub : G.neighborFinset c ⊆ W := by
    intro v hvc
    have hvU : v ∈ X ∪ Y ∪ W := by rw [hcover]; simp
    rcases Finset.mem_union.mp hvU with hvXY | hvW
    · rcases Finset.mem_union.mp hvXY with hvX | hvY
      · exact (hnoX v hvX ((G.adj_comm c v).mp
          ((SimpleGraph.mem_neighborFinset G c v).mp hvc))).elim
      · exact (hnoY v hvY ((G.adj_comm c v).mp
          ((SimpleGraph.mem_neighborFinset G c v).mp hvc))).elim
    · exact hvW
  have hle := Finset.card_le_card hsub
  rw [G.card_neighborFinset_eq_degree, hreg c, hWcard] at hle
  omega

#print axioms false_of_threeSeparator_negativeSpike_laplacianProfile

end

end Erdos85
