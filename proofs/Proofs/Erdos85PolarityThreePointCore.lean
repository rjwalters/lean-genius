import Proofs.Erdos85PolarityTwoPointCore

open SimpleGraph
open scoped LinearAlgebra.Projectivization

namespace Erdos85.Polarity
universe u
variable (K : Type u) [Field K] [Finite K] [DecidableEq K]
private noncomputable abbrev P := ℙ K (Fin 3 → K)

noncomputable abbrev threePointCore {a b c : P K} :=
  deleteVertexSetGraph (graph K) {a,b,c}

noncomputable def threePointPairDefect {a b c : P K}
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b)
    (hc : Projectivization.orthogonal c c) (hab : a ≠ b) :
    {v : P K // v ∉ ({a,b,c} : Finset (P K))} :=
  ⟨absolutePairCommonNeighbor K ha hb hab, by
    intro hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm | hm
    · exact (absolutePairCommonNeighbor_spec K ha hb hab).2.2 (by simpa [hm] using ha)
    · exact (absolutePairCommonNeighbor_spec K ha hb hab).2.2 (by simpa [hm] using hb)
    · exact (absolutePairCommonNeighbor_spec K ha hb hab).2.2 (by simpa [hm] using hc)⟩

theorem threePointPairDefect_degree {a b c : P K}
    (h2 : (2 : K) ≠ 0)
    (ha : Projectivization.orthogonal a a)
    (hb : Projectivization.orthogonal b b) (hc : Projectivization.orthogonal c c)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    (threePointCore K).degree (threePointPairDefect K (c := c) ha hb hc hab) =
      Nat.card K - 1 := by
  let x := threePointPairDefect K (c := c) ha hb hc hab
  have hs := degree_deleteVertexSetGraph_add (graph K)
    ({a,b,c} : Finset (P K)) x
  have hxnon : ¬ Projectivization.orthogonal x.1 x.1 := by
    simpa [x, threePointPairDefect] using
      (absolutePairCommonNeighbor_spec K ha hb hab).2.2
  rw [degree_eq_card_add_one_of_not_selfOrthogonal hxnon] at hs
  have hxc := not_adj_absolutePairCommonNeighbor_of_third_absolute K h2
    ha hb hab hc hca hcb
  have hinc : ((graph K).neighborFinset x.1 ∩
      ({a,b,c} : Finset (P K))).card = 2 := by
    have heq : (graph K).neighborFinset x.1 ∩ ({a,b,c} : Finset (P K)) = {a,b} := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hz, rfl | rfl | rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact (hxc (by simpa [x, threePointPairDefect] using hz)).elim
      · rintro (rfl | rfl)
        · exact ⟨by simpa [x, threePointPairDefect] using
            (absolutePairCommonNeighbor_spec K ha hb hab).1.symm, Or.inl rfl⟩
        · exact ⟨by simpa [x, threePointPairDefect] using
            (absolutePairCommonNeighbor_spec K ha hb hab).2.1.symm,
              Or.inr (Or.inl rfl)⟩
    rw [heq]
    simp [hab]
  change (threePointCore K).degree x + _ = Nat.card K + 1 at hs
  change (threePointCore K).degree x = Nat.card K - 1
  rw [hinc] at hs
  have hq := three_le_card_of_two_ne_zero K h2
  omega

end Erdos85.Polarity
