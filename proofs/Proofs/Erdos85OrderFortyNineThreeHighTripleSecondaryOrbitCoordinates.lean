import Proofs.Erdos85ThreeHighSecondaryOrbitCover

namespace Erdos85
open SimpleGraph
noncomputable section

theorem threeHigh_triple_secondary_orbit_coordinates
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z) :
    let N := G.neighborFinset u ∩ threeHighTripleEmptySet G
    let R := threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)
    let m := (G.induce (↑N : Set (Fin 49))).edgeFinset.card
    ∃ k : Fin 21, threeHighSecondaryRepresentative k ∈ threeHighSecondaryDomain ∧
    ∃ l : Fin 8 ≃ (↑R : Set (Fin 49)),
      m = (threeHighSecondaryRepresentative k).1.val + 1 ∧
      (∀ i : Fin 6, (l (Fin.castAdd 2 i)).val ∈ N) ∧
      (∀ a : Fin 2, (l (Fin.natAdd 6 a)).val ∈ R \ N) ∧
      ∀ p q, decide (G.Adj (l p).val (l q).val) = threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative k) p q := by
  classical
  obtain ⟨t, ht, l, hm, hN, hT, hadj⟩ :=
    threeHigh_triple_secondary_domain_cover G hfree hmin hHigh hone z hz hu huz
  obtain ⟨k, ρ, hk, hmatch, hnear, henc⟩ := threeHighSecondaryDomain_orbit_cover t ht
  refine ⟨k, hk, ρ.symm.trans l, ?_, ?_, ?_, ?_⟩
  · simpa only [hmatch] using hm
  · intro i
    have hn : (ρ.symm (Fin.castAdd 2 i)).val < 6 :=
      (hnear _).mp (by simpa only [Equiv.apply_symm_apply, Fin.val_castAdd] using i.isLt)
    let j : Fin 6 := ⟨_, hn⟩
    have hj : Fin.castAdd 2 j = ρ.symm (Fin.castAdd 2 i) := by rfl
    simpa only [Equiv.trans_apply, hj] using hN j
  · intro a
    have hn : ¬ (ρ.symm (Fin.natAdd 6 a)).val < 6 := by
      intro hn
      have he := (hnear _).mpr hn
      simp only [Equiv.apply_symm_apply, Fin.val_natAdd] at he
      omega
    let b : Fin 2 := ⟨(ρ.symm (Fin.natAdd 6 a)).val - 6, by
      have hb := (ρ.symm (Fin.natAdd 6 a)).isLt
      omega⟩
    have hb : Fin.natAdd 6 b = ρ.symm (Fin.natAdd 6 a) := by
      apply Fin.ext
      dsimp [b]
      omega
    simpa only [Equiv.trans_apply, hb] using hT b
  · intro p q
    apply Bool.eq_iff_iff.mpr
    have he := (hadj (ρ.symm p) (ρ.symm q)).trans (henc (ρ.symm p) (ρ.symm q))
    have hp := Bool.eq_iff_iff.mp he
    simpa only [decide_eq_true_eq, Equiv.trans_apply, Equiv.apply_symm_apply] using hp

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_secondary_orbit_coordinates
