import Proofs.Erdos85SRGLocalCycle

/-!
# Closing the finite signing obstruction at order 32
-/

namespace Erdos85

open SimpleGraph

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def firstSix : Finset (Fin 16) := {1, 2, 3, 4, 5, 6}

private theorem getLsbD_007e (y : Fin 16) :
    (0x007e : BitVec 16).getLsbD y = decide (y ∈ firstSix) := by
  native_decide +revert

private theorem degree_comap_equiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (E : Fin 16 ≃ V) (hreg : ∀ x, H.degree x = 6) :
    ∀ i, (H.comap E).degree i = 6 := by
  intro i
  rw [SimpleGraph.degree]
  calc
    ((H.comap E).neighborFinset i).card = (H.neighborFinset (E i)).card := by
      apply Finset.card_bij (fun z _ => E z)
      · intro z hz
        simpa using hz
      · intro a ha b hb hab
        exact E.injective hab
      · intro z hz
        refine ⟨E.symm z, by simpa using hz, by simp⟩
    _ = 6 := by
      change H.degree (E i) = 6
      exact hreg (E i)

private theorem common_comap_equiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (E : Fin 16 ≃ V)
    (hc : ∀ x y, x ≠ y →
      (H.neighborFinset x ∩ H.neighborFinset y).card = 2) :
    ∀ i j, i ≠ j →
      ((H.comap E).neighborFinset i ∩
        (H.comap E).neighborFinset j).card = 2 := by
  intro i j hij
  rw [← hc (E i) (E j) (E.injective.ne hij)]
  apply Finset.card_bij (fun z _ => E z)
  · intro z hz
    simpa using hz
  · intro a ha b hb hab
    exact E.injective hab
  · intro z hz
    refine ⟨E.symm z, by simpa using hz, by simp⟩

/-- The finite statement needed by the order-32 quotient: no negative signing
of an SRG with parameters `(16,6,2,2)` exists. -/
theorem noNegativeSigning1622 : NoNegativeSigning1622 := by
  intro V _ _ H _ s hsign
  rcases hsign with ⟨hcard, hreg, hcommon, hsym, hpath⟩
  by_cases hk4 : HasK4 H
  · rcases hk4 with ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd,
      Aab, Aac, Aad, Abc, Abd, Acd⟩
    exact not_isNegativeSignedSRG1622_of_k4 H s hab hac had hbc hbd hcd
      Aab Aac Aad Abc Abd Acd ⟨hcard, hreg, hcommon, hsym, hpath⟩
  · rcases hasSixCycleNeighborhood_of_srg1622_of_not_hasK4
        H hcard hreg hcommon hk4 with
      ⟨x, u, hu, hxu, A01, A12, A23, A34, A45, A50⟩
    let b : Fin 16 ≃ V := (Fintype.equivFinOfCardEq hcard).symm
    let f : Fin 7 → V := fun i => b ⟨i.val, by omega⟩
    let g : Fin 7 → V := Fin.cases x u
    have hf : Function.Injective f := by
      intro i j hij
      apply Fin.ext
      have he : (⟨i.val, by omega⟩ : Fin 16) = ⟨j.val, by omega⟩ :=
        b.injective hij
      exact congrArg (fun z : Fin 16 => z.val) he
    have hxune (i : Fin 6) : x ≠ u i := by
      intro h
      exact H.loopless.irrefl x (h ▸ hxu i)
    have hg : Function.Injective g := by
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases (fun _ => rfl) (fun j h => ?_) j
        exact (hxune j (by simpa [g] using h)).elim
      · refine Fin.cases
          (fun h => (hxune i (by simpa [g] using h.symm)).elim)
          (fun j h => congrArg Fin.succ (hu (by simpa [g] using h))) j
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
    let E : Fin 16 ≃ V := b.trans σ
    have hE (i : Fin 7) : E ⟨i.val, by omega⟩ = g i := by
      exact hσ i
    let HF : SimpleGraph (Fin 16) := H.comap E
    let sF : Fin 16 → Fin 16 → Prop := fun i j => s (E i) (E j)
    letI : DecidableRel sF := Classical.decRel sF
    have hregF : ∀ i, HF.degree i = 6 := degree_comap_equiv H E hreg
    have hcommonF : ∀ i j, i ≠ j →
        (HF.neighborFinset i ∩ HF.neighborFinset j).card = 2 :=
      common_comap_equiv H E hcommon
    have hsignF : IsNegativeSignedSRG1622 HF sF := by
      refine ⟨by simp, hregF, hcommonF, ?_, ?_⟩
      · intro i j
        exact hsym (E i) (E j)
      · intro i j p q hij hpq Aip Apj Aiq Aqj
        exact hpath (E.injective.ne hij) (E.injective.ne hpq)
          Aip Apj Aiq Aqj
    have hE0 : E 0 = x := by simpa [g] using hE 0
    have hE1 : E 1 = u 0 := by
      convert hE (Fin.succ (0 : Fin 6)) using 1 <;> rfl
    have hE2 : E 2 = u 1 := by
      convert hE (Fin.succ (1 : Fin 6)) using 1 <;> rfl
    have hE3 : E 3 = u 2 := by
      convert hE (Fin.succ (2 : Fin 6)) using 1 <;> rfl
    have hE4 : E 4 = u 3 := by
      convert hE (Fin.succ (3 : Fin 6)) using 1 <;> rfl
    have hE5 : E 5 = u 4 := by
      convert hE (Fin.succ (4 : Fin 6)) using 1 <;> rfl
    have hE6 : E 6 = u 5 := by
      convert hE (Fin.succ (5 : Fin 6)) using 1 <;> rfl
    have hneighbor : HF.neighborFinset 0 = firstSix := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        simp only [firstSix, Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals
          rw [SimpleGraph.mem_neighborFinset]
          change H.Adj (E 0) (E _)
          simp only [hE0, hE1, hE2, hE3, hE4, hE5, hE6]
          apply hxu
      · rw [show (HF.neighborFinset 0).card = 6 by
          change HF.degree 0 = 6
          exact hregF 0]
        native_decide
    have ha0 : row256 (matrixBV (graphBool HF)) 0 = 0x007e := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      let y : Fin 16 := ⟨i, hi⟩
      rw [show (row256 (matrixBV (graphBool HF)) 0).getLsbD i =
          graphBool HF 0 y by
        simpa [y] using row256_matrixBV_getLsbD (graphBool HF) 0 y]
      change graphBool HF 0 y = (0x007e : BitVec 16).getLsbD y.val
      rw [getLsbD_007e y]
      simp only [graphBool, decide_eq_decide]
      rw [← SimpleGraph.mem_neighborFinset, hneighbor]
    apply not_isNegativeSignedSRG1622_of_normalizedCycle HF sF ha0
    · change H.Adj (E 1) (E 2)
      simpa only [hE1, hE2] using A01
    · change H.Adj (E 2) (E 3)
      simpa only [hE2, hE3] using A12
    · change H.Adj (E 3) (E 4)
      simpa only [hE3, hE4] using A23
    · change H.Adj (E 4) (E 5)
      simpa only [hE4, hE5] using A34
    · change H.Adj (E 5) (E 6)
      simpa only [hE5, hE6] using A45
    · change H.Adj (E 6) (E 1)
      simpa only [hE6, hE1] using A50
    · exact hsignF

/-- Exact order-32 value. -/
theorem minDegreeForC4_thirtytwo_eq_six : minDegreeForC4 32 = 6 :=
  minDegreeForC4_thirtytwo_eq_six_of_noNegativeSigning
    noNegativeSigning1622

end Erdos85
