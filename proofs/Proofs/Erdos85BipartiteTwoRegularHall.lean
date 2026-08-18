import Proofs.Erdos85BipartiteTwoRegularMatchingBridge
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! # Hall extraction for finite two-regular bipartite relations -/

namespace Erdos85

open Finset Function

theorem twoRegularBipartite_hall {S T : Type*}
    [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (R : S → T → Prop) [DecidableRel R]
    (hS : ∀ s, #(Finset.univ.filter (R s)) = 2)
    (hT : ∀ t, #(Finset.univ.filter (fun s => R s t)) = 2) :
    ∀ A : Finset S,
      #A ≤ #(A.biUnion (fun s => Finset.univ.filter (R s))) := by
  intro A
  let N := A.biUnion (fun s => Finset.univ.filter (R s))
  have hleft : ∀ s ∈ A, 2 ≤ #(N.bipartiteAbove R s) := by
    intro s hs
    have heq : N.bipartiteAbove R s = Finset.univ.filter (R s) := by
      ext t
      simp only [Finset.mem_bipartiteAbove, Finset.mem_univ, true_and,
        Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨Finset.mem_biUnion.mpr ⟨s, hs, by simpa using h⟩, h⟩
    rw [heq, hS]
  have hright : ∀ t ∈ N, #(A.bipartiteBelow R t) ≤ 2 := by
    intro t _ht
    calc
      #(A.bipartiteBelow R t) ≤ #(Finset.univ.filter (fun s => R s t)) := by
        apply Finset.card_le_card
        intro s hs
        rw [Finset.mem_bipartiteBelow] at hs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hs.2
      _ = 2 := hT t
  have hcount : #A * 2 ≤ #N * 2 :=
    Finset.card_mul_le_card_mul (r := R) hleft hright
  change #A ≤ #N
  exact Nat.le_of_mul_le_mul_right hcount (by omega)

private theorem existsUnique_mem_ne_of_card_eq_two {α : Type*}
    [DecidableEq α] (u : Finset α) (a : α)
    (hu : #u = 2) (ha : a ∈ u) :
    ∃! b, b ∈ u ∧ b ≠ a := by
  rw [Finset.card_eq_two] at hu
  obtain ⟨x, y, hxy, rfl⟩ := hu
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
  rcases ha with rfl | rfl
  · refine ⟨y, ⟨Or.inr rfl, hxy.symm⟩, ?_⟩
    intro z hz
    rcases hz.1 with rfl | rfl
    · exact (hz.2 rfl).elim
    · rfl
  · refine ⟨x, ⟨Or.inl rfl, hxy⟩, ?_⟩
    intro z hz
    rcases hz.1 with rfl | rfl
    · rfl
    · exact (hz.2 rfl).elim

theorem twoRegularBipartite_afterMatching
    {S T : Type*} [Fintype S] [Fintype T]
    [DecidableEq S] [DecidableEq T]
    (R : S → T → Prop) [DecidableRel R]
    (hS : ∀ s, #(Finset.univ.filter (R s)) = 2)
    (hT : ∀ t, #(Finset.univ.filter (fun s => R s t)) = 2)
    (f : S ≃ T) (hf : ∀ s, R s (f s)) :
    BipartiteTwoRegularAfterMatching R f := by
  refine
    { matching_mem := hf
      residual_unique_left := fun s => ?_
      residual_unique_right := fun t => ?_ }
  · obtain ⟨b, hb, hub⟩ := existsUnique_mem_ne_of_card_eq_two
      (Finset.univ.filter (R s)) (f s) (hS s) (by simp [hf s])
    refine ⟨b, ?_, fun y hy => hub y ?_⟩
    · exact ⟨(Finset.mem_filter.mp hb.1).2, hb.2⟩
    · exact ⟨by simp [hy.1], hy.2⟩
  · have hmatch : R (f.symm t) t := by
      simpa using hf (f.symm t)
    obtain ⟨b, hb, hub⟩ := existsUnique_mem_ne_of_card_eq_two
      (Finset.univ.filter (fun s => R s t)) (f.symm t) (hT t)
      (by simp [hmatch])
    refine ⟨b, ?_, fun y hy => hub y ?_⟩
    · refine ⟨(Finset.mem_filter.mp hb.1).2, ?_⟩
      intro htf
      apply hb.2
      exact f.injective (by simpa using htf.symm)
    · refine ⟨by simp [hy.1], ?_⟩
      intro hyb
      apply hy.2
      rw [hyb, f.apply_symm_apply]

/-- Every finite two-regular bipartite relation contains a perfect matching,
presented directly as an equivalence between its shores. -/
theorem twoRegularBipartite_exists_matchingEquiv
    {S T : Type*} [Fintype S] [Fintype T]
    [DecidableEq S] [DecidableEq T]
    (R : S → T → Prop) [DecidableRel R]
    (hS : ∀ s, #(Finset.univ.filter (R s)) = 2)
    (hT : ∀ t, #(Finset.univ.filter (fun s => R s t)) = 2) :
    ∃ f : S ≃ T, ∀ s, R s (f s) := by
  have hHall := twoRegularBipartite_hall R hS hT
  obtain ⟨f, hf_inj, hf_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      (fun s : S => Finset.univ.filter (R s))).mp hHall
  have hcard_mul : Fintype.card S * 2 = Fintype.card T * 2 := by
    simpa [hS, hT] using
      (Finset.card_mul_eq_card_mul
        (r := R) (s := (Finset.univ : Finset S))
        (t := (Finset.univ : Finset T))
        (m := 2) (n := 2)
        (fun s _ => hS s) (fun t _ => hT t))
  have hcard : Fintype.card S = Fintype.card T :=
    Nat.eq_of_mul_eq_mul_right (by omega) hcard_mul
  have hf_bij : Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf_inj, hcard⟩
  let e := Equiv.ofBijective f hf_bij
  refine ⟨e, fun s => ?_⟩
  exact (Finset.mem_filter.mp (hf_mem s)).2

/-- A finite degree-two bipartite relation admits the complete two-matching
package used by the shore-shadow cycle-profile theorem. -/
theorem twoRegularBipartite_exists_afterMatching
    {S T : Type*} [Fintype S] [Fintype T]
    [DecidableEq S] [DecidableEq T]
    (R : S → T → Prop) [DecidableRel R]
    (hS : ∀ s, #(Finset.univ.filter (R s)) = 2)
    (hT : ∀ t, #(Finset.univ.filter (fun s => R s t)) = 2) :
    ∃ f : S ≃ T, BipartiteTwoRegularAfterMatching R f := by
  obtain ⟨f, hf⟩ := twoRegularBipartite_exists_matchingEquiv R hS hT
  exact ⟨f, twoRegularBipartite_afterMatching R hS hT f hf⟩

end Erdos85
