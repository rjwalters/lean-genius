import Proofs.Erdos85MixedAnchorMasterQuantization
import Proofs.Erdos85CoverFiberCount

/-!
# Component partition for mixed anchor pair masses

This file reindexes the off-target vertex sum by defect components and records
the abstract uniqueness consequence of pair-mass quantization.
-/

namespace Erdos85

noncomputable section

/-- Reindex a sum over vertices outside one labeled component as nested sums
over all the other components. -/
theorem sum_filter_not_range_eq_sum_components_erase
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    {ℓ : C → ℕ} [∀ c, NeZero (ℓ c)]
    (u : ∀ c : C, ZMod (ℓ c) → V)
    (hu : ∀ c, Function.Injective (u c))
    (hsep : ∀ {c e : C}, c ≠ e → ∀ x y, u c x ≠ u e y)
    (hcover : ∀ v : V, ∃ c x, u c x = v)
    (e : C) (F : V → ℕ) :
    ∑ x ∈ Finset.univ.filter (fun x : V ↦ x ∉ Set.range (u e)), F x =
      ∑ c ∈ Finset.univ.erase e, ∑ z : ZMod (ℓ c), F (u c z) := by
  classical
  let E : (Σ c : C, ZMod (ℓ c)) ≃ V :=
    Equiv.ofBijective (mixedCycleLabeling u)
      (mixedCycleLabeling_bijective hu hsep hcover)
  have hrange : ∀ q : Σ c : C, ZMod (ℓ c),
      u q.1 q.2 ∈ Set.range (u e) ↔ q.1 = e := by
    rintro ⟨c, z⟩
    constructor
    · rintro ⟨y, hy⟩
      by_contra hce
      exact hsep hce z y hy.symm
    · rintro rfl
      exact ⟨z, rfl⟩
  change (∑ x ∈ Finset.univ with x ∉ Set.range (u e), F x) = _
  rw [Finset.sum_filter]
  calc
    ∑ x : V, (if (x ∉ Set.range (u e)) then F x else (0 : ℕ)) =
        ∑ q : Σ c : C, ZMod (ℓ c),
          (if (E q ∉ Set.range (u e)) then F (E q) else (0 : ℕ)) := by
      symm
      exact Equiv.sum_comp E
        (fun x ↦ if (x ∉ Set.range (u e)) then F x else (0 : ℕ))
    _ = ∑ q : Σ c : C, ZMod (ℓ c),
          (if q.1 ≠ e then F (u q.1 q.2) else (0 : ℕ)) := by
      apply Finset.sum_congr rfl
      rintro ⟨c, z⟩ _
      have hE : E ⟨c, z⟩ = u c z := rfl
      rw [hE]
      by_cases hce : c = e
      · simp [hce, hrange ⟨c, z⟩]
      · simp [hce, hrange ⟨c, z⟩]
    _ = ∑ c : C, (if c ≠ e then ∑ z : ZMod (ℓ c), F (u c z)
        else (0 : ℕ)) := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro c _
      split_ifs <;> simp
    _ = ∑ c ∈ Finset.univ.erase e, ∑ z : ZMod (ℓ c), F (u c z) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext c
        simp [eq_comm]
      · intro c hc
        rfl

/-- If finitely many component masses are each `0` or `m` and their total is
`m>0`, exactly one component has full mass. -/
theorem existsUnique_fullMass_of_quantized_sum
    {C : Type*} [Fintype C] [DecidableEq C]
    (M : C → ℕ) {m : ℕ} (hm : 0 < m)
    (hquant : ∀ c, M c ∈ ({0, m} : Set ℕ))
    (hsum : ∑ c, M c = m) :
    ∃! c, M c = m := by
  have hex : ∃ c, M c = m := by
    by_contra hnone
    push_neg at hnone
    have hz : ∀ c, M c = 0 := by
      intro c
      rcases hquant c with h | h
      · exact h
      · exact absurd h (hnone c)
    simp_rw [hz] at hsum
    have : 0 = m := by simpa using hsum
    omega
  obtain ⟨c, hc⟩ := hex
  refine ⟨c, hc, ?_⟩
  intro e he
  by_contra hne
  have hle : M c + M e ≤ ∑ z, M z := by
    have hcMem : c ∈ (Finset.univ : Finset C) := Finset.mem_univ c
    have heMem : e ∈ (Finset.univ.erase c : Finset C) := by simp [hne]
    calc
      M c + M e ≤ M c + ∑ z ∈ Finset.univ.erase c, M z :=
        Nat.add_le_add_left (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
          heMem) _
      _ = (∑ z ∈ Finset.univ.erase c, M z) + M c := by omega
      _ = ∑ z, M z := Finset.sum_erase_add _ _ hcMem
  rw [hc, he, hsum] at hle
  omega

/-- Finset-indexed version of full-mass uniqueness. -/
theorem existsUnique_mem_fullMass_of_quantized_sum
    {C : Type*} [DecidableEq C] (S : Finset C)
    (M : C → ℕ) {m : ℕ} (hm : 0 < m)
    (hquant : ∀ c ∈ S, M c ∈ ({0, m} : Set ℕ))
    (hsum : ∑ c ∈ S, M c = m) :
    ∃! c, c ∈ S ∧ M c = m := by
  have hex : ∃ c ∈ S, M c = m := by
    by_contra hnone
    push_neg at hnone
    have hz : ∀ c ∈ S, M c = 0 := by
      intro c hc
      rcases hquant c hc with h | h
      · exact h
      · exact absurd h (hnone c hc)
    have hzero : ∑ c ∈ S, M c = 0 :=
      Finset.sum_eq_zero (fun c hc ↦ hz c hc)
    omega
  obtain ⟨c, hcS, hc⟩ := hex
  refine ⟨c, ⟨hcS, hc⟩, ?_⟩
  intro e he
  by_contra hne
  have hle : M c + M e ≤ ∑ z ∈ S, M z := by
    have heErase : e ∈ S.erase c := by simp [he.1, hne]
    calc
      M c + M e ≤ M c + ∑ z ∈ S.erase c, M z :=
        Nat.add_le_add_left (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
          heErase) _
      _ = (∑ z ∈ S.erase c, M z) + M c := by omega
      _ = ∑ z ∈ S, M z := Finset.sum_erase_add _ _ hcS
  rw [hc, he.2, hsum] at hle
  omega

end

end Erdos85
