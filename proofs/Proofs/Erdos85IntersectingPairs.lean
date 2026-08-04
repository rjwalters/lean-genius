import Mathlib.Combinatorics.SetFamily.KruskalKatona

/-!
# Intersecting two-set families on arbitrary finite types

Mathlib's Erdős--Ko--Rado theorem is stated on `Fin n`.  This small bridge
transports it across `Fintype.equivFin` for use with geometric point sets.
-/

open Finset

namespace Erdos85

theorem pair_intersecting_card_le {α : Type*} [Fintype α] [DecidableEq α]
    (𝒜 : Finset (Finset α))
    (h𝒜 : (𝒜 : Set (Finset α)).Intersecting)
    (hsized : (𝒜 : Set (Finset α)).Sized 2)
    (hcard : 4 ≤ Fintype.card α) :
    𝒜.card ≤ Fintype.card α - 1 := by
  classical
  let e := Fintype.equivFin α
  let emb : Finset α ↪ Finset (Fin (Fintype.card α)) :=
    ⟨fun s => s.map e.toEmbedding, fun s t h => by
      simpa using Finset.map_injective e.toEmbedding h⟩
  let ℬ := 𝒜.map emb
  have hcardmap : ℬ.card = 𝒜.card := Finset.card_map emb
  have hBint : (ℬ : Set (Finset (Fin (Fintype.card α)))).Intersecting := by
    intro s hs t ht hdisj
    rw [Finset.mem_coe, Finset.mem_map] at hs ht
    obtain ⟨s, hsA, rfl⟩ := hs
    obtain ⟨t, htA, rfl⟩ := ht
    exact h𝒜 hsA htA (by
      rw [Finset.disjoint_left] at hdisj ⊢
      intro a haS haT
      have heS : e a ∈ t.map e.toEmbedding := by simp [haT]
      have heT : e a ∈ s.map e.toEmbedding := by simp [haS]
      exact hdisj heT heS)
  have hBsized :
      (ℬ : Set (Finset (Fin (Fintype.card α)))).Sized 2 := by
    intro s hs
    rw [Finset.mem_coe, Finset.mem_map] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    dsimp [emb]
    rw [Finset.card_map]
    exact hsized ht
  have hhalf : 2 ≤ Fintype.card α / 2 :=
    (Nat.le_div_iff_mul_le (by omega)).2 hcard
  have h := Finset.erdos_ko_rado hBint hBsized hhalf
  rw [hcardmap] at h
  simpa using h

end Erdos85
