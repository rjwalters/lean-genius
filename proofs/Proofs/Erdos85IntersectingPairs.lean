import Mathlib.Combinatorics.SetFamily.KruskalKatona
import Mathlib.Tactic

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

/-- Every intersecting family of two-subsets is either a star or has at most
three members (in the latter case the proof places it inside a triangle). -/
theorem pair_intersecting_star_or_card_le_three {α : Type*} [Fintype α] [DecidableEq α]
    (𝒜 : Finset (Finset α))
    (h𝒜 : (𝒜 : Set (Finset α)).Intersecting)
    (hsized : (𝒜 : Set (Finset α)).Sized 2) :
    (∃ a : α, ∀ D ∈ 𝒜, a ∈ D) ∨ 𝒜.card ≤ 3 := by
  classical
  by_cases hne : 𝒜.Nonempty
  · let D := hne.choose
    have hDmem : D ∈ 𝒜 := hne.choose_spec
    obtain ⟨a, b, hab, hD⟩ := Finset.card_eq_two.mp (hsized hDmem)
    by_cases ha : ∀ E ∈ 𝒜, a ∈ E
    · exact Or.inl ⟨a, ha⟩
    · push Not at ha
      obtain ⟨E, hEmem, haE⟩ := ha
      have hDE : ¬ Disjoint D E := h𝒜 hDmem hEmem
      have hbE : b ∈ E := by
        rw [hD] at hDE
        rw [Finset.not_disjoint_iff] at hDE
        obtain ⟨x, hxD, hxE⟩ := hDE
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxD
        exact hxD.elim (fun h => (haE (h ▸ hxE)).elim) (fun h => h ▸ hxE)
      obtain ⟨u, v, huv, hE⟩ := Finset.card_eq_two.mp (hsized hEmem)
      have hub : u = b ∨ v = b := by
        rw [hE] at hbE
        simpa [eq_comm] using hbE
      let c := if u = b then v else u
      have hEbc : E = {b, c} := by
        rcases hub with hub | hvb
        · subst u
          dsimp [c]
          rw [if_pos rfl]
          exact hE
        · subst v
          dsimp [c]
          rw [if_neg huv]
          exact hE.trans (Finset.pair_comm _ _)
      have hcb : c ≠ b := by
        intro h
        have hc := hsized hEmem
        rw [hEbc, h] at hc
        simp at hc
      have hca : c ≠ a := by
        intro h
        apply haE
        rw [hEbc, h]
        simp
      by_cases hb : ∀ H ∈ 𝒜, b ∈ H
      · exact Or.inl ⟨b, hb⟩
      · push Not at hb
        obtain ⟨H, hHmem, hbH⟩ := hb
        have haH : a ∈ H := by
          have hDH : ¬ Disjoint D H := h𝒜 hDmem hHmem
          rw [hD, Finset.not_disjoint_iff] at hDH
          obtain ⟨x, hxD, hxH⟩ := hDH
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxD
          exact hxD.elim (fun h => h ▸ hxH) (fun h => (hbH (h ▸ hxH)).elim)
        have hcH : c ∈ H := by
          have hEH : ¬ Disjoint E H := h𝒜 hEmem hHmem
          rw [hEbc, Finset.not_disjoint_iff] at hEH
          obtain ⟨x, hxE, hxH⟩ := hEH
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxE
          exact hxE.elim (fun h => (hbH (h ▸ hxH)).elim) (fun h => h ▸ hxH)
        have hHac : H = {a,c} := by
          symm
          apply Finset.eq_of_subset_of_card_le
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact haH
            · exact hcH
          · rw [hsized hHmem]
            rw [Finset.card_pair]
            exact hca.symm
        right
        have hsub : 𝒜 ⊆ {{a,b},{b,c},{a,c}} := by
          intro T hT
          obtain ⟨r,s,hrs,hTrs⟩ := Finset.card_eq_two.mp (hsized hT)
          have hTD : r = a ∨ r = b ∨ s = a ∨ s = b := by
            have hh := h𝒜 hT hDmem
            rw [hTrs, hD, Finset.not_disjoint_iff] at hh
            simpa [eq_comm, or_assoc, or_left_comm, or_comm] using hh
          have hTE : r = b ∨ r = c ∨ s = b ∨ s = c := by
            have hh := h𝒜 hT hEmem
            rw [hTrs, hEbc, Finset.not_disjoint_iff] at hh
            simpa [eq_comm, or_assoc, or_left_comm, or_comm] using hh
          have hTH : r = a ∨ r = c ∨ s = a ∨ s = c := by
            have hh := h𝒜 hT hHmem
            rw [hTrs, hHac, Finset.not_disjoint_iff] at hh
            simpa [eq_comm, or_assoc, or_left_comm, or_comm] using hh
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases hTD with h | h | h | h <;>
            rcases hTE with j | j | j | j <;>
            rcases hTH with k | k | k | k <;>
            subst_vars <;> simp_all [Finset.pair_comm]
        calc
          𝒜.card ≤ ({{a,b},{b,c},{a,c}} : Finset (Finset α)).card :=
            Finset.card_le_card hsub
          _ ≤ 3 := by
            calc
              ({{a,b},{b,c},{a,c}} : Finset (Finset α)).card
                  ≤ ({{b,c},{a,c}} : Finset (Finset α)).card + 1 :=
                    by simpa only using (Finset.card_insert_le
                      (a := ({a,b} : Finset α))
                      (s := ({{b,c},{a,c}} : Finset (Finset α))))
              _ ≤ ({ {a,c} } : Finset (Finset α)).card + 1 + 1 := by
                    have hh := Finset.card_insert_le
                      (a := ({b,c} : Finset α))
                      (s := ({ {a,c} } : Finset (Finset α)))
                    omega
              _ = 3 := by simp
  · right
    have hempty : 𝒜 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp

/-- The rank-two Kneser coloring lower bound: covering every two-subset of an
`n`-element type by intersecting families requires at least `n-2` families. -/
theorem pair_intersecting_cover_card_ge {α I : Type*} [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I]
    (𝒜 : I → Finset (Finset α))
    (hint : ∀ i, (𝒜 i : Set (Finset α)).Intersecting)
    (hsized : ∀ i, (𝒜 i : Set (Finset α)).Sized 2)
    (hcover : Finset.univ.powersetCard 2 ⊆ Finset.univ.biUnion 𝒜)
    (hn : 4 ≤ Fintype.card α) :
    Fintype.card α - 2 ≤ Fintype.card I := by
  classical
  let Star : I → Prop := fun i => ∃ a : α, ∀ D ∈ 𝒜 i, a ∈ D
  let J : Finset I := Finset.univ.filter Star
  letI : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  let center : I → α := fun i => if h : Star i then Classical.choose h else Classical.choice inferInstance
  have hcenter (i : I) (hi : i ∈ J) : ∀ D ∈ 𝒜 i, center i ∈ D := by
    have hs : Star i := (Finset.mem_filter.mp hi).2
    dsimp [center]
    rw [dif_pos hs]
    exact Classical.choose_spec hs
  let C : Finset α := J.image center
  let R : Finset I := Finset.univ \ J
  have hJR : J.card + R.card = Fintype.card I := by
    have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ J)
    change (Finset.univ \ J).card + J.card = Fintype.card I at hh
    dsimp [R]
    omega
  have hCcard : C.card ≤ J.card := Finset.card_image_le
  have hnonstar (i : I) (hi : i ∈ R) : (𝒜 i).card ≤ 3 := by
    have hiJ : i ∉ J := (Finset.mem_sdiff.mp hi).2
    have hnstar : ¬ Star i := by
      intro hs
      exact hiJ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)
    exact (pair_intersecting_star_or_card_le_three (𝒜 i) (hint i) (hsized i)).resolve_left hnstar
  have hpairsSub : (Finset.univ \ C).powersetCard 2 ⊆ R.biUnion 𝒜 := by
    intro D hD
    have hDin : D ∈ Finset.univ.powersetCard 2 := by
      rw [Finset.mem_powersetCard] at hD ⊢
      exact ⟨hD.1.trans (Finset.sdiff_subset), hD.2⟩
    have hcovered := hcover hDin
    rw [Finset.mem_biUnion] at hcovered ⊢
    obtain ⟨i, _, hiD⟩ := hcovered
    refine ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩, hiD⟩
    intro hiJ
    have hcC : center i ∈ C := Finset.mem_image.mpr ⟨i, hiJ, rfl⟩
    have hcD : center i ∈ D := hcenter i hiJ D hiD
    have hDsub := (Finset.mem_powersetCard.mp hD).1 hcD
    exact (Finset.mem_sdiff.mp hDsub).2 hcC
  have hpairsCount : Nat.choose ((Finset.univ \ C).card) 2 ≤ 3 * R.card := by
    calc
      Nat.choose ((Finset.univ \ C).card) 2 =
          ((Finset.univ \ C).powersetCard 2).card := by
            rw [Finset.card_powersetCard]
      _ ≤ (R.biUnion 𝒜).card := Finset.card_le_card hpairsSub
      _ ≤ ∑ i ∈ R, (𝒜 i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ R, 3 := by
            apply Finset.sum_le_sum
            intro i hi
            exact hnonstar i hi
      _ = 3 * R.card := by simp [Nat.mul_comm]
  by_contra hbad
  have hIlt : Fintype.card I < Fintype.card α - 2 := Nat.lt_of_not_ge hbad
  have hm : R.card + 3 ≤ (Finset.univ \ C).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ C), Finset.card_univ]
    omega
  have hdouble := Nat.mul_le_mul_left 2 hpairsCount
  rw [mul_comm 2, Nat.choose_two_right,
    Nat.div_two_mul_two_of_even
      (Nat.even_mul_pred_self ((Finset.univ \ C).card))] at hdouble
  have hmpos : 1 ≤ (Finset.univ \ C).card := by omega
  have hpred : (Finset.univ \ C).card - 1 ≥ R.card + 2 := by omega
  have hprod := Nat.mul_le_mul hm hpred
  rcases Nat.eq_zero_or_pos R.card with hr | hr
  · rw [hr] at hdouble hm hpred hprod
    norm_num at hdouble hprod
    rcases hdouble with hC | hp
    · rw [hC] at hm
      simp at hm
    · omega
  · have hrr : R.card ≤ R.card * R.card := by
      calc
        R.card = R.card * 1 := by omega
        _ ≤ R.card * R.card := Nat.mul_le_mul_left _ hr
    nlinarith [hprod, hrr]

/-- An explicit optimal rank-two Kneser cover: one triangle on three chosen
points, and one star for every point outside that triangle. -/
abbrev PairCoverIndex {α : Type*} [DecidableEq α] (T : Finset α) :=
  Option {x : α // x ∉ T}

noncomputable def pairCoverFamily {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset α) : PairCoverIndex T → Finset (Finset α)
  | none => T.powersetCard 2
  | some x => Finset.univ.powersetCard 2 |>.filter fun D => x.1 ∈ D

theorem pairCoverFamily_sized {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset α) (i : PairCoverIndex T) :
    (pairCoverFamily T i : Set (Finset α)).Sized 2 := by
  intro D hD
  cases i with
  | none => exact (Finset.mem_powersetCard.mp hD).2
  | some x => exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hD).1).2

theorem pairCoverFamily_intersecting {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset α) (hT : T.card = 3) (i : PairCoverIndex T) :
    (pairCoverFamily T i : Set (Finset α)).Intersecting := by
  intro D hD E hE hdisj
  cases i with
  | some x =>
      exact Finset.disjoint_left.mp hdisj
        (Finset.mem_filter.mp hD).2 (Finset.mem_filter.mp hE).2
  | none =>
      have hD' := Finset.mem_powersetCard.mp hD
      have hE' := Finset.mem_powersetCard.mp hE
      have hUsub : D ∪ E ⊆ T := Finset.union_subset hD'.1 hE'.1
      have hUcard : (D ∪ E).card = 4 := by
        rw [Finset.card_union_of_disjoint hdisj, hD'.2, hE'.2]
      have := Finset.card_le_card hUsub
      rw [hUcard, hT] at this
      omega

theorem pairCoverFamily_cover {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset α) :
    (Finset.univ : Finset α).powersetCard 2 ⊆
      Finset.univ.biUnion (pairCoverFamily T) := by
  intro D hD
  rw [Finset.mem_biUnion]
  by_cases hDT : D ⊆ T
  · refine ⟨none, Finset.mem_univ _, ?_⟩
    exact Finset.mem_powersetCard.mpr ⟨hDT, (Finset.mem_powersetCard.mp hD).2⟩
  · simp only [Finset.not_subset] at hDT
    obtain ⟨x, hxD, hxT⟩ := hDT
    let xx : {x : α // x ∉ T} := ⟨x, hxT⟩
    refine ⟨some xx, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hD, hxD⟩⟩

theorem card_pairCoverIndex {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset α) (hT : T.card = 3) (hcard : 3 ≤ Fintype.card α) :
    Fintype.card (PairCoverIndex T) = Fintype.card α - 2 := by
  rw [Fintype.card_option, Fintype.card_subtype_compl
    (fun x : α => x ∈ T), Fintype.card_coe, hT]
  omega

end Erdos85
