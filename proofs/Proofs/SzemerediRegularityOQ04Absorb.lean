/-
  Szemerédi Regularity OQ04 — S26: deficient absorption (upgrade to exact {m, m+1} sizes)

  S25 (`SzemerediRegularityOQ04Recut.lean`) re-cut any pairwise-disjoint family
  into nonempty pieces of size ≤ `m` with at most ONE deficient (`< m`) piece
  globally, at energy cost `2·|P|·m/n`.  But the Chain oracle
  (`exists_afksFineRegular_of_maintained_oracle`) demands the FULL maintained
  invariant — in particular ±1-equitability and the mass floor `m` — which a
  single deficient piece already violates.  The missing step (named by the S26
  sizing triage) is an ABSORPTION lemma: upgrade "pieces ≤ m, ≤ 1 deficient"
  to exact sizes ∈ {m, m+1} while retaining energy up to a bounded loss.

  This file proves exactly that:

  * `exists_absorb_deficient` — if the family has absorption capacity
    (`m ≤ #(size-m pieces) + 1`), redistribute the single deficient piece's
    `d ≤ m−1` vertices bijectively into `d` DISTINCT size-`m` pieces (each
    becomes size `m+1`).  The replaced subfamily (deficient piece + `d`
    receivers) has mass ≤ `(d+1)·m ≤ m²`, so by S24's
    `partitionEnergy_replace_ge_of_small` the energy loss is ≤ `2·m²/n`.
  * `exists_absorb_deficient_of_ground` — the capacity hypothesis follows from
    the ground-mass condition `m² ≤ |⋃R|` (S22's size-condition shape).
  * `exists_equitable_recut_absorbed` — capstone composing S25 + absorption:
    every pairwise-disjoint family `P` with `m² ≤ |⋃P|` re-cuts into a
    pairwise-disjoint family of the SAME ground set with ALL piece sizes in
    {m, m+1} (±1-equitable with mass floor `m`), losing at most
    `2·|P|·m/n + 2·m²/n` of partition energy.

  What this does NOT yet do: the Chain oracle also requires the successor to
  refine the coarse partition `Vparts`; the global re-cut pools deficient
  remainders ACROSS parents, so the oracle wiring must apply this machinery
  per coarse block (S27).  The absorption lemma here is block-local by
  construction, so it composes with that wiring unchanged.

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large
  graphs", Combinatorica 20 (2000); Komlós–Simonovits (1996).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04Recut

namespace Szemeredi.RegularityOQ04Absorb

open Szemeredi.Core Szemeredi.Regularity Szemeredi.RegularityOQ04Energy
open Szemeredi.RegularityOQ04Bridge Szemeredi.RegularityOQ04MergeLoss
open Szemeredi.RegularityOQ04Recut

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Deficient absorption (S26 core).**  A pairwise-disjoint family of
nonempty pieces of size ≤ `m` with at most one deficient (`< m`) piece and
absorption capacity `m ≤ #(size-m pieces) + 1` upgrades to a family of the
same ground set with ALL pieces of size exactly `m` or `m+1`, losing at most
`2·m²/n` of partition energy.

Construction: send each of the `d ≤ m−1` vertices of the deficient piece into
a distinct size-`m` piece (a bijection onto `d` chosen receivers), turning
each receiver into a size-`m+1` piece.  The replaced subfamily — deficient
piece plus receivers — has mass ≤ `(d+1)·m ≤ m²`, so S24's replacement bound
gives the energy estimate. -/
theorem exists_absorb_deficient (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hm : 1 ≤ m) (R : Finset (Finset V))
    (hdisj : (↑R : Set (Finset V)).PairwiseDisjoint id)
    (hne : ∀ c ∈ R, c.Nonempty)
    (hcard : ∀ c ∈ R, c.card ≤ m)
    (hdef : (R.filter (fun c => c.card < m)).card ≤ 1)
    (hcap : m ≤ (R.filter (fun c => c.card = m)).card + 1) :
    ∃ R' : Finset (Finset V),
      R'.biUnion id = R.biUnion id ∧
      (↑R' : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ c ∈ R', c.card = m ∨ c.card = m + 1) ∧
      partitionEnergy G R - 2 * (m * m : ℚ) / (Fintype.card V : ℚ) ≤
        partitionEnergy G R' := by
  classical
  by_cases hDempty : R.filter (fun c => c.card < m) = ∅
  · -- no deficient piece: R itself already has all pieces of size exactly m
    refine ⟨R, rfl, hdisj, ?_, sub_le_self _ (by positivity)⟩
    intro c hc
    left
    have hnlt : ¬ c.card < m := by
      intro hlt
      have : c ∈ R.filter (fun c => c.card < m) := Finset.mem_filter.mpr ⟨hc, hlt⟩
      simp [hDempty] at this
    have := hcard c hc
    omega
  · -- exactly one deficient piece D0
    have hone : (R.filter (fun c => c.card < m)).card = 1 := by
      have hpos : 0 < (R.filter (fun c => c.card < m)).card :=
        Finset.card_pos.mpr (Finset.nonempty_of_ne_empty hDempty)
      omega
    obtain ⟨D0, hD0⟩ := Finset.card_eq_one.mp hone
    have hD0mem : D0 ∈ R.filter (fun c => c.card < m) := by
      rw [hD0]; exact Finset.mem_singleton_self D0
    have hD0R : D0 ∈ R := (Finset.mem_filter.mp hD0mem).1
    have hD0lt : D0.card < m := (Finset.mem_filter.mp hD0mem).2
    have hD0pos : 1 ≤ D0.card := Finset.card_pos.mpr (hne D0 hD0R)
    -- the size-m pieces
    set Fm : Finset (Finset V) := R.filter (fun c => c.card = m) with hFm_def
    have hFm_R : ∀ S ∈ Fm, S ∈ R := fun S hS => (Finset.mem_filter.mp hS).1
    have hFm_m : ∀ S ∈ Fm, S.card = m := fun S hS => (Finset.mem_filter.mp hS).2
    -- every non-D0 member of R has size exactly m
    have hmem_Fm : ∀ c ∈ R, c ≠ D0 → c.card = m := by
      intro c hc hcne
      by_contra hne2
      have hlt : c.card < m := lt_of_le_of_ne (hcard c hc) hne2
      have hmem : c ∈ R.filter (fun c => c.card < m) := Finset.mem_filter.mpr ⟨hc, hlt⟩
      rw [hD0] at hmem
      exact hcne (Finset.mem_singleton.mp hmem)
    -- capacity: enough size-m receivers for the deficient vertices
    have hcap' : D0.card ≤ Fm.card := by omega
    obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hcap'
    have hT_R : ∀ S ∈ T, S ∈ R := fun S hS => hFm_R S (hT_sub hS)
    have hT_m : ∀ S ∈ T, S.card = m := fun S hS => hFm_m S (hT_sub hS)
    have hD0nT : D0 ∉ T := by
      intro h
      have := hT_m D0 h
      omega
    -- D0 is disjoint from every receiver
    have hD0_disj : ∀ S ∈ T, Disjoint D0 S := by
      intro S hS
      have hne' : D0 ≠ S := by
        intro h
        have := hT_m S hS
        rw [← h] at this
        omega
      exact hdisj (Finset.mem_coe.mpr hD0R) (Finset.mem_coe.mpr (hT_R S hS)) hne'
    -- the vertex-to-receiver bijection
    let e : ↥D0 ≃ ↥T := Finset.equivOfCardEq hT_card.symm
    have hvne : ∀ v : ↥D0, v.1 ∉ (e v).1 := fun v =>
      Finset.disjoint_left.mp (hD0_disj _ (e v).2) v.2
    -- the grown pieces
    set New : Finset (Finset V) :=
      D0.attach.image (fun v => insert v.1 (e v).1) with hNew_def
    refine ⟨(R \ insert D0 T) ∪ New, ?_, ?_, ?_, ?_⟩
    · -- same ground set
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_union, id_eq]
      constructor
      · rintro ⟨c, hc | hc, hx⟩
        · exact ⟨c, (Finset.mem_sdiff.mp hc).1, hx⟩
        · obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hc
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact ⟨D0, hD0R, v.2⟩
          · exact ⟨(e v).1, hT_R _ (e v).2, hx'⟩
      · rintro ⟨c, hc, hx⟩
        by_cases hcD0 : c = D0
        · subst hcD0
          refine ⟨insert x (e ⟨x, hx⟩).1,
            Or.inr (Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩), ?_⟩
          exact Finset.mem_insert_self _ _
        · by_cases hcT : c ∈ T
          · set w : ↥D0 := e.symm ⟨c, hcT⟩ with hw
            have hwc : (e w).1 = c := by
              rw [hw, Equiv.apply_symm_apply]
            refine ⟨insert w.1 (e w).1,
              Or.inr (Finset.mem_image.mpr ⟨w, Finset.mem_attach _ _, rfl⟩), ?_⟩
            rw [hwc]
            exact Finset.mem_insert_of_mem hx
          · refine ⟨c, Or.inl (Finset.mem_sdiff.mpr ⟨hc, ?_⟩), hx⟩
            intro h
            rcases Finset.mem_insert.mp h with h' | h'
            · exact hcD0 h'
            · exact hcT h'
    · -- pairwise disjointness
      intro a ha b hb hab
      simp only [Function.onFun, id_eq]
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · -- old / old
        exact hdisj (Finset.mem_coe.mpr (Finset.mem_sdiff.mp ha).1)
          (Finset.mem_coe.mpr (Finset.mem_sdiff.mp hb).1) hab
      · -- old / new
        obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hb
        obtain ⟨haR, haD⟩ := Finset.mem_sdiff.mp ha
        have haD0 : a ≠ D0 := fun h => haD (h ▸ Finset.mem_insert_self _ _)
        have haT : a ∉ T := fun h => haD (Finset.mem_insert_of_mem h)
        rw [Finset.disjoint_insert_right]
        refine ⟨?_, ?_⟩
        · intro hva
          exact Finset.disjoint_left.mp
            (hdisj (Finset.mem_coe.mpr haR) (Finset.mem_coe.mpr hD0R) haD0) hva v.2
        · exact hdisj (Finset.mem_coe.mpr haR) (Finset.mem_coe.mpr (hT_R _ (e v).2))
            (fun h => haT (h ▸ (e v).2))
      · -- new / old (mirror)
        obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨hbR, hbD⟩ := Finset.mem_sdiff.mp hb
        have hbD0 : b ≠ D0 := fun h => hbD (h ▸ Finset.mem_insert_self _ _)
        have hbT : b ∉ T := fun h => hbD (Finset.mem_insert_of_mem h)
        rw [Finset.disjoint_insert_left]
        refine ⟨?_, ?_⟩
        · intro hvb
          exact Finset.disjoint_left.mp
            (hdisj (Finset.mem_coe.mpr hbR) (Finset.mem_coe.mpr hD0R) hbD0) hvb v.2
        · exact (hdisj (Finset.mem_coe.mpr hbR) (Finset.mem_coe.mpr (hT_R _ (e v).2))
            (fun h => hbT (h ▸ (e v).2))).symm
      · -- new / new
        obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hb
        have hvw : v ≠ w := by
          rintro rfl
          exact hab rfl
        have hevc : (e v).1 ≠ (e w).1 :=
          fun h => hvw (e.injective (Subtype.ext h))
        have hvwc : v.1 ≠ w.1 := fun h => hvw (Subtype.ext h)
        rw [Finset.disjoint_insert_left, Finset.disjoint_insert_right]
        refine ⟨?_, ?_, ?_⟩
        · intro h
          rcases Finset.mem_insert.mp h with h' | h'
          · exact hvwc h'
          · exact Finset.disjoint_left.mp (hD0_disj _ (e w).2) v.2 h'
        · exact fun h => Finset.disjoint_left.mp (hD0_disj _ (e v).2) w.2 h
        · exact hdisj (Finset.mem_coe.mpr (hT_R _ (e v).2))
            (Finset.mem_coe.mpr (hT_R _ (e w).2)) hevc
    · -- sizes: kept pieces are exactly m, grown pieces are m+1
      intro c hc
      rcases Finset.mem_union.mp hc with h | h
      · left
        obtain ⟨hcR, hcD⟩ := Finset.mem_sdiff.mp h
        exact hmem_Fm c hcR (fun hh => hcD (hh ▸ Finset.mem_insert_self _ _))
      · right
        obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp h
        rw [Finset.card_insert_of_notMem (hvne v), hT_m _ (e v).2]
    · -- energy: replace {D0} ∪ T, mass ≤ (d+1)·m ≤ m²
      have hDsub : insert D0 T ⊆ R :=
        Finset.insert_subset_iff.mpr ⟨hD0R, fun S hS => hT_R S hS⟩
      have hsmall : ∀ A ∈ insert D0 T, A.card ≤ m := by
        intro A hA
        rcases Finset.mem_insert.mp hA with rfl | h
        · omega
        · exact le_of_eq (hT_m A h)
      have hpe := partitionEnergy_replace_ge_of_small G hDsub hdisj
        (Finset.subset_union_left (s₂ := New)) hsmall
      have hDcard : (insert D0 T).card ≤ m := by
        rw [Finset.card_insert_of_notMem hD0nT]
        omega
      have hDm : (insert D0 T).card * m ≤ m * m :=
        Nat.mul_le_mul_right m hDcard
      have hloss : 2 * ((insert D0 T).card * m : ℚ) / (Fintype.card V : ℚ) ≤
          2 * (m * m : ℚ) / (Fintype.card V : ℚ) := by
        have hnum : ((insert D0 T).card * m : ℚ) ≤ (m * m : ℚ) := by
          exact_mod_cast hDm
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (by linarith)
          (inv_nonneg.mpr (Nat.cast_nonneg _))
      linarith

/-- **Capacity from ground mass.**  The absorption capacity hypothesis of
`exists_absorb_deficient` follows from the size condition `m² ≤ |⋃R|` (the
S22 shape): mass ≤ `|R|·m` forces `m ≤ |R|`, and all but at most one piece
has size exactly `m`. -/
theorem exists_absorb_deficient_of_ground (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hm : 1 ≤ m) (R : Finset (Finset V))
    (hdisj : (↑R : Set (Finset V)).PairwiseDisjoint id)
    (hne : ∀ c ∈ R, c.Nonempty)
    (hcard : ∀ c ∈ R, c.card ≤ m)
    (hdef : (R.filter (fun c => c.card < m)).card ≤ 1)
    (hground : m * m ≤ (R.biUnion id).card) :
    ∃ R' : Finset (Finset V),
      R'.biUnion id = R.biUnion id ∧
      (↑R' : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ c ∈ R', c.card = m ∨ c.card = m + 1) ∧
      partitionEnergy G R - 2 * (m * m : ℚ) / (Fintype.card V : ℚ) ≤
        partitionEnergy G R' := by
  classical
  refine exists_absorb_deficient G m hm R hdisj hne hcard hdef ?_
  -- ground mass = total piece mass ≤ |R|·m, so m ≤ |R|
  have hmass : (R.biUnion id).card = ∑ c ∈ R, c.card :=
    Finset.card_biUnion (fun x hx y hy hxy => hdisj hx hy hxy)
  have hsum : ∑ c ∈ R, c.card ≤ R.card * m := by
    calc ∑ c ∈ R, c.card ≤ ∑ _c ∈ R, m := Finset.sum_le_sum (fun c hc => hcard c hc)
      _ = R.card * m := by rw [Finset.sum_const, smul_eq_mul]
  have hRm : m ≤ R.card := by
    have h1 : m * m ≤ R.card * m := le_trans (hmass ▸ hground) hsum
    exact Nat.le_of_mul_le_mul_right h1 hm
  -- |R| = #(size-m pieces) + #(deficient pieces)
  have hsplit := Finset.card_filter_add_card_filter_not (s := R) (fun c => c.card = m)
  have hfeq : R.filter (fun c => ¬ c.card = m) = R.filter (fun c => c.card < m) :=
    Finset.filter_congr (fun c hc => by have := hcard c hc; omega)
  rw [hfeq] at hsplit
  omega

/-- **The absorbed equitable re-cut (S26 capstone).**  Every pairwise-disjoint
family `P` whose ground set has at least `m²` vertices re-cuts into a
pairwise-disjoint family `R` of the SAME ground set with ALL piece sizes in
`{m, m+1}` — i.e. ±1-equitable with mass floor `m` — losing at most
`2·|P|·m/n + 2·m²/n` of partition energy.  S25's `exists_equitable_recut`
followed by deficient absorption. -/
theorem exists_equitable_recut_absorbed (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hm : 1 ≤ m) (P : Finset (Finset V))
    (hdisj : (↑P : Set (Finset V)).PairwiseDisjoint id)
    (hground : m * m ≤ (P.biUnion id).card) :
    ∃ R : Finset (Finset V),
      R.biUnion id = P.biUnion id ∧
      (↑R : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ c ∈ R, c.card = m ∨ c.card = m + 1) ∧
      partitionEnergy G P - 2 * (P.card * m : ℚ) / (Fintype.card V : ℚ)
          - 2 * (m * m : ℚ) / (Fintype.card V : ℚ) ≤
        partitionEnergy G R := by
  obtain ⟨Q, hQcov, hQdisj, hQne, hQcard, hQdef, hQpe⟩ :=
    exists_equitable_recut G m hm P hdisj
  obtain ⟨R, hRcov, hRdisj, hRsize, hRpe⟩ :=
    exists_absorb_deficient_of_ground G m hm Q hQdisj hQne hQcard hQdef
      (by rw [hQcov]; exact hground)
  exact ⟨R, by rw [hRcov, hQcov], hRdisj, hRsize, by linarith⟩

/-- Convenience form of the capstone conclusion: exact-size membership in
`{m, m+1}` restated as the mass floor `m ≤ |c|` plus the ceiling
`|c| ≤ m + 1` — the vocabulary of the Chain oracle's maintained invariant. -/
theorem exists_equitable_recut_absorbed' (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hm : 1 ≤ m) (P : Finset (Finset V))
    (hdisj : (↑P : Set (Finset V)).PairwiseDisjoint id)
    (hground : m * m ≤ (P.biUnion id).card) :
    ∃ R : Finset (Finset V),
      R.biUnion id = P.biUnion id ∧
      (↑R : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ c ∈ R, m ≤ c.card ∧ c.card ≤ m + 1) ∧
      partitionEnergy G P - 2 * (P.card * m : ℚ) / (Fintype.card V : ℚ)
          - 2 * (m * m : ℚ) / (Fintype.card V : ℚ) ≤
        partitionEnergy G R := by
  obtain ⟨R, hcov, hdisj', hsize, hpe⟩ :=
    exists_equitable_recut_absorbed G m hm P hdisj hground
  exact ⟨R, hcov, hdisj', fun c hc => by rcases hsize c hc with h | h <;> omega, hpe⟩

end Szemeredi.RegularityOQ04Absorb
