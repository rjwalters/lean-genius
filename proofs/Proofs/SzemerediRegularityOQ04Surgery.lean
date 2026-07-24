/-
  Szemerédi Regularity OQ04 — S27a: ambient surgery (in-place fiber absorption)

  S26 (`SzemerediRegularityOQ04Absorb.lean`) upgraded a STANDALONE family
  ("pieces ≤ m, ≤ 1 deficient") to exact sizes {m, m+1} with energy loss
  ≤ 2·m²/n.  But the Chain oracle's successor must REFINE the coarse partition
  `Vparts`, so re-equitization has to run PER COARSE BLOCK: the fiber of the
  fine partition inside one block gets re-cut while the rest of the ambient
  family stays untouched.  The energy accounting must therefore live on the
  AMBIENT family — the fiber's own `partitionEnergy` is not a summand of the
  ambient energy (cross-block pairs), so the standalone S26 statement does not
  compose.

  This file provides the ambient (in-place) form:

  * `exists_absorb_deficient_within` — for a subfamily `R` of a
    pairwise-disjoint ambient family `Q₀`, with `R`'s pieces ≤ m, ≤ 1
    deficient, and absorption capacity, there is `R'` with all sizes in
    {m, m+1}, the same fiber ground set, such that swapping `R → R'` inside
    `Q₀` keeps the ambient family pairwise disjoint, keeps the ambient ground
    set, and costs at most `2·m²/n` of AMBIENT partition energy.  The
    construction is S26's bijective redistribution verbatim; the energy bound
    is S24's `partitionEnergy_replace_ge_of_small` applied to the ambient
    family (replaced subfamily = deficient piece + receivers, all inside `R`).

  Specializing `Q₀ = R` recovers S26's standalone statement.

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large
  graphs", Combinatorica 20 (2000); Komlós–Simonovits (1996).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04Absorb

namespace Szemeredi.RegularityOQ04Surgery

open Szemeredi.Core Szemeredi.Regularity Szemeredi.RegularityOQ04Energy
open Szemeredi.RegularityOQ04Bridge Szemeredi.RegularityOQ04MergeLoss
open Szemeredi.RegularityOQ04Recut Szemeredi.RegularityOQ04Absorb
open Szemeredi.RegularityOQ04ChopRefine Szemeredi.RegularityOQ04FullRefine

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Ambient deficient absorption (S27a).**  Let `R ⊆ Q₀` be a subfamily of a
pairwise-disjoint ambient family, with `R`'s pieces nonempty of size ≤ `m`,
at most one deficient (`< m`), and absorption capacity
`m ≤ #(size-m pieces of R) + 1`.  Then there is a family `R'` with

* the same fiber ground set (`⋃R' = ⋃R`), all pieces of size `m` or `m+1`;
* swapping the fiber in place — `(Q₀ \ R) ∪ R'` — preserves the ambient
  ground set and ambient pairwise disjointness;
* the AMBIENT energy drops by at most `2·m²/n`.

The redistribution never leaves the fiber, so pieces of `Q₀ \ R` are
untouched; the energy estimate is one S24 replacement on the ambient family. -/
theorem exists_absorb_deficient_within (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hm : 1 ≤ m) (Q₀ R : Finset (Finset V)) (hR : R ⊆ Q₀)
    (hdisj : (↑Q₀ : Set (Finset V)).PairwiseDisjoint id)
    (hne : ∀ c ∈ R, c.Nonempty)
    (hcard : ∀ c ∈ R, c.card ≤ m)
    (hdef : (R.filter (fun c => c.card < m)).card ≤ 1)
    (hcap : m ≤ (R.filter (fun c => c.card = m)).card + 1) :
    ∃ R' : Finset (Finset V),
      R'.biUnion id = R.biUnion id ∧
      (∀ c ∈ R', c.card = m ∨ c.card = m + 1) ∧
      ((Q₀ \ R) ∪ R').biUnion id = Q₀.biUnion id ∧
      (↑((Q₀ \ R) ∪ R') : Set (Finset V)).PairwiseDisjoint id ∧
      partitionEnergy G Q₀ - 2 * (m * m : ℚ) / (Fintype.card V : ℚ) ≤
        partitionEnergy G ((Q₀ \ R) ∪ R') := by
  classical
  by_cases hDempty : R.filter (fun c => c.card < m) = ∅
  · -- no deficient piece: the fiber is untouched
    have hsizes : ∀ c ∈ R, c.card = m ∨ c.card = m + 1 := by
      intro c hc
      left
      have hnlt : ¬ c.card < m := by
        intro hlt
        have : c ∈ R.filter (fun c => c.card < m) := Finset.mem_filter.mpr ⟨hc, hlt⟩
        simp [hDempty] at this
      have := hcard c hc
      omega
    have hcup : (Q₀ \ R) ∪ R = Q₀ := by
      ext c
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (⟨h, -⟩ | h)
        · exact h
        · exact hR h
      · intro h
        by_cases hcR : c ∈ R
        · exact Or.inr hcR
        · exact Or.inl ⟨h, hcR⟩
    refine ⟨R, rfl, hsizes, by rw [hcup], by rw [hcup]; exact hdisj,
      sub_le_self _ (by positivity) |>.trans (le_of_eq (by rw [hcup]))⟩
  · -- exactly one deficient piece D0 in the fiber
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
    -- the size-m pieces of the fiber
    set Fm : Finset (Finset V) := R.filter (fun c => c.card = m) with hFm_def
    have hFm_R : ∀ S ∈ Fm, S ∈ R := fun S hS => (Finset.mem_filter.mp hS).1
    have hFm_m : ∀ S ∈ Fm, S.card = m := fun S hS => (Finset.mem_filter.mp hS).2
    have hmem_Fm : ∀ c ∈ R, c ≠ D0 → c.card = m := by
      intro c hc hcne
      by_contra hne2
      have hlt : c.card < m := lt_of_le_of_ne (hcard c hc) hne2
      have hmem : c ∈ R.filter (fun c => c.card < m) := Finset.mem_filter.mpr ⟨hc, hlt⟩
      rw [hD0] at hmem
      exact hcne (Finset.mem_singleton.mp hmem)
    have hcap' : D0.card ≤ Fm.card := by omega
    obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hcap'
    have hT_R : ∀ S ∈ T, S ∈ R := fun S hS => hFm_R S (hT_sub hS)
    have hT_m : ∀ S ∈ T, S.card = m := fun S hS => hFm_m S (hT_sub hS)
    have hD0nT : D0 ∉ T := by
      intro h
      have := hT_m D0 h
      omega
    -- ambient disjointness specializes to the fiber pieces
    have hD0_disj : ∀ S ∈ T, Disjoint D0 S := by
      intro S hS
      have hne' : D0 ≠ S := by
        intro h
        have := hT_m S hS
        rw [← h] at this
        omega
      exact hdisj (Finset.mem_coe.mpr (hR hD0R))
        (Finset.mem_coe.mpr (hR (hT_R S hS))) hne'
    let e : ↥D0 ≃ ↥T := Finset.equivOfCardEq hT_card.symm
    have hvne : ∀ v : ↥D0, v.1 ∉ (e v).1 := fun v =>
      Finset.disjoint_left.mp (hD0_disj _ (e v).2) v.2
    set New : Finset (Finset V) :=
      D0.attach.image (fun v => insert v.1 (e v).1) with hNew_def
    set R' : Finset (Finset V) := (R \ insert D0 T) ∪ New with hR'_def
    -- fiber ground set is preserved (same chase as S26)
    have hfib : R'.biUnion id = R.biUnion id := by
      ext x
      simp only [hR'_def, Finset.mem_biUnion, Finset.mem_union, id_eq]
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
    -- fiber sizes
    have hsizes : ∀ c ∈ R', c.card = m ∨ c.card = m + 1 := by
      intro c hc
      rcases Finset.mem_union.mp hc with h | h
      · left
        obtain ⟨hcR, hcD⟩ := Finset.mem_sdiff.mp h
        exact hmem_Fm c hcR (fun hh => hcD (hh ▸ Finset.mem_insert_self _ _))
      · right
        obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp h
        rw [Finset.card_insert_of_notMem (hvne v), hT_m _ (e v).2]
    -- every "old" ambient piece survives: Q₀ minus the replaced subfamily
    have hold_sub : Q₀ \ insert D0 T ⊆ (Q₀ \ R) ∪ R' := by
      intro c hc
      obtain ⟨hcQ, hcD⟩ := Finset.mem_sdiff.mp hc
      by_cases hcR : c ∈ R
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr
          (Or.inl (Finset.mem_sdiff.mpr ⟨hcR, hcD⟩))))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hcQ, hcR⟩))
    -- generic disjointness of an old ambient piece from a grown piece
    have hold_new : ∀ a ∈ Q₀, a ∉ insert D0 T →
        ∀ v : ↥D0, Disjoint a (insert v.1 (e v).1) := by
      intro a haQ haD v
      have haD0 : a ≠ D0 := fun h => haD (h ▸ Finset.mem_insert_self _ _)
      have haT : a ∉ T := fun h => haD (Finset.mem_insert_of_mem h)
      rw [Finset.disjoint_insert_right]
      refine ⟨?_, ?_⟩
      · intro hva
        exact Finset.disjoint_left.mp
          (hdisj (Finset.mem_coe.mpr haQ) (Finset.mem_coe.mpr (hR hD0R)) haD0)
          hva v.2
      · exact hdisj (Finset.mem_coe.mpr haQ)
          (Finset.mem_coe.mpr (hR (hT_R _ (e v).2)))
          (fun h => haT (h ▸ (e v).2))
    -- membership in the new ambient family implies old-ambient or grown
    have hmem_cases : ∀ a ∈ (Q₀ \ R) ∪ R',
        (a ∈ Q₀ ∧ a ∉ insert D0 T) ∨ a ∈ New := by
      intro a ha
      rcases Finset.mem_union.mp ha with h | h
      · obtain ⟨haQ, haR⟩ := Finset.mem_sdiff.mp h
        exact Or.inl ⟨haQ, fun hh => haR (by
          rcases Finset.mem_insert.mp hh with h' | h'
          · exact h' ▸ hD0R
          · exact hT_R _ h')⟩
      · rcases Finset.mem_union.mp h with h' | h'
        · obtain ⟨haR, haD⟩ := Finset.mem_sdiff.mp h'
          exact Or.inl ⟨hR haR, haD⟩
        · exact Or.inr h'
    -- ambient ground set is preserved
    have hcov : ((Q₀ \ R) ∪ R').biUnion id = Q₀.biUnion id := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_union, id_eq]
      constructor
      · rintro ⟨c, hc, hx⟩
        rcases hc with hc | hc
        · exact ⟨c, (Finset.mem_sdiff.mp hc).1, hx⟩
        · have hx' : x ∈ R'.biUnion id :=
            Finset.mem_biUnion.mpr ⟨c, hc, hx⟩
          rw [hfib] at hx'
          obtain ⟨d, hd, hxd⟩ := Finset.mem_biUnion.mp hx'
          exact ⟨d, hR hd, hxd⟩
      · rintro ⟨c, hc, hx⟩
        by_cases hcR : c ∈ R
        · have hx' : x ∈ R.biUnion id := Finset.mem_biUnion.mpr ⟨c, hcR, hx⟩
          rw [← hfib] at hx'
          obtain ⟨d, hd, hxd⟩ := Finset.mem_biUnion.mp hx'
          exact ⟨d, Or.inr hd, hxd⟩
        · exact ⟨c, Or.inl (Finset.mem_sdiff.mpr ⟨hc, hcR⟩), hx⟩
    -- ambient pairwise disjointness
    have hdisj' : (↑((Q₀ \ R) ∪ R') : Set (Finset V)).PairwiseDisjoint id := by
      intro a ha b hb hab
      simp only [Function.onFun, id_eq]
      rcases hmem_cases a (Finset.mem_coe.mp ha) with ⟨haQ, haD⟩ | haN <;>
        rcases hmem_cases b (Finset.mem_coe.mp hb) with ⟨hbQ, hbD⟩ | hbN
      · exact hdisj (Finset.mem_coe.mpr haQ) (Finset.mem_coe.mpr hbQ) hab
      · obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hbN
        exact hold_new a haQ haD v
      · obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp haN
        exact (hold_new b hbQ hbD v).symm
      · obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp haN
        obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hbN
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
        · exact hdisj (Finset.mem_coe.mpr (hR (hT_R _ (e v).2)))
            (Finset.mem_coe.mpr (hR (hT_R _ (e w).2))) hevc
    -- ambient energy: one S24 replacement, subfamily D0 + receivers
    have henergy : partitionEnergy G Q₀ -
        2 * (m * m : ℚ) / (Fintype.card V : ℚ) ≤
        partitionEnergy G ((Q₀ \ R) ∪ R') := by
      have hDsub : insert D0 T ⊆ Q₀ :=
        Finset.insert_subset_iff.mpr ⟨hR hD0R, fun S hS => hR (hT_R S hS)⟩
      have hsmall : ∀ A ∈ insert D0 T, A.card ≤ m := by
        intro A hA
        rcases Finset.mem_insert.mp hA with rfl | h
        · omega
        · exact le_of_eq (hT_m A h)
      have hpe := partitionEnergy_replace_ge_of_small G hDsub hdisj hold_sub hsmall
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
    exact ⟨R', hfib, hsizes, hcov, hdisj', henergy⟩

/-- **Ambient chop refinement (S27a).**  Chopping only the fiber `S ⊆ Q₀`
(each part into size-`m` pieces, ≤ 1 deficient remainder per part) while
keeping the rest of the ambient family untouched is an ambient REFINEMENT, so
it retains the FULL ambient partition energy.  The cell assignment is S23's
fiber chop on `S` and the trivial cell `{A}` elsewhere;
`partitionEnergy_refine_mono` does the energy work. -/
theorem exists_chop_refinement_within (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hm : 1 ≤ m) (Q₀ S : Finset (Finset V)) (hS : S ⊆ Q₀)
    (hdisj : (↑Q₀ : Set (Finset V)).PairwiseDisjoint id) :
    ∃ C : Finset (Finset V),
      C.biUnion id = S.biUnion id ∧
      (∀ c ∈ C, ∃ A ∈ S, c ⊆ A) ∧
      (∀ c ∈ C, c.Nonempty) ∧
      (∀ c ∈ C, c.card ≤ m) ∧
      (C.filter (fun c => c.card < m)).card ≤ S.card ∧
      ((Q₀ \ S) ∪ C).biUnion id = Q₀.biUnion id ∧
      (↑((Q₀ \ S) ∪ C) : Set (Finset V)).PairwiseDisjoint id ∧
      partitionEnergy G Q₀ ≤ partitionEnergy G ((Q₀ \ S) ∪ C) := by
  classical
  have hSdisj : (↑S : Set (Finset V)).PairwiseDisjoint id :=
    hdisj.subset (Finset.coe_subset.mpr hS)
  obtain ⟨C, hCpar, hCcov, hCdisj, hCne, hCcard, hCdef, _hCpe⟩ :=
    exists_chop_refinement G m hm S hSdisj
  -- each cell has a unique parent block; cells of A are exactly C.filter (· ⊆ A)
  have hcell_par : ∀ c ∈ C, ∀ A ∈ S, (c ∩ A).Nonempty → c ⊆ A := by
    intro c hc A hA hint
    obtain ⟨A', hA', hsub⟩ := hCpar c hc
    obtain ⟨x, hx⟩ := hint
    have hxA : x ∈ A := (Finset.mem_inter.mp hx).2
    have hxA' : x ∈ A' := hsub (Finset.mem_inter.mp hx).1
    have : A = A' := by
      by_contra hne'
      exact Finset.disjoint_left.mp
        (hSdisj (Finset.mem_coe.mpr hA) (Finset.mem_coe.mpr hA') hne') hxA hxA'
    exact this ▸ hsub
  -- ambient pieces of Q₀ \ S are disjoint from every cell
  have hold_cell : ∀ B ∈ Q₀, B ∉ S → ∀ c ∈ C, Disjoint B c := by
    intro B hBQ hBS c hc
    obtain ⟨A, hA, hsub⟩ := hCpar c hc
    have hBA : B ≠ A := fun h => hBS (h ▸ hA)
    exact (hdisj (Finset.mem_coe.mpr hBQ) (Finset.mem_coe.mpr (hS hA))
      hBA).mono_right hsub
  refine ⟨C, hCcov, hCpar, hCne, hCcard, hCdef, ?_, ?_, ?_⟩
  · -- ambient ground set
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_union, id_eq]
    constructor
    · rintro ⟨c, hc | hc, hx⟩
      · exact ⟨c, (Finset.mem_sdiff.mp hc).1, hx⟩
      · have hx' : x ∈ S.biUnion id := by
          rw [← hCcov]
          exact Finset.mem_biUnion.mpr ⟨c, hc, hx⟩
        obtain ⟨A, hA, hxA⟩ := Finset.mem_biUnion.mp hx'
        exact ⟨A, hS hA, hxA⟩
    · rintro ⟨c, hc, hx⟩
      by_cases hcS : c ∈ S
      · have hx' : x ∈ C.biUnion id := by
          rw [hCcov]
          exact Finset.mem_biUnion.mpr ⟨c, hcS, hx⟩
        obtain ⟨d, hd, hxd⟩ := Finset.mem_biUnion.mp hx'
        exact ⟨d, Or.inr hd, hxd⟩
      · exact ⟨c, Or.inl (Finset.mem_sdiff.mpr ⟨hc, hcS⟩), hx⟩
  · -- ambient pairwise disjointness
    intro a ha b hb hab
    simp only [Function.onFun, id_eq]
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hdisj (Finset.mem_coe.mpr (Finset.mem_sdiff.mp ha).1)
        (Finset.mem_coe.mpr (Finset.mem_sdiff.mp hb).1) hab
    · exact hold_cell a (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp ha).2 b hb
    · exact (hold_cell b (Finset.mem_sdiff.mp hb).1 (Finset.mem_sdiff.mp hb).2
        a ha).symm
    · exact hCdisj (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
  · -- ambient energy retention via full refinement monotonicity
    set pieces : Finset V → Finset (Finset V) :=
      fun A => if A ∈ S then C.filter (fun c => c ⊆ A) else {A} with hpieces_def
    have hcover : ∀ A ∈ Q₀, (pieces A).biUnion id = A := by
      intro A hAQ
      by_cases hAS : A ∈ S
      · simp only [hpieces_def, if_pos hAS]
        ext x
        simp only [Finset.mem_biUnion, Finset.mem_filter, id_eq]
        constructor
        · rintro ⟨c, ⟨-, hsub⟩, hx⟩
          exact hsub hx
        · intro hx
          have hx' : x ∈ C.biUnion id := by
            rw [hCcov]
            exact Finset.mem_biUnion.mpr ⟨A, hAS, hx⟩
          obtain ⟨c, hc, hxc⟩ := Finset.mem_biUnion.mp hx'
          have hsub : c ⊆ A := hcell_par c hc A hAS ⟨x, Finset.mem_inter.mpr ⟨hxc, hx⟩⟩
          exact ⟨c, ⟨hc, hsub⟩, hxc⟩
      · simp [hpieces_def, if_neg hAS]
    have hdisjIn : ∀ A ∈ Q₀, (↑(pieces A) : Set (Finset V)).PairwiseDisjoint id := by
      intro A _hAQ
      by_cases hAS : A ∈ S
      · simp only [hpieces_def, if_pos hAS]
        exact hCdisj.subset (Finset.coe_subset.mpr (Finset.filter_subset _ _))
      · simp only [hpieces_def, if_neg hAS, Finset.coe_singleton]
        exact Set.pairwiseDisjoint_singleton _ _
    have hdisjOut : (↑Q₀ : Set (Finset V)).PairwiseDisjoint pieces := by
      intro A hA B hB hAB
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro c hcA hcB
      by_cases hAS : A ∈ S <;> by_cases hBS : B ∈ S
      · -- both fibers: a common cell meets both blocks
        simp only [hpieces_def, if_pos hAS] at hcA
        simp only [hpieces_def, if_pos hBS] at hcB
        obtain ⟨hcC, hsubA⟩ := Finset.mem_filter.mp hcA
        obtain ⟨-, hsubB⟩ := Finset.mem_filter.mp hcB
        obtain ⟨x, hx⟩ := hCne c hcC
        exact Finset.disjoint_left.mp
          (hdisj hA hB hAB) (hsubA hx) (hsubB hx)
      · -- c is a cell of A and c = B: B would be a nonempty subset of A
        simp only [hpieces_def, if_pos hAS] at hcA
        simp only [hpieces_def, if_neg hBS, Finset.mem_singleton] at hcB
        obtain ⟨hcC, hsubA⟩ := Finset.mem_filter.mp hcA
        obtain ⟨x, hx⟩ := hCne c hcC
        subst hcB
        exact Finset.disjoint_left.mp (hdisj hA hB hAB) (hsubA hx) hx
      · simp only [hpieces_def, if_neg hAS, Finset.mem_singleton] at hcA
        simp only [hpieces_def, if_pos hBS] at hcB
        obtain ⟨hcC, hsubB⟩ := Finset.mem_filter.mp hcB
        obtain ⟨x, hx⟩ := hCne c hcC
        subst hcA
        exact Finset.disjoint_left.mp (hdisj hA hB hAB) hx (hsubB hx)
      · simp only [hpieces_def, if_neg hAS, if_neg hBS,
          Finset.mem_singleton] at hcA hcB
        exact hAB (hcA ▸ hcB ▸ rfl)
    have hmono := partitionEnergy_refine_mono G Q₀ pieces hcover hdisjIn hdisjOut
    have hfam : Q₀.biUnion pieces = (Q₀ \ S) ∪ C := by
      ext c
      simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro ⟨A, hAQ, hc⟩
        by_cases hAS : A ∈ S
        · simp only [hpieces_def, if_pos hAS] at hc
          exact Or.inr (Finset.mem_filter.mp hc).1
        · simp only [hpieces_def, if_neg hAS, Finset.mem_singleton] at hc
          exact Or.inl ⟨hc ▸ hAQ, hc ▸ hAS⟩
      · rintro (⟨hcQ, hcS⟩ | hcC)
        · exact ⟨c, hcQ, by simp [hpieces_def, if_neg hcS]⟩
        · obtain ⟨A, hAS, hsub⟩ := hCpar c hcC
          exact ⟨A, hS hAS, by
            simp only [hpieces_def, if_pos hAS]
            exact Finset.mem_filter.mpr ⟨hcC, hsub⟩⟩
    rw [hfam] at hmono
    exact hmono

/-- **Ambient equitable re-cut (S27a capstone).**  For a subfamily `S` of a
pairwise-disjoint ambient family `Q₀` whose fiber ground set carries at least
`m²` vertices, the fiber re-cuts IN PLACE into pieces of exact sizes
`{m, m+1}` — ambient cover, ambient disjointness, and ambient energy up to
`2·|S|·m/n + 2·m²/n` all preserved.  Chop the fiber (ambient refinement, free)
→ pool the ≤ `|S|` deficient remainders and re-cut them (one S24 replacement)
→ absorb the single remaining deficient piece (`exists_absorb_deficient_within`).

This is the per-coarse-block re-equitization brick: applied inside one block
of the coarse partition it never moves vertices across blocks, so the
refinement invariant of the Chain oracle survives. -/
theorem exists_equitable_recut_within (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hm : 1 ≤ m) (Q₀ S : Finset (Finset V)) (hS : S ⊆ Q₀)
    (hdisj : (↑Q₀ : Set (Finset V)).PairwiseDisjoint id)
    (hground : m * m ≤ (S.biUnion id).card) :
    ∃ R : Finset (Finset V),
      R.biUnion id = S.biUnion id ∧
      (∀ c ∈ R, c.card = m ∨ c.card = m + 1) ∧
      ((Q₀ \ S) ∪ R).biUnion id = Q₀.biUnion id ∧
      (↑((Q₀ \ S) ∪ R) : Set (Finset V)).PairwiseDisjoint id ∧
      partitionEnergy G Q₀ - 2 * (S.card * m : ℚ) / (Fintype.card V : ℚ)
          - 2 * (m * m : ℚ) / (Fintype.card V : ℚ) ≤
        partitionEnergy G ((Q₀ \ S) ∪ R) := by
  classical
  -- Step 1: ambient chop refinement (energy-free)
  obtain ⟨C, hCcov, hCpar, hCne, hCcard, hCdef, hCacov, hCadisj, hCape⟩ :=
    exists_chop_refinement_within G m hm Q₀ S hS hdisj
  set A₁ : Finset (Finset V) := (Q₀ \ S) ∪ C with hA₁_def
  -- Step 2: pool the deficient cells and re-cut their union
  set D : Finset (Finset V) := C.filter (fun c => c.card < m) with hD_def
  have hD_C : D ⊆ C := Finset.filter_subset _ _
  have hD_A₁ : D ⊆ A₁ := hD_C.trans Finset.subset_union_right
  obtain ⟨F, hFcov, hFdisj, hFne, hFcard, hFdef⟩ :=
    exists_chop_pieces (V := V) m hm (D.biUnion id)
  have hF_sub : ∀ c ∈ F, c ⊆ D.biUnion id := by
    intro c hc
    calc c = id c := rfl
      _ ⊆ F.biUnion id := Finset.subset_biUnion_of_mem id hc
      _ = D.biUnion id := hFcov
  set R₁ : Finset (Finset V) := (C \ D) ∪ F with hR₁_def
  -- the recut fiber: pieces ≤ m, nonempty, ≤ 1 deficient, same fiber ground set
  have hR₁ne : ∀ c ∈ R₁, c.Nonempty := by
    intro c hc
    rcases Finset.mem_union.mp hc with h | h
    · exact hCne c (Finset.mem_sdiff.mp h).1
    · exact hFne c h
  have hR₁card : ∀ c ∈ R₁, c.card ≤ m := by
    intro c hc
    rcases Finset.mem_union.mp hc with h | h
    · exact hCcard c (Finset.mem_sdiff.mp h).1
    · exact hFcard c h
  have hR₁def : (R₁.filter (fun c => c.card < m)).card ≤ 1 := by
    have hsub : R₁.filter (fun c => c.card < m) ⊆ F.filter (fun c => c.card < m) := by
      intro c hc
      rw [Finset.mem_filter] at hc ⊢
      rcases Finset.mem_union.mp hc.1 with h | h
      · exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp h).1, hc.2⟩)
          (Finset.mem_sdiff.mp h).2
      · exact ⟨h, hc.2⟩
    exact le_trans (Finset.card_le_card hsub) hFdef
  have hR₁cov : R₁.biUnion id = S.biUnion id := by
    have hCD : (C \ D) ∪ D = C := Finset.sdiff_union_of_subset hD_C
    calc R₁.biUnion id = (C \ D).biUnion id ∪ F.biUnion id :=
          Finset.union_biUnion
      _ = (C \ D).biUnion id ∪ D.biUnion id := by rw [hFcov]
      _ = ((C \ D) ∪ D).biUnion id := Finset.union_biUnion.symm
      _ = C.biUnion id := by rw [hCD]
      _ = S.biUnion id := hCcov
  -- cells kept in C \ D are disjoint from the pooled union
  have hkeep_pool : ∀ c ∈ C \ D, Disjoint c (D.biUnion id) := by
    intro c hc
    rw [Finset.disjoint_biUnion_right]
    intro A hA
    obtain ⟨hcC, hcD⟩ := Finset.mem_sdiff.mp hc
    have hne_ : c ≠ A := fun h => hcD (h ▸ hA)
    exact hCadisj (Finset.mem_coe.mpr (Finset.mem_union_right _ hcC))
      (Finset.mem_coe.mpr (Finset.mem_union_right _ (hD_C hA))) hne_
  -- old ambient pieces are disjoint from every cell (via the cell's parent)
  have hold_cell : ∀ B ∈ Q₀ \ S, ∀ c ∈ C, Disjoint B c := by
    intro B hB c hc
    obtain ⟨P, hP, hsubP⟩ := hCpar c hc
    obtain ⟨hBQ, hBS⟩ := Finset.mem_sdiff.mp hB
    have hBP : B ≠ P := fun h => hBS (h ▸ hP)
    exact (hdisj (Finset.mem_coe.mpr hBQ) (Finset.mem_coe.mpr (hS hP))
      hBP).mono_right hsubP
  have hold_pool : ∀ B ∈ Q₀ \ S, Disjoint B (D.biUnion id) := by
    intro B hB
    rw [Finset.disjoint_biUnion_right]
    intro A hA
    exact hold_cell B hB A (hD_C hA)
  set A₂ : Finset (Finset V) := (Q₀ \ S) ∪ R₁ with hA₂_def
  -- ambient disjointness after the pooled re-cut
  have hA₂disj : (↑A₂ : Set (Finset V)).PairwiseDisjoint id := by
    intro a ha b hb hab
    simp only [Function.onFun, id_eq]
    have haA₂ := Finset.mem_coe.mp ha
    have hbA₂ := Finset.mem_coe.mp hb
    have hsplit : ∀ x ∈ A₂, x ∈ Q₀ \ S ∨ x ∈ C \ D ∨ x ∈ F := by
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact Or.inl h
      · rcases Finset.mem_union.mp h with h' | h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h')
    rcases hsplit a haA₂ with haO | haK | haF <;>
      rcases hsplit b hbA₂ with hbO | hbK | hbF
    · exact hdisj (Finset.mem_coe.mpr (Finset.mem_sdiff.mp haO).1)
        (Finset.mem_coe.mpr (Finset.mem_sdiff.mp hbO).1) hab
    · exact hold_cell a haO b (Finset.mem_sdiff.mp hbK).1
    · exact (hold_pool a haO).mono_right (hF_sub b hbF)
    · exact (hold_cell b hbO a (Finset.mem_sdiff.mp haK).1).symm
    · exact hCadisj
        (Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_sdiff.mp haK).1))
        (Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_sdiff.mp hbK).1)) hab
    · exact (hkeep_pool a haK).mono_right (hF_sub b hbF)
    · exact ((hold_pool b hbO).mono_right (hF_sub a haF)).symm
    · exact ((hkeep_pool b hbK).mono_right (hF_sub a haF)).symm
    · exact hFdisj (Finset.mem_coe.mpr haF) (Finset.mem_coe.mpr hbF) hab
  -- Step 2 energy: one S24 replacement of the pooled deficient cells
  have hA₂pe : partitionEnergy G A₁ -
      2 * (S.card * m : ℚ) / (Fintype.card V : ℚ) ≤ partitionEnergy G A₂ := by
    have hkeep : A₁ \ D ⊆ A₂ := by
      intro x hx
      obtain ⟨hxA₁, hxD⟩ := Finset.mem_sdiff.mp hx
      rcases Finset.mem_union.mp hxA₁ with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _
          (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h, hxD⟩))
    have hsmall : ∀ A ∈ D, A.card ≤ m :=
      fun A hA => le_of_lt (Finset.mem_filter.mp hA).2
    have h1 := partitionEnergy_replace_ge_of_small G hD_A₁ hCadisj hkeep hsmall
    have hDS : (D.card : ℚ) ≤ (S.card : ℚ) := by exact_mod_cast hCdef
    have hm0 : (0 : ℚ) ≤ (m : ℚ) := Nat.cast_nonneg m
    have h2 : 2 * (D.card * m : ℚ) / (Fintype.card V : ℚ) ≤
        2 * (S.card * m : ℚ) / (Fintype.card V : ℚ) := by
      have hnum : 2 * (D.card * m : ℚ) ≤ 2 * (S.card * m : ℚ) := by
        have := mul_le_mul_of_nonneg_right hDS hm0
        linarith
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr (Nat.cast_nonneg _))
    linarith
  -- Step 3: absorb the single remaining deficient piece, in ambient form
  have hR₁sub : R₁ ⊆ A₂ := Finset.subset_union_right
  have hR₁disj : (↑R₁ : Set (Finset V)).PairwiseDisjoint id :=
    hA₂disj.subset (Finset.coe_subset.mpr hR₁sub)
  -- absorption capacity from the ground-mass hypothesis
  have hcap : m ≤ (R₁.filter (fun c => c.card = m)).card + 1 := by
    have hmass : (R₁.biUnion id).card = ∑ c ∈ R₁, c.card :=
      Finset.card_biUnion (fun x hx y hy hxy => hR₁disj hx hy hxy)
    have hsum : ∑ c ∈ R₁, c.card ≤ R₁.card * m := by
      calc ∑ c ∈ R₁, c.card ≤ ∑ _c ∈ R₁, m :=
            Finset.sum_le_sum (fun c hc => hR₁card c hc)
        _ = R₁.card * m := by rw [Finset.sum_const, smul_eq_mul]
    have hRm : m ≤ R₁.card := by
      have hg : m * m ≤ (R₁.biUnion id).card := by
        rw [hR₁cov]; exact hground
      have h1 : m * m ≤ R₁.card * m := le_trans (hmass ▸ hg) hsum
      exact Nat.le_of_mul_le_mul_right h1 hm
    have hsplit := Finset.card_filter_add_card_filter_not (s := R₁)
      (fun c => c.card = m)
    have hfeq : R₁.filter (fun c => ¬ c.card = m) =
        R₁.filter (fun c => c.card < m) :=
      Finset.filter_congr (fun c hc => by have := hR₁card c hc; omega)
    rw [hfeq] at hsplit
    omega
  obtain ⟨R', hfib', hsizes', hacov', hadisj', hpe'⟩ :=
    exists_absorb_deficient_within G m hm A₂ R₁ hR₁sub hA₂disj
      hR₁ne hR₁card hR₁def hcap
  -- Step 4: the untouched ambient part is exactly Q₀ \ S
  have hA₂R₁ : A₂ \ R₁ = Q₀ \ S := by
    ext x
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨hxA₂, hxR₁⟩
      rcases Finset.mem_union.mp hxA₂ with h | h
      · exact Finset.mem_sdiff.mp h
      · exact absurd h hxR₁
    · rintro ⟨hxQ, hxS⟩
      refine ⟨Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxQ, hxS⟩), ?_⟩
      intro hxR₁
      obtain ⟨y, hy⟩ := hR₁ne x hxR₁
      have hysub : y ∈ S.biUnion id := by
        rw [← hR₁cov]
        exact Finset.mem_biUnion.mpr ⟨x, hxR₁, hy⟩
      obtain ⟨A, hA, hyA⟩ := Finset.mem_biUnion.mp hysub
      have hxA : x ≠ A := fun h => hxS (h ▸ hA)
      exact Finset.disjoint_left.mp
        (hdisj (Finset.mem_coe.mpr hxQ) (Finset.mem_coe.mpr (hS hA)) hxA) hy hyA
  have hfam : (A₂ \ R₁) ∪ R' = (Q₀ \ S) ∪ R' := by rw [hA₂R₁]
  -- assemble
  refine ⟨R', by rw [hfib', hR₁cov], hsizes', ?_, ?_, ?_⟩
  · -- ambient ground set
    have hA₂cov : A₂.biUnion id = Q₀.biUnion id := by
      calc A₂.biUnion id = (Q₀ \ S).biUnion id ∪ R₁.biUnion id :=
            Finset.union_biUnion
        _ = (Q₀ \ S).biUnion id ∪ C.biUnion id := by rw [hR₁cov, hCcov]
        _ = A₁.biUnion id := Finset.union_biUnion.symm
        _ = Q₀.biUnion id := hCacov
    rw [← hfam, hacov', hA₂cov]
  · rw [← hfam]
    exact hadisj'
  · have hA₁pe := hCape
    have hfinal : partitionEnergy G ((A₂ \ R₁) ∪ R') =
        partitionEnergy G ((Q₀ \ S) ∪ R') := by rw [hfam]
    linarith [hpe', hA₂pe, hA₁pe, hfinal.symm.le, hfinal.le]

end Szemeredi.RegularityOQ04Surgery
