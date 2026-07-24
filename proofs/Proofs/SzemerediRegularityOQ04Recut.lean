/-
  Szemerédi Regularity OQ04 — S25: the equitable re-cut (merging half, combinatorial)

  S23 (`ChopRefine`) chopped every part of a pairwise-disjoint family into
  size-`m` pieces with at most one deficient (`< m`) remainder PER PART and full
  energy retention.  S24 (`MergeLoss`) bounded the energy cost of replacing any
  subfamily `D` by fresh material at `2·mass(D)/n`.  This file executes the
  outstanding MERGING step and closes the combinatorial half of re-equitization:

  **`exists_equitable_recut`** — every pairwise-disjoint family `P` admits a
  re-cut `R` of the same ground set into nonempty pieces of size ≤ `m` with
  **at most ONE deficient piece globally**, at an energy cost of at most
  `2·|P|·m/n`:

      `partitionEnergy G P − 2·|P|·m/n ≤ partitionEnergy G R`.

  Construction: chop-refine `P` into `Q` (S23; ≤ `|P|` deficient pieces, no
  energy loss), pool the deficient pieces `D = {c ∈ Q : |c| < m}`, re-cut their
  union with the single-block chopping engine (S22/S23 `exists_chop_pieces`,
  ≤ 1 deficient piece), and keep `Q \ D` untouched.  Every piece of `Q \ D`
  has size exactly ≥ `m`, so the only possible deficient piece of the result
  is the single remainder of the pooled re-cut.  The energy bound is S24's
  `partitionEnergy_replace_ge_of_small` with `|D| ≤ |P|`.

  This discharges the "single-block re-cut of the pooled deficient union"
  residual recorded in S24; what remains for the AFKS assembly is pure
  parameter bookkeeping (`2·|P|·m/n` below the retained gain) in the
  maintained-oracle invariant.

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large
  graphs", Combinatorica 20 (2000); Komlós–Simonovits (1996).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04ChopRefine
import Proofs.SzemerediRegularityOQ04MergeLoss

namespace Szemeredi.RegularityOQ04Recut

open Szemeredi.Core Szemeredi.Regularity Szemeredi.RegularityOQ04Energy
open Szemeredi.RegularityOQ04Bridge Szemeredi.RegularityOQ04ChopRefine
open Szemeredi.RegularityOQ04MergeLoss

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The equitable re-cut (S25 capstone).**  Every pairwise-disjoint family
`P` re-cuts into a pairwise-disjoint family `R` covering the same ground set,
with all pieces nonempty of size ≤ `m` and **at most one deficient piece
(`< m`) globally**, losing at most `2·|P|·m/n` of partition energy.

Chop-refine (S23, lossless, ≤ `|P|` deficient) → pool the deficient pieces →
re-cut the pooled union (S22 engine, ≤ 1 deficient) → bound the swap cost
(S24).  This is the merging half of AFKS re-equitization. -/
theorem exists_equitable_recut (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hm : 1 ≤ m) (P : Finset (Finset V))
    (hdisj : (↑P : Set (Finset V)).PairwiseDisjoint id) :
    ∃ R : Finset (Finset V),
      R.biUnion id = P.biUnion id ∧
      (↑R : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ c ∈ R, c.Nonempty) ∧
      (∀ c ∈ R, c.card ≤ m) ∧
      (R.filter (fun c => c.card < m)).card ≤ 1 ∧
      partitionEnergy G P - 2 * (P.card * m : ℚ) / (Fintype.card V : ℚ) ≤
        partitionEnergy G R := by
  classical
  -- S23: lossless chop-refinement with ≤ |P| deficient pieces
  obtain ⟨Q, _hQref, hQcov, hQdisj, hQne, hQcard, hQdef, hQpe⟩ :=
    exists_chop_refinement G m hm P hdisj
  -- pool the deficient pieces
  set D : Finset (Finset V) := Q.filter (fun c => c.card < m) with hD_def
  have hD_sub : D ⊆ Q := Finset.filter_subset _ _
  -- S22 engine: re-cut the pooled union with ≤ 1 deficient piece
  obtain ⟨F, hFcov, hFdisj, hFne, hFcard, hFdef⟩ :=
    exists_chop_pieces (V := V) m hm (D.biUnion id)
  -- every piece of F sits inside the pooled union
  have hF_sub : ∀ c ∈ F, c ⊆ D.biUnion id := by
    intro c hc
    calc c = id c := rfl
      _ ⊆ F.biUnion id := Finset.subset_biUnion_of_mem id hc
      _ = D.biUnion id := hFcov
  -- kept pieces are disjoint from the pooled union
  have hkeep_disj_pool : ∀ c ∈ Q \ D, Disjoint c (D.biUnion id) := by
    intro c hc
    rw [Finset.disjoint_biUnion_right]
    intro A hA
    obtain ⟨hcQ, hcD⟩ := Finset.mem_sdiff.mp hc
    have hne_ : c ≠ A := fun h => hcD (h ▸ hA)
    exact hQdisj (Finset.mem_coe.mpr hcQ) (Finset.mem_coe.mpr (hD_sub hA)) hne_
  refine ⟨(Q \ D) ∪ F, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- same ground set
    have hsplit : ((Q \ D) ∪ F).biUnion id = Q.biUnion id := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_union, id_eq]
      constructor
      · rintro ⟨c, hc | hc, hx⟩
        · exact ⟨c, (Finset.mem_sdiff.mp hc).1, hx⟩
        · obtain ⟨A, hA, hxA⟩ := Finset.mem_biUnion.mp (hF_sub c hc hx)
          exact ⟨A, hD_sub hA, hxA⟩
      · rintro ⟨c, hc, hx⟩
        by_cases hcD : c ∈ D
        · have hxU : x ∈ F.biUnion id := by
            rw [hFcov]
            exact Finset.mem_biUnion.mpr ⟨c, hcD, hx⟩
          obtain ⟨d, hd, hxd⟩ := Finset.mem_biUnion.mp hxU
          exact ⟨d, Or.inr hd, hxd⟩
        · exact ⟨c, Or.inl (Finset.mem_sdiff.mpr ⟨hc, hcD⟩), hx⟩
    rw [hsplit, hQcov]
  · -- pairwise disjointness of the assembled family
    intro a ha b hb hab
    simp only [Function.onFun, id_eq]
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hQdisj (Finset.mem_coe.mpr (Finset.mem_sdiff.mp ha).1)
        (Finset.mem_coe.mpr (Finset.mem_sdiff.mp hb).1) hab
    · exact (hkeep_disj_pool a ha).mono_right (hF_sub b hb)
    · exact ((hkeep_disj_pool b hb).mono_right (hF_sub a ha)).symm
    · exact hFdisj (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
  · -- nonempty pieces
    intro c hc
    rcases Finset.mem_union.mp hc with h | h
    · exact hQne c (Finset.mem_sdiff.mp h).1
    · exact hFne c h
  · -- size bound
    intro c hc
    rcases Finset.mem_union.mp hc with h | h
    · exact hQcard c (Finset.mem_sdiff.mp h).1
    · exact hFcard c h
  · -- at most one deficient piece: all of Q \ D has size ≥ m by construction
    have hsub : ((Q \ D) ∪ F).filter (fun c => c.card < m) ⊆
        F.filter (fun c => c.card < m) := by
      intro c hc
      rw [Finset.mem_filter] at hc ⊢
      rcases Finset.mem_union.mp hc.1 with h | h
      · exact absurd (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp h).1, hc.2⟩)
          (Finset.mem_sdiff.mp h).2
      · exact ⟨h, hc.2⟩
    exact le_trans (Finset.card_le_card hsub) hFdef
  · -- energy: S24 replace bound with |D| ≤ |P|
    have hkeep : Q \ D ⊆ (Q \ D) ∪ F := Finset.subset_union_left
    have hsmall : ∀ A ∈ D, A.card ≤ m :=
      fun A hA => le_of_lt (Finset.mem_filter.mp hA).2
    have h1 := partitionEnergy_replace_ge_of_small G hD_sub hQdisj hkeep hsmall
    have hDP : (D.card : ℚ) ≤ (P.card : ℚ) := by exact_mod_cast hQdef
    have hm0 : (0 : ℚ) ≤ (m : ℚ) := Nat.cast_nonneg m
    have h2 : 2 * (D.card * m : ℚ) / (Fintype.card V : ℚ) ≤
        2 * (P.card * m : ℚ) / (Fintype.card V : ℚ) := by
      have hnum : 2 * (D.card * m : ℚ) ≤ 2 * (P.card * m : ℚ) := by
        have := mul_le_mul_of_nonneg_right hDP hm0
        linarith
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr (Nat.cast_nonneg _))
    linarith

/-- **Granularity-1 sanity instance**: at `m = 1` the re-cut is the discrete
partition bound — every piece is a nonempty singleton-sized set (`≤ 1`), no
piece is deficient (`< 1` means empty, excluded by nonemptiness), and the
energy cost bound specializes to `2·|P|/n`. -/
theorem exists_equitable_recut_unit (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset (Finset V))
    (hdisj : (↑P : Set (Finset V)).PairwiseDisjoint id) :
    ∃ R : Finset (Finset V),
      R.biUnion id = P.biUnion id ∧
      (↑R : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ c ∈ R, c.card = 1) ∧
      partitionEnergy G P - 2 * (P.card : ℚ) / (Fintype.card V : ℚ) ≤
        partitionEnergy G R := by
  obtain ⟨R, hcov, hRdisj, hRne, hRcard, _hRdef, hRpe⟩ :=
    exists_equitable_recut G 1 le_rfl P hdisj
  refine ⟨R, hcov, hRdisj, ?_, ?_⟩
  · intro c hc
    have h1 := hRcard c hc
    have h2 := Finset.card_pos.mpr (hRne c hc)
    omega
  · calc partitionEnergy G P - 2 * (P.card : ℚ) / (Fintype.card V : ℚ)
        = partitionEnergy G P - 2 * (P.card * (1 : ℕ) : ℚ) / (Fintype.card V : ℚ) := by
          norm_num
      _ ≤ partitionEnergy G R := hRpe

end Szemeredi.RegularityOQ04Recut
