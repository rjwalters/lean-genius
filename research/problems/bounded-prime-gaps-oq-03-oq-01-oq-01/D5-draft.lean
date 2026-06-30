/-
  DRAFT SKELETON (NOT registered, NOT in Proofs.lean — zero build-gate risk).
  bounded-prime-gaps-oq-03-oq-01-oq-01 — D(5) = 12 from scratch.

  OBSERVE/PROVE-phase draft (researcher-1, 2026-06-16). Authored under DUAL
  BLACKOUT (Docker `docker run` hangs exit 124; Aristotle MCP `prove` 404), so
  the full file is UNVERIFIED (build-pending). Mirrors the parent's
  `minAdmissibleDiameter_2` / `minAdmissibleDiameter_3` proof shape
  (`BoundedPrimeGapsOQ03OQ01.lean:173/188`) and reuses the verified library
  lemma `BoundedPrimeGaps.admissible_quintuple_0_2_6_8_12` for the witness.

  Obligations — both now discharged in this draft (build-pending):
    (1) `admissible_5tuple_0_2_6_8_12` — witness admissibility. **DONE.** Now a
        one-line delegation to the already-registered, verified
        `admissible_quintuple_0_2_6_8_12` (BoundedPrimeGaps.lean:572) — the
        earlier hand-transcribed copy was redundant.
    (2) `admissible_5tuple_diam_ge_12` — the lower bound (the real content).
        **DONE** (S3, researcher-1, 2026-06-16). Self-contained proof, no
        `native_decide`, mirroring the verified `admissible_triple_diam_ge_6`
        parity argument. Structure:
          • p = 2 admissibility forces ALL elements to share `min`'s parity
            (`(H.image (·%2)).card < 2 ⇒ = 1`), exactly the mixed-parity step
            of the D(3) proof.
          • Same parity + diameter < 12 ⇒ every element is `min + 2k`,
            `k ∈ {0,…,5}`, i.e. `H ⊆ {m, m+2, m+4, m+6, m+8, m+10}` (`hsub6`).
          • Split that 6-set into two disjoint mod-3-complete triples
            `{m, m+2, m+4}` and `{m+6, m+8, m+10}`: the residues
            `m, m+2, m+4 (mod 3)` are all of `{0,1,2}` (and likewise the shift
            by 6). If H contained an entire triple, `(H.image (·%3)).card = 3`,
            contradicting p = 3 admissibility — so H omits ≥ 1 element from
            EACH triple, i.e. ≥ 2 omissions. But `H ⊆` a 6-set with `card 5`
            omits exactly 1. The card bookkeeping (`insert a (insert b H)` has
            card 7 ≤ 6) closes it.

  This decidability route AVOIDS the `native_decide`/`Decidable IsAdmissible`
  obstruction noted in S2: `IsAdmissible` is `∀ p prime, …` and is handled
  symbolically (only p ∈ {2,3} are interrogated), so the proof is `decide`-free
  on the admissibility predicate and should compile from Mathlib alone.

  On a Docker-up worktree: build this file; if green, transcribe into a new
  registered `Proofs/BoundedPrimeGapsOQ03OQ01OQ01.lean` (or fold into the parent
  next to D(2)/D(3)) and register in `Proofs.lean`.
-/
import Mathlib
import Proofs.BoundedPrimeGaps
import Proofs.BoundedPrimeGapsOQ03OQ01

namespace BoundedPrimeGapsOQ03OQ01OQ01

open Nat Finset BoundedPrimeGaps BoundedPrimeGapsOQ03OQ01

/-- Witness admissibility: `{0, 2, 6, 8, 12}` is admissible (diameter 12).
    Delegates to the verified, already-registered
    `BoundedPrimeGaps.admissible_quintuple_0_2_6_8_12`. -/
theorem admissible_5tuple_0_2_6_8_12 :
    IsAdmissible ({0, 2, 6, 8, 12} : Finset ℕ) :=
  admissible_quintuple_0_2_6_8_12

/-- **Lower bound — the real content.** Every admissible 5-tuple has diameter
    ≥ 12. Parity (mod 2) forces same parity; then diameter < 12 confines the set
    to `{m, m+2, m+4, m+6, m+8, m+10}`, whose two disjoint mod-3-complete triples
    each must lose an element, forcing ≥ 2 omissions from a 6-set of card 5. -/
theorem admissible_5tuple_diam_ge_12
    (H : Finset ℕ) (hcard : H.card = 5) (hadm : IsAdmissible H) :
    12 ≤ fsDiameter H := by
  have hne : H.Nonempty := Finset.card_pos.mp (by omega)
  unfold fsDiameter; simp only [hne, dite_true]
  by_contra h_lt; push_neg at h_lt
  -- Facts about min'/max' captured BEFORE `set` so the abbreviation folds them.
  have hmle0 : ∀ x ∈ H, H.min' hne ≤ x := fun x hx => Finset.min'_le H x hx
  have hmmem0 : H.min' hne ∈ H := Finset.min'_mem H hne
  have hmaxmem0 : H.max' hne ∈ H := Finset.max'_mem H hne
  have hxmax0 : ∀ x ∈ H, x ≤ H.max' hne := fun x hx => Finset.le_max' H x hx
  set m := H.min' hne with hm
  -- Now: h_lt : H.max' hne - m < 12, hmle0 : ∀ x ∈ H, m ≤ x, hmmem0 : m ∈ H.
  -- Step 1: p = 2 admissibility ⇒ every element shares m's parity.
  have h2 := hadm 2 (by norm_num)
  have hpar : ∀ x ∈ H, x % 2 = m % 2 := by
    intro x hx
    by_contra hdiff
    have hsub : ({x % 2, m % 2} : Finset ℕ) ⊆ H.image (· % 2) := by
      rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hmmem0⟩
    have hc2 : ({x % 2, m % 2} : Finset ℕ).card = 2 :=
      Finset.card_eq_two.mpr ⟨x % 2, m % 2, hdiff, rfl⟩
    have := Finset.card_le_card hsub
    omega
  -- Step 2: same parity + diameter < 12 ⇒ H ⊆ {m, m+2, m+4, m+6, m+8, m+10}.
  have hsub6 : H ⊆ ({m, m + 2, m + 4, m + 6, m + 8, m + 10} : Finset ℕ) := by
    intro x hx
    have hxge := hmle0 x hx
    have hxle := hxmax0 x hx
    have hmaxle : H.max' hne ≤ m + 11 := by
      have := hmle0 _ hmaxmem0; omega
    have hpx := hpar x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    set d := x - m with hd
    have hdle : d ≤ 11 := by omega
    have hdev : d % 2 = 0 := by omega
    interval_cases d <;> omega
  -- Step 3a: H cannot contain all of {m, m+2, m+4} (mod 3 would be covered).
  have hnotT1 : m ∉ H ∨ m + 2 ∉ H ∨ m + 4 ∉ H := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h0, h2', h4'⟩ := hcon
    have h3 := hadm 3 (by norm_num)
    have hsub : ({m % 3, (m + 2) % 3, (m + 4) % 3} : Finset ℕ) ⊆ H.image (· % 3) := by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · exact Finset.mem_image_of_mem _ h0
      · exact Finset.mem_image_of_mem _ h2'
      · exact Finset.mem_image_of_mem _ h4'
    have hc3 : ({m % 3, (m + 2) % 3, (m + 4) % 3} : Finset ℕ).card = 3 :=
      Finset.card_eq_three.mpr
        ⟨m % 3, (m + 2) % 3, (m + 4) % 3, by omega, by omega, by omega, rfl⟩
    have := Finset.card_le_card hsub
    omega
  -- Step 3b: likewise H cannot contain all of {m+6, m+8, m+10}.
  have hnotT2 : m + 6 ∉ H ∨ m + 8 ∉ H ∨ m + 10 ∉ H := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h6, h8, h10⟩ := hcon
    have h3 := hadm 3 (by norm_num)
    have hsub : ({(m + 6) % 3, (m + 8) % 3, (m + 10) % 3} : Finset ℕ) ⊆ H.image (· % 3) := by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · exact Finset.mem_image_of_mem _ h6
      · exact Finset.mem_image_of_mem _ h8
      · exact Finset.mem_image_of_mem _ h10
    have hc3 : ({(m + 6) % 3, (m + 8) % 3, (m + 10) % 3} : Finset ℕ).card = 3 :=
      Finset.card_eq_three.mpr
        ⟨(m + 6) % 3, (m + 8) % 3, (m + 10) % 3, by omega, by omega, by omega, rfl⟩
    have := Finset.card_le_card hsub
    omega
  -- Step 4: two omissions a (from T1) and b (from T2), a ≠ b, both in the
  -- 6-set ⇒ insert a (insert b H) has card 7 inside a card-≤-6 set. Absurd.
  have key : ∀ a b : ℕ,
      a ∈ ({m, m + 2, m + 4, m + 6, m + 8, m + 10} : Finset ℕ) →
      b ∈ ({m, m + 2, m + 4, m + 6, m + 8, m + 10} : Finset ℕ) →
      a ≠ b → a ∉ H → b ∉ H → False := by
    intro a b ha hb hab hna hnb
    have ha_notin : a ∉ insert b H := by
      simp only [Finset.mem_insert]; push_neg; exact ⟨hab, hna⟩
    have hcardins : (insert a (insert b H)).card = 7 := by
      rw [Finset.card_insert_of_not_mem ha_notin,
          Finset.card_insert_of_not_mem hnb, hcard]
    have hins : insert a (insert b H) ⊆
        ({m, m + 2, m + 4, m + 6, m + 8, m + 10} : Finset ℕ) := by
      intro x hx
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | rfl | hx
      · exact ha
      · exact hb
      · exact hsub6 hx
    have hcardle := Finset.card_le_card hins
    have c1 := Finset.card_insert_le m ({m + 2, m + 4, m + 6, m + 8, m + 10} : Finset ℕ)
    have c2 := Finset.card_insert_le (m + 2) ({m + 4, m + 6, m + 8, m + 10} : Finset ℕ)
    have c3 := Finset.card_insert_le (m + 4) ({m + 6, m + 8, m + 10} : Finset ℕ)
    have c4 := Finset.card_insert_le (m + 6) ({m + 8, m + 10} : Finset ℕ)
    have c5 := Finset.card_insert_le (m + 8) ({m + 10} : Finset ℕ)
    have c6 : ({m + 10} : Finset ℕ).card = 1 := Finset.card_singleton _
    omega
  rcases hnotT1 with ha | ha | ha
  · rcases hnotT2 with hb | hb | hb
    · exact key m (m + 6)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega) (by omega) ha hb
    · exact key m (m + 8)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega) (by omega) ha hb
    · exact key m (m + 10)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega) (by omega) ha hb
  · rcases hnotT2 with hb | hb | hb
    · exact key (m + 2) (m + 6)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega) (by omega) ha hb
    · exact key (m + 2) (m + 8)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega) (by omega) ha hb
    · exact key (m + 2) (m + 10)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega) (by omega) ha hb
  · rcases hnotT2 with hb | hb | hb
    · exact key (m + 4) (m + 6)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega) (by omega) ha hb
    · exact key (m + 4) (m + 8)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega) (by omega) ha hb
    · exact key (m + 4) (m + 10)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
        (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega) (by omega) ha hb

/-- D(5) = 12. Same `le_antisymm` assembly as `minAdmissibleDiameter_3`. -/
theorem minAdmissibleDiameter_5 : minAdmissibleDiameter 5 = 12 := by
  apply le_antisymm
  · -- Upper: {0,2,6,8,12} witnesses D(5) ≤ 12
    apply csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩
    exact ⟨{0, 2, 6, 8, 12}, by decide, admissible_5tuple_0_2_6_8_12, by native_decide⟩
  · -- Lower: every admissible 5-tuple has diameter ≥ 12
    have hne : Set.Nonempty
        {d | ∃ H : Finset ℕ, H.card = 5 ∧ IsAdmissible H ∧ fsDiameter H = d} :=
      ⟨12, {0, 2, 6, 8, 12}, by decide, admissible_5tuple_0_2_6_8_12, by native_decide⟩
    apply le_csInf hne
    rintro d ⟨H, hcard, hadm, rfl⟩
    exact admissible_5tuple_diam_ge_12 H hcard hadm

end BoundedPrimeGapsOQ03OQ01OQ01
