/-
  bounded-prime-gaps-oq-03-oq-01-oq-01 — D(5) = 12 from scratch.

  Proves `minAdmissibleDiameter 5 = 12`: the minimal diameter of an admissible
  5-tuple is exactly 12 (OEIS A008407, k = 5). This is the next rung in the
  parent's materialized minimal-admissible-diameter series:

    D(2) = 2  (`BoundedPrimeGapsOQ03OQ01.minAdmissibleDiameter_2`, witness {0,2})
    D(3) = 6  (`BoundedPrimeGapsOQ03OQ01.minAdmissibleDiameter_3`, witness {0,2,6})
    D(4) = 8  (sibling slug …-oq-03-oq-01-oq-04)
    D(5) = 12 (this file, witness {0,2,6,8,12})

  This is a finite combinatorial fact — NOT the parent's open Maynard–Tao /
  Engelsma-246 barrier.

  Upper bound `D(5) ≤ 12`: the admissible witness {0,2,6,8,12} (reusing the
  verified `BoundedPrimeGaps.admissible_quintuple_0_2_6_8_12`); its diameter is
  computed symbolically by `fsDiameter_0_2_6_8_12` (`max' = 12`, `min' = 0`), so
  the headline `D(5) = 12` is now `native_decide`-free and carries **no**
  `Lean.ofReduceBool` axiom — the whole result is fully kernel-verified.

  Lower bound `D(5) ≥ 12` (`admissible_5tuple_diam_ge_12`): a self-contained,
  `native_decide`-free parity argument mirroring the verified parent lemma
  `admissible_triple_diam_ge_6`:
    • p = 2 admissibility forces every element to share `min`'s parity.
    • Same parity + diameter < 12 confines H to {m, m+2, m+4, m+6, m+8, m+10}.
    • That 6-set splits into two disjoint mod-3-complete triples
      {m,m+2,m+4} and {m+6,m+8,m+10}; p = 3 admissibility forbids H from
      containing either triple in full, so H omits ≥ 1 element from EACH —
      ≥ 2 omissions from a 6-set, impossible for a 5-set.
  Only the primes p ∈ {2,3} are interrogated, so the proof needs no
  `Decidable IsAdmissible` instance.
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

/-- `fsDiameter {0,2,6,8,12} = 12`, proved symbolically (`max' = 12`,
    `min' = 0`) so that the headline `D(5) = 12` carries **no**
    `Lean.ofReduceBool` axiom. This replaces the previous `native_decide`
    closed-term reductions of the witness diameter, leaving the whole entry
    fully kernel-verified. -/
theorem fsDiameter_0_2_6_8_12 :
    fsDiameter ({0, 2, 6, 8, 12} : Finset ℕ) = 12 := by
  have hne : ({0, 2, 6, 8, 12} : Finset ℕ).Nonempty := ⟨0, by decide⟩
  have hmax : ({0, 2, 6, 8, 12} : Finset ℕ).max' hne = 12 := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      omega
    · apply Finset.le_max'
      decide
  have hmin : ({0, 2, 6, 8, 12} : Finset ℕ).min' hne = 0 := by
    apply le_antisymm
    · apply Finset.min'_le
      decide
    · apply Finset.le_min'
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      omega
  unfold fsDiameter
  rw [dif_pos hne, hmax, hmin]

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
  -- Membership of each candidate element in the 6-set, by explicit
  -- `Finset.mem_insert` terms (search-free — avoids an `omega` blow-up on the
  -- 6-way disjunction that `simp [mem_insert]` produces).
  have e0 : m ∈ ({m, m + 2, m + 4, m + 6, m + 8, m + 10} : Finset ℕ) :=
    Finset.mem_insert_self _ _
  have e2 : m + 2 ∈ ({m, m + 2, m + 4, m + 6, m + 8, m + 10} : Finset ℕ) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have e4 : m + 4 ∈ ({m, m + 2, m + 4, m + 6, m + 8, m + 10} : Finset ℕ) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have e6 : m + 6 ∈ ({m, m + 2, m + 4, m + 6, m + 8, m + 10} : Finset ℕ) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  have e8 : m + 8 ∈ ({m, m + 2, m + 4, m + 6, m + 8, m + 10} : Finset ℕ) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))
  have e10 : m + 10 ∈ ({m, m + 2, m + 4, m + 6, m + 8, m + 10} : Finset ℕ) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))))
  rcases hnotT1 with ha | ha | ha
  · rcases hnotT2 with hb | hb | hb
    · exact key m (m + 6) e0 e6 (by omega) ha hb
    · exact key m (m + 8) e0 e8 (by omega) ha hb
    · exact key m (m + 10) e0 e10 (by omega) ha hb
  · rcases hnotT2 with hb | hb | hb
    · exact key (m + 2) (m + 6) e2 e6 (by omega) ha hb
    · exact key (m + 2) (m + 8) e2 e8 (by omega) ha hb
    · exact key (m + 2) (m + 10) e2 e10 (by omega) ha hb
  · rcases hnotT2 with hb | hb | hb
    · exact key (m + 4) (m + 6) e4 e6 (by omega) ha hb
    · exact key (m + 4) (m + 8) e4 e8 (by omega) ha hb
    · exact key (m + 4) (m + 10) e4 e10 (by omega) ha hb

/-- **D(5) = 12.** Same `le_antisymm` assembly as `minAdmissibleDiameter_3`. -/
theorem minAdmissibleDiameter_5 : minAdmissibleDiameter 5 = 12 := by
  apply le_antisymm
  · -- Upper: {0,2,6,8,12} witnesses D(5) ≤ 12
    apply csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩
    exact ⟨{0, 2, 6, 8, 12}, by decide, admissible_5tuple_0_2_6_8_12, fsDiameter_0_2_6_8_12⟩
  · -- Lower: every admissible 5-tuple has diameter ≥ 12
    have hne : Set.Nonempty
        {d | ∃ H : Finset ℕ, H.card = 5 ∧ IsAdmissible H ∧ fsDiameter H = d} :=
      ⟨12, {0, 2, 6, 8, 12}, by decide, admissible_5tuple_0_2_6_8_12, fsDiameter_0_2_6_8_12⟩
    apply le_csInf hne
    rintro d ⟨H, hcard, hadm, rfl⟩
    exact admissible_5tuple_diam_ge_12 H hcard hadm

end BoundedPrimeGapsOQ03OQ01OQ01
