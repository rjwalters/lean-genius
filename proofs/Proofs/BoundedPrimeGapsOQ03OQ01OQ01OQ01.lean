/-
  bounded-prime-gaps-oq-03-oq-01-oq-01-oq-01 — D(6) = 16 from scratch.

  Proves `minAdmissibleDiameter 6 = 16`: the minimal diameter of an admissible
  6-tuple is exactly 16 (OEIS A008407, k = 6). This is the next rung in the
  parent's materialized minimal-admissible-diameter series:

    D(2) = 2  (`BoundedPrimeGapsOQ03OQ01.minAdmissibleDiameter_2`, witness {0,2})
    D(3) = 6  (`BoundedPrimeGapsOQ03OQ01.minAdmissibleDiameter_3`, witness {0,2,6})
    D(4) = 8  (sibling slug …-oq-03-oq-01-oq-04)
    D(5) = 12 (sibling slug …-oq-03-oq-01-oq-01, witness {0,2,6,8,12})
    D(6) = 16 (this file, witness {0,4,6,10,12,16})

  This is a finite combinatorial fact — NOT the parent's open Maynard–Tao /
  Engelsma-246 barrier.

  Upper bound `D(6) ≤ 16`: the admissible witness {0,4,6,10,12,16} has diameter
  16. The diameter is computed `native_decide`-free via `min'`/`max'`
  antisymmetry, so the whole entry is axiom-free (verified).

  Lower bound `D(6) ≥ 16` (`admissible_6tuple_diam_ge_16`): a self-contained,
  `native_decide`-free argument. Unlike D(5) (which only needed p ∈ {2,3}), the
  D(6) lower bound genuinely needs p = 5:
    • p = 2 admissibility forces every element to share `min`'s parity.
    • Same parity + diameter < 16 confines H to the 8 slots
      {m, m+2, m+4, m+6, m+8, m+10, m+12, m+14}.
    • Those 8 slots split into three residue-mod-3 groups
        A = {m, m+6, m+12},  B = {m+2, m+8, m+14},  C = {m+4, m+10}.
      p = 3 admissibility forces H to miss one group entirely; missing a
      3-element group (A or B) would leave ≤ 5 slots for a 6-set, so H must
      miss the 2-element group C — pinning H to {m,m+2,m+6,m+8,m+12,m+14}.
    • That set's residues mod 5 are {m, m+1, m+2, m+3, m+4} mod 5 = all five
      classes, contradicting p = 5 admissibility.
  Only the primes p ∈ {2,3,5} are interrogated, so the proof needs no
  `Decidable IsAdmissible` instance.
-/
import Mathlib
import Proofs.BoundedPrimeGaps
import Proofs.BoundedPrimeGapsOQ03OQ01

namespace BoundedPrimeGapsOQ03OQ01OQ01OQ01

open Nat Finset BoundedPrimeGaps BoundedPrimeGapsOQ03OQ01

/-- Witness admissibility: `{0, 4, 6, 10, 12, 16}` is admissible (diameter 16).
    mod 2 → {0}; mod 3 → {0,1}; mod 5 → {0,1,2,4}; p ≥ 7 → card ≤ 6 < 7 ≤ p. -/
theorem admissible_6tuple_0_4_6_10_12_16 :
    IsAdmissible ({0, 4, 6, 10, 12, 16} : Finset ℕ) := by
  intro p hp
  have himg : (({0, 4, 6, 10, 12, 16} : Finset ℕ).image (· % p)).card ≤ 6 := by
    calc (({0, 4, 6, 10, 12, 16} : Finset ℕ).image (· % p)).card
        ≤ ({0, 4, 6, 10, 12, 16} : Finset ℕ).card := Finset.card_image_le
      _ = 6 := by decide
  by_cases hp2 : p = 2
  · subst hp2; decide
  · by_cases hp3 : p = 3
    · subst hp3; decide
    · by_cases hp5 : p = 5
      · subst hp5; decide
      · -- p ≥ 7, so image card ≤ 6 < 7 ≤ p
        have hp7 : p ≥ 7 := by
          have h2le := hp.two_le
          rcases hp.eq_two_or_odd with h2 | hodd
          · exact absurd h2 hp2
          · omega
        linarith

/-- The witness `{0, 4, 6, 10, 12, 16}` has diameter 16, proved
    `native_decide`-free via `min'`/`max'` antisymmetry. -/
theorem diam_witness : fsDiameter ({0, 4, 6, 10, 12, 16} : Finset ℕ) = 16 := by
  have hne : ({0, 4, 6, 10, 12, 16} : Finset ℕ).Nonempty := ⟨0, by decide⟩
  have hmin : ({0, 4, 6, 10, 12, 16} : Finset ℕ).min' hne = 0 := by
    apply le_antisymm
    · exact Finset.min'_le _ 0 (by decide)
    · exact Nat.zero_le _
  have hmax : ({0, 4, 6, 10, 12, 16} : Finset ℕ).max' hne = 16 := by
    apply le_antisymm
    · apply Finset.max'_le
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      omega
    · exact Finset.le_max' _ 16 (by decide)
  unfold fsDiameter
  rw [dif_pos hne, hmax, hmin]

/-- **Lower bound — the real content.** Every admissible 6-tuple has diameter
    ≥ 16. Parity (p=2) forces same parity; diameter < 16 then confines H to 8
    slots; p=3 pins H to {m,m+2,m+6,m+8,m+12,m+14}; p=5 contradicts it. -/
theorem admissible_6tuple_diam_ge_16
    (H : Finset ℕ) (hcard : H.card = 6) (hadm : IsAdmissible H) :
    16 ≤ fsDiameter H := by
  have hne : H.Nonempty := Finset.card_pos.mp (by omega)
  unfold fsDiameter; simp only [hne, dite_true]
  by_contra h_lt; push_neg at h_lt
  have hmle0 : ∀ x ∈ H, H.min' hne ≤ x := fun x hx => Finset.min'_le H x hx
  have hmmem0 : H.min' hne ∈ H := Finset.min'_mem H hne
  have hmaxmem0 : H.max' hne ∈ H := Finset.max'_mem H hne
  have hxmax0 : ∀ x ∈ H, x ≤ H.max' hne := fun x hx => Finset.le_max' H x hx
  set m := H.min' hne with hm
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
  -- Step 2: same parity + diameter < 16 ⇒ H ⊆ the 8 even-offset slots.
  have hsub8 : H ⊆ ({m, m + 2, m + 4, m + 6, m + 8, m + 10, m + 12, m + 14} : Finset ℕ) := by
    intro x hx
    have hxge := hmle0 x hx
    have hxle := hxmax0 x hx
    have hmaxle : H.max' hne ≤ m + 15 := by have := hmle0 _ hmaxmem0; omega
    have hpx := hpar x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    set d := x - m with hd
    have hdle : d ≤ 15 := by omega
    have hdev : d % 2 = 0 := by omega
    interval_cases d <;> omega
  have h3 := hadm 3 (by norm_num)
  -- Step 3a: group A = {m, m+6, m+12} (residue m%3) is met by H.
  have hPA : ∃ a ∈ H, a % 3 = m % 3 := by
    by_contra hnA
    push_neg at hnA
    have h0 : m ∉ H := fun hh => hnA m hh rfl
    have h6 : m + 6 ∉ H := fun hh => hnA (m + 6) hh (by omega)
    have h12 : m + 12 ∉ H := fun hh => hnA (m + 12) hh (by omega)
    have hsub5 : H ⊆ ({m + 2, m + 4, m + 8, m + 10, m + 14} : Finset ℕ) := by
      intro x hx
      have hx8 := hsub8 hx
      have hne0 : x ≠ m := fun h => h0 (h ▸ hx)
      have hne6 : x ≠ m + 6 := fun h => h6 (h ▸ hx)
      have hne12 : x ≠ m + 12 := fun h => h12 (h ▸ hx)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx8 ⊢
      omega
    have hle := Finset.card_le_card hsub5
    have c1 := Finset.card_insert_le (m + 2) ({m + 4, m + 8, m + 10, m + 14} : Finset ℕ)
    have c2 := Finset.card_insert_le (m + 4) ({m + 8, m + 10, m + 14} : Finset ℕ)
    have c3 := Finset.card_insert_le (m + 8) ({m + 10, m + 14} : Finset ℕ)
    have c4 := Finset.card_insert_le (m + 10) ({m + 14} : Finset ℕ)
    have c5 : ({m + 14} : Finset ℕ).card = 1 := Finset.card_singleton _
    omega
  -- Step 3b: group B = {m+2, m+8, m+14} (residue (m+2)%3) is met by H.
  have hPB : ∃ a ∈ H, a % 3 = (m + 2) % 3 := by
    by_contra hnB
    push_neg at hnB
    have h2' : m + 2 ∉ H := fun hh => hnB (m + 2) hh rfl
    have h8 : m + 8 ∉ H := fun hh => hnB (m + 8) hh (by omega)
    have h14 : m + 14 ∉ H := fun hh => hnB (m + 14) hh (by omega)
    have hsub5 : H ⊆ ({m, m + 4, m + 6, m + 10, m + 12} : Finset ℕ) := by
      intro x hx
      have hx8 := hsub8 hx
      have hne2 : x ≠ m + 2 := fun h => h2' (h ▸ hx)
      have hne8 : x ≠ m + 8 := fun h => h8 (h ▸ hx)
      have hne14 : x ≠ m + 14 := fun h => h14 (h ▸ hx)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx8 ⊢
      omega
    have hle := Finset.card_le_card hsub5
    have c1 := Finset.card_insert_le m ({m + 4, m + 6, m + 10, m + 12} : Finset ℕ)
    have c2 := Finset.card_insert_le (m + 4) ({m + 6, m + 10, m + 12} : Finset ℕ)
    have c3 := Finset.card_insert_le (m + 6) ({m + 10, m + 12} : Finset ℕ)
    have c4 := Finset.card_insert_le (m + 10) ({m + 12} : Finset ℕ)
    have c5 : ({m + 12} : Finset ℕ).card = 1 := Finset.card_singleton _
    omega
  -- Step 3c: if H also met group C = {m+4, m+10} (residue (m+4)%3), then the
  -- three distinct group-residues all appear in H.image (·%3), forcing card ≥ 3
  -- and contradicting p = 3 admissibility. So C is missed: m+4, m+10 ∉ H.
  have hnPC : ¬ ∃ a ∈ H, a % 3 = (m + 4) % 3 := by
    intro hPC
    obtain ⟨a, ha, hae⟩ := hPA
    obtain ⟨b, hb, hbe⟩ := hPB
    obtain ⟨c, hc, hce⟩ := hPC
    have hsub : ({m % 3, (m + 2) % 3, (m + 4) % 3} : Finset ℕ) ⊆ H.image (· % 3) := by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · exact Finset.mem_image.mpr ⟨a, ha, hae⟩
      · exact Finset.mem_image.mpr ⟨b, hb, hbe⟩
      · exact Finset.mem_image.mpr ⟨c, hc, hce⟩
    have hc3 : ({m % 3, (m + 2) % 3, (m + 4) % 3} : Finset ℕ).card = 3 :=
      Finset.card_eq_three.mpr
        ⟨m % 3, (m + 2) % 3, (m + 4) % 3, by omega, by omega, by omega, rfl⟩
    have := Finset.card_le_card hsub
    omega
  push_neg at hnPC
  have h4 : m + 4 ∉ H := fun hh => hnPC (m + 4) hh rfl
  have h10 : m + 10 ∉ H := fun hh => hnPC (m + 10) hh (by omega)
  -- Step 3d: H ⊆ the 6-set, and |H| = 6, so H equals it (all six are present).
  have hsubT : H ⊆ ({m, m + 2, m + 6, m + 8, m + 12, m + 14} : Finset ℕ) := by
    intro x hx
    have hx8 := hsub8 hx
    have hne4 : x ≠ m + 4 := fun h => h4 (h ▸ hx)
    have hne10 : x ≠ m + 10 := fun h => h10 (h ▸ hx)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx8 ⊢
    omega
  have hTle : ({m, m + 2, m + 6, m + 8, m + 12, m + 14} : Finset ℕ).card ≤ H.card := by
    rw [hcard]
    have c1 := Finset.card_insert_le m ({m + 2, m + 6, m + 8, m + 12, m + 14} : Finset ℕ)
    have c2 := Finset.card_insert_le (m + 2) ({m + 6, m + 8, m + 12, m + 14} : Finset ℕ)
    have c3 := Finset.card_insert_le (m + 6) ({m + 8, m + 12, m + 14} : Finset ℕ)
    have c4 := Finset.card_insert_le (m + 8) ({m + 12, m + 14} : Finset ℕ)
    have c5 := Finset.card_insert_le (m + 12) ({m + 14} : Finset ℕ)
    have c6 : ({m + 14} : Finset ℕ).card = 1 := Finset.card_singleton _
    omega
  have hHeq : H = ({m, m + 2, m + 6, m + 8, m + 12, m + 14} : Finset ℕ) :=
    Finset.eq_of_subset_of_card_le hsubT hTle
  have hm0 : m ∈ H := by rw [hHeq]; simp
  have hm2 : m + 2 ∈ H := by rw [hHeq]; simp
  have hm6 : m + 6 ∈ H := by rw [hHeq]; simp
  have hm8 : m + 8 ∈ H := by rw [hHeq]; simp
  have hm14 : m + 14 ∈ H := by rw [hHeq]; simp
  -- Step 4: those six elements realize all five residues mod 5 — contradiction.
  have h5 := hadm 5 (by norm_num)
  have hsub5img :
      ({m % 5, (m + 1) % 5, (m + 2) % 5, (m + 3) % 5, (m + 4) % 5} : Finset ℕ)
        ⊆ H.image (· % 5) := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨m, hm0, rfl⟩
    · exact Finset.mem_image.mpr ⟨m + 6, hm6, by omega⟩
    · exact Finset.mem_image.mpr ⟨m + 2, hm2, rfl⟩
    · exact Finset.mem_image.mpr ⟨m + 8, hm8, by omega⟩
    · exact Finset.mem_image.mpr ⟨m + 14, hm14, by omega⟩
  have heq5 :
      ({m % 5, (m + 1) % 5, (m + 2) % 5, (m + 3) % 5, (m + 4) % 5} : Finset ℕ)
        = ({0, 1, 2, 3, 4} : Finset ℕ) := by
    ext r
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hc5 : ({0, 1, 2, 3, 4} : Finset ℕ).card = 5 := by decide
  have hle := Finset.card_le_card hsub5img
  rw [heq5] at hle
  omega

/-- **D(6) = 16.** Same `le_antisymm` assembly as `minAdmissibleDiameter_5`. -/
theorem minAdmissibleDiameter_6 : minAdmissibleDiameter 6 = 16 := by
  apply le_antisymm
  · -- Upper: {0,4,6,10,12,16} witnesses D(6) ≤ 16
    apply csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩
    exact ⟨{0, 4, 6, 10, 12, 16}, by decide, admissible_6tuple_0_4_6_10_12_16, diam_witness⟩
  · -- Lower: every admissible 6-tuple has diameter ≥ 16
    have hne : Set.Nonempty
        {d | ∃ H : Finset ℕ, H.card = 6 ∧ IsAdmissible H ∧ fsDiameter H = d} :=
      ⟨16, {0, 4, 6, 10, 12, 16}, by decide, admissible_6tuple_0_4_6_10_12_16, diam_witness⟩
    apply le_csInf hne
    rintro d ⟨H, hcard, hadm, rfl⟩
    exact admissible_6tuple_diam_ge_16 H hcard hadm

end BoundedPrimeGapsOQ03OQ01OQ01OQ01
