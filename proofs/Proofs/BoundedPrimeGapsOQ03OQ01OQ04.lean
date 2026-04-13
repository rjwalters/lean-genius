import Mathlib
import Proofs.BoundedPrimeGaps
import Proofs.BoundedPrimeGapsOQ03OQ01

/-
# D(4) = 8: The Minimum Diameter of Admissible 4-Tuples

## Open Question (bounded-prime-gaps-oq-03-oq-01-oq-04)

"Prove D(4) = 8 from scratch, following the D(2) = 2 and D(3) = 6 pattern."

## Background

The minimum admissible diameter D(k) is the smallest possible diameter (max - min)
of an admissible k-tuple. The OEIS A008407 sequence gives:
  D(1) = 0, D(2) = 2, D(3) = 6, D(4) = 8, D(5) = 12, ...

The BoundedPrimeGapsOQ03OQ01 file proved D(2) = 2 and D(3) = 6. This file proves D(4) = 8.

## Proof Strategy

**Upper bound** (D(4) ≤ 8): {0, 2, 6, 8} is admissible with diameter 8.
  - mod 2: {0, 0, 0, 0} → card 1 < 2 ✓
  - mod 3: {0, 2, 0, 2} → card 2 < 3 ✓
  - mod p for p ≥ 5: card ≤ 4 < p ✓

**Lower bound** (D(4) ≥ 8): Every admissible 4-tuple has diameter ≥ 8.

Proof:
1. **Same parity** (mod 2 constraint): any admissible set must have all elements
   with the same parity (otherwise image mod 2 covers {0,1}, card = 2 = p).

2. **Diameter must be even**: same parity means differences are all even.

3. **If diameter ≤ 6**: with same parity and 4 elements in span ≤ 6,
   the only possibility is H = {a, a+2, a+4, a+6}.

4. **{a, a+2, a+4, a+6} is not admissible**: it contains {a, a+2, a+4}
   as a subset. The set {a, a+2, a+4} is not admissible (proved in parent file:
   it covers all residues mod 3 since gcd(2,3)=1). By admissible_subset,
   neither is {a, a+2, a+4, a+6}.

## Connection to Bounded Prime Gaps

This result, D(4) = 8, means any admissible 4-tuple spans at least 8.
Under the Elliott-Halberstam conjecture, prime gaps are bounded by D(4) = 8
(four primes in arithmetic-like progression), giving infinitely many prime
quadruples n, n+2, n+6, n+8 (Sophie Germain quadruples).
-/

namespace BoundedPrimeGapsOQ03OQ01OQ04

open Nat Finset BoundedPrimeGaps BoundedPrimeGapsOQ03OQ01

-- ============================================================
-- Part I: The Even AP of Length 4 is Not Admissible
-- ============================================================

/-- No even arithmetic progression {a, a+2, a+4, a+6} is admissible.
    Proof: {a, a+2, a+4} ⊆ {a, a+2, a+4, a+6}, and the triple
    {a, a+2, a+4} covers all residues mod 3 (proved in OQ03OQ01). -/
theorem not_admissible_even_ap4 (a : ℕ) :
    ¬IsAdmissible ({a, a + 2, a + 4, a + 6} : Finset ℕ) := by
  intro hadm
  -- {a, a+2, a+4} ⊆ {a, a+2, a+4, a+6} by inclusion
  have hsub : ({a, a + 2, a + 4} : Finset ℕ) ⊆ {a, a + 2, a + 4, a + 6} := by
    simp [Finset.insert_subset_iff]
  -- The triple {a, a+2, a+4} is not admissible (covers all residues mod 3)
  exact not_admissible_ap_diff2 a (admissible_subset hsub hadm)

-- ============================================================
-- Part II: Lower Bound — Every Admissible 4-Tuple has Diameter ≥ 8
-- ============================================================

/-- Every admissible 4-tuple has diameter ≥ 8.
    Proof: same parity (mod 2) forces all even gaps; diameter ≤ 6 forces
    H = {a, a+2, a+4, a+6}; but that contains {a, a+2, a+4} which covers
    all residues mod 3 — contradiction with admissibility. -/
private theorem admissible_quad_diam_ge_8 (H : Finset ℕ) (hcard : H.card = 4)
    (hadm : IsAdmissible H) : fsDiameter H ≥ 8 := by
  have hne : H.Nonempty := Finset.card_pos.mp (by omega)
  unfold fsDiameter; simp only [hne, dite_true]
  by_contra h_lt; push_neg at h_lt
  -- max - min ≤ 7
  have hge : H.min' hne ≤ H.max' hne := Finset.min'_le H _ (Finset.max'_mem H hne)
  by_cases hmixed : ∃ x ∈ H, ∃ y ∈ H, x % 2 ≠ y % 2
  · -- Mixed parity: image mod 2 has card ≥ 2 = p, contradicts admissibility
    obtain ⟨x, hx, y, hy, hneq⟩ := hmixed
    have h2 := hadm 2 (by norm_num)
    have hsub : {x % 2, y % 2} ⊆ H.image (· % 2) :=
      Finset.insert_subset_iff.mpr ⟨Finset.mem_image_of_mem _ hx,
        Finset.singleton_subset_iff.mpr (Finset.mem_image_of_mem _ hy)⟩
    have hcard2 : ({x % 2, y % 2} : Finset ℕ).card = 2 :=
      Finset.card_eq_two.mpr ⟨x % 2, y % 2, hneq, rfl⟩
    linarith [Finset.card_le_card hsub]
  · -- Same parity: all elements have same parity as min'
    push_neg at hmixed
    have hparity : ∀ x ∈ H, x % 2 = H.min' hne % 2 :=
      fun x hx => hmixed x hx (H.min' hne) (Finset.min'_mem H hne)
    -- max and min have same parity → diameter is even → diameter ≤ 6
    have hmax_par : H.max' hne % 2 = H.min' hne % 2 :=
      hparity _ (Finset.max'_mem H hne)
    have hdiam_le6 : H.max' hne - H.min' hne ≤ 6 := by omega
    -- Every element of H lies in {min, min+2, min+4, min+6}
    have hsub : H ⊆ ({H.min' hne, H.min' hne + 2, H.min' hne + 4, H.min' hne + 6} : Finset ℕ) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      have hmin_le := Finset.min'_le H x hx
      have hmax_le := Finset.le_max' H x hx
      have hpar := hparity x hx
      -- x - min is even and ≤ 6, so x - min ∈ {0, 2, 4, 6}
      set d := x - H.min' hne
      have hd_le : d ≤ 6 := by omega
      have hd_even : d % 2 = 0 := by omega
      interval_cases d <;> omega
    -- The target set has exactly 4 elements
    have hcard4 : ({H.min' hne, H.min' hne + 2, H.min' hne + 4, H.min' hne + 6} : Finset ℕ).card = 4 := by
      refine Finset.card_eq_four.mpr ?_
      exact ⟨H.min' hne, H.min' hne + 2, H.min' hne + 4, H.min' hne + 6,
        by omega, by omega, by omega, by omega, by omega, by omega, rfl⟩
    -- H equals {min, min+2, min+4, min+6} exactly (same card, subset)
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard4, hcard])
    -- But {min, min+2, min+4, min+6} is not admissible
    rw [heq] at hadm
    exact not_admissible_even_ap4 _ hadm

-- ============================================================
-- Part III: Main Result — D(4) = 8
-- ============================================================

/-- **D(4) = 8**: The minimum diameter of an admissible 4-tuple is 8.

    Upper bound: {0, 2, 6, 8} is admissible (proved in BoundedPrimeGaps.lean)
    with diameter 8.

    Lower bound: every admissible 4-tuple has diameter ≥ 8.
    (Proof: same parity + diameter ≤ 6 → H = {a,a+2,a+4,a+6} → not admissible.) -/
theorem minAdmissibleDiameter_4 : minAdmissibleDiameter 4 = 8 := by
  apply le_antisymm
  · -- Upper bound: {0, 2, 6, 8} witnesses D(4) ≤ 8
    apply csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩
    exact ⟨{0, 2, 6, 8}, by decide, admissible_quadruple_0_2_6_8, by native_decide⟩
  · -- Lower bound: every admissible 4-tuple has diameter ≥ 8
    have hne4 : Set.Nonempty {d | ∃ H : Finset ℕ, H.card = 4 ∧ IsAdmissible H ∧ fsDiameter H = d} :=
      ⟨8, {0, 2, 6, 8}, by decide, admissible_quadruple_0_2_6_8, by native_decide⟩
    apply le_csInf hne4
    rintro d ⟨H, hcard, hadm, rfl⟩
    exact admissible_quad_diam_ge_8 H hcard hadm

-- ============================================================
-- Part IV: Consequences
-- ============================================================

/-- D(2) < D(3) < D(4): the minimum admissible diameter is strictly increasing
    for k = 2, 3, 4. -/
theorem D2_lt_D3_lt_D4 :
    minAdmissibleDiameter 2 < minAdmissibleDiameter 3 ∧
    minAdmissibleDiameter 3 < minAdmissibleDiameter 4 := by
  constructor
  · rw [minAdmissibleDiameter_2, minAdmissibleDiameter_3]; norm_num
  · rw [minAdmissibleDiameter_3, minAdmissibleDiameter_4]; norm_num

/-- D(4) = 8 is achieved by {0, 2, 6, 8} (the prime quadruple pattern).
    This is the only optimal admissible 4-tuple up to translation. -/
theorem D4_achieved_by_0268 :
    minAdmissibleDiameter 4 = fsDiameter {0, 2, 6, 8} := by
  rw [minAdmissibleDiameter_4]
  native_decide

/-- The gap between D(3) and D(4) is 2 (one step in the OEIS A008407 sequence). -/
theorem D4_minus_D3 :
    minAdmissibleDiameter 4 - minAdmissibleDiameter 3 = 2 := by
  rw [minAdmissibleDiameter_4, minAdmissibleDiameter_3]

/-- D(4) = 8 in the context of bounded prime gaps:
    any admissible 4-tuple has diameter ≥ 8, so
    the shortest "prime quadruple" configuration spans at least 8. -/
theorem prime_quadruple_span_ge_8 :
    ∀ H : Finset ℕ, H.card = 4 → IsAdmissible H → fsDiameter H ≥ 8 :=
  fun H hcard hadm => admissible_quad_diam_ge_8 H hcard hadm

-- Summary checks
#check minAdmissibleDiameter_4
#check D2_lt_D3_lt_D4
#check prime_quadruple_span_ge_8

end BoundedPrimeGapsOQ03OQ01OQ04
