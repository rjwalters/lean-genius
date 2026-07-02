import Proofs.Erdos1204Problem

/-
# Erdős #1204 — the exact value `A(4) = 8`

Continues the exact-value frontier of `Erdos1204Problem.lean`
(`A(2) = 2`, `A(3) = 6`) with the next Hardy–Littlewood minimal diameter
`A(4) = H(4) = 8`, verified and axiom-free.

- **Upper bound** `A(4) ≤ 8`: the witness `{0,2,6,8}` is admissible (all even ⇒
  misses the odd class mod 2; residues `0,2,0,2` mod 3 ⇒ misses class 1).
- **Lower bound** `A(4) ≥ 8`: any admissible 4-set with maximum `≤ 7` sits in
  `{0,…,7}`; missing a class mod 2 forces a single parity, pinning the set to the
  only 4-element single-parity subsets `{0,2,4,6}` or `{1,3,5,7}`, both of which
  cover every class mod 3 and so are inadmissible.

`A(4) = 8` lies between the general bounds `2(k−1) = 6 ≤ A(k)` and
`A(k) ≤ (k−1)·primorial`; here the mod-3 constraint (beyond parity) is binding.
The asymptotics `A(k) ∼ k log k` remain OPEN (need sieve theory).
-/

namespace Erdos1204

open Finset

/-- The witness `{0,2,6,8}` is admissible: even ⇒ misses the odd class mod 2;
residues `0,2,0,2` mod 3 ⇒ misses class 1. (Primes `p ≥ 5` are automatic since
`|a| = 4 < p`.) Gives `A(4) ≤ 8`. -/
theorem admissible_zero_two_six_eight : Admissible ({0, 2, 6, 8} : Finset ℕ) := by
  rw [admissible_iff_card]
  intro p hp hcard
  have hc : ({0, 2, 6, 8} : Finset ℕ).card = 4 := by decide
  rw [hc] at hcard
  interval_cases p
  · exact absurd hp (by decide)   -- p = 0
  · exact absurd hp (by decide)   -- p = 1
  · exact ⟨1, by intro x hx; fin_cases hx <;> decide⟩   -- p = 2: miss class 1
  · exact ⟨1, by intro x hx; fin_cases hx <;> decide⟩   -- p = 3: miss class 1
  · exact absurd hp (by decide)   -- p = 4: not prime

/-- `{0,2,4,6}` is **not** admissible: mod 3 the residues `{0,2,1,0}` cover all
three classes. -/
theorem not_admissible_evens_four : ¬ Admissible ({0, 2, 4, 6} : Finset ℕ) := by
  intro h
  obtain ⟨r, hr⟩ := h 3 (by decide)
  fin_cases r
  · exact hr 0 (by decide) (by decide)   -- class 0 occupied by 0
  · exact hr 4 (by decide) (by decide)   -- class 1 occupied by 4
  · exact hr 2 (by decide) (by decide)   -- class 2 occupied by 2

/-- `{1,3,5,7}` is **not** admissible: mod 3 the residues `{1,0,2,1}` cover all
three classes. -/
theorem not_admissible_odds_four : ¬ Admissible ({1, 3, 5, 7} : Finset ℕ) := by
  intro h
  obtain ⟨r, hr⟩ := h 3 (by decide)
  fin_cases r
  · exact hr 3 (by decide) (by decide)   -- class 0 occupied by 3
  · exact hr 1 (by decide) (by decide)   -- class 1 occupied by 1
  · exact hr 5 (by decide) (by decide)   -- class 2 occupied by 5

/-- **Lower-bound core.** Every admissible `4`-set has largest element at least `8`.
If the maximum were `≤ 7`, the set would sit in `{0,…,7}`; missing a class mod `2`
forces a single parity, pinning the set to `{0,2,4,6}` or `{1,3,5,7}`, both
inadmissible mod `3`. -/
theorem admissible_four_sup_ge {a : Finset ℕ} (hcard : a.card = 4)
    (ha : Admissible a) : 8 ≤ a.sup id := by
  by_contra hlt
  push_neg at hlt
  have hbound : ∀ x ∈ a, x ≤ 7 := by
    intro x hx
    have h1 : id x ≤ a.sup id := Finset.le_sup hx
    simp only [id_eq] at h1
    omega
  have hy : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  have hdvd : ∀ x : ℕ, (x : ZMod 2) = 0 ↔ 2 ∣ x := fun x =>
    ZMod.natCast_eq_zero_iff x 2
  obtain ⟨r2, hr2⟩ := ha 2 (by decide)
  fin_cases r2
  · -- misses class 0 ⇒ all elements odd ⇒ a = {1,3,5,7}
    have hsub : a ⊆ ({1, 3, 5, 7} : Finset ℕ) := by
      intro x hx
      have hx7 := hbound x hx
      have hne : (x : ZMod 2) ≠ 0 := hr2 x hx
      have hodd : ¬ 2 ∣ x := fun hd => hne ((hdvd x).mpr hd)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have : a = ({1, 3, 5, 7} : Finset ℕ) :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; decide)
    rw [this] at ha
    exact not_admissible_odds_four ha
  · -- misses class 1 ⇒ all elements even ⇒ a = {0,2,4,6}
    have hsub : a ⊆ ({0, 2, 4, 6} : Finset ℕ) := by
      intro x hx
      have hx7 := hbound x hx
      have hne : (x : ZMod 2) ≠ 1 := hr2 x hx
      have heven : 2 ∣ x := by
        rcases hy (x : ZMod 2) with h0 | h1
        · exact (hdvd x).mp h0
        · exact absurd h1 hne
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have : a = ({0, 2, 4, 6} : Finset ℕ) :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; decide)
    rw [this] at ha
    exact not_admissible_evens_four ha

/-- **`A(4) = 8`.** The minimal largest element of an admissible `4`-set is `8`,
attained by `{0,2,6,8}`. This matches the Hardy–Littlewood minimal diameter
`H(4) = 8` and continues the frontier `A(2)=2, A(3)=6, A(4)=8`. -/
theorem A_four : A 4 = 8 := by
  apply le_antisymm
  · have h := A_le (k := 4) (a := ({0, 2, 6, 8} : Finset ℕ)) (by decide)
      admissible_zero_two_six_eight
    have hs : ({0, 2, 6, 8} : Finset ℕ).sup id = 8 := by decide
    rwa [hs] at h
  · obtain ⟨a, hcard, ha, hsup⟩ := A_mem 4
    have hge := admissible_four_sup_ge hcard ha
    omega

end Erdos1204
