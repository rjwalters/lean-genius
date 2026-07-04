import Proofs.Erdos1204Problem

/-
# Erdős #1204 — the exact value `A(5) = 12`

Continues the exact-value frontier of `Erdos1204Problem.lean`
(`A(2) = 2`, `A(3) = 6`) and `Erdos1204A4.lean` (`A(4) = 8`) with the next
Hardy–Littlewood minimal diameter `A(5) = H(5) = 12`, verified and axiom-free.

- **Upper bound** `A(5) ≤ 12`: the witness `{0,2,6,8,12}` is admissible — all even
  (misses the odd class mod 2); residues `0,2,0,2,0` mod 3 (misses class 1);
  residues `0,2,1,3,2` mod 5 (misses class 4). Primes `p ≥ 7` are automatic since
  `|a| = 5 < p`.
- **Lower bound** `A(5) ≥ 12`: any admissible 5-set with maximum `≤ 11` sits in
  `{0,…,11}`; missing a class mod 2 forces a single parity, so it is a 5-element
  subset of the six evens `{0,2,4,6,8,10}` or the six odds `{1,3,5,7,9,11}`. Within
  each of those six-element sets the three residue classes mod 3 each contain
  **exactly two** elements, so missing one class mod 3 leaves only four admissible
  slots — too few for a 5-set. Contradiction.

`A(5) = 12` lies between the general bounds `2(k−1) = 8 ≤ A(k)` and
`A(k) ≤ (k−1)·primorial`; here the mod-3 constraint (beyond parity) is binding,
and `12 > 8 = 2(k−1)`. The asymptotics `A(k) ∼ k log k` remain OPEN (need sieve
theory).
-/

namespace Erdos1204

open Finset

/-- The witness `{0,2,6,8,12}` is admissible: even ⇒ misses the odd class mod 2;
residues `0,2,0,2,0` mod 3 ⇒ misses class 1; residues `0,2,1,3,2` mod 5 ⇒ misses
class 4. (Primes `p ≥ 7` are automatic since `|a| = 5 < p`.) Gives `A(5) ≤ 12`. -/
theorem admissible_witness_five : Admissible ({0, 2, 6, 8, 12} : Finset ℕ) := by
  rw [admissible_iff_card]
  intro p hp hcard
  have hc : ({0, 2, 6, 8, 12} : Finset ℕ).card = 5 := by decide
  rw [hc] at hcard
  interval_cases p
  · exact absurd hp (by decide)   -- p = 0
  · exact absurd hp (by decide)   -- p = 1
  · exact ⟨1, by intro x hx; fin_cases hx <;> decide⟩   -- p = 2: miss class 1
  · exact ⟨1, by intro x hx; fin_cases hx <;> decide⟩   -- p = 3: miss class 1
  · exact absurd hp (by decide)   -- p = 4: not prime
  · exact ⟨4, by intro x hx; fin_cases hx <;> decide⟩   -- p = 5: miss class 4

/-- **Lower-bound core (even parity).** A 5-element subset of the six evens
`{0,2,4,6,8,10}` is never admissible: each residue class mod 3 occupies exactly two
of the six elements (`0,6` ↦ 0; `4,10` ↦ 1; `2,8` ↦ 2), so missing any class mod 3
confines the set to four elements — impossible for a 5-set. -/
theorem no_admissible_five_evens {a : Finset ℕ}
    (hsub : a ⊆ ({0, 2, 4, 6, 8, 10} : Finset ℕ)) (hcard : a.card = 5) :
    ¬ Admissible a := by
  intro ha
  obtain ⟨r, hr⟩ := ha 3 (by decide)
  fin_cases r
  · -- misses class 0 mod 3 ⇒ a ⊆ {2,4,8,10}
    have hs : a ⊆ ({2, 4, 8, 10} : Finset ℕ) := by
      intro x hx
      have hxE := hsub hx
      have hxne : (x : ZMod 3) ≠ 0 := hr x hx
      fin_cases hxE <;> first | decide | exact absurd (by decide) hxne
    have hle := Finset.card_le_card hs
    rw [hcard] at hle; revert hle; decide
  · -- misses class 1 mod 3 ⇒ a ⊆ {0,2,6,8}
    have hs : a ⊆ ({0, 2, 6, 8} : Finset ℕ) := by
      intro x hx
      have hxE := hsub hx
      have hxne : (x : ZMod 3) ≠ 1 := hr x hx
      fin_cases hxE <;> first | decide | exact absurd (by decide) hxne
    have hle := Finset.card_le_card hs
    rw [hcard] at hle; revert hle; decide
  · -- misses class 2 mod 3 ⇒ a ⊆ {0,4,6,10}
    have hs : a ⊆ ({0, 4, 6, 10} : Finset ℕ) := by
      intro x hx
      have hxE := hsub hx
      have hxne : (x : ZMod 3) ≠ 2 := hr x hx
      fin_cases hxE <;> first | decide | exact absurd (by decide) hxne
    have hle := Finset.card_le_card hs
    rw [hcard] at hle; revert hle; decide

/-- **Lower-bound core (odd parity).** A 5-element subset of the six odds
`{1,3,5,7,9,11}` is never admissible: each residue class mod 3 occupies exactly two
of the six elements (`3,9` ↦ 0; `1,7` ↦ 1; `5,11` ↦ 2), so missing any class mod 3
confines the set to four elements — impossible for a 5-set. -/
theorem no_admissible_five_odds {a : Finset ℕ}
    (hsub : a ⊆ ({1, 3, 5, 7, 9, 11} : Finset ℕ)) (hcard : a.card = 5) :
    ¬ Admissible a := by
  intro ha
  obtain ⟨r, hr⟩ := ha 3 (by decide)
  fin_cases r
  · -- misses class 0 mod 3 ⇒ a ⊆ {1,5,7,11}
    have hs : a ⊆ ({1, 5, 7, 11} : Finset ℕ) := by
      intro x hx
      have hxE := hsub hx
      have hxne : (x : ZMod 3) ≠ 0 := hr x hx
      fin_cases hxE <;> first | decide | exact absurd (by decide) hxne
    have hle := Finset.card_le_card hs
    rw [hcard] at hle; revert hle; decide
  · -- misses class 1 mod 3 ⇒ a ⊆ {3,5,9,11}
    have hs : a ⊆ ({3, 5, 9, 11} : Finset ℕ) := by
      intro x hx
      have hxE := hsub hx
      have hxne : (x : ZMod 3) ≠ 1 := hr x hx
      fin_cases hxE <;> first | decide | exact absurd (by decide) hxne
    have hle := Finset.card_le_card hs
    rw [hcard] at hle; revert hle; decide
  · -- misses class 2 mod 3 ⇒ a ⊆ {1,3,7,9}
    have hs : a ⊆ ({1, 3, 7, 9} : Finset ℕ) := by
      intro x hx
      have hxE := hsub hx
      have hxne : (x : ZMod 3) ≠ 2 := hr x hx
      fin_cases hxE <;> first | decide | exact absurd (by decide) hxne
    have hle := Finset.card_le_card hs
    rw [hcard] at hle; revert hle; decide

/-- **Lower-bound core.** Every admissible `5`-set has largest element at least `12`.
If the maximum were `≤ 11`, the set would sit in `{0,…,11}`; missing a class mod `2`
forces a single parity, placing the 5-set inside the six evens `{0,2,4,6,8,10}` or
six odds `{1,3,5,7,9,11}`, where the mod-3 constraint then leaves too few slots. -/
theorem admissible_five_sup_ge {a : Finset ℕ} (hcard : a.card = 5)
    (ha : Admissible a) : 12 ≤ a.sup id := by
  by_contra hlt
  push_neg at hlt
  have hbound : ∀ x ∈ a, x ≤ 11 := by
    intro x hx
    have h1 : id x ≤ a.sup id := Finset.le_sup hx
    simp only [id_eq] at h1
    omega
  have hy : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  have hdvd : ∀ x : ℕ, (x : ZMod 2) = 0 ↔ 2 ∣ x := fun x =>
    ZMod.natCast_eq_zero_iff x 2
  obtain ⟨r2, hr2⟩ := ha 2 (by decide)
  fin_cases r2
  · -- misses class 0 mod 2 ⇒ all elements odd ⇒ a ⊆ {1,3,5,7,9,11}
    have hsub : a ⊆ ({1, 3, 5, 7, 9, 11} : Finset ℕ) := by
      intro x hx
      have hx11 := hbound x hx
      have hne : (x : ZMod 2) ≠ 0 := hr2 x hx
      have hodd : ¬ 2 ∣ x := fun hd => hne ((hdvd x).mpr hd)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    exact no_admissible_five_odds hsub hcard ha
  · -- misses class 1 mod 2 ⇒ all elements even ⇒ a ⊆ {0,2,4,6,8,10}
    have hsub : a ⊆ ({0, 2, 4, 6, 8, 10} : Finset ℕ) := by
      intro x hx
      have hx11 := hbound x hx
      have hne : (x : ZMod 2) ≠ 1 := hr2 x hx
      have heven : 2 ∣ x := by
        rcases hy (x : ZMod 2) with h0 | h1
        · exact (hdvd x).mp h0
        · exact absurd h1 hne
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    exact no_admissible_five_evens hsub hcard ha

/-- **`A(5) = 12`.** The minimal largest element of an admissible `5`-set is `12`,
attained by `{0,2,6,8,12}`. This matches the Hardy–Littlewood minimal diameter
`H(5) = 12` and continues the frontier `A(2)=2, A(3)=6, A(4)=8, A(5)=12`. -/
theorem A_five : A 5 = 12 := by
  apply le_antisymm
  · have h := A_le (k := 5) (a := ({0, 2, 6, 8, 12} : Finset ℕ)) (by decide)
      admissible_witness_five
    have hs : ({0, 2, 6, 8, 12} : Finset ℕ).sup id = 12 := by decide
    rwa [hs] at h
  · obtain ⟨a, hcard, ha, hsup⟩ := A_mem 5
    have hge := admissible_five_sup_ge hcard ha
    omega

end Erdos1204
