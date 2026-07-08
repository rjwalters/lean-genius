import Proofs.Erdos1204Problem

/-
# Erdős #1204 — the exact value `A(7) = 20`

Continues the exact-value frontier of `Erdos1204Problem.lean` (`A(2) = 2`,
`A(3) = 6`), `Erdos1204A4.lean` (`A(4) = 8`), `Erdos1204A5.lean` (`A(5) = 12`)
and `Erdos1204A6.lean` (`A(6) = 16`) with the next Hardy–Littlewood minimal
diameter `A(7) = H(7) = 20`, verified and axiom-free.

- **Upper bound** `A(7) ≤ 20`: the witness `{0,2,6,8,12,18,20}` is admissible —
  all even (misses the odd class mod 2); residues `0,2,0,2,0,0,2` mod 3 (misses
  class 1); residues `0,2,1,3,2,3,0` mod 5 (misses class 4); residues
  `0,2,6,1,5,4,6` mod 7 (misses class 3). Primes `p ≥ 11` are automatic since
  `|a| = 7 < p`.
- **Lower bound** `A(7) ≥ 20`: any admissible 7-set with maximum `≤ 19` sits in
  `{0,…,19}`; missing a class mod 2 forces a single parity, so it is a 7-element
  subset of the ten evens `{0,2,4,6,8,10,12,14,16,18}` or the ten odds
  `{1,3,5,7,9,11,13,15,17,19}`. Within each ten-element window the residue classes
  mod 3 have sizes `4,3,3`; missing the size-4 class leaves only `6` slots (too
  few for a 7-set — contradiction), while missing either size-3 class leaves a
  *forced* 7-set. Each of the four forced 7-sets covers **every** residue class
  mod 5, contradicting admissibility at `p = 5`.

So — unlike a naive extrapolation of the "one further prime per value" pattern —
`A(7) = 20` does **not** actually need the prime `7` in its lower bound: the two
size-3 mod-3 classes (rather than one, as at `A(6)`) produce two forced 7-sets per
parity, but all four are still killed by `p = 5`. The prime `7` first becomes
binding only later in the frontier. `A(7) = 20` lies between the general bounds
`2(k−1) = 12 ≤ A(k)` and `A(k) ≤ (k−1)·primorial`; `20 > 12 = 2(k−1)`. The
asymptotics `A(k) ∼ k log k` remain OPEN (need sieve theory).
-/

namespace Erdos1204

open Finset

/-- The witness `{0,2,6,8,12,18,20}` is admissible: even ⇒ misses the odd class
mod 2; residues `0,2,0,2,0,0,2` mod 3 ⇒ misses class 1; residues `0,2,1,3,2,3,0`
mod 5 ⇒ misses class 4; residues `0,2,6,1,5,4,6` mod 7 ⇒ misses class 3. (Primes
`p ≥ 11` are automatic since `|a| = 7 < p`.) Gives `A(7) ≤ 20`. -/
theorem admissible_witness_seven :
    Admissible ({0, 2, 6, 8, 12, 18, 20} : Finset ℕ) := by
  rw [admissible_iff_card]
  intro p hp hcard
  have hc : ({0, 2, 6, 8, 12, 18, 20} : Finset ℕ).card = 7 := by decide
  rw [hc] at hcard
  interval_cases p
  · exact absurd hp (by decide)   -- p = 0
  · exact absurd hp (by decide)   -- p = 1
  · exact ⟨1, by intro x hx; fin_cases hx <;> decide⟩   -- p = 2: miss class 1
  · exact ⟨1, by intro x hx; fin_cases hx <;> decide⟩   -- p = 3: miss class 1
  · exact absurd hp (by decide)   -- p = 4: not prime
  · exact ⟨4, by intro x hx; fin_cases hx <;> decide⟩   -- p = 5: miss class 4
  · exact absurd hp (by decide)   -- p = 6: not prime
  · exact ⟨3, by intro x hx; fin_cases hx <;> decide⟩   -- p = 7: miss class 3

/-- **Lower-bound core (even parity).** A 7-element subset of the ten evens
`{0,2,4,6,8,10,12,14,16,18}` is never admissible. Missing a class mod 3 leaves
either six elements (the size-4 class `0 mod 3` = `{0,6,12,18}`; dropping it leaves
`{2,4,8,10,14,16}` — too few for a 7-set), or one of the two forced seven-element
sets `{0,2,6,8,12,14,18}` (drop class `1 mod 3`) / `{0,4,6,10,12,16,18}` (drop
class `2 mod 3`); each of those covers *every* residue class mod 5, so it fails
admissibility at `p = 5`. -/
theorem no_admissible_seven_evens {a : Finset ℕ}
    (hsub : a ⊆ ({0, 2, 4, 6, 8, 10, 12, 14, 16, 18} : Finset ℕ)) (hcard : a.card = 7) :
    ¬ Admissible a := by
  intro ha
  obtain ⟨r, hr⟩ := ha 3 (by decide)
  fin_cases r
  · -- misses class 0 mod 3 ⇒ a ⊆ {2,4,8,10,14,16} (card 6)
    have hs : a ⊆ ({2, 4, 8, 10, 14, 16} : Finset ℕ) := by
      intro x hx
      have hxE := hsub hx
      have hxne : (x : ZMod 3) ≠ 0 := hr x hx
      fin_cases hxE <;> first | decide | exact absurd (by decide) hxne
    have hle := Finset.card_le_card hs
    rw [hcard] at hle; revert hle; decide
  · -- misses class 1 mod 3 ⇒ a = {0,2,6,8,12,14,18}, which hits every class mod 5
    have hs : a ⊆ ({0, 2, 6, 8, 12, 14, 18} : Finset ℕ) := by
      intro x hx
      have hxE := hsub hx
      have hxne : (x : ZMod 3) ≠ 1 := hr x hx
      fin_cases hxE <;> first | decide | exact absurd (by decide) hxne
    have heq : a = ({0, 2, 6, 8, 12, 14, 18} : Finset ℕ) :=
      Finset.eq_of_subset_of_card_le hs (by rw [hcard]; decide)
    rw [heq] at ha
    obtain ⟨r5, hr5⟩ := ha 5 (by decide)
    fin_cases r5
    · exact absurd (by decide) (hr5 0 (by decide))
    · exact absurd (by decide) (hr5 6 (by decide))
    · exact absurd (by decide) (hr5 2 (by decide))
    · exact absurd (by decide) (hr5 8 (by decide))
    · exact absurd (by decide) (hr5 14 (by decide))
  · -- misses class 2 mod 3 ⇒ a = {0,4,6,10,12,16,18}, which hits every class mod 5
    have hs : a ⊆ ({0, 4, 6, 10, 12, 16, 18} : Finset ℕ) := by
      intro x hx
      have hxE := hsub hx
      have hxne : (x : ZMod 3) ≠ 2 := hr x hx
      fin_cases hxE <;> first | decide | exact absurd (by decide) hxne
    have heq : a = ({0, 4, 6, 10, 12, 16, 18} : Finset ℕ) :=
      Finset.eq_of_subset_of_card_le hs (by rw [hcard]; decide)
    rw [heq] at ha
    obtain ⟨r5, hr5⟩ := ha 5 (by decide)
    fin_cases r5
    · exact absurd (by decide) (hr5 0 (by decide))
    · exact absurd (by decide) (hr5 6 (by decide))
    · exact absurd (by decide) (hr5 12 (by decide))
    · exact absurd (by decide) (hr5 18 (by decide))
    · exact absurd (by decide) (hr5 4 (by decide))

/-- **Lower-bound core (odd parity).** A 7-element subset of the ten odds
`{1,3,5,7,9,11,13,15,17,19}` is never admissible. Missing a class mod 3 leaves
either six elements (the size-4 class `1 mod 3` = `{1,7,13,19}`; dropping it leaves
`{3,5,9,11,15,17}` — too few for a 7-set), or one of the two forced seven-element
sets `{1,5,7,11,13,17,19}` (drop class `0 mod 3`) / `{1,3,7,9,13,15,19}` (drop
class `2 mod 3`); each of those covers *every* residue class mod 5, so it fails
admissibility at `p = 5`. -/
theorem no_admissible_seven_odds {a : Finset ℕ}
    (hsub : a ⊆ ({1, 3, 5, 7, 9, 11, 13, 15, 17, 19} : Finset ℕ)) (hcard : a.card = 7) :
    ¬ Admissible a := by
  intro ha
  obtain ⟨r, hr⟩ := ha 3 (by decide)
  fin_cases r
  · -- misses class 0 mod 3 ⇒ a = {1,5,7,11,13,17,19}, which hits every class mod 5
    have hs : a ⊆ ({1, 5, 7, 11, 13, 17, 19} : Finset ℕ) := by
      intro x hx
      have hxE := hsub hx
      have hxne : (x : ZMod 3) ≠ 0 := hr x hx
      fin_cases hxE <;> first | decide | exact absurd (by decide) hxne
    have heq : a = ({1, 5, 7, 11, 13, 17, 19} : Finset ℕ) :=
      Finset.eq_of_subset_of_card_le hs (by rw [hcard]; decide)
    rw [heq] at ha
    obtain ⟨r5, hr5⟩ := ha 5 (by decide)
    fin_cases r5
    · exact absurd (by decide) (hr5 5 (by decide))
    · exact absurd (by decide) (hr5 1 (by decide))
    · exact absurd (by decide) (hr5 7 (by decide))
    · exact absurd (by decide) (hr5 13 (by decide))
    · exact absurd (by decide) (hr5 19 (by decide))
  · -- misses class 1 mod 3 ⇒ a ⊆ {3,5,9,11,15,17} (card 6)
    have hs : a ⊆ ({3, 5, 9, 11, 15, 17} : Finset ℕ) := by
      intro x hx
      have hxE := hsub hx
      have hxne : (x : ZMod 3) ≠ 1 := hr x hx
      fin_cases hxE <;> first | decide | exact absurd (by decide) hxne
    have hle := Finset.card_le_card hs
    rw [hcard] at hle; revert hle; decide
  · -- misses class 2 mod 3 ⇒ a = {1,3,7,9,13,15,19}, which hits every class mod 5
    have hs : a ⊆ ({1, 3, 7, 9, 13, 15, 19} : Finset ℕ) := by
      intro x hx
      have hxE := hsub hx
      have hxne : (x : ZMod 3) ≠ 2 := hr x hx
      fin_cases hxE <;> first | decide | exact absurd (by decide) hxne
    have heq : a = ({1, 3, 7, 9, 13, 15, 19} : Finset ℕ) :=
      Finset.eq_of_subset_of_card_le hs (by rw [hcard]; decide)
    rw [heq] at ha
    obtain ⟨r5, hr5⟩ := ha 5 (by decide)
    fin_cases r5
    · exact absurd (by decide) (hr5 15 (by decide))
    · exact absurd (by decide) (hr5 1 (by decide))
    · exact absurd (by decide) (hr5 7 (by decide))
    · exact absurd (by decide) (hr5 3 (by decide))
    · exact absurd (by decide) (hr5 9 (by decide))

/-- **Lower-bound core.** Every admissible `7`-set has largest element at least `20`.
If the maximum were `≤ 19`, the set would sit in `{0,…,19}`; missing a class mod `2`
forces a single parity, placing the 7-set inside the ten evens
`{0,2,4,6,8,10,12,14,16,18}` or ten odds `{1,3,5,7,9,11,13,15,17,19}`, where the
combined mod-3 and mod-5 constraints then leave too few slots. -/
theorem admissible_seven_sup_ge {a : Finset ℕ} (hcard : a.card = 7)
    (ha : Admissible a) : 20 ≤ a.sup id := by
  by_contra hlt
  push_neg at hlt
  have hbound : ∀ x ∈ a, x ≤ 19 := by
    intro x hx
    have h1 : id x ≤ a.sup id := Finset.le_sup hx
    simp only [id_eq] at h1
    omega
  have hy : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  have hdvd : ∀ x : ℕ, (x : ZMod 2) = 0 ↔ 2 ∣ x := fun x =>
    ZMod.natCast_eq_zero_iff x 2
  obtain ⟨r2, hr2⟩ := ha 2 (by decide)
  fin_cases r2
  · -- misses class 0 mod 2 ⇒ all elements odd ⇒ a ⊆ {1,3,…,19}
    have hsub : a ⊆ ({1, 3, 5, 7, 9, 11, 13, 15, 17, 19} : Finset ℕ) := by
      intro x hx
      have hx19 := hbound x hx
      have hne : (x : ZMod 2) ≠ 0 := hr2 x hx
      have hodd : ¬ 2 ∣ x := fun hd => hne ((hdvd x).mpr hd)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    exact no_admissible_seven_odds hsub hcard ha
  · -- misses class 1 mod 2 ⇒ all elements even ⇒ a ⊆ {0,2,…,18}
    have hsub : a ⊆ ({0, 2, 4, 6, 8, 10, 12, 14, 16, 18} : Finset ℕ) := by
      intro x hx
      have hx19 := hbound x hx
      have hne : (x : ZMod 2) ≠ 1 := hr2 x hx
      have heven : 2 ∣ x := by
        rcases hy (x : ZMod 2) with h0 | h1
        · exact (hdvd x).mp h0
        · exact absurd h1 hne
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    exact no_admissible_seven_evens hsub hcard ha

/-- **`A(7) = 20`.** The minimal largest element of an admissible `7`-set is `20`,
attained by `{0,2,6,8,12,18,20}`. This matches the Hardy–Littlewood minimal
diameter `H(7) = 20` and continues the frontier
`A(2)=2, A(3)=6, A(4)=8, A(5)=12, A(6)=16, A(7)=20`. Its lower bound combines the
primes `2, 3, 5` (two forced 7-sets per parity, all killed at `p = 5`); the prime
`7` is not yet binding. -/
theorem A_seven : A 7 = 20 := by
  apply le_antisymm
  · have h := A_le (k := 7) (a := ({0, 2, 6, 8, 12, 18, 20} : Finset ℕ)) (by decide)
      admissible_witness_seven
    have hs : ({0, 2, 6, 8, 12, 18, 20} : Finset ℕ).sup id = 20 := by decide
    rwa [hs] at h
  · obtain ⟨a, hcard, ha, hsup⟩ := A_mem 7
    have hge := admissible_seven_sup_ge hcard ha
    omega

end Erdos1204
