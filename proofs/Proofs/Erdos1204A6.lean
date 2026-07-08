import Proofs.Erdos1204Problem

/-
# Erdős #1204 — the exact value `A(6) = 16`

Continues the exact-value frontier of `Erdos1204Problem.lean`
(`A(2) = 2`, `A(3) = 6`), `Erdos1204A4.lean` (`A(4) = 8`) and `Erdos1204A5.lean`
(`A(5) = 12`) with the next Hardy–Littlewood minimal diameter
`A(6) = H(6) = 16`, verified and axiom-free.

- **Upper bound** `A(6) ≤ 16`: the witness `{0,4,6,10,12,16}` is admissible — all
  even (misses the odd class mod 2); residues `0,1,0,1,0,1` mod 3 (misses class 2);
  residues `0,4,1,0,2,1` mod 5 (misses class 3). Primes `p ≥ 7` are automatic since
  `|a| = 6 < p`.
- **Lower bound** `A(6) ≥ 16`: any admissible 6-set with maximum `≤ 15` sits in
  `{0,…,15}`; missing a class mod 2 forces a single parity, so it is a 6-element
  subset of the eight evens `{0,2,4,6,8,10,12,14}` or the eight odds
  `{1,3,5,7,9,11,13,15}`. Within each of those eight-element sets the residue
  classes mod 3 have sizes `3,2,3`, so missing a class mod 3 leaves either `5`
  slots (too few for a 6-set — contradiction) **or**, in exactly one case, all `6`
  surviving elements — and *that* forced 6-set turns out to cover **every** residue
  class mod 5, contradicting admissibility at `p = 5`.

This is the first exact value where the prime `5` is genuinely binding in the lower
bound: parity and mod 3 alone no longer suffice, and the argument must combine the
three small primes `2, 3, 5` — the finite analogue of the sieve heuristic behind
`A(k) ∼ k log k`. `A(6) = 16` lies between the general bounds
`2(k−1) = 10 ≤ A(k)` and `A(k) ≤ (k−1)·primorial`; `16 > 10 = 2(k−1)`. The
asymptotics `A(k) ∼ k log k` remain OPEN (need sieve theory).
-/

namespace Erdos1204

open Finset

/-- The witness `{0,4,6,10,12,16}` is admissible: even ⇒ misses the odd class mod 2;
residues `0,1,0,1,0,1` mod 3 ⇒ misses class 2; residues `0,4,1,0,2,1` mod 5 ⇒ misses
class 3. (Primes `p ≥ 7` are automatic since `|a| = 6 < p`.) Gives `A(6) ≤ 16`. -/
theorem admissible_witness_six : Admissible ({0, 4, 6, 10, 12, 16} : Finset ℕ) := by
  rw [admissible_iff_card]
  intro p hp hcard
  have hc : ({0, 4, 6, 10, 12, 16} : Finset ℕ).card = 6 := by decide
  rw [hc] at hcard
  interval_cases p
  · exact absurd hp (by decide)   -- p = 0
  · exact absurd hp (by decide)   -- p = 1
  · exact ⟨1, by intro x hx; fin_cases hx <;> decide⟩   -- p = 2: miss class 1
  · exact ⟨2, by intro x hx; fin_cases hx <;> decide⟩   -- p = 3: miss class 2
  · exact absurd hp (by decide)   -- p = 4: not prime
  · exact ⟨3, by intro x hx; fin_cases hx <;> decide⟩   -- p = 5: miss class 3
  · exact absurd hp (by decide)   -- p = 6: not prime

/-- **Lower-bound core (even parity).** A 6-element subset of the eight evens
`{0,2,4,6,8,10,12,14}` is never admissible. Missing a class mod 3 leaves either five
elements (classes `0` and `2` mod 3 each occupy three of the eight, so dropping them
leaves `{2,4,8,10,14}` / `{0,4,6,10,12}` — too few for a 6-set), or, dropping the
two-element class `1 mod 3`, the full six-element set `{0,2,6,8,12,14}`; but that set
covers *every* residue class mod 5, so it fails admissibility at `p = 5`. -/
theorem no_admissible_six_evens {a : Finset ℕ}
    (hsub : a ⊆ ({0, 2, 4, 6, 8, 10, 12, 14} : Finset ℕ)) (hcard : a.card = 6) :
    ¬ Admissible a := by
  intro ha
  obtain ⟨r, hr⟩ := ha 3 (by decide)
  fin_cases r
  · -- misses class 0 mod 3 ⇒ a ⊆ {2,4,8,10,14} (card 5)
    have hs : a ⊆ ({2, 4, 8, 10, 14} : Finset ℕ) := by
      intro x hx
      have hxE := hsub hx
      have hxne : (x : ZMod 3) ≠ 0 := hr x hx
      fin_cases hxE <;> first | decide | exact absurd (by decide) hxne
    have hle := Finset.card_le_card hs
    rw [hcard] at hle; revert hle; decide
  · -- misses class 1 mod 3 ⇒ a = {0,2,6,8,12,14}, which hits every class mod 5
    have hs : a ⊆ ({0, 2, 6, 8, 12, 14} : Finset ℕ) := by
      intro x hx
      have hxE := hsub hx
      have hxne : (x : ZMod 3) ≠ 1 := hr x hx
      fin_cases hxE <;> first | decide | exact absurd (by decide) hxne
    have heq : a = ({0, 2, 6, 8, 12, 14} : Finset ℕ) :=
      Finset.eq_of_subset_of_card_le hs (by rw [hcard]; decide)
    rw [heq] at ha
    obtain ⟨r5, hr5⟩ := ha 5 (by decide)
    fin_cases r5
    · exact absurd (by decide) (hr5 0 (by decide))
    · exact absurd (by decide) (hr5 6 (by decide))
    · exact absurd (by decide) (hr5 2 (by decide))
    · exact absurd (by decide) (hr5 8 (by decide))
    · exact absurd (by decide) (hr5 14 (by decide))
  · -- misses class 2 mod 3 ⇒ a ⊆ {0,4,6,10,12} (card 5)
    have hs : a ⊆ ({0, 4, 6, 10, 12} : Finset ℕ) := by
      intro x hx
      have hxE := hsub hx
      have hxne : (x : ZMod 3) ≠ 2 := hr x hx
      fin_cases hxE <;> first | decide | exact absurd (by decide) hxne
    have hle := Finset.card_le_card hs
    rw [hcard] at hle; revert hle; decide

/-- **Lower-bound core (odd parity).** A 6-element subset of the eight odds
`{1,3,5,7,9,11,13,15}` is never admissible. Missing a class mod 3 leaves either five
elements (`{1,5,7,11,13}` / `{3,5,9,11,15}` — too few for a 6-set), or, dropping the
two-element class `2 mod 3`, the full six-element set `{1,3,7,9,13,15}`; but that set
covers *every* residue class mod 5, so it fails admissibility at `p = 5`. -/
theorem no_admissible_six_odds {a : Finset ℕ}
    (hsub : a ⊆ ({1, 3, 5, 7, 9, 11, 13, 15} : Finset ℕ)) (hcard : a.card = 6) :
    ¬ Admissible a := by
  intro ha
  obtain ⟨r, hr⟩ := ha 3 (by decide)
  fin_cases r
  · -- misses class 0 mod 3 ⇒ a ⊆ {1,5,7,11,13} (card 5)
    have hs : a ⊆ ({1, 5, 7, 11, 13} : Finset ℕ) := by
      intro x hx
      have hxE := hsub hx
      have hxne : (x : ZMod 3) ≠ 0 := hr x hx
      fin_cases hxE <;> first | decide | exact absurd (by decide) hxne
    have hle := Finset.card_le_card hs
    rw [hcard] at hle; revert hle; decide
  · -- misses class 1 mod 3 ⇒ a ⊆ {3,5,9,11,15} (card 5)
    have hs : a ⊆ ({3, 5, 9, 11, 15} : Finset ℕ) := by
      intro x hx
      have hxE := hsub hx
      have hxne : (x : ZMod 3) ≠ 1 := hr x hx
      fin_cases hxE <;> first | decide | exact absurd (by decide) hxne
    have hle := Finset.card_le_card hs
    rw [hcard] at hle; revert hle; decide
  · -- misses class 2 mod 3 ⇒ a = {1,3,7,9,13,15}, which hits every class mod 5
    have hs : a ⊆ ({1, 3, 7, 9, 13, 15} : Finset ℕ) := by
      intro x hx
      have hxE := hsub hx
      have hxne : (x : ZMod 3) ≠ 2 := hr x hx
      fin_cases hxE <;> first | decide | exact absurd (by decide) hxne
    have heq : a = ({1, 3, 7, 9, 13, 15} : Finset ℕ) :=
      Finset.eq_of_subset_of_card_le hs (by rw [hcard]; decide)
    rw [heq] at ha
    obtain ⟨r5, hr5⟩ := ha 5 (by decide)
    fin_cases r5
    · exact absurd (by decide) (hr5 15 (by decide))
    · exact absurd (by decide) (hr5 1 (by decide))
    · exact absurd (by decide) (hr5 7 (by decide))
    · exact absurd (by decide) (hr5 3 (by decide))
    · exact absurd (by decide) (hr5 9 (by decide))

/-- **Lower-bound core.** Every admissible `6`-set has largest element at least `16`.
If the maximum were `≤ 15`, the set would sit in `{0,…,15}`; missing a class mod `2`
forces a single parity, placing the 6-set inside the eight evens `{0,2,4,6,8,10,12,14}`
or eight odds `{1,3,5,7,9,11,13,15}`, where the combined mod-3 and mod-5 constraints
then leave too few slots. -/
theorem admissible_six_sup_ge {a : Finset ℕ} (hcard : a.card = 6)
    (ha : Admissible a) : 16 ≤ a.sup id := by
  by_contra hlt
  push_neg at hlt
  have hbound : ∀ x ∈ a, x ≤ 15 := by
    intro x hx
    have h1 : id x ≤ a.sup id := Finset.le_sup hx
    simp only [id_eq] at h1
    omega
  have hy : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  have hdvd : ∀ x : ℕ, (x : ZMod 2) = 0 ↔ 2 ∣ x := fun x =>
    ZMod.natCast_eq_zero_iff x 2
  obtain ⟨r2, hr2⟩ := ha 2 (by decide)
  fin_cases r2
  · -- misses class 0 mod 2 ⇒ all elements odd ⇒ a ⊆ {1,3,5,7,9,11,13,15}
    have hsub : a ⊆ ({1, 3, 5, 7, 9, 11, 13, 15} : Finset ℕ) := by
      intro x hx
      have hx15 := hbound x hx
      have hne : (x : ZMod 2) ≠ 0 := hr2 x hx
      have hodd : ¬ 2 ∣ x := fun hd => hne ((hdvd x).mpr hd)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    exact no_admissible_six_odds hsub hcard ha
  · -- misses class 1 mod 2 ⇒ all elements even ⇒ a ⊆ {0,2,4,6,8,10,12,14}
    have hsub : a ⊆ ({0, 2, 4, 6, 8, 10, 12, 14} : Finset ℕ) := by
      intro x hx
      have hx15 := hbound x hx
      have hne : (x : ZMod 2) ≠ 1 := hr2 x hx
      have heven : 2 ∣ x := by
        rcases hy (x : ZMod 2) with h0 | h1
        · exact (hdvd x).mp h0
        · exact absurd h1 hne
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    exact no_admissible_six_evens hsub hcard ha

/-- **`A(6) = 16`.** The minimal largest element of an admissible `6`-set is `16`,
attained by `{0,4,6,10,12,16}`. This matches the Hardy–Littlewood minimal diameter
`H(6) = 16` and continues the frontier `A(2)=2, A(3)=6, A(4)=8, A(5)=12, A(6)=16`.
It is the first value whose lower bound genuinely needs the prime `5` (parity and
mod 3 no longer suffice). -/
theorem A_six : A 6 = 16 := by
  apply le_antisymm
  · have h := A_le (k := 6) (a := ({0, 4, 6, 10, 12, 16} : Finset ℕ)) (by decide)
      admissible_witness_six
    have hs : ({0, 4, 6, 10, 12, 16} : Finset ℕ).sup id = 16 := by decide
    rwa [hs] at h
  · obtain ⟨a, hcard, ha, hsup⟩ := A_mem 6
    have hge := admissible_six_sup_ge hcard ha
    omega

end Erdos1204
