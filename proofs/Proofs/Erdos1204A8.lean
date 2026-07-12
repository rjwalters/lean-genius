import Proofs.Erdos1204A7

/-
# Erdős #1204 — the exact value `A(8) = 26`

Continues the exact-value frontier `A(2)=2, A(3)=6, A(4)=8, A(5)=12, A(6)=16,
A(7)=20` (`Erdos1204Problem.lean`, `Erdos1204A4`–`A7`) with the next Hardy–Littlewood
minimal diameter `A(8) = H(8) = 26`, verified and axiom-free.

Note the *jump of six* (`20 → 26`, not the `+4` of every earlier step): `H(8)` is the
first place in the sequence where a single-parity window minus one mod-3 class still
admits an 8-set, so a *second* prime (namely `7`) is needed to close the lower bound.
This is the qualitative milestone the frontier had been approaching — at `A(7)` the
prime `7` was not yet binding.

- **Upper bound** `A(8) ≤ 26` (`A_eight_le`): the witness `{0,2,6,8,12,18,20,26}`
  (the `A(7)` witness extended by `26`) is admissible — all even (misses the odd class
  mod 2); residues `0,2,0,2,0,0,2,2` mod 3 (misses class 1); residues `0,2,1,3,2,3,0,1`
  mod 5 (misses class 4); residues `0,2,6,1,5,4,6,5` mod 7 (misses class 3). Primes
  `p ≥ 11` are automatic since `|a| = 8 < p`.
- **Lower bound** `A(8) ≥ 26` (`admissible_eight_sup_ge`): any admissible 8-set with
  maximum `≤ 25` sits in `{0,…,25}`; missing a class mod 2 forces a single parity, so
  it is an 8-element subset of the thirteen evens `{0,2,…,24}` or thirteen odds
  `{1,3,…,25}`. Within each thirteen-element window the residue classes mod 3 have
  sizes `5,4,4`.
  * Missing the *size-5* class leaves exactly `8` slots — a single **forced** 8-set,
    which covers every residue class mod `5`, so it dies at `p = 5`.
  * Missing a *size-4* class leaves `9` slots. Among the five residue classes mod `5`
    in this 9-element pool, four have two elements and one is a singleton; an
    admissible 8-subset must miss a class mod `5`, but a two-element class cannot be
    avoided by dropping a single element, so the missed class is the singleton — pinning
    the 8-subset to one **forced** set. Each such forced set covers every class mod `7`,
    so it dies at `p = 7`.

So `p = 7` is genuinely binding here (unlike at `A(7) = 20`): the even branches
`mod 3 ≡ 1,2` and the odd branches `mod 3 ≡ 0,2` each produce a forced 8-set that
survives `p = 5` and is killed only at `p = 7`. `A(8) = 26` lies between the general
bounds `2(k−1) = 14 ≤ A(k)` and `A(k) ≤ (k−1)·primorial`; `26 > 14 = 2(k−1)`. The
asymptotics `A(k) ∼ k log k` remain OPEN (need sieve theory).
-/

namespace Erdos1204

open Finset

/-- A set whose image in `ZMod p` is all of `ZMod p` cannot be admissible: it fails
to miss any residue class at the prime `p`. This is the workhorse for killing the
"forced" sets that arise in the lower-bound case analysis. -/
private theorem not_admissible_of_image_univ {a : Finset ℕ} {p : ℕ} (hp : p.Prime)
    (hcov : a.image (fun x : ℕ => (x : ZMod p)) = Finset.univ) : ¬ Admissible a := by
  intro ha
  obtain ⟨r, hr⟩ := ha p hp
  have hmem : r ∈ a.image (fun x : ℕ => (x : ZMod p)) := by
    rw [hcov]; exact Finset.mem_univ r
  obtain ⟨x, hx, hxr⟩ := Finset.mem_image.mp hmem
  exact hr x hx hxr

/-- The witness `{0,2,6,8,12,18,20,26}` (the `A(7)` witness plus `26`) is admissible:
even ⇒ misses the odd class mod 2; residues `0,2,0,2,0,0,2,2` mod 3 ⇒ misses class 1;
residues `0,2,1,3,2,3,0,1` mod 5 ⇒ misses class 4; residues `0,2,6,1,5,4,6,5` mod 7 ⇒
misses class 3. (Primes `p ≥ 11` are automatic since `|a| = 8 < p`.) Gives `A(8) ≤ 26`. -/
theorem admissible_witness_eight :
    Admissible ({0, 2, 6, 8, 12, 18, 20, 26} : Finset ℕ) := by
  rw [admissible_iff_card]
  intro p hp hcard
  have hc : ({0, 2, 6, 8, 12, 18, 20, 26} : Finset ℕ).card = 8 := by decide
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
  · exact absurd hp (by decide)   -- p = 8: not prime

/-- **`A(8) ≤ 26`.** The admissible `8`-set `{0,2,6,8,12,18,20,26}` has largest
element `26`, so the minimal largest element of an admissible `8`-set is at most `26`.
This is the upper half of the Hardy–Littlewood value `H(8) = 26`. -/
theorem A_eight_le : A 8 ≤ 26 := by
  have h := A_le (k := 8) (a := ({0, 2, 6, 8, 12, 18, 20, 26} : Finset ℕ)) (by decide)
    admissible_witness_eight
  have hs : ({0, 2, 6, 8, 12, 18, 20, 26} : Finset ℕ).sup id = 26 := by decide
  rwa [hs] at h

/-- **Lower-bound core (even parity).** An 8-element subset of the thirteen evens
`{0,2,4,…,24}` is never admissible. The size-5 class mod 3 is `0 mod 3`; missing it
forces the 8-set `{2,4,8,10,14,16,20,22}`, which covers every class mod 5 (dies at
`p = 5`). Missing either size-4 class (`1 mod 3` / `2 mod 3`) leaves a 9-element pool,
and admissibility at `p = 5` pins the 8-subset to a forced set
(`{0,2,8,12,14,18,20,24}` / `{0,4,6,10,12,16,22,24}`), each covering every class mod 7
(dies at `p = 7`). -/
theorem no_admissible_eight_evens {a : Finset ℕ}
    (hsub : a ⊆ ({0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24} : Finset ℕ))
    (hcard : a.card = 8) : ¬ Admissible a := by
  intro ha
  obtain ⟨r, hr⟩ := ha 3 (by decide)
  fin_cases r
  · -- misses class 0 mod 3 ⇒ forced 8-set {2,4,8,10,14,16,20,22}, covers mod 5
    have hs : a ⊆ ({2, 4, 8, 10, 14, 16, 20, 22} : Finset ℕ) := by
      intro x hx
      have hxE := hsub hx
      have hxne : (x : ZMod 3) ≠ 0 := hr x hx
      fin_cases hxE <;> first | decide | exact absurd (by decide) hxne
    have heq : a = ({2, 4, 8, 10, 14, 16, 20, 22} : Finset ℕ) :=
      Finset.eq_of_subset_of_card_le hs (by rw [hcard]; decide)
    rw [heq] at ha
    exact not_admissible_of_image_univ (p := 5) (by decide) (by decide) ha
  · -- misses class 1 mod 3 ⇒ pool {0,2,6,8,12,14,18,20,24} (card 9)
    have hs : a ⊆ ({0, 2, 6, 8, 12, 14, 18, 20, 24} : Finset ℕ) := by
      intro x hx
      have hxE := hsub hx
      have hxne : (x : ZMod 3) ≠ 1 := hr x hx
      fin_cases hxE <;> first | decide | exact absurd (by decide) hxne
    obtain ⟨r5, hr5⟩ := ha 5 (by decide)
    fin_cases r5
    · -- miss 0 mod 5 ⇒ ⊆ {2,6,8,12,14,18,24} (card 7)
      have hs5 : a ⊆ ({2, 6, 8, 12, 14, 18, 24} : Finset ℕ) := by
        intro x hx
        have hxP := hs hx
        have hxne : (x : ZMod 5) ≠ 0 := hr5 x hx
        fin_cases hxP <;> first | decide | exact absurd (by decide) hxne
      have hle := Finset.card_le_card hs5; rw [hcard] at hle; revert hle; decide
    · -- miss 1 mod 5 ⇒ forced {0,2,8,12,14,18,20,24}, covers mod 7
      have hs5 : a ⊆ ({0, 2, 8, 12, 14, 18, 20, 24} : Finset ℕ) := by
        intro x hx
        have hxP := hs hx
        have hxne : (x : ZMod 5) ≠ 1 := hr5 x hx
        fin_cases hxP <;> first | decide | exact absurd (by decide) hxne
      have heq : a = ({0, 2, 8, 12, 14, 18, 20, 24} : Finset ℕ) :=
        Finset.eq_of_subset_of_card_le hs5 (by rw [hcard]; decide)
      rw [heq] at ha
      exact not_admissible_of_image_univ (p := 7) (by decide) (by decide) ha
    · -- miss 2 mod 5 ⇒ ⊆ {0,6,8,14,18,20,24} (card 7)
      have hs5 : a ⊆ ({0, 6, 8, 14, 18, 20, 24} : Finset ℕ) := by
        intro x hx
        have hxP := hs hx
        have hxne : (x : ZMod 5) ≠ 2 := hr5 x hx
        fin_cases hxP <;> first | decide | exact absurd (by decide) hxne
      have hle := Finset.card_le_card hs5; rw [hcard] at hle; revert hle; decide
    · -- miss 3 mod 5 ⇒ ⊆ {0,2,6,12,14,20,24} (card 7)
      have hs5 : a ⊆ ({0, 2, 6, 12, 14, 20, 24} : Finset ℕ) := by
        intro x hx
        have hxP := hs hx
        have hxne : (x : ZMod 5) ≠ 3 := hr5 x hx
        fin_cases hxP <;> first | decide | exact absurd (by decide) hxne
      have hle := Finset.card_le_card hs5; rw [hcard] at hle; revert hle; decide
    · -- miss 4 mod 5 ⇒ ⊆ {0,2,6,8,12,18,20} (card 7)
      have hs5 : a ⊆ ({0, 2, 6, 8, 12, 18, 20} : Finset ℕ) := by
        intro x hx
        have hxP := hs hx
        have hxne : (x : ZMod 5) ≠ 4 := hr5 x hx
        fin_cases hxP <;> first | decide | exact absurd (by decide) hxne
      have hle := Finset.card_le_card hs5; rw [hcard] at hle; revert hle; decide
  · -- misses class 2 mod 3 ⇒ pool {0,4,6,10,12,16,18,22,24} (card 9)
    have hs : a ⊆ ({0, 4, 6, 10, 12, 16, 18, 22, 24} : Finset ℕ) := by
      intro x hx
      have hxE := hsub hx
      have hxne : (x : ZMod 3) ≠ 2 := hr x hx
      fin_cases hxE <;> first | decide | exact absurd (by decide) hxne
    obtain ⟨r5, hr5⟩ := ha 5 (by decide)
    fin_cases r5
    · -- miss 0 mod 5 ⇒ ⊆ {4,6,12,16,18,22,24} (card 7)
      have hs5 : a ⊆ ({4, 6, 12, 16, 18, 22, 24} : Finset ℕ) := by
        intro x hx
        have hxP := hs hx
        have hxne : (x : ZMod 5) ≠ 0 := hr5 x hx
        fin_cases hxP <;> first | decide | exact absurd (by decide) hxne
      have hle := Finset.card_le_card hs5; rw [hcard] at hle; revert hle; decide
    · -- miss 1 mod 5 ⇒ ⊆ {0,4,10,12,18,22,24} (card 7)
      have hs5 : a ⊆ ({0, 4, 10, 12, 18, 22, 24} : Finset ℕ) := by
        intro x hx
        have hxP := hs hx
        have hxne : (x : ZMod 5) ≠ 1 := hr5 x hx
        fin_cases hxP <;> first | decide | exact absurd (by decide) hxne
      have hle := Finset.card_le_card hs5; rw [hcard] at hle; revert hle; decide
    · -- miss 2 mod 5 ⇒ ⊆ {0,4,6,10,16,18,24} (card 7)
      have hs5 : a ⊆ ({0, 4, 6, 10, 16, 18, 24} : Finset ℕ) := by
        intro x hx
        have hxP := hs hx
        have hxne : (x : ZMod 5) ≠ 2 := hr5 x hx
        fin_cases hxP <;> first | decide | exact absurd (by decide) hxne
      have hle := Finset.card_le_card hs5; rw [hcard] at hle; revert hle; decide
    · -- miss 3 mod 5 ⇒ forced {0,4,6,10,12,16,22,24}, covers mod 7
      have hs5 : a ⊆ ({0, 4, 6, 10, 12, 16, 22, 24} : Finset ℕ) := by
        intro x hx
        have hxP := hs hx
        have hxne : (x : ZMod 5) ≠ 3 := hr5 x hx
        fin_cases hxP <;> first | decide | exact absurd (by decide) hxne
      have heq : a = ({0, 4, 6, 10, 12, 16, 22, 24} : Finset ℕ) :=
        Finset.eq_of_subset_of_card_le hs5 (by rw [hcard]; decide)
      rw [heq] at ha
      exact not_admissible_of_image_univ (p := 7) (by decide) (by decide) ha
    · -- miss 4 mod 5 ⇒ ⊆ {0,6,10,12,16,18,22} (card 7)
      have hs5 : a ⊆ ({0, 6, 10, 12, 16, 18, 22} : Finset ℕ) := by
        intro x hx
        have hxP := hs hx
        have hxne : (x : ZMod 5) ≠ 4 := hr5 x hx
        fin_cases hxP <;> first | decide | exact absurd (by decide) hxne
      have hle := Finset.card_le_card hs5; rw [hcard] at hle; revert hle; decide

/-- **Lower-bound core (odd parity).** An 8-element subset of the thirteen odds
`{1,3,5,…,25}` is never admissible. The size-5 class mod 3 is now `1 mod 3`; missing
it forces `{3,5,9,11,15,17,21,23}`, which covers every class mod 5 (dies at `p = 5`).
Missing either size-4 class (`0 mod 3` / `2 mod 3`) leaves a 9-element pool, and
admissibility at `p = 5` pins the 8-subset to a forced set
(`{1,5,7,11,13,17,23,25}` / `{1,3,9,13,15,19,21,25}`), each covering every class
mod 7 (dies at `p = 7`). -/
theorem no_admissible_eight_odds {a : Finset ℕ}
    (hsub : a ⊆ ({1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25} : Finset ℕ))
    (hcard : a.card = 8) : ¬ Admissible a := by
  intro ha
  obtain ⟨r, hr⟩ := ha 3 (by decide)
  fin_cases r
  · -- misses class 0 mod 3 ⇒ pool {1,5,7,11,13,17,19,23,25} (card 9)
    have hs : a ⊆ ({1, 5, 7, 11, 13, 17, 19, 23, 25} : Finset ℕ) := by
      intro x hx
      have hxE := hsub hx
      have hxne : (x : ZMod 3) ≠ 0 := hr x hx
      fin_cases hxE <;> first | decide | exact absurd (by decide) hxne
    obtain ⟨r5, hr5⟩ := ha 5 (by decide)
    fin_cases r5
    · -- miss 0 mod 5 ⇒ ⊆ {1,7,11,13,17,19,23} (card 7)
      have hs5 : a ⊆ ({1, 7, 11, 13, 17, 19, 23} : Finset ℕ) := by
        intro x hx
        have hxP := hs hx
        have hxne : (x : ZMod 5) ≠ 0 := hr5 x hx
        fin_cases hxP <;> first | decide | exact absurd (by decide) hxne
      have hle := Finset.card_le_card hs5; rw [hcard] at hle; revert hle; decide
    · -- miss 1 mod 5 ⇒ ⊆ {5,7,13,17,19,23,25} (card 7)
      have hs5 : a ⊆ ({5, 7, 13, 17, 19, 23, 25} : Finset ℕ) := by
        intro x hx
        have hxP := hs hx
        have hxne : (x : ZMod 5) ≠ 1 := hr5 x hx
        fin_cases hxP <;> first | decide | exact absurd (by decide) hxne
      have hle := Finset.card_le_card hs5; rw [hcard] at hle; revert hle; decide
    · -- miss 2 mod 5 ⇒ ⊆ {1,5,11,13,19,23,25} (card 7)
      have hs5 : a ⊆ ({1, 5, 11, 13, 19, 23, 25} : Finset ℕ) := by
        intro x hx
        have hxP := hs hx
        have hxne : (x : ZMod 5) ≠ 2 := hr5 x hx
        fin_cases hxP <;> first | decide | exact absurd (by decide) hxne
      have hle := Finset.card_le_card hs5; rw [hcard] at hle; revert hle; decide
    · -- miss 3 mod 5 ⇒ ⊆ {1,5,7,11,17,19,25} (card 7)
      have hs5 : a ⊆ ({1, 5, 7, 11, 17, 19, 25} : Finset ℕ) := by
        intro x hx
        have hxP := hs hx
        have hxne : (x : ZMod 5) ≠ 3 := hr5 x hx
        fin_cases hxP <;> first | decide | exact absurd (by decide) hxne
      have hle := Finset.card_le_card hs5; rw [hcard] at hle; revert hle; decide
    · -- miss 4 mod 5 ⇒ forced {1,5,7,11,13,17,23,25}, covers mod 7
      have hs5 : a ⊆ ({1, 5, 7, 11, 13, 17, 23, 25} : Finset ℕ) := by
        intro x hx
        have hxP := hs hx
        have hxne : (x : ZMod 5) ≠ 4 := hr5 x hx
        fin_cases hxP <;> first | decide | exact absurd (by decide) hxne
      have heq : a = ({1, 5, 7, 11, 13, 17, 23, 25} : Finset ℕ) :=
        Finset.eq_of_subset_of_card_le hs5 (by rw [hcard]; decide)
      rw [heq] at ha
      exact not_admissible_of_image_univ (p := 7) (by decide) (by decide) ha
  · -- misses class 1 mod 3 ⇒ forced 8-set {3,5,9,11,15,17,21,23}, covers mod 5
    have hs : a ⊆ ({3, 5, 9, 11, 15, 17, 21, 23} : Finset ℕ) := by
      intro x hx
      have hxE := hsub hx
      have hxne : (x : ZMod 3) ≠ 1 := hr x hx
      fin_cases hxE <;> first | decide | exact absurd (by decide) hxne
    have heq : a = ({3, 5, 9, 11, 15, 17, 21, 23} : Finset ℕ) :=
      Finset.eq_of_subset_of_card_le hs (by rw [hcard]; decide)
    rw [heq] at ha
    exact not_admissible_of_image_univ (p := 5) (by decide) (by decide) ha
  · -- misses class 2 mod 3 ⇒ pool {1,3,7,9,13,15,19,21,25} (card 9)
    have hs : a ⊆ ({1, 3, 7, 9, 13, 15, 19, 21, 25} : Finset ℕ) := by
      intro x hx
      have hxE := hsub hx
      have hxne : (x : ZMod 3) ≠ 2 := hr x hx
      fin_cases hxE <;> first | decide | exact absurd (by decide) hxne
    obtain ⟨r5, hr5⟩ := ha 5 (by decide)
    fin_cases r5
    · -- miss 0 mod 5 ⇒ ⊆ {1,3,7,9,13,19,21} (card 7)
      have hs5 : a ⊆ ({1, 3, 7, 9, 13, 19, 21} : Finset ℕ) := by
        intro x hx
        have hxP := hs hx
        have hxne : (x : ZMod 5) ≠ 0 := hr5 x hx
        fin_cases hxP <;> first | decide | exact absurd (by decide) hxne
      have hle := Finset.card_le_card hs5; rw [hcard] at hle; revert hle; decide
    · -- miss 1 mod 5 ⇒ ⊆ {3,7,9,13,15,19,25} (card 7)
      have hs5 : a ⊆ ({3, 7, 9, 13, 15, 19, 25} : Finset ℕ) := by
        intro x hx
        have hxP := hs hx
        have hxne : (x : ZMod 5) ≠ 1 := hr5 x hx
        fin_cases hxP <;> first | decide | exact absurd (by decide) hxne
      have hle := Finset.card_le_card hs5; rw [hcard] at hle; revert hle; decide
    · -- miss 2 mod 5 ⇒ forced {1,3,9,13,15,19,21,25}, covers mod 7
      have hs5 : a ⊆ ({1, 3, 9, 13, 15, 19, 21, 25} : Finset ℕ) := by
        intro x hx
        have hxP := hs hx
        have hxne : (x : ZMod 5) ≠ 2 := hr5 x hx
        fin_cases hxP <;> first | decide | exact absurd (by decide) hxne
      have heq : a = ({1, 3, 9, 13, 15, 19, 21, 25} : Finset ℕ) :=
        Finset.eq_of_subset_of_card_le hs5 (by rw [hcard]; decide)
      rw [heq] at ha
      exact not_admissible_of_image_univ (p := 7) (by decide) (by decide) ha
    · -- miss 3 mod 5 ⇒ ⊆ {1,7,9,15,19,21,25} (card 7)
      have hs5 : a ⊆ ({1, 7, 9, 15, 19, 21, 25} : Finset ℕ) := by
        intro x hx
        have hxP := hs hx
        have hxne : (x : ZMod 5) ≠ 3 := hr5 x hx
        fin_cases hxP <;> first | decide | exact absurd (by decide) hxne
      have hle := Finset.card_le_card hs5; rw [hcard] at hle; revert hle; decide
    · -- miss 4 mod 5 ⇒ ⊆ {1,3,7,13,15,21,25} (card 7)
      have hs5 : a ⊆ ({1, 3, 7, 13, 15, 21, 25} : Finset ℕ) := by
        intro x hx
        have hxP := hs hx
        have hxne : (x : ZMod 5) ≠ 4 := hr5 x hx
        fin_cases hxP <;> first | decide | exact absurd (by decide) hxne
      have hle := Finset.card_le_card hs5; rw [hcard] at hle; revert hle; decide

/-- **Lower-bound core.** Every admissible `8`-set has largest element at least `26`.
If the maximum were `≤ 25`, the set would sit in `{0,…,25}`; missing a class mod `2`
forces a single parity, placing the 8-set inside the thirteen evens `{0,2,…,24}` or
thirteen odds `{1,3,…,25}`, where the combined mod-3, mod-5 and mod-7 constraints then
rule it out. -/
theorem admissible_eight_sup_ge {a : Finset ℕ} (hcard : a.card = 8)
    (ha : Admissible a) : 26 ≤ a.sup id := by
  by_contra hlt
  push_neg at hlt
  have hbound : ∀ x ∈ a, x ≤ 25 := by
    intro x hx
    have h1 : id x ≤ a.sup id := Finset.le_sup hx
    simp only [id_eq] at h1
    omega
  have hy : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  have hdvd : ∀ x : ℕ, (x : ZMod 2) = 0 ↔ 2 ∣ x := fun x =>
    ZMod.natCast_eq_zero_iff x 2
  obtain ⟨r2, hr2⟩ := ha 2 (by decide)
  fin_cases r2
  · -- misses class 0 mod 2 ⇒ all elements odd ⇒ a ⊆ {1,3,…,25}
    have hsub : a ⊆ ({1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25} : Finset ℕ) := by
      intro x hx
      have hx25 := hbound x hx
      have hne : (x : ZMod 2) ≠ 0 := hr2 x hx
      have hodd : ¬ 2 ∣ x := fun hd => hne ((hdvd x).mpr hd)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    exact no_admissible_eight_odds hsub hcard ha
  · -- misses class 1 mod 2 ⇒ all elements even ⇒ a ⊆ {0,2,…,24}
    have hsub : a ⊆ ({0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24} : Finset ℕ) := by
      intro x hx
      have hx25 := hbound x hx
      have hne : (x : ZMod 2) ≠ 1 := hr2 x hx
      have heven : 2 ∣ x := by
        rcases hy (x : ZMod 2) with h0 | h1
        · exact (hdvd x).mp h0
        · exact absurd h1 hne
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    exact no_admissible_eight_evens hsub hcard ha

/-- **`A(8) = 26`.** The minimal largest element of an admissible `8`-set is `26`,
attained by `{0,2,6,8,12,18,20,26}`. This matches the Hardy–Littlewood minimal
diameter `H(8) = 26` and continues the frontier
`A(2)=2, A(3)=6, A(4)=8, A(5)=12, A(6)=16, A(7)=20, A(8)=26`. Its lower bound is the
first in the sequence to genuinely require the prime `7`: two forced 8-sets per parity
survive `p = 5` and are killed only at `p = 7`. -/
theorem A_eight : A 8 = 26 := by
  refine le_antisymm A_eight_le ?_
  obtain ⟨a, hcard, ha, hsup⟩ := A_mem 8
  have hge := admissible_eight_sup_ge hcard ha
  omega

/-- **`A(8) ≥ 26`.** Restatement of the lower bound now that the exact value is
known, superseding the earlier one-step-monotonicity bound `A(8) ≥ 21`. -/
theorem A_eight_ge : 26 ≤ A 8 := by rw [A_eight]

/-- **`A(8) = 26`, as the sharp two-sided sandwich.** Both bounds are now exact. -/
theorem A_eight_bounds : 26 ≤ A 8 ∧ A 8 ≤ 26 :=
  ⟨A_eight_ge, A_eight_le⟩

end Erdos1204
