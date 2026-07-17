import Proofs.Erdos1204A8

/-
# Erdős #1204 — the exact value `A(9) = 30`

Continues the exact-value frontier
`A(2)=2, A(3)=6, A(4)=8, A(5)=12, A(6)=16, A(7)=20, A(8)=26`
(`Erdos1204Problem.lean`, `Erdos1204A4`–`A8`) with the next Hardy–Littlewood minimal
diameter `A(9) = H(9) = 30` (OEIS A008407), verified and axiom-free.

- **Upper bound** `A(9) ≤ 30` (`A_nine_le`): the witness `{0,2,6,8,12,18,20,26,30}` (the
  `A(8)` witness extended by `30`) is admissible — all even (misses the odd class mod 2);
  residues `0,2,0,2,0,0,2,2,0` mod 3 (misses class 1); residues `0,2,1,3,2,3,0,1,0` mod 5
  (misses class 4); residues `0,2,6,1,5,4,6,5,2` mod 7 (misses class 3). Primes `p ≥ 11`
  are automatic since `|a| = 9 < p`.
- **Lower bound** `A(9) ≥ 30` (`admissible_nine_sup_ge`): here the mod-`2,3,5` sieve alone
  already closes the bound — the prime `7` is *not* needed. An admissible set misses one
  residue class modulo each of `2, 3, 5`; by CRT the residues mod `2·3·5 = 30` that survive
  all three exclusions number exactly `30·(1/2)·(2/3)·(4/5) = 8`. So an admissible set
  contained in `{0,…,29}` has at most `8` elements — strictly fewer than `9`. Any admissible
  `9`-set therefore has an element `≥ 30`.

This is a cleaner mechanism than `A(8) = 26`, whose lower bound genuinely required `p = 7`:
the window `{0,…,25}` has `13` elements per parity, and the mod-`2,3,5` count leaves room
for `9`-slot pools that only `p = 7` rules out. For `A(9)` the window `{0,…,29}` has `15`
per parity and the `2·3·5 = 30` primorial divides the window length exactly, so the
mod-`2,3,5` density `8` already falls below the target `9`.

The asymptotics `A(k) ∼ k log k` remain OPEN (need sieve theory).
-/

namespace Erdos1204

open Finset

/-- The witness `{0,2,6,8,12,18,20,26,30}` (the `A(8)` witness plus `30`) is admissible:
even ⇒ misses the odd class mod 2; residues `0,2,0,2,0,0,2,2,0` mod 3 ⇒ misses class 1;
residues `0,2,1,3,2,3,0,1,0` mod 5 ⇒ misses class 4; residues `0,2,6,1,5,4,6,5,2` mod 7 ⇒
misses class 3. (Primes `p ≥ 11` are automatic since `|a| = 9 < p`.) Gives `A(9) ≤ 30`. -/
theorem admissible_witness_nine :
    Admissible ({0, 2, 6, 8, 12, 18, 20, 26, 30} : Finset ℕ) := by
  rw [admissible_iff_card]
  intro p hp hcard
  have hc : ({0, 2, 6, 8, 12, 18, 20, 26, 30} : Finset ℕ).card = 9 := by decide
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
  · exact absurd hp (by decide)   -- p = 9: not prime

/-- **`A(9) ≤ 30`.** The admissible `9`-set `{0,2,6,8,12,18,20,26,30}` has largest
element `30`, so the minimal largest element of an admissible `9`-set is at most `30`.
This is the upper half of the Hardy–Littlewood value `H(9) = 30`. -/
theorem A_nine_le : A 9 ≤ 30 := by
  have h := A_le (k := 9) (a := ({0, 2, 6, 8, 12, 18, 20, 26, 30} : Finset ℕ)) (by decide)
    admissible_witness_nine
  have hs : ({0, 2, 6, 8, 12, 18, 20, 26, 30} : Finset ℕ).sup id = 30 := by decide
  rwa [hs] at h

/-- **Lower-bound core.** Every admissible `9`-set has largest element at least `30`.

If the maximum were `≤ 29`, the set would sit in `{0,…,29}`. Admissibility supplies a
missed residue class modulo each of `2`, `3` and `5`, so the set is contained in the
filter of `{0,…,29}` avoiding all three classes. By the Chinese Remainder Theorem the
surviving residues modulo `2·3·5 = 30` number exactly `1·2·4 = 8`, so that filter has
`8` elements for *every* choice of the three missed classes (checked by `decide` over
the `2·3·5 = 30` combinations). Hence the set has at most `8 < 9` elements — impossible.

Unlike `A(8) = 26`, the prime `7` plays no role: the primorial `2·3·5 = 30` already
matches the window length `{0,…,29}`, forcing the mod-`2,3,5` density below `9`. -/
theorem admissible_nine_sup_ge {a : Finset ℕ} (hcard : a.card = 9)
    (ha : Admissible a) : 30 ≤ a.sup id := by
  by_contra hlt
  push_neg at hlt
  have hbound : ∀ x ∈ a, x ≤ 29 := by
    intro x hx
    have h1 : id x ≤ a.sup id := Finset.le_sup hx
    simp only [id_eq] at h1
    omega
  obtain ⟨r2, hr2⟩ := ha 2 (by decide)
  obtain ⟨r3, hr3⟩ := ha 3 (by decide)
  obtain ⟨r5, hr5⟩ := ha 5 (by decide)
  -- Every element of `a` lies in `{0,…,29}` and dodges the three missed classes.
  have hsub : a ⊆ (Finset.range 30).filter
      (fun x : ℕ => (x : ZMod 2) ≠ r2 ∧ (x : ZMod 3) ≠ r3 ∧ (x : ZMod 5) ≠ r5) := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := hbound x hx; omega, hr2 x hx, hr3 x hx, hr5 x hx⟩
  -- For every triple of missed classes the surviving filter has exactly `8` elements.
  have hcardf : ((Finset.range 30).filter
      (fun x : ℕ => (x : ZMod 2) ≠ r2 ∧ (x : ZMod 3) ≠ r3 ∧ (x : ZMod 5) ≠ r5)).card ≤ 8 := by
    fin_cases r2 <;> fin_cases r3 <;> fin_cases r5 <;> decide
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  omega

/-- **`A(9) = 30`.** The minimal largest element of an admissible `9`-set is `30`,
attained by `{0,2,6,8,12,18,20,26,30}`. This matches the Hardy–Littlewood minimal
diameter `H(9) = 30` (OEIS A008407) and continues the frontier
`A(2)=2, A(3)=6, A(4)=8, A(5)=12, A(6)=16, A(7)=20, A(8)=26, A(9)=30`. Its lower bound is
the first in the sequence where the mod-`2,3,5` sieve alone suffices: the primorial
`2·3·5 = 30` equals the window length, so `p = 7` — binding at `A(8)` — is not needed. -/
theorem A_nine : A 9 = 30 := by
  refine le_antisymm A_nine_le ?_
  obtain ⟨a, hcard, ha, hsup⟩ := A_mem 9
  have hge := admissible_nine_sup_ge hcard ha
  omega

/-- **`A(9) ≥ 30`.** Restatement of the lower bound now that the exact value is known,
superseding the earlier one-step-monotonicity bound `A(9) ≥ 27`. -/
theorem A_nine_ge : 30 ≤ A 9 := by rw [A_nine]

/-- **`A(9) = 30`, as the sharp two-sided sandwich.** Both bounds are now exact,
tightening the earlier `27 ≤ A(9) ≤ 30` bracket to a single value. -/
theorem A_nine_bounds : 30 ≤ A 9 ∧ A 9 ≤ 30 :=
  ⟨A_nine_ge, A_nine_le⟩

end Erdos1204
