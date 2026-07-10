import Proofs.Erdos1204A7

/-
# Erdős #1204 — the upper bound `A(8) ≤ 26` (Hardy–Littlewood witness)

Continues the exact-value frontier `A(2)=2, A(3)=6, A(4)=8, A(5)=12, A(6)=16,
A(7)=20` (`Erdos1204Problem.lean`, `Erdos1204A4`–`A7`) toward the next Hardy–
Littlewood minimal diameter `H(8) = 26`.

This file certifies the **upper half** of `A(8) = 26`: the explicit admissible
`8`-tuple `{0,2,6,8,12,18,20,26}` (the `A(7)` witness extended by `26`), whose
largest element is `26`, so `A(8) ≤ 26`. Together with the one-step strict
monotonicity `A(7) < A(8)` (`A_lt_A_succ`, giving `A(8) ≥ 21`) this sandwiches
`21 ≤ A(8) ≤ 26`.

The **matching lower bound** `A(8) ≥ 26` — no admissible `8`-set fits in `{0,…,25}` —
is the hard extremal direction: unlike `A(7)` (killed already at `p = 5`), the `A(8)`
lower bound is where the prime `7` first becomes binding, requiring a mod-`2,3,5,7`
pruning over the `26`-element window. It is left for future work; the exact value and
the asymptotics `A(k) ∼ k log k` (sieve theory) remain OPEN.

- **Witness admissibility.** `{0,2,6,8,12,18,20,26}` is admissible: all even (misses
  the odd class mod 2); residues `0,2,0,2,0,0,2,2` mod 3 (misses class 1); residues
  `0,2,1,3,2,3,0,1` mod 5 (misses class 4); residues `0,2,6,1,5,4,6,5` mod 7 (misses
  class 3). Primes `p ≥ 11` are automatic since `|a| = 8 < p`.
-/

namespace Erdos1204

open Finset

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

/-- **`A(8) ≥ 21`.** Strict one-step monotonicity `A(7) < A(8)` (`A_lt_A_succ`)
together with the exact value `A(7) = 20` (`A_seven`) forces `A(8) ≥ 21` — sharper
than the general parity bound `2·(8−1) = 14 ≤ A(8)`. -/
theorem A_eight_ge : 21 ≤ A 8 := by
  have hlt : A 7 < A 8 := A_lt_A_succ (k := 7) (by norm_num)
  rw [A_seven] at hlt
  omega

/-- **`21 ≤ A(8) ≤ 26`.** The current sandwich for the next frontier value. The upper
bound is the Hardy–Littlewood witness `{0,2,6,8,12,18,20,26}`; the lower bound is
one-step strict monotonicity from `A(7) = 20`. Closing the gap to the exact
`A(8) = 26` needs the mod-`2,3,5,7` lower-bound case analysis (where `p = 7` first
becomes binding), left as future work. -/
theorem A_eight_bounds : 21 ≤ A 8 ∧ A 8 ≤ 26 :=
  ⟨A_eight_ge, A_eight_le⟩

end Erdos1204
