import Proofs.Erdos1204A8

/-
# Erdős #1204 — bracketing the next frontier value `A(9)`

Continues the exact-value frontier
`A(2)=2, A(3)=6, A(4)=8, A(5)=12, A(6)=16, A(7)=20, A(8)=26`
(`Erdos1204Problem.lean`, `Erdos1204A4`–`A8`) one step further. The Hardy–Littlewood
minimal diameter is `H(9) = 30`, and we pin `A(9)` into the tight window `27 ≤ A(9) ≤ 30`:

- **Upper bound** `A(9) ≤ 30` (`A_nine_le`): the witness `{0,2,6,8,12,18,20,26,30}` (the
  `A(8)` witness extended by `30`) is admissible — all even (misses the odd class mod 2);
  residues `0,2,0,2,0,0,2,2,0` mod 3 (misses class 1); residues `0,2,1,3,2,3,0,1,0` mod 5
  (misses class 4); residues `0,2,6,1,5,4,6,5,2` mod 7 (misses class 3). Primes `p ≥ 11`
  are automatic since `|a| = 9 < p`.
- **Lower bound** `A(9) ≥ 27` (`A_nine_ge`): strict one-step monotonicity
  (`A_lt_A_succ`) applied at the now-exact value `A(8) = 26` gives `A(9) > 26`, hence
  `A(9) ≥ 27`.

The remaining gap `27 ≤ A(9) ≤ 30` is only an integer-scale ambiguity: the exact value
`A(9) = 30 = H(9)` awaits the same exhaustive `p = 2,3,5,7` pruning over `{0,…,29}` used
for `A(8) = 26` in `Erdos1204A8`. The asymptotics `A(k) ∼ k log k` remain OPEN.
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

/-- **`A(9) ≥ 27`.** Strict one-step monotonicity `A_lt_A_succ` at the exact value
`A(8) = 26` forces `A(9) > 26`, i.e. `A(9) ≥ 27`. This already separates `A(9)` from
`A(8)`, so the frontier stays strictly increasing past the last computed exact value. -/
theorem A_nine_ge : 27 ≤ A 9 := by
  have h : A 8 < A 9 := A_lt_A_succ (k := 8) (by norm_num)
  rw [A_eight] at h
  omega

/-- **`A(9)` bracket.** Combining the witness upper bound with strict monotonicity off
`A(8) = 26` pins `A(9)` to the four-value window `27 ≤ A(9) ≤ 30`. The exact value
`A(9) = 30 = H(9)` awaits the exhaustive `p = 2,3,5,7` lower-bound search over
`{0,…,29}` (cf. `Erdos1204A8` for `A(8)`). -/
theorem A_nine_bounds : 27 ≤ A 9 ∧ A 9 ≤ 30 :=
  ⟨A_nine_ge, A_nine_le⟩

end Erdos1204
