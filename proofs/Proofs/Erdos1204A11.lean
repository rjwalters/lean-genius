import Proofs.Erdos1204A10

/-
# Erdős #1204 — the exact value `A(11) = 36`

Continues the exact-value frontier
`A(2)=2, A(3)=6, A(4)=8, A(5)=12, A(6)=16, A(7)=20, A(8)=26, A(9)=30, A(10)=32`
(`Erdos1204Problem.lean`, `Erdos1204A4`–`A10`) with the next Hardy–Littlewood minimal
diameter `A(11) = H(11) = 36` (OEIS A008407), verified and axiom-free.

- **Upper bound** `A(11) ≤ 36` (`A_eleven_le`): the witness `{0,2,6,8,12,18,20,26,30,32,36}`
  (the `A(10)` witness extended by `36`) is admissible — all even (misses the odd class
  mod 2); residues `0,2,0,2,0,0,2,2,0,2,0` mod 3 (misses class 1); residues
  `0,2,1,3,2,3,0,1,0,2,1` mod 5 (misses class 4); residues `0,2,6,1,5,4,6,5,2,4,1` mod 7
  (misses class 3); residues `0,2,6,8,1,7,9,4,8,10,3` mod 11 (misses class 5). Now that
  `|a| = 11`, the prime `11 = |a|` itself must miss a class — and it does. Primes `p ≥ 13`
  are automatic since `|a| = 11 < p`.
- **Lower bound** `A(11) ≥ 36` (`admissible_eleven_sup_ge`): as at `A(9)` and `A(10)`, the
  mod-`2,3,5` sieve alone already closes the bound — the primes `7` and `11` are *not*
  needed. An admissible set misses one residue class modulo each of `2, 3, 5`; the surviving
  residues inside the window `{0,…,35}` number at most `10` for *every* choice of the three
  missed classes (checked by `decide` over the `2·3·5 = 30` combinations). So an admissible
  set contained in `{0,…,35}` has at most `10` elements — strictly fewer than `11`. Any
  admissible `11`-set therefore has an element `≥ 36`.

**Why `p = 5` still suffices.** The mod-`2,3,5` density on the window `{0,…,35}` (length
`36`) is `36·(1/2)(2/3)(4/5) = 9.6` on average, and the exact maximum over all `30`
class-triples is `10` (e.g. missing `0` mod `2`, `0` mod `3`, `2` mod `5`) — still below the
target `11`. The window `{0,…,35}` sits just above the primorial `2·3·5 = 30`, so the sieve
density has not yet climbed to `11`. This is the third consecutive frontier value
(`A(9), A(10), A(11)`) that the small-prime sieve settles without the deeper forced-set
analysis that `A(8)` required.

The asymptotics `A(k) ∼ k log k` remain OPEN (need sieve theory).
-/

namespace Erdos1204

open Finset

/-- The witness `{0,2,6,8,12,18,20,26,30,32,36}` (the `A(10)` witness plus `36`) is
admissible: even ⇒ misses the odd class mod 2; residues `0,2,0,2,0,0,2,2,0,2,0` mod 3 ⇒
misses class 1; residues `0,2,1,3,2,3,0,1,0,2,1` mod 5 ⇒ misses class 4; residues
`0,2,6,1,5,4,6,5,2,4,1` mod 7 ⇒ misses class 3; residues `0,2,6,8,1,7,9,4,8,10,3` mod 11 ⇒
misses class 5. (Primes `p ≥ 13` are automatic since `|a| = 11 < p`.) Gives `A(11) ≤ 36`. -/
theorem admissible_witness_eleven :
    Admissible ({0, 2, 6, 8, 12, 18, 20, 26, 30, 32, 36} : Finset ℕ) := by
  rw [admissible_iff_card]
  intro p hp hcard
  have hc : ({0, 2, 6, 8, 12, 18, 20, 26, 30, 32, 36} : Finset ℕ).card = 11 := by decide
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
  · exact absurd hp (by decide)   -- p = 10: not prime
  · exact ⟨5, by intro x hx; fin_cases hx <;> decide⟩   -- p = 11: miss class 5

/-- **`A(11) ≤ 36`.** The admissible `11`-set `{0,2,6,8,12,18,20,26,30,32,36}` has largest
element `36`, so the minimal largest element of an admissible `11`-set is at most `36`.
This is the upper half of the Hardy–Littlewood value `H(11) = 36`. -/
theorem A_eleven_le : A 11 ≤ 36 := by
  have h := A_le (k := 11) (a := ({0, 2, 6, 8, 12, 18, 20, 26, 30, 32, 36} : Finset ℕ))
    (by decide) admissible_witness_eleven
  have hs : ({0, 2, 6, 8, 12, 18, 20, 26, 30, 32, 36} : Finset ℕ).sup id = 36 := by decide
  rwa [hs] at h

/-- **Lower-bound core.** Every admissible `11`-set has largest element at least `36`.

If the maximum were `≤ 35`, the set would sit in `{0,…,35}`. Admissibility supplies a
missed residue class modulo each of `2`, `3` and `5`, so the set is contained in the
filter of `{0,…,35}` avoiding all three classes. That filter has at most `10` elements for
*every* choice of the three missed classes (checked by `decide` over the `2·3·5 = 30`
combinations). Hence the set has at most `10 < 11` elements — impossible.

As with `A(9)` and `A(10)`, the primes `7` and `11` play no role: the mod-`2,3,5` sieve
density already falls below `11` on the window `{0,…,35}`. -/
theorem admissible_eleven_sup_ge {a : Finset ℕ} (hcard : a.card = 11)
    (ha : Admissible a) : 36 ≤ a.sup id := by
  by_contra hlt
  push_neg at hlt
  have hbound : ∀ x ∈ a, x ≤ 35 := by
    intro x hx
    have h1 : id x ≤ a.sup id := Finset.le_sup hx
    simp only [id_eq] at h1
    omega
  obtain ⟨r2, hr2⟩ := ha 2 (by decide)
  obtain ⟨r3, hr3⟩ := ha 3 (by decide)
  obtain ⟨r5, hr5⟩ := ha 5 (by decide)
  -- Every element of `a` lies in `{0,…,35}` and dodges the three missed classes.
  have hsub : a ⊆ (Finset.range 36).filter
      (fun x : ℕ => (x : ZMod 2) ≠ r2 ∧ (x : ZMod 3) ≠ r3 ∧ (x : ZMod 5) ≠ r5) := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := hbound x hx; omega, hr2 x hx, hr3 x hx, hr5 x hx⟩
  -- For every triple of missed classes the surviving filter has at most `10` elements.
  have hcardf : ((Finset.range 36).filter
      (fun x : ℕ => (x : ZMod 2) ≠ r2 ∧ (x : ZMod 3) ≠ r3 ∧ (x : ZMod 5) ≠ r5)).card ≤ 10 := by
    fin_cases r2 <;> fin_cases r3 <;> fin_cases r5 <;> decide
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  omega

/-- **`A(11) = 36`.** The minimal largest element of an admissible `11`-set is `36`,
attained by `{0,2,6,8,12,18,20,26,30,32,36}`. This matches the Hardy–Littlewood minimal
diameter `H(11) = 36` (OEIS A008407) and continues the frontier
`A(2)=2, …, A(10)=32, A(11)=36`. Like `A(9)` and `A(10)`, its lower bound is settled by the
mod-`2,3,5` sieve alone — neither `7` nor `11` is needed. -/
theorem A_eleven : A 11 = 36 := by
  refine le_antisymm A_eleven_le ?_
  obtain ⟨a, hcard, ha, hsup⟩ := A_mem 11
  have hge := admissible_eleven_sup_ge hcard ha
  omega

/-- **`A(11) ≥ 36`.** Restatement of the lower bound now that the exact value is known. -/
theorem A_eleven_ge : 36 ≤ A 11 := by rw [A_eleven]

/-- **`A(11) = 36`, as the sharp two-sided sandwich.** -/
theorem A_eleven_bounds : 36 ≤ A 11 ∧ A 11 ≤ 36 :=
  ⟨A_eleven_ge, A_eleven_le⟩

-- Axiom audit: axiom-free (only `propext, Classical.choice, Quot.sound`).
#print axioms A_eleven

end Erdos1204
