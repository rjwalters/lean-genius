import Proofs.Erdos1204A9

/-
# Erdős #1204 — the exact value `A(10) = 32`

Continues the exact-value frontier
`A(2)=2, A(3)=6, A(4)=8, A(5)=12, A(6)=16, A(7)=20, A(8)=26, A(9)=30`
(`Erdos1204Problem.lean`, `Erdos1204A4`–`A9`) with the next Hardy–Littlewood minimal
diameter `A(10) = H(10) = 32` (OEIS A008407), verified and axiom-free.

- **Upper bound** `A(10) ≤ 32` (`A_ten_le`): the witness `{0,2,6,8,12,18,20,26,30,32}`
  (the `A(9)` witness extended by `32`) is admissible — all even (misses the odd class
  mod 2); residues `0,2,0,2,0,0,2,2,0,2` mod 3 (misses class 1); residues
  `0,2,1,3,2,3,0,1,0,2` mod 5 (misses class 4); residues `0,2,6,1,5,4,6,5,2,4` mod 7
  (misses class 3). Primes `p ≥ 11` are automatic since `|a| = 10 < p`.
- **Lower bound** `A(10) ≥ 32` (`admissible_ten_sup_ge`): as at `A(9)`, the mod-`2,3,5`
  sieve alone already closes the bound — the prime `7` is *not* needed. An admissible set
  misses one residue class modulo each of `2, 3, 5`; the surviving residues inside the
  window `{0,…,31}` number at most `9` for *every* choice of the three missed classes
  (checked by `decide` over the `2·3·5 = 30` combinations). So an admissible set contained
  in `{0,…,31}` has at most `9` elements — strictly fewer than `10`. Any admissible
  `10`-set therefore has an element `≥ 32`.

**Correcting the earlier estimate.** The prior next-step note (see `erdos-1204.json`)
predicted that `A(10)` would need `p = 7` back as a binding constraint, reasoning from the
*average* mod-`2,3,5` density `32·(1/2)(2/3)(4/5) = 8.53` that "up to ~10–11 survive". The
exact maximum over all `30` class-triples is only `9`, not `10` or `11`: the odd-`+`
mod-`3` mod-`5` filter of `{0,…,31}` peaks at `9` survivors (e.g. missing `0` mod each of
`2,3,5`). So `A(10)` joins `A(9)` as a value the mod-`2,3,5` sieve settles outright, and the
window `{0,…,31}` (length `32`, just above the primorial `2·3·5 = 30`) still holds the
density below the target `10`.

The asymptotics `A(k) ∼ k log k` remain OPEN (need sieve theory).
-/

namespace Erdos1204

open Finset

/-- The witness `{0,2,6,8,12,18,20,26,30,32}` (the `A(9)` witness plus `32`) is admissible:
even ⇒ misses the odd class mod 2; residues `0,2,0,2,0,0,2,2,0,2` mod 3 ⇒ misses class 1;
residues `0,2,1,3,2,3,0,1,0,2` mod 5 ⇒ misses class 4; residues `0,2,6,1,5,4,6,5,2,4` mod 7
⇒ misses class 3. (Primes `p ≥ 11` are automatic since `|a| = 10 < p`.) Gives `A(10) ≤ 32`. -/
theorem admissible_witness_ten :
    Admissible ({0, 2, 6, 8, 12, 18, 20, 26, 30, 32} : Finset ℕ) := by
  rw [admissible_iff_card]
  intro p hp hcard
  have hc : ({0, 2, 6, 8, 12, 18, 20, 26, 30, 32} : Finset ℕ).card = 10 := by decide
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

/-- **`A(10) ≤ 32`.** The admissible `10`-set `{0,2,6,8,12,18,20,26,30,32}` has largest
element `32`, so the minimal largest element of an admissible `10`-set is at most `32`.
This is the upper half of the Hardy–Littlewood value `H(10) = 32`. -/
theorem A_ten_le : A 10 ≤ 32 := by
  have h := A_le (k := 10) (a := ({0, 2, 6, 8, 12, 18, 20, 26, 30, 32} : Finset ℕ)) (by decide)
    admissible_witness_ten
  have hs : ({0, 2, 6, 8, 12, 18, 20, 26, 30, 32} : Finset ℕ).sup id = 32 := by decide
  rwa [hs] at h

/-- **Lower-bound core.** Every admissible `10`-set has largest element at least `32`.

If the maximum were `≤ 31`, the set would sit in `{0,…,31}`. Admissibility supplies a
missed residue class modulo each of `2`, `3` and `5`, so the set is contained in the
filter of `{0,…,31}` avoiding all three classes. That filter has at most `9` elements for
*every* choice of the three missed classes (checked by `decide` over the `2·3·5 = 30`
combinations). Hence the set has at most `9 < 10` elements — impossible.

As with `A(9)`, the prime `7` plays no role: the mod-`2,3,5` sieve density already falls
below `10` on the window `{0,…,31}`. -/
theorem admissible_ten_sup_ge {a : Finset ℕ} (hcard : a.card = 10)
    (ha : Admissible a) : 32 ≤ a.sup id := by
  by_contra hlt
  push_neg at hlt
  have hbound : ∀ x ∈ a, x ≤ 31 := by
    intro x hx
    have h1 : id x ≤ a.sup id := Finset.le_sup hx
    simp only [id_eq] at h1
    omega
  obtain ⟨r2, hr2⟩ := ha 2 (by decide)
  obtain ⟨r3, hr3⟩ := ha 3 (by decide)
  obtain ⟨r5, hr5⟩ := ha 5 (by decide)
  -- Every element of `a` lies in `{0,…,31}` and dodges the three missed classes.
  have hsub : a ⊆ (Finset.range 32).filter
      (fun x : ℕ => (x : ZMod 2) ≠ r2 ∧ (x : ZMod 3) ≠ r3 ∧ (x : ZMod 5) ≠ r5) := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := hbound x hx; omega, hr2 x hx, hr3 x hx, hr5 x hx⟩
  -- For every triple of missed classes the surviving filter has at most `9` elements.
  have hcardf : ((Finset.range 32).filter
      (fun x : ℕ => (x : ZMod 2) ≠ r2 ∧ (x : ZMod 3) ≠ r3 ∧ (x : ZMod 5) ≠ r5)).card ≤ 9 := by
    fin_cases r2 <;> fin_cases r3 <;> fin_cases r5 <;> decide
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  omega

/-- **`A(10) = 32`.** The minimal largest element of an admissible `10`-set is `32`,
attained by `{0,2,6,8,12,18,20,26,30,32}`. This matches the Hardy–Littlewood minimal
diameter `H(10) = 32` (OEIS A008407) and continues the frontier
`A(2)=2, …, A(9)=30, A(10)=32`. Like `A(9)`, its lower bound is settled by the mod-`2,3,5`
sieve alone — `p = 7` is not needed. -/
theorem A_ten : A 10 = 32 := by
  refine le_antisymm A_ten_le ?_
  obtain ⟨a, hcard, ha, hsup⟩ := A_mem 10
  have hge := admissible_ten_sup_ge hcard ha
  omega

/-- **`A(10) ≥ 32`.** Restatement of the lower bound now that the exact value is known. -/
theorem A_ten_ge : 32 ≤ A 10 := by rw [A_ten]

/-- **`A(10) = 32`, as the sharp two-sided sandwich.** -/
theorem A_ten_bounds : 32 ≤ A 10 ∧ A 10 ≤ 32 :=
  ⟨A_ten_ge, A_ten_le⟩

end Erdos1204
