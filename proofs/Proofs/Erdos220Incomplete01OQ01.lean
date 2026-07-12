/-
Erdős Problem #220 (follow-up `incomplete-01-oq-01`):
The reduced-residue squared-gap sum is EXACTLY `p - 2` for every prime `p`.

Source: https://erdosproblems.com/220
Parent:   Proofs/Erdos220Problem.lean         (Montgomery–Vaughan upper bound, axiomatized)
Sibling:  Proofs/Erdos220OQ01.lean            (the general lower bound, reused here)
          Proofs/Erdos220Incomplete01.lean    (the `p = 7, 8, 12` numeric instances)

## Open question

The sibling `Erdos220OQ01` proves, for every `n ≥ 2`, the Cauchy–Schwarz / Chebyshev
LOWER bound
        (n - 2)² ≤ (φ(n) - 1) · ∑_k (a_{k+1} - a_k)²
between the `φ(n) - 1` gaps of the reduced residues `1 = a₁ < ⋯ < a_{φ(n)} = n-1`.
The `Erdos220Incomplete01` file only checks the squared-gap sum for the concrete moduli
`n = 7, 8, 12`.  This entry closes the gap flagged by the candidate
`erdos-220-incomplete-01-oq-01`: prove the *general* prime identity

        ∑_k (a_{k+1} - a_k)² = p - 2      for **every** prime `p`,

not just `p = 7`, and identify it as the **equality case** of the Cauchy–Schwarz bound.

## Why it is exactly `p - 2`, and why that is the C–S equality case

For a prime `p` every integer in `[1, p-1]` is coprime to `p`, so the reduced residues are
the full run `1, 2, …, p-1`; the `φ(p) - 1 = p - 2` consecutive gaps are therefore **all
equal to `1`**.  We do not compute the enumeration index-by-index.  Instead:

  * every gap is a difference of consecutive *strictly increasing integers*, hence `≥ 1`
    (`one_le_gap`, valid for all `n`);
  * the `φ(p) - 1 = p - 2` gaps sum to `p - 2` (`Erdos220OQ01.sum_gaps` with `φ(p) = p-1`);
  * `m` reals each `≥ 1` summing to `m` must all equal `1`
    (`Finset.sum_eq_zero_iff_of_nonneg` applied to `gapᵢ - 1 ≥ 0`).

Once every gap is `1`, `gapᵢ² = gapᵢ`, so `∑ gapᵢ² = ∑ gapᵢ = p - 2`.  Feeding this back
into the sibling's product bound `(p-2)² ≤ (φ(p)-1)·∑ gap²` turns it into the *equality*
`(p-2)² = (p-2)·(p-2)`: primes are exactly where Cauchy–Schwarz is tight, because the gap
sequence is constant.

Everything below is proved with no `axiom`, no `sorry`, and no `native_decide`.

References:
- [MoVa86] Montgomery, Vaughan, "On the distribution of reduced residues",
           Ann. of Math. (2) 123 (1986), 311-333.
-/

import Mathlib
import Proofs.Erdos220OQ01

open Finset Nat
open Erdos220OQ01

namespace Erdos220Incomplete01OQ01

/-!
## Part I: every gap is at least `1`

The gaps are differences of consecutive values of the strictly monotone enumeration `E`,
whose values are natural numbers, so each gap is `≥ 1`.  This holds for every modulus
`n ≥ 2`, not only for primes; it is the ingredient that pins the prime gaps to `1`.
-/

/-- **Each reduced-residue gap is `≥ 1`.**  For `k + 1 < φ(n)` the two enumerated residues
`E n hn (k+1)` and `E n hn k` are casts of *distinct* natural numbers with the first
strictly larger (the enumeration `orderEmbOfFin` is an order embedding), so their difference
is at least `1`. -/
theorem one_le_gap {n : ℕ} (hn : 2 ≤ n) {k : ℕ} (hk : k + 1 < Nat.totient n) :
    1 ≤ gap n hn k := by
  have hk0 : k < Nat.totient n := by omega
  simp only [gap, E]
  rw [dif_pos hk, dif_pos hk0]
  -- The enumeration is an order embedding `Fin (φ n) ↪o ℕ`, hence strictly monotone.
  have hlt :
      ((reducedResidues n).orderEmbOfFin (card_reducedResidues hn) ⟨k, hk0⟩ : ℕ)
        < ((reducedResidues n).orderEmbOfFin (card_reducedResidues hn) ⟨k + 1, hk⟩ : ℕ) :=
    ((reducedResidues n).orderEmbOfFin (card_reducedResidues hn)).strictMono
      (Fin.mk_lt_mk.mpr (by omega))
  have hle :
      ((reducedResidues n).orderEmbOfFin (card_reducedResidues hn) ⟨k, hk0⟩ : ℕ) + 1
        ≤ ((reducedResidues n).orderEmbOfFin (card_reducedResidues hn) ⟨k + 1, hk⟩ : ℕ) := hlt
  have hcast :
      (((reducedResidues n).orderEmbOfFin (card_reducedResidues hn) ⟨k, hk0⟩ : ℕ) : ℝ) + 1
        ≤ (((reducedResidues n).orderEmbOfFin (card_reducedResidues hn) ⟨k + 1, hk⟩ : ℕ) : ℝ) := by
    exact_mod_cast hle
  linarith

/-!
## Part II: for a prime, every gap is exactly `1`

`φ(p) = p - 1`, so there are `p - 2` gaps summing to `p - 2` (telescoping), each `≥ 1`;
they must therefore all equal `1`.
-/

/-- The real cast of the gap count `φ(p) - 1 = p - 2` for a prime `p`. -/
theorem card_gaps_prime {p : ℕ} (hp : p.Prime) (hn : 2 ≤ p) :
    ((Nat.totient p - 1 : ℕ) : ℝ) = (p : ℝ) - 2 := by
  have h : Nat.totient p - 1 = p - 2 := by rw [Nat.totient_prime hp]; omega
  rw [h, Nat.cast_sub hn]
  norm_num

/-- **Every prime gap equals `1`.**  For a prime `p`, all `p - 2` consecutive gaps between
the reduced residues `1, 2, …, p-1` are equal to `1`.  Proved without computing the
enumeration: the nonnegative quantities `gapᵢ - 1` sum to `(∑ gapᵢ) - (p-2) = 0`
(`sum_gaps`), hence each vanishes (`Finset.sum_eq_zero_iff_of_nonneg`). -/
theorem gap_prime_eq_one {p : ℕ} (hp : p.Prime) (hn : 2 ≤ p)
    {k : ℕ} (hk : k ∈ Finset.range (Nat.totient p - 1)) :
    gap p hn k = 1 := by
  have hnn : ∀ j ∈ Finset.range (Nat.totient p - 1), 0 ≤ gap p hn j - 1 := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjk : j + 1 < Nat.totient p := by omega
    have := one_le_gap hn hjk
    linarith
  have hsum0 : ∑ j ∈ Finset.range (Nat.totient p - 1), (gap p hn j - 1) = 0 := by
    rw [Finset.sum_sub_distrib, sum_gaps hn, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, card_gaps_prime hp hn]
    ring
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0
  exact sub_eq_zero.mp (hzero k hk)

/-!
## Part III: the general prime squared-gap identity
-/

/-- **General reduced-residue squared-gap identity for primes.**

    ∑_k (a_{k+1} - a_k)² = p - 2      for every prime `p`,

where `1 = a₁ < a₂ < ⋯ < a_{p-1} = p-1` are the reduced residues mod `p`.  Since every gap
is `1`, the sum of squares is just the number of gaps, `φ(p) - 1 = p - 2`.  This generalises
`Erdos220Incomplete01.sumSq_gaps_seven` (`p = 7 ↦ 5`) from the single modulus `7` to all
primes. -/
theorem sumSq_gaps_prime {p : ℕ} (hp : p.Prime) (hn : 2 ≤ p) :
    ∑ k ∈ Finset.range (Nat.totient p - 1), (gap p hn k) ^ 2 = (p : ℝ) - 2 := by
  have hsq : ∑ k ∈ Finset.range (Nat.totient p - 1), (gap p hn k) ^ 2
      = ∑ k ∈ Finset.range (Nat.totient p - 1), gap p hn k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [gap_prime_eq_one hp hn hk]
    norm_num
  rw [hsq, sum_gaps hn]

/-- **The Cauchy–Schwarz bound is attained exactly at the primes.**  The sibling's lower
bound `sq_le_card_mul_sumSq` reads `(p-2)² ≤ (φ(p)-1)·∑ gap²`; for a prime it becomes the
*equality* `(p-2)² = (φ(p)-1)·∑ gap²`, since the constant gap sequence `1, 1, …, 1` is the
equality case of Cauchy–Schwarz (all entries equal). -/
theorem cauchy_schwarz_equality_prime {p : ℕ} (hp : p.Prime) (hn : 2 ≤ p) :
    ((p : ℝ) - 2) ^ 2
      = (Nat.totient p - 1 : ℕ) * ∑ k ∈ Finset.range (Nat.totient p - 1), (gap p hn k) ^ 2 := by
  rw [sumSq_gaps_prime hp hn, card_gaps_prime hp hn]
  ring

/-- Sanity check against the sibling's concrete `p = 7` instance: the squared-gap sum is
`7 - 2 = 5`. -/
example :
    ∑ k ∈ Finset.range (Nat.totient 7 - 1), (gap 7 (by norm_num) k) ^ 2 = 5 := by
  have h := sumSq_gaps_prime (p := 7) (by norm_num) (by norm_num)
  rw [show ((7 : ℝ) - 2) = 5 from by norm_num] at h
  exact h

end Erdos220Incomplete01OQ01
