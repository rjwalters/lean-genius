/-
  **Improving the general (non-squarefree) magnitude lower bound by a factor of 5.**

  `AbundantNumberOQ02OQ01LowerBound.lean` proves the radical bound

      n odd, coprime to 3, abundant  ⟹  n ≥ 5·7·11·13·17·19·23 = 37182145,

  obtained from `ω(n) ≥ 7` and `radical ∣ n`.  `AbundantNumberOQ02OQ01Squarefree.lean`
  resolves the **squarefree** subproblem exactly: a squarefree such `n` has `ω(n) ≥ 9`
  and `n ≥ 5·7·11·13·17·19·23·29·31 = 33426748355`.

  This file combines the two to push the **general** bound up by a clean factor of `5`:

      n odd, coprime to 3, abundant  ⟹  n ≥ 185910725  (= 5 · 37182145).

  The argument is a two-line dichotomy on squarefreeness, needing no new search:

  * **Squarefree case.**  By the companion's squarefree theorem `n ≥ 33426748355`,
    which already exceeds `185910725`.
  * **Non-squarefree case.**  Some prime `p` (necessarily `≥ 5`, since `n` is odd and
    coprime to 3) has `p² ∣ n`.  Then `p · radical ∣ n`: writing the radical as
    `p · ∏_{q∣n, q≠p} q`, we have `p · radical = p² · ∏_{q≠p} q`, a product of the
    coprime divisors `p² ∣ n` and `∏_{q≠p} q ∣ n`.  Hence
    `n ≥ p · radical ≥ 5 · 37182145 = 185910725`.

  Why this is the right increment: the genuine minimum `5391411025 = 5²·7·11·13·17·19·23·29`
  is **non-squarefree** (the `5²` is what lets only 8 primes suffice).  The radical bound
  `37182145` cannot see the repeated prime at all; this file extracts exactly the *one*
  extra factor of the smallest prime that non-squarefreeness forces, which is the cheapest
  structural information beyond the radical.  Closing the remaining gap to `5391411025`
  needs the full exponent/size structure and stays open.

  Everything is axiom-free (only `propext`/`Classical.choice`/`Quot.sound`; no
  `Lean.ofReduceBool`, no `native_decide`, no `sorry`).
-/
import Mathlib
import Proofs.AbundantNumberOQ02OQ01LowerBound
import Proofs.AbundantNumberOQ02OQ01Squarefree

namespace AbundantNumberOQ02OQ01GeneralBound

open AbundantNumberOQ02OQ01Unconditional
open AbundantNumberOQ02OQ01LowerBound
open AbundantNumberOQ02OQ01Squarefree

/-- Every prime factor of an odd number coprime to 3 is at least 5. -/
lemma primeFactor_ge_five {n : ℕ} (hodd : Odd n) (h3 : ¬ (3 ∣ n)) :
    ∀ p ∈ n.primeFactors, 5 ≤ p := by
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have h2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hodd
    obtain ⟨m, hm⟩ := hpn
    omega
  have h3' : p ≠ 3 := by rintro rfl; exact h3 hpn
  have hp2 := hpp.two_le
  rcases Nat.lt_or_ge p 5 with h5 | h5
  · interval_cases p
    · exact absurd rfl h2
    · exact absurd rfl h3'
    · exact absurd hpp (by decide)
  · exact h5

/-- **The radical lower bound, isolated.**  The radical `∏_{p∣n} p` of an odd abundant
number coprime to 3 is at least `37182145 = 5·7·11·13·17·19·23` (the product of the seven
smallest primes `≥ 5`).  This is the radical-domination core of
`AbundantNumberOQ02OQ01LowerBound.odd_abundant_coprime_three_ge`, extracted so it can be
multiplied by the extra prime in the non-squarefree case below. -/
lemma radical_ge
    {n : ℕ} (hodd : Odd n) (h3 : ¬ (3 ∣ n)) (habund : Nat.Abundant n) :
    37182145 ≤ ∏ p ∈ n.primeFactors, p := by
  have h7 := odd_abundant_coprime_three_seven_primeFactors hodd h3 habund
  set S := n.primeFactors with hS
  have hge5 : ∀ p ∈ S, 5 ≤ p := primeFactor_ge_five hodd h3
  have hLpair : (S.sort (· ≤ ·)).Pairwise (· < ·) := by
    have hsorted : List.Pairwise (· ≤ ·) (S.sort (· ≤ ·)) := Finset.pairwise_sort S (· ≤ ·)
    have hnodup : (S.sort (· ≤ ·)).Nodup := Finset.sort_nodup S (· ≤ ·)
    exact (hsorted.and hnodup).imp (fun h => lt_of_le_of_ne h.1 h.2)
  have hLprime : ∀ x ∈ S.sort (· ≤ ·), x.Prime := by
    intro x hx
    rw [Finset.mem_sort] at hx
    exact Nat.prime_of_mem_primeFactors (hS ▸ hx)
  have hLfloor : ∀ x ∈ S.sort (· ≤ ·), ∀ c0 ∈ ([5, 7, 11, 13, 17, 19, 23] : List ℕ).head?, c0 ≤ x := by
    intro x hx c0 hc0
    simp only [List.head?_cons, Option.mem_some_iff] at hc0
    subst hc0
    rw [Finset.mem_sort] at hx
    exact hge5 x hx
  have hLlen : ([5, 7, 11, 13, 17, 19, 23] : List ℕ).length ≤ (S.sort (· ≤ ·)).length := by
    rw [Finset.length_sort]
    simpa using h7
  have hdom : ([5, 7, 11, 13, 17, 19, 23] : List ℕ).prod ≤ (S.sort (· ≤ ·)).prod :=
    domProd [5, 7, 11, 13, 17, 19, 23] (S.sort (· ≤ ·)) hLpair hLprime hLfloor hLlen gapList_canon7
  rw [canon7_prod] at hdom
  have hprodList : (S.sort (· ≤ ·)).prod = ∏ p ∈ S, p := by
    have h1 : (S.sort (· ≤ ·)).prod = S.toList.prod :=
      List.Perm.prod_eq (Finset.sort_perm_toList S (· ≤ ·))
    have h2 : S.toList.prod = ∏ p ∈ S, p := by
      simpa using Finset.prod_map_toList S (fun p => p)
    rw [h1]; exact h2
  rw [hprodList] at hdom
  exact hdom

/-- **Improved general lower bound.**  Every odd abundant number coprime to 3 is at least
`185910725 = 5 · 37182145`, a factor of `5` above the bare radical bound.  The extra
factor comes for free from squarefreeness analysis: a squarefree witness is already past
`33426748355`, and a non-squarefree one carries a repeated prime `p ≥ 5` giving
`p · radical ∣ n`. -/
theorem odd_abundant_coprime_three_ge_185M
    {n : ℕ} (hodd : Odd n) (h3 : ¬ (3 ∣ n)) (habund : Nat.Abundant n) :
    185910725 ≤ n := by
  -- `n ≠ 0` (`ω(n) ≥ 7 > 0`).
  have h7 := odd_abundant_coprime_three_seven_primeFactors hodd h3 habund
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [Nat.primeFactors_zero, Finset.card_empty] at h7
    omega
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  by_cases hsf : Squarefree n
  · -- Squarefree: already ≥ 33426748355.
    have := squarefree_odd_abundant_coprime_three_ge hsf hodd h3 habund
    omega
  · -- Non-squarefree: a repeated prime `p ≥ 5` gives `p · radical ∣ n`.
    set S := n.primeFactors with hS
    -- Extract a prime `p` with `p * p ∣ n`.
    rw [Nat.squarefree_iff_prime_squarefree] at hsf
    push_neg at hsf
    obtain ⟨p, hp_prime, hp_sq⟩ := hsf
    -- `Nat.squarefree_iff_prime_squarefree` lives in `namespace Nat`, so its `Prime`
    -- is `Nat.Prime`; `hp_prime : p.Prime` already.
    have hpp : p.Prime := hp_prime
    have hpn : p ∣ n := dvd_trans (dvd_mul_right p p) hp_sq
    have hpS : p ∈ S := Nat.mem_primeFactors.mpr ⟨hpp, hpn, hn0⟩
    have hp5 : 5 ≤ p := primeFactor_ge_five hodd h3 p hpS
    -- Radical `R = p · R'` with `R' = ∏_{q ∈ S.erase p} q`.
    have hRsplit : (∏ q ∈ S, q) = p * ∏ q ∈ S.erase p, q :=
      (Finset.mul_prod_erase S (fun q => q) hpS).symm
    -- `R' ∣ n` (it divides the radical, which divides `n`).
    have hR'_dvd_R : (∏ q ∈ S.erase p, q) ∣ ∏ q ∈ S, q :=
      Finset.prod_dvd_prod_of_subset _ _ (fun q => q) (Finset.erase_subset p S)
    have hR_dvd_n : (∏ q ∈ S, q) ∣ n := hS ▸ Nat.prod_primeFactors_dvd n
    have hR'_dvd_n : (∏ q ∈ S.erase p, q) ∣ n := dvd_trans hR'_dvd_R hR_dvd_n
    -- `p² = p * p` is coprime to `R'` (a product of primes `≠ p`).
    have hcop : Nat.Coprime (p * p) (∏ q ∈ S.erase p, q) := by
      refine Nat.Coprime.prod_right ?_
      intro q hq
      have hqS : q ∈ S := Finset.mem_of_mem_erase hq
      have hqp : q ≠ p := Finset.ne_of_mem_erase hq
      have hqprime : q.Prime := Nat.prime_of_mem_primeFactors (hS ▸ hqS)
      have hcoprime_pq : Nat.Coprime p q :=
        (Nat.coprime_primes hpp hqprime).mpr (fun h => hqp h.symm)
      exact hcoprime_pq.mul_left hcoprime_pq
    -- `(p*p) * R' ∣ n`, i.e. `p · radical ∣ n`.
    have hdvd : (p * p) * (∏ q ∈ S.erase p, q) ∣ n :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hp_sq hR'_dvd_n
    have hpR_dvd : p * (∏ q ∈ S, q) ∣ n := by
      rw [hRsplit, show p * (p * ∏ q ∈ S.erase p, q) = (p * p) * ∏ q ∈ S.erase p, q by ring]
      exact hdvd
    -- `n ≥ p · radical ≥ 5 · 37182145 = 185910725`.
    have hle : p * (∏ q ∈ S, q) ≤ n := Nat.le_of_dvd hnpos hpR_dvd
    have hRge : 37182145 ≤ ∏ q ∈ S, q := hS ▸ radical_ge hodd h3 habund
    have hmul : 5 * 37182145 ≤ p * (∏ q ∈ S, q) := Nat.mul_le_mul hp5 hRge
    omega

#check @odd_abundant_coprime_three_ge_185M

-- Axiom audit: only the foundational axioms (`propext`, `Classical.choice`, `Quot.sound`);
-- in particular NO `Lean.ofReduceBool` (no `native_decide`) and NO `sorryAx`.
#print axioms odd_abundant_coprime_three_ge_185M

end AbundantNumberOQ02OQ01GeneralBound
