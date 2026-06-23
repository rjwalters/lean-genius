/-
  Erdős Problem #1000 — Open Question OQ-03:
  Generalized totients with *different denominator conditions*.

  Source of the open question: src/data/proofs/erdos-1000 (parent),
  openQuestion: "Does the result extend to other generalized totients
  (e.g., with different denominator conditions)?"

  ## Context

  The parent entry (Proofs/Erdos1000Problem.lean) studies Cassels' generalized
  totient φ_A(k) = #{m ≤ n_k : reduced denominator of m/n_k is "unused"}.
  Its master structural theorem is the *exact divisor decomposition*

      φ_A(k) = Σ_{e | n_k, e admissible} φ(e),

  i.e. counting m by the reduced denominator e = n/gcd(m,n) of m/n turns the
  generalized totient into a *restricted Gauss sum* Σ_{e | n} φ(e) over an
  admissible set of divisors. The classical Gauss identity Σ_{e | n} φ(e) = n
  corresponds to the unrestricted count.

  ## This file

  We answer OQ-03 by evaluating these restricted Gauss sums *in closed form*
  for natural "denominator conditions", and by giving the corresponding
  closed-form counts of m. The headline results:

  * `sum_totient_filter_not_dvd` :
        Σ_{d | n, p ∤ d} φ(d) = ordCompl[p] n   (the p-free part of n)
  * `sum_totient_filter_odd` :
        Σ_{d | n, d odd} φ(d) = odd part of n      (the p = 2 case)
  * `sum_totient_filter_dvd` :
        Σ_{d | n, p ∣ d} φ(d) = n − ordCompl[p] n  (the complementary count)
  * `card_reducedDenom_not_dvd` / `card_reducedDenom_odd` :
        the *counting* form — #{m < n : the reduced denominator of m/n is
        coprime to p (resp. odd)} = ordCompl[p] n (resp. the odd part of n).

  These are genuinely different generalized totients from the parent's, sharing
  the same reduced-denominator engine but with a multiplicative denominator
  condition, and they all collapse to the classical Gauss identity Σ_{d|n} φ(d)=n
  when the condition is vacuous.

  No axioms, no native_decide.

  Tags: number-theory, totient-function, gauss-identity, divisor-sums,
  generalized-totient, erdos-1000
-/

import Mathlib

namespace Erdos1000OQ03

open Finset Nat

/- ## Part I: A generic "restricted Gauss sum" evaluator -/

/-- If the divisors of `n` satisfying a predicate `P` are *exactly* the divisors
    of some `m`, then the totient sum over them telescopes to `m` by Gauss'
    identity `Σ_{d | m} φ(d) = m`. This is the engine behind every closed form
    below: each denominator condition is shown to carve out `m.divisors` for an
    appropriate `m | n`. -/
theorem sum_totient_filter_eq_of_divisors_eq {n m : ℕ} (P : ℕ → Prop)
    [DecidablePred P] (h : n.divisors.filter P = m.divisors) :
    ∑ d ∈ n.divisors.filter P, φ d = m := by
  rw [h]; exact Nat.sum_totient m

/- ## Part II: The prime-free denominator condition -/

/-- For a prime `p` and `n ≠ 0`, a divisor `d | n` is coprime-to-`p`
    (equivalently `p ∤ d`) **iff** it divides the `p`-free part `ordCompl[p] n`.

    Forward: `d | n = p^a · ordCompl` and `gcd(d, p^a) = 1`, so `d | ordCompl`.
    Backward: `d | ordCompl` and `p ∤ ordCompl`, so `p ∤ d`. -/
theorem not_dvd_iff_dvd_ordCompl {n p d : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (hd : d ∣ n) : ¬ p ∣ d ↔ d ∣ ordCompl[p] n := by
  constructor
  · intro hpd
    -- `d` is coprime to `ordProj[p] n = p ^ (n.factorization p)`.
    have hcop : Nat.Coprime d (ordProj[p] n) :=
      (Nat.Coprime.pow_right _ ((hp.coprime_iff_not_dvd.mpr hpd).symm))
    -- `d ∣ ordProj * ordCompl = n`.
    have hdvd : d ∣ ordProj[p] n * ordCompl[p] n := by
      rwa [Nat.ordProj_mul_ordCompl_eq_self]
    exact hcop.dvd_of_dvd_mul_left hdvd
  · intro hdc hpd
    exact Nat.not_dvd_ordCompl hp hn (dvd_trans hpd hdc)

/-- **The `p`-free restricted Gauss sum.**
    `Σ_{d | n, p ∤ d} φ(d) = ordCompl[p] n`, the largest divisor of `n` coprime
    to `p`. This is a generalized totient with the denominator condition
    "denominator not divisible by `p`". -/
theorem sum_totient_filter_not_dvd {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors.filter (fun d => ¬ p ∣ d), φ d = ordCompl[p] n := by
  apply sum_totient_filter_eq_of_divisors_eq
  have hcongr : n.divisors.filter (fun d => ¬ p ∣ d)
      = n.divisors.filter (fun d => d ∣ ordCompl[p] n) := by
    apply Finset.filter_congr
    intro d hd
    simpa using not_dvd_iff_dvd_ordCompl hp hn (Nat.dvd_of_mem_divisors hd)
  rw [hcongr]
  exact Nat.divisors_filter_dvd_of_dvd hn (Nat.ordCompl_dvd n p)

/-- **The odd-denominator restricted Gauss sum** (the `p = 2` headline).
    `Σ_{d | n, d odd} φ(d) = ordCompl[2] n`, the odd part of `n`.
    Equivalently: the number of `m ∈ [1, n]` whose reduced fraction `m/n` has an
    odd denominator equals the odd part of `n`. -/
theorem sum_totient_filter_odd (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors.filter (fun d => Odd d), φ d = ordCompl[2] n := by
  have hcongr : n.divisors.filter (fun d => Odd d)
      = n.divisors.filter (fun d => ¬ (2 : ℕ) ∣ d) := by
    apply Finset.filter_congr
    intro d _
    simp [Nat.odd_iff, Nat.two_dvd_ne_zero]
  rw [hcongr]
  exact sum_totient_filter_not_dvd Nat.prime_two hn

/- ## Part III: The complementary (`p ∣ d`) condition -/

/-- **The `p`-divisible restricted Gauss sum.**
    `Σ_{d | n, p ∣ d} φ(d) = n − ordCompl[p] n`. Together with
    `sum_totient_filter_not_dvd` this partitions Gauss' identity
    `Σ_{d|n} φ(d) = n` according to divisibility by `p`. -/
theorem sum_totient_filter_dvd {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors.filter (fun d => p ∣ d), φ d = n - ordCompl[p] n := by
  have hsplit := Finset.sum_filter_add_sum_filter_not n.divisors
    (fun d => p ∣ d) φ
  rw [Nat.sum_totient] at hsplit
  -- The "¬ p ∣ d" part is the p-free sum = ordCompl[p] n.
  have hnot : ∑ d ∈ n.divisors.filter (fun d => ¬ p ∣ d), φ d = ordCompl[p] n :=
    sum_totient_filter_not_dvd hp hn
  rw [hnot] at hsplit
  omega

/- ## Part IV: Recovering the classical Gauss identity -/

/-- When the denominator condition is vacuous, the restricted sum is the full
    Gauss identity `Σ_{d | n} φ(d) = n`. (Sanity check that our generalized
    totients specialize correctly.) -/
theorem sum_totient_filter_true (n : ℕ) :
    ∑ d ∈ n.divisors.filter (fun _ => True), φ d = n := by
  simp [Nat.sum_totient]

/-- Every restricted generalized totient is bounded by `n` (it is a sub-sum of
    Gauss' identity). -/
theorem sum_totient_filter_le (n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ∑ d ∈ n.divisors.filter P, φ d ≤ n := by
  calc ∑ d ∈ n.divisors.filter P, φ d
      ≤ ∑ d ∈ n.divisors, φ d :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => Nat.zero_le _)
    _ = n := Nat.sum_totient n

/- ## Part V: The counting form (connection to the φ_A engine) -/

/-- The reduced denominator of the fraction `m / n`: writing `m/n` in lowest
    terms, the denominator is `n / gcd(n, m)`. This is the same quantity that
    drives the parent's generalized totient `φ_A`. -/
def reducedDenom (m n : ℕ) : ℕ := n / Nat.gcd n m

/-- For `g, e` both dividing `n > 0`: `n / g = e ↔ g = n / e`.
    (Both say `g · e = n`.) -/
private lemma div_eq_iff_eq_div {n g e : ℕ} (hg : g ∣ n) (he : e ∣ n)
    (hgpos : 0 < g) (hepos : 0 < e) : n / g = e ↔ g = n / e := by
  constructor
  · intro h
    have hmul : g * e = n := by rw [← h, Nat.mul_div_cancel' hg]
    rw [← hmul, Nat.mul_div_cancel _ hepos]
  · intro h
    have hmul : e * g = n := by rw [h]; exact Nat.mul_div_cancel' he
    rw [← hmul, Nat.mul_div_cancel _ hgpos]

/-- **Fiber count.** For a divisor `e | n` (with `n > 0`), exactly `φ(e)` of the
    integers `m ∈ {0,…,n−1}` have reduced denominator `e` in `m/n`. This is the
    bijection underlying `Nat.sum_totient`, expressed via the reduced
    denominator. -/
theorem card_reducedDenom_eq_totient {n e : ℕ} (hn : 0 < n) (he : e ∣ n) :
    #{m ∈ range n | reducedDenom m n = e} = φ e := by
  have hepos : 0 < e := pos_of_dvd_of_pos he hn
  have hd : (n / e) ∣ n := Nat.div_dvd_of_dvd he
  have hee : n / (n / e) = e := Nat.div_div_self he hn.ne'
  have hfib : #{m ∈ range n | n.gcd m = n / e} = φ e := by
    rw [← Nat.totient_div_of_dvd hd, hee]
  rw [← hfib]
  congr 1
  apply Finset.filter_congr
  intro m hm
  have hg : Nat.gcd n m ∣ n := Nat.gcd_dvd_left n m
  have hgpos : 0 < Nat.gcd n m := by
    rcases Nat.eq_zero_or_pos (Nat.gcd n m) with h | h
    · rw [Nat.gcd_eq_zero_iff] at h; omega
    · exact h
  simpa [reducedDenom] using div_eq_iff_eq_div hg he hgpos hepos

/-- **Master counting identity.** For any denominator condition `P`, the number
    of `m ∈ {0,…,n−1}` whose reduced denominator satisfies `P` equals the
    restricted Gauss sum `Σ_{e | n, P e} φ(e)`. This is the exact analogue of
    the parent's `phiA_decomposition`, with the admissibility condition `P`
    applied to the reduced denominator. -/
theorem card_reducedDenom_filter {n : ℕ} (hn : 0 < n) (P : ℕ → Prop)
    [DecidablePred P] :
    #{m ∈ range n | P (reducedDenom m n)}
      = ∑ e ∈ n.divisors.filter P, φ e := by
  -- Each `m` maps to its reduced denominator, a divisor of `n` satisfying `P`.
  have H : Set.MapsTo (fun m => reducedDenom m n)
      ({m ∈ range n | P (reducedDenom m n)} : Finset ℕ) (n.divisors.filter P) := by
    intro m hm
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hm
    simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors, reducedDenom]
    exact ⟨⟨Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n m), hn.ne'⟩, hm.2⟩
  rw [Finset.card_eq_sum_card_fiberwise H]
  apply Finset.sum_congr rfl
  intro e he
  simp only [Finset.mem_filter, Nat.mem_divisors] at he
  -- The fiber over `e` is exactly {m < n : reducedDenom m n = e}.
  have hfilt : {m ∈ range n | P (reducedDenom m n)}.filter
      (fun m => reducedDenom m n = e)
      = {m ∈ range n | reducedDenom m n = e} := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hmr, _⟩, hrd⟩; exact ⟨hmr, hrd⟩
    · rintro ⟨hmr, hrd⟩; exact ⟨⟨hmr, by rw [hrd]; exact he.2⟩, hrd⟩
  rw [hfilt, card_reducedDenom_eq_totient hn he.1.1]

/-- **Counting form of the `p`-free Gauss sum.**
    The number of `m ∈ {0,…,n−1}` whose reduced fraction `m/n` has denominator
    coprime to the prime `p` equals `ordCompl[p] n`, the `p`-free part of `n`. -/
theorem card_reducedDenom_not_dvd {n p : ℕ} (hp : p.Prime) (hn : 0 < n) :
    #{m ∈ range n | ¬ p ∣ reducedDenom m n} = ordCompl[p] n := by
  rw [card_reducedDenom_filter hn (fun e => ¬ p ∣ e),
      sum_totient_filter_not_dvd hp hn.ne']

/-- **Counting form of the odd Gauss sum** (`p = 2`).
    The number of `m ∈ {0,…,n−1}` whose reduced fraction `m/n` has an *odd*
    denominator equals the odd part of `n`. -/
theorem card_reducedDenom_odd {n : ℕ} (hn : 0 < n) :
    #{m ∈ range n | Odd (reducedDenom m n)} = ordCompl[2] n := by
  rw [card_reducedDenom_filter hn (fun e => Odd e), sum_totient_filter_odd n hn.ne']

end Erdos1000OQ03
