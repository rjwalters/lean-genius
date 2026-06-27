/-
Erdős Problem #493 — OQ-01: Exact image and representation count of
the product-minus-sum map  (a, b) ↦ a * b - (a + b)  over a, b ≥ 2.

Parent: `Proofs.Erdos493Problem` proves only the ⊇ direction of the image,
i.e. `n ≥ 0 ⟹ HasProdMinusSum2 n` (witness a = 2, b = n + 2).

This file supplies the two backbone results of OQ-01:

* `prodMinusSum2_iff_nonneg` — the **exact image** `{a*b-(a+b) : a,b ≥ 2} = {n ≥ 0}`.
  The converse `HasProdMinusSum2 n ⟹ n ≥ 0` is new (the parent leaves it open
  and even flags the imprecision in its Part III).

* `hasProdMinusSum2_iff_factor` — the **representation ↔ factorization bijection**
  coming from the central identity `a*b-(a+b) = (a-1)(b-1) - 1`:
        n = a*b-(a+b),  a,b ≥ 2   ⟺   n+1 = u*v,  u,v ≥ 1     (u = a-1, v = b-1).
  Every counting statement (ordered count = τ(n+1), unordered = ⌈τ(n+1)/2⌉,
  uniqueness ⟺ n+1 prime or 1) is a corollary of this equivalence; see the
  knowledge base `research/problems/erdos-493-oq-01/` and the verified certificate
  `verify_prodminussum.py`.

Reference: https://erdosproblems.com/493
-/

import Proofs.Erdos493Problem
import Mathlib.Tactic

open Finset

namespace Erdos493

/-- **(C1) Exact image.** The product-minus-sum representation `n = a*b-(a+b)`
with `a, b ≥ 2` exists **iff** `n ≥ 0`. The `←` direction is the parent theorem
`erdos_493_nonneg`; the `→` (converse) direction is new: from `a, b ≥ 2` we get
`a*b-(a+b) = (a-1)(b-1) - 1 ≥ 1·1 - 1 = 0`, so every negative integer is
unrepresentable. -/
theorem prodMinusSum2_iff_nonneg (n : ℤ) : HasProdMinusSum2 n ↔ n ≥ 0 := by
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ a - 2)
      (by linarith : (0 : ℤ) ≤ b - 2), ha, hb]
  · exact fun hn => erdos_493_nonneg n hn

/-- **Representation ↔ factorization bijection (central identity).**
`n = a*b-(a+b)` with `a, b ≥ 2` is equivalent to `n+1 = u*v` with `u, v ≥ 1`,
via the substitution `u = a-1, v = b-1`. This is the engine behind the
representation-counting results (ordered count `= τ(n+1)`, etc.). -/
theorem hasProdMinusSum2_iff_factor (n : ℤ) :
    HasProdMinusSum2 n ↔ ∃ u v : ℤ, 1 ≤ u ∧ 1 ≤ v ∧ u * v = n + 1 := by
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨a - 1, b - 1, by linarith, by linarith, by ring⟩
  · rintro ⟨u, v, hu, hv, huv⟩
    exact ⟨u + 1, v + 1, by linarith, by linarith, by linear_combination -huv⟩

/-- Every negative integer is unrepresentable (immediate corollary of C1). -/
theorem not_hasProdMinusSum2_of_neg {n : ℤ} (hn : n < 0) : ¬ HasProdMinusSum2 n := by
  rw [prodMinusSum2_iff_nonneg]
  exact not_le.mpr hn

/-- **(C3) Diagonal (square) representation.** A representation with `a = b`
(equivalently `n = a*a - (a+a) = a² - 2a`) exists **iff** `n + 1` is a perfect
square. From the central identity `a² - 2a = (a-1)² - 1`, so `n + 1 = (a-1)²`.

This is the structural reason a *prime square* `n+1 = p²` has the extra unordered
representation `{p, p}` beyond `{1, p²}`: the perfect-square values of `n+1` are
exactly those whose factor list contains the diagonal `u = v = √(n+1)`. -/
theorem hasSquareRep_iff (n : ℤ) :
    (∃ a : ℤ, a ≥ 2 ∧ n = a * a - (a + a)) ↔ ∃ u : ℤ, 1 ≤ u ∧ n + 1 = u * u := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a - 1, by linarith, by ring⟩
  · rintro ⟨u, hu, huv⟩
    exact ⟨u + 1, by linarith, by linear_combination huv⟩

/-- **(C4) Nontrivial representation ↔ nontrivial factorization.** A representation
with *both* `a, b ≥ 3` exists **iff** `n + 1` factors as `u * v` with both
`u, v ≥ 2` (i.e. `n + 1` is composite). The "trivial" representations `(2, n+2)`
correspond exactly to the factorizations with a unit factor `u = 1`.

Hence the *unordered* representation of `n` is unique precisely when `n + 1` admits
no such nontrivial factorization — i.e. `n = 0` (`n+1 = 1`) or `n + 1` is prime. -/
theorem hasNontrivialRep_iff_factor (n : ℤ) :
    (∃ a b : ℤ, a ≥ 3 ∧ b ≥ 3 ∧ n = a * b - (a + b)) ↔
      ∃ u v : ℤ, 2 ≤ u ∧ 2 ≤ v ∧ u * v = n + 1 := by
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨a - 1, b - 1, by linarith, by linarith, by ring⟩
  · rintro ⟨u, v, hu, hv, huv⟩
    exact ⟨u + 1, v + 1, by linarith, by linarith, by linear_combination -huv⟩

/-- The `Finset` of ordered representations `(a, b)`, `a, b ≥ 2`, of a natural
number `n` as `n = a*b - (a+b)`. The defining condition is written multiplicatively
(`a*b = a + b + n`) to avoid `ℕ` subtraction; the bounds `2 ≤ a, b ≤ n+2` are the
sharp range coming from the central identity `(a-1)(b-1) = n+1`. -/
def repsFinset (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 2 (n + 2)) ×ˢ (Finset.Icc 2 (n + 2))).filter
    (fun p => p.1 * p.2 = p.1 + p.2 + n)

@[simp] theorem mem_repsFinset {n a b : ℕ} :
    (a, b) ∈ repsFinset n ↔
      (2 ≤ a ∧ a ≤ n + 2) ∧ (2 ≤ b ∧ b ≤ n + 2) ∧ a * b = a + b + n := by
  simp [repsFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, and_assoc]

/-- **(C2) Ordered representation count = τ(n+1).** The number of ordered pairs
`(a, b)` with `a, b ≥ 2` and `n = a*b - (a+b)` equals the number of divisors of
`n + 1`. This is the quantitative form of the representation↔factorization
bijection `hasProdMinusSum2_iff_factor`: the explicit bijection sends a divisor
`u ∣ n+1` to the representation `(u+1, (n+1)/u + 1)`. Every counting corollary
(unordered count `= ⌈τ(n+1)/2⌉`, uniqueness ⟺ `n+1 ∈ {1} ∪ primes`) follows from
this together with `hasSquareRep_iff` (C3) and `hasNontrivialRep_iff_factor` (C4). -/
theorem reps_card_eq_tau (n : ℕ) :
    (repsFinset n).card = (n + 1).divisors.card := by
  symm
  apply Finset.card_bij (fun u _ => (u + 1, (n + 1) / u + 1))
  · intro u hu
    have hu_pos : 0 < u := Nat.pos_of_mem_divisors hu
    have hdvd : u ∣ (n + 1) := (Nat.mem_divisors.mp hu).1
    have hule : u ≤ n + 1 := Nat.le_of_dvd (by omega) hdvd
    have huw : u * ((n + 1) / u) = n + 1 := Nat.mul_div_cancel' hdvd
    have hw1 : 1 ≤ (n + 1) / u := (Nat.one_le_div_iff hu_pos).mpr hule
    have hwle : (n + 1) / u ≤ n + 1 := Nat.div_le_self _ _
    simp only [mem_repsFinset]
    refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_⟩
    have key : (u + 1) * ((n + 1) / u + 1)
             = u * ((n + 1) / u) + (u + (n + 1) / u + 1) := by ring
    rw [key, huw]; ring
  · intro u₁ _ u₂ _ h
    simp only [Prod.mk.injEq] at h; omega
  · rintro ⟨a, b⟩ hp
    simp only [mem_repsFinset] at hp
    obtain ⟨⟨ha2, _⟩, ⟨hb2, _⟩, hprod⟩ := hp
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ha2
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hb2
    have hst : (s + 1) * (r + 1) = n + 1 := by
      have key : (2 + s) * (2 + r) = (s + 1) * (r + 1) + (s + r + 3) := by ring
      rw [key] at hprod; linarith
    refine ⟨s + 1, Nat.mem_divisors.mpr ⟨⟨r + 1, hst.symm⟩, by omega⟩, ?_⟩
    have hdiv : (n + 1) / (s + 1) = r + 1 := by
      rw [← hst]; exact Nat.mul_div_cancel_left _ (by omega)
    simp only [Prod.mk.injEq, hdiv]; omega

/-- A natural number has **exactly two divisors iff it is prime** — the two
divisors being `1` and the number itself. This is the divisor-count form of
primality; it lets us read primality directly off the representation count. -/
theorem card_divisors_eq_two_iff_prime {N : ℕ} : N.divisors.card = 2 ↔ N.Prime := by
  constructor
  · intro h
    have hN0 : N ≠ 0 := by rintro rfl; simp [Nat.divisors_zero] at h
    have hN1 : N ≠ 1 := by rintro rfl; simp [Nat.divisors_one] at h
    have h2 : 2 ≤ N := by omega
    have hsub : ({1, N} : Finset ℕ) ⊆ N.divisors := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Nat.one_mem_divisors.mpr hN0
      · exact Nat.mem_divisors_self _ hN0
    have hpair : ({1, N} : Finset ℕ).card = 2 := Finset.card_pair (Ne.symm hN1)
    have heq : N.divisors = {1, N} :=
      (Finset.eq_of_subset_of_card_le hsub (by rw [hpair]; omega)).symm
    rw [Nat.prime_def]
    refine ⟨h2, fun m hm => ?_⟩
    have hmem : m ∈ N.divisors := Nat.mem_divisors.mpr ⟨hm, hN0⟩
    rw [heq, Finset.mem_insert, Finset.mem_singleton] at hmem
    exact hmem
  · intro hp
    rw [Nat.Prime.divisors hp, Finset.card_pair hp.one_lt.ne]

/-- **(C5) Primality capstone.** There are **exactly two** ordered
representations `n = a*b - (a+b)` (with `a, b ≥ 2`) **iff** `n + 1` is prime.
For prime `n + 1 = p` the two representations are `(2, n+2)` and `(n+2, 2)` — the
single *unordered* representation `{2, n+2}` counted in both orders — so the
representation is unordered-unique exactly when `n + 1` is prime. This is the
quantitative reading of `hasNontrivialRep_iff_factor` (C4): no representation with
both parts `≥ 3` exists iff `n + 1` has no nontrivial factorization. The proof is
immediate from `reps_card_eq_tau` (C2): the ordered count is `τ(n+1)`, which equals
`2` iff `n + 1` is prime. -/
theorem reps_card_eq_two_iff_prime (n : ℕ) :
    (repsFinset n).card = 2 ↔ (n + 1).Prime := by
  rw [reps_card_eq_tau, card_divisors_eq_two_iff_prime]

/-- The representation is *ordered-unique* (exactly one ordered pair) **iff**
`n = 0`, the lone representation being `(2, 2)` since `n + 1 = 1` has the single
divisor `1`. Together with `reps_card_eq_two_iff_prime`, the unordered
representation of `n` is unique exactly when `n = 0` or `n + 1` is prime. -/
theorem reps_card_eq_one_iff (n : ℕ) :
    (repsFinset n).card = 1 ↔ n = 0 := by
  rw [reps_card_eq_tau]
  constructor
  · intro h
    by_contra hne
    have hsub : ({1, n + 1} : Finset ℕ) ⊆ (n + 1).divisors := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Nat.one_mem_divisors.mpr (by omega)
      · exact Nat.mem_divisors_self _ (by omega)
    have hpair : ({1, n + 1} : Finset ℕ).card = 2 := Finset.card_pair (by omega)
    have hge : 2 ≤ (n + 1).divisors.card := hpair ▸ Finset.card_le_card hsub
    omega
  · rintro rfl
    simp [Nat.divisors_one]

end Erdos493
