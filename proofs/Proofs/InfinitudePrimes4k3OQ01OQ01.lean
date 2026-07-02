/-
# Infinitely Many Primes ≡ 7 (mod 8) — An Elementary, L-function-Free Euclid Argument

This file answers open question `infinitude-primes-4k3-oq-01-oq-01`:

> Prove `Set.Infinite {p prime | p ≡ 7 [MOD 8]}` by a purely elementary
> Euclidean argument, removing the dependence on Dirichlet's theorem for
> this residue class.

The whole proof rests on a single classical quadratic-residue fact, already in
Mathlib: for an odd prime `p`, `2` is a square mod `p` **iff** `p ≡ ±1 (mod 8)`
(`ZMod.exists_sq_eq_two_iff`). Everything else is elementary arithmetic and a
Euclid-style construction, with no L-functions and no appeal to Dirichlet's
theorem.

## The mechanism

For any *odd* `a`, put `M = a² − 2`.

* `M ≡ 7 (mod 8)`: an odd square is `≡ 1 (mod 8)`, so `a² − 2 ≡ −1 ≡ 7`.
* Every prime `p ∣ M` is odd (as `M` is odd) and makes `2 = a²` a square mod `p`,
  hence `p ≡ 1` or `7 (mod 8)`.
* A product of numbers all `≡ 1 (mod 8)` is again `≡ 1 (mod 8)`. Since `M ≡ 7`,
  **not** every prime factor can be `≡ 1`, so `M` has a prime factor `≡ 7 (mod 8)`.

Feeding a Euclid construction into this — take `a = 3 · ∏(known primes ≡ 7)` — the
resulting new prime `≡ 7 (mod 8)` cannot already be on the list, so the list of
such primes is never complete.
-/
import Mathlib

open scoped BigOperators

namespace InfinitudePrimes4k3OQ01OQ01

/-- An odd natural number has square `≡ 1 (mod 8)`. This is the arithmetic reason
`a² − 2 ≡ 7 (mod 8)` for odd `a`. -/
theorem odd_sq_mod_eight {a : ℕ} (ha : Odd a) : a ^ 2 % 8 = 1 := by
  obtain ⟨k, rfl⟩ := ha
  obtain ⟨t, ht⟩ := Nat.even_mul_succ_self k
  have key : (2 * k + 1) ^ 2 = 8 * t + 1 := by
    have e : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    rw [e, ht]; ring
  rw [key]; omega

/-- **Quadratic-residue step.** If an odd prime `p` divides `a² − 2` (with
`a² ≥ 2`), then `2` is a square mod `p`, so `p ≡ 1` or `7 (mod 8)`.

This is the only place quadratic reciprocity enters, through Mathlib's
`ZMod.exists_sq_eq_two_iff`. -/
theorem prime_factor_two_qr {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ a ^ 2 - 2) (ha2 : 2 ≤ a ^ 2) : p % 8 = 1 ∨ p % 8 = 7 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcast : ((a ^ 2 - 2 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  rw [Nat.cast_sub ha2] at hcast
  push_cast at hcast
  have h2 : (a : ZMod p) ^ 2 = 2 := by
    have := sub_eq_zero.mp hcast
    linear_combination this
  refine (ZMod.exists_sq_eq_two_iff hp2).mp ⟨(a : ZMod p), ?_⟩
  rw [← h2]; ring

/-- **The core lemma.** For odd `a ≥ 3`, the number `a² − 2` has a prime factor
`≡ 7 (mod 8)`.

The prime factors are all `≡ 1` or `7 (mod 8)`; were they *all* `≡ 1`, the product
`a² − 2` would be `≡ 1 (mod 8)`, contradicting `a² − 2 ≡ 7 (mod 8)`. -/
theorem exists_prime_factor_seven_mod_eight {a : ℕ} (ha : Odd a) (ha3 : 3 ≤ a) :
    ∃ p, p.Prime ∧ p ∣ a ^ 2 - 2 ∧ p % 8 = 7 := by
  set M := a ^ 2 - 2 with hM
  have ha2 : 2 ≤ a ^ 2 := by nlinarith
  have hM2 : 2 ≤ M := by
    have : 9 ≤ a ^ 2 := by nlinarith
    omega
  have hM7 : M % 8 = 7 := by
    have h1 : a ^ 2 % 8 = 1 := odd_sq_mod_eight ha
    omega
  by_contra hcon
  push_neg at hcon
  -- Every prime factor of `M` is `≡ 1 (mod 8)`, hence casts to `1` in `ZMod 8`.
  have hall : ∀ x ∈ M.primeFactorsList.map (Nat.cast : ℕ → ZMod 8), x = 1 := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨p, hpmem, rfl⟩ := hx
    have hpp : p.Prime := Nat.prime_of_mem_primeFactorsList hpmem
    have hpd : p ∣ M := Nat.dvd_of_mem_primeFactorsList hpmem
    have hp2 : p ≠ 2 := by
      rintro rfl
      omega
    have hcases := prime_factor_two_qr hpp hp2 hpd ha2
    have hne7 : p % 8 ≠ 7 := hcon p hpp hpd
    have hp1 : p % 8 = 1 := by tauto
    have : (p : ZMod 8) = ((p % 8 : ℕ) : ZMod 8) := (ZMod.natCast_mod p 8).symm
    rw [hp1] at this
    simpa using this
  -- Therefore `M ≡ 1 (mod 8)`.
  have hprod : (M : ZMod 8) = 1 := by
    conv_lhs => rw [← Nat.prod_primeFactorsList (n := M) (by omega)]
    rw [Nat.cast_list_prod]
    exact List.prod_eq_one hall
  -- But `M ≡ 7 (mod 8)`.
  have hM7cast : (M : ZMod 8) = 7 := by
    have : (M : ZMod 8) = ((M % 8 : ℕ) : ZMod 8) := (ZMod.natCast_mod M 8).symm
    rw [hM7] at this
    simpa using this
  rw [hM7cast] at hprod
  exact absurd hprod (by decide)

/-- **Main theorem.** There are infinitely many primes `≡ 7 (mod 8)`.

Proof by Euclid: were the set finite, take `a = 3 · ∏(all such primes)`. Then `a`
is odd and `≥ 3`, so `a² − 2` has a prime factor `p ≡ 7 (mod 8)` by
`exists_prime_factor_seven_mod_eight`. That `p` is on the list, hence divides `a`,
hence divides `2` — impossible for an odd prime. -/
theorem primes_seven_mod_eight_infinite :
    {p : ℕ | p.Prime ∧ p % 8 = 7}.Infinite := by
  by_contra hcon
  rw [Set.not_infinite] at hcon
  set S := hcon.toFinset with hSdef
  have hmemS : ∀ q, q ∈ S ↔ q.Prime ∧ q % 8 = 7 := by
    intro q; rw [Set.Finite.mem_toFinset]; rfl
  set a := 3 * ∏ q ∈ S, q with hadef
  -- Each factor is odd, so `a` is odd.
  have ha_odd : Odd a := by
    rw [Nat.odd_iff]
    by_contra h
    have hdvd : (2 : ℕ) ∣ a := Nat.dvd_of_mod_eq_zero (by omega)
    rw [hadef] at hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hdvd with h3 | hprod
    · norm_num at h3
    · obtain ⟨q, hqS, hq2⟩ := (Prime.dvd_finset_prod_iff Nat.prime_two.prime _).mp hprod
      have hq := (hmemS q).mp hqS
      have hqeq : q = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq.1).mp hq2).symm
      have h7 := hq.2
      omega
  have ha3 : 3 ≤ a := by
    have hp1 : 1 ≤ ∏ q ∈ S, q :=
      Finset.one_le_prod' (fun q hq => ((hmemS q).mp hq).1.one_lt.le)
    omega
  obtain ⟨p, hpp, hpd, hp7⟩ := exists_prime_factor_seven_mod_eight ha_odd ha3
  -- `p` is on the list, so `p ∣ a`.
  have hpS : p ∈ S := (hmemS p).mpr ⟨hpp, hp7⟩
  have hp_dvd_a : p ∣ a := by
    rw [hadef]; exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hpS) 3
  have ha2 : 2 ≤ a ^ 2 := by nlinarith [ha3]
  -- `p ∣ a²` and `p ∣ a² − 2`, so `p ∣ 2`, forcing `p = 2`, contradicting `p ≡ 7`.
  have hp_dvd_sq : p ∣ a ^ 2 := Dvd.dvd.pow hp_dvd_a (by norm_num)
  have hp_dvd_two : p ∣ 2 := by
    have := Nat.dvd_sub hp_dvd_sq hpd
    rwa [Nat.sub_sub_self ha2] at this
  have : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp hp_dvd_two
  omega

/-- Restatement: there is no largest prime `≡ 7 (mod 8)`. -/
theorem no_largest_prime_seven_mod_eight :
    ∀ n, ∃ p, p.Prime ∧ p % 8 = 7 ∧ n < p := by
  intro n
  have h := primes_seven_mod_eight_infinite
  obtain ⟨p, hp, hlt⟩ := (Set.Infinite.exists_gt h) n
  exact ⟨p, hp.1, hp.2, hlt⟩

end InfinitudePrimes4k3OQ01OQ01
