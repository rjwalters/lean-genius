/-
  **Forced prime-power exponents — and the closure — of the open `ω = 7` residual case.**

  Companion files reduce exact minimality of "the smallest odd abundant number not
  divisible by 3 is `5391411025 = 5²·7·11·13·17·19·23·29`" to a single residual shape:
  a counterexample below `5391411025` must be **non-squarefree with exactly seven
  distinct prime factors** (`GeneralBound.odd_abundant_coprime_three_below_min_structure`),
  and its prime support is forced to be one of four explicit seven-element sets
  `{5,7,11,13,17,19,q}`, `q ∈ {23,29,31,37}` (`OmegaSevenPrimes`).  What remained open was
  bounding the *exponents* on those four supports.

  This file closes that gap.  The engine is a refined Euler abundancy bound that keeps the
  **exact** local factor `σ(p^{vₚ})/p^{vₚ}` of a *set* of chosen primes (`refined_euler_set`)
  while bounding every other prime by the limit `p/(p−1)`.

  * Keeping one prime exact forces the two smallest primes to carry exponent ≥ 2:
        `n odd, coprime to 3, abundant, ω(n) = 7  ⟹  5² ∣ n  ∧  7² ∣ n`.
  * Keeping the three primes `{5,7,11}` exact at the minimal corner `(v₅,v₇,v₁₁)=(2,2,1)`
    forces `∏_{p∣n} p/(p−1) > 1037575/508896`, contradicting the sharp per-support weight
    bound `< 1037575/508896`.  Hence the minimal corner is impossible:
        `v₅ ≥ 3  ∨  v₇ ≥ 3  ∨  v₁₁ ≥ 2`.
    Each disjunct multiplies the floor `5²·7²·11·13·17·19·q` by at least `5`, and that floor
    times `5` already exceeds `5391411025` on every admissible support.  Therefore

        `n odd, coprime to 3, abundant, ω(n) = 7  ⟹  n ≥ 5391411025`.

  Combined with the `ω ≥ 8` and squarefree shapes (discharged in `GeneralBound`), this gives
  the **unconditional** exact lower bound for every odd abundant number coprime to 3:

        `odd_abundant_coprime_three_ge_witness : Odd n → ¬ 3∣n → Abundant n → 5391411025 ≤ n`.

  Everything is axiom-free (only `propext`/`Classical.choice`/`Quot.sound`; no
  `Lean.ofReduceBool`, no `native_decide`, no `sorry`).
-/
import Mathlib
import Proofs.AbundantNumberOQ02OQ01OmegaSevenPrimes

namespace AbundantNumberOQ02OQ01SevenPrimeExponents

open Nat ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma
open AbundantNumberOQ02OQ01Minimality
open AbundantNumberOQ02OQ01Unconditional
open AbundantNumberOQ02OQ01GeneralBound
open AbundantNumberOQ02OQ01OmegaSevenPrimes

/-- The exact local Euler factor `σ(p^{vₚ(n)})/p^{vₚ(n)} = (∑_{i≤vₚ(n)} pⁱ)/p^{vₚ(n)}` of the
prime `p` in `n`, as a rational. -/
noncomputable def Ffac (n p : ℕ) : ℚ :=
  (∑ i ∈ Finset.range (n.factorization p + 1), (p : ℚ) ^ i) / (p : ℚ) ^ (n.factorization p)

/-- The exact local factor is always nonnegative. -/
lemma Ffac_nonneg (n p : ℕ) : 0 ≤ Ffac n p := by
  rw [Ffac]
  apply div_nonneg
  · exact Finset.sum_nonneg (fun i _ => by positivity)
  · positivity

/-- The exact local factor never exceeds the limit weight `f p = p/(p−1)`. -/
lemma factor_le_f {n p : ℕ} (hp : p ∈ n.primeFactors) : Ffac n p ≤ f p := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have h2 : 2 ≤ p := hpp.two_le
  have hpQ2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast h2
  have hden : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  have hpvpos : (0 : ℚ) < (p : ℚ) ^ n.factorization p := by positivity
  have hgeo := geomSum_mul_pred_lt h2 (n.factorization p)
  have hsum_cast :
      ((∑ i ∈ Finset.range (n.factorization p + 1), p ^ i : ℕ) : ℚ)
        = ∑ i ∈ Finset.range (n.factorization p + 1), (p : ℚ) ^ i := by
    push_cast; rfl
  have hcastlt :
      (∑ i ∈ Finset.range (n.factorization p + 1), (p : ℚ) ^ i) * ((p : ℚ) - 1)
        ≤ (p : ℚ) ^ (n.factorization p + 1) := by
    have hc :
        (((∑ i ∈ Finset.range (n.factorization p + 1), p ^ i) * (p - 1) : ℕ) : ℚ)
          ≤ ((p ^ (n.factorization p + 1) : ℕ) : ℚ) := by exact_mod_cast le_of_lt hgeo
    rwa [Nat.cast_mul, Nat.cast_pow, hsum_cast, Nat.cast_sub (by omega : 1 ≤ p),
      Nat.cast_one] at hc
  simp only [Ffac, f]
  rw [div_le_div_iff₀ hpvpos hden]
  calc
    (∑ i ∈ Finset.range (n.factorization p + 1), (p : ℚ) ^ i) * ((p : ℚ) - 1)
        ≤ (p : ℚ) ^ (n.factorization p + 1) := hcastlt
    _ = (p : ℚ) * (p : ℚ) ^ n.factorization p := by rw [pow_succ]; ring

/-- The abundancy index exceeds `2`, expressed as the product of the exact local Euler
factors over the prime support. -/
lemma two_lt_prod_Ffac {n : ℕ} (habund : Nat.Abundant n) :
    (2 : ℚ) < ∏ p ∈ n.primeFactors, Ffac n p := by
  set S := n.primeFactors with hSdef
  have hn' : n < ∑ i ∈ n.properDivisors, i := habund
  have hn1 : 1 < n := by
    rcases n with _ | _ | n
    · simp [Nat.properDivisors_zero] at hn'
    · simp [Nat.properDivisors_one] at hn'
    · omega
  have hn0 : n ≠ 0 := by omega
  have hnposQ : (0 : ℚ) < (n : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hσ : 2 * n < σ 1 n := by
    rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]; omega
  have hsigN : σ 1 n = ∏ p ∈ S, ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i := by
    rw [hSdef, sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn0]; simp only [mul_one]
  have hpow : ∏ p ∈ S, p ^ n.factorization p = n := by
    rw [hSdef]; exact Nat.factorization_prod_pow_eq_self hn0
  have hsigQ : (σ 1 n : ℚ) = ∏ p ∈ S, ∑ i ∈ Finset.range (n.factorization p + 1), (p : ℚ) ^ i := by
    rw [hsigN, Nat.cast_prod]
    refine Finset.prod_congr rfl (fun p _ => ?_)
    rw [Nat.cast_sum]; exact Finset.sum_congr rfl (fun i _ => by rw [Nat.cast_pow])
  have hnQ : (n : ℚ) = ∏ p ∈ S, (p : ℚ) ^ n.factorization p := by
    have hcast : ((∏ p ∈ S, p ^ n.factorization p : ℕ) : ℚ)
        = ∏ p ∈ S, (p : ℚ) ^ n.factorization p := by push_cast; rfl
    rw [← hcast, hpow]
  have hSf : (σ 1 n : ℚ) / (n : ℚ) = ∏ p ∈ S, Ffac n p := by
    simp only [Ffac]
    rw [hsigQ, hnQ, ← Finset.prod_div_distrib]
  have h2lt : (2 : ℚ) < (σ 1 n : ℚ) / (n : ℚ) := by
    rw [lt_div_iff₀ hnposQ]
    have hcast : (2 : ℚ) * (n : ℚ) = ((2 * n : ℕ) : ℚ) := by push_cast; ring
    rw [hcast]; exact_mod_cast hσ
  rwa [hSf] at h2lt

/-- **Refined Euler bound (one prime kept exact).**  For an abundant `n` and a prime
`p₀ ∣ n`, isolating the exact local factor at `p₀` while bounding all other primes by the
limit weight gives `2 · (p₀/(p₀−1))  <  Ffac n p₀ · ∏_{p∣n} p/(p−1)`. -/
lemma refined_euler {n : ℕ} (habund : Nat.Abundant n) {p0 : ℕ} (hp0 : p0 ∈ n.primeFactors) :
    2 * f p0 < Ffac n p0 * ∏ p ∈ n.primeFactors, f p := by
  set S := n.primeFactors with hSdef
  have h2lt : (2 : ℚ) < ∏ p ∈ S, Ffac n p := two_lt_prod_Ffac habund
  have hsplitF : ∏ p ∈ S, Ffac n p = Ffac n p0 * ∏ p ∈ S.erase p0, Ffac n p :=
    (Finset.mul_prod_erase S (Ffac n) hp0).symm
  have hsplitf : ∏ p ∈ S, f p = f p0 * ∏ p ∈ S.erase p0, f p :=
    (Finset.mul_prod_erase S f hp0).symm
  have hle : ∏ p ∈ S.erase p0, Ffac n p ≤ ∏ p ∈ S.erase p0, f p :=
    Finset.prod_le_prod (fun p _ => Ffac_nonneg n p)
      (fun p hp => factor_le_f (Finset.mem_of_mem_erase hp))
  have hFp0nn : 0 ≤ Ffac n p0 := Ffac_nonneg n p0
  have step : (2 : ℚ) < Ffac n p0 * ∏ p ∈ S.erase p0, f p := by
    rw [hsplitF] at h2lt
    exact lt_of_lt_of_le h2lt (mul_le_mul_of_nonneg_left hle hFp0nn)
  have hp0prime : p0.Prime := Nat.prime_of_mem_primeFactors hp0
  have hfp0pos : 0 < f p0 := f_pos hp0prime.two_le
  have hmul : 2 * f p0 < (Ffac n p0 * ∏ p ∈ S.erase p0, f p) * f p0 :=
    mul_lt_mul_of_pos_right step hfp0pos
  have hrw : (Ffac n p0 * ∏ p ∈ S.erase p0, f p) * f p0 = Ffac n p0 * ∏ p ∈ S, f p := by
    rw [hsplitf]; ring
  rwa [hrw] at hmul

/-- **Refined Euler bound keeping a whole set of primes exact.**  For abundant `n` and any
`T ⊆ n.primeFactors`, isolating the exact local factors at every prime of `T` while bounding
the remaining primes by the limit weight gives
`2 · ∏_{p∈T} f p  <  (∏_{p∈T} Ffac n p) · ∏_{p∣n} f p`. -/
lemma refined_euler_set {n : ℕ} (habund : Nat.Abundant n) {T : Finset ℕ}
    (hT : T ⊆ n.primeFactors) :
    2 * ∏ p ∈ T, f p < (∏ p ∈ T, Ffac n p) * ∏ p ∈ n.primeFactors, f p := by
  have hcore : (2 : ℚ) < ∏ p ∈ n.primeFactors, Ffac n p := two_lt_prod_Ffac habund
  have hFsplit : (∏ p ∈ n.primeFactors \ T, Ffac n p) * ∏ p ∈ T, Ffac n p
      = ∏ p ∈ n.primeFactors, Ffac n p := Finset.prod_sdiff hT
  have hfsplit : (∏ p ∈ n.primeFactors \ T, f p) * ∏ p ∈ T, f p
      = ∏ p ∈ n.primeFactors, f p := Finset.prod_sdiff hT
  have hle : ∏ p ∈ n.primeFactors \ T, Ffac n p ≤ ∏ p ∈ n.primeFactors \ T, f p :=
    Finset.prod_le_prod (fun p _ => Ffac_nonneg n p)
      (fun p hp => factor_le_f (Finset.mem_sdiff.mp hp).1)
  have hTFnn : 0 ≤ ∏ p ∈ T, Ffac n p := Finset.prod_nonneg (fun p _ => Ffac_nonneg n p)
  have hTfpos : 0 < ∏ p ∈ T, f p :=
    Finset.prod_pos (fun p hp => f_pos (Nat.prime_of_mem_primeFactors (hT hp)).two_le)
  have h1 : (∏ p ∈ n.primeFactors \ T, Ffac n p) * ∏ p ∈ T, Ffac n p
      ≤ (∏ p ∈ n.primeFactors \ T, f p) * ∏ p ∈ T, Ffac n p :=
    mul_le_mul_of_nonneg_right hle hTFnn
  rw [hFsplit] at h1
  have step : (2 : ℚ) < (∏ p ∈ T, Ffac n p) * ∏ p ∈ n.primeFactors \ T, f p := by
    have h2 := lt_of_lt_of_le hcore h1
    rwa [mul_comm] at h2
  have hmul : 2 * ∏ p ∈ T, f p
      < ((∏ p ∈ T, Ffac n p) * ∏ p ∈ n.primeFactors \ T, f p) * ∏ p ∈ T, f p :=
    mul_lt_mul_of_pos_right step hTfpos
  have hrw : ((∏ p ∈ T, Ffac n p) * ∏ p ∈ n.primeFactors \ T, f p) * ∏ p ∈ T, f p
      = (∏ p ∈ T, Ffac n p) * ∏ p ∈ n.primeFactors, f p := by
    rw [← hfsplit]; ring
  rwa [hrw] at hmul

/-- The limit weight product `∏_{p∣n} p/(p−1)` over any admissible `ω = 7` support is
`< 49/24`.  (Largest at `q = 23`, where it equals `676039/331776 < 49/24`.) -/
lemma prod_primeFactors_f_lt {n : ℕ} (hodd : Odd n) (h3 : ¬ (3 ∣ n)) (habund : Nat.Abundant n)
    (hcard7 : n.primeFactors.card = 7) :
    ∏ p ∈ n.primeFactors, f p < 49 / 24 := by
  rcases omega_seven_prime_support hodd h3 habund hcard7 with h | h | h | h <;>
    rw [h, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton] <;>
    · simp only [f]; norm_num

/-- **Sharper weight bound.**  `∏_{p∣n} p/(p−1) < 1037575/508896` over any admissible `ω = 7`
support.  (Largest at `q = 23`, where it equals `676039/331776 < 1037575/508896`.)  This is
the cutoff produced by the three-prime refined Euler bound at the minimal corner. -/
lemma prod_primeFactors_f_lt_sharp {n : ℕ} (hodd : Odd n) (h3 : ¬ (3 ∣ n))
    (habund : Nat.Abundant n) (hcard7 : n.primeFactors.card = 7) :
    ∏ p ∈ n.primeFactors, f p < 1037575 / 508896 := by
  rcases omega_seven_prime_support hodd h3 habund hcard7 with h | h | h | h <;>
    rw [h, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton] <;>
    · simp only [f]; norm_num

/-- **`5² ∣ n`.**  An odd abundant number coprime to 3 with exactly seven distinct prime
factors is divisible by `25`: the smallest prime must carry exponent at least two. -/
theorem five_sq_dvd {n : ℕ} (hodd : Odd n) (h3 : ¬ (3 ∣ n)) (habund : Nat.Abundant n)
    (hcard7 : n.primeFactors.card = 7) : 25 ∣ n := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hcard7
  have h5mem : (5 : ℕ) ∈ n.primeFactors := by
    rcases omega_seven_prime_support hodd h3 habund hcard7 with h | h | h | h <;> rw [h] <;> decide
  have hfact : 2 ≤ n.factorization 5 := by
    by_contra hlt
    push_neg at hlt
    have hge1 : 1 ≤ n.factorization 5 := by
      have hne : n.factorization 5 ≠ 0 := by
        rw [← Nat.support_factorization] at h5mem
        exact Finsupp.mem_support_iff.mp h5mem
      omega
    have hv : n.factorization 5 = 1 := by omega
    have hre := refined_euler habund h5mem
    have hf5 : f 5 = 5 / 4 := by simp only [f]; norm_num
    have hF5 : Ffac n 5 = 6 / 5 := by
      simp only [Ffac, hv]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hf5, hF5] at hre
    have hb := prod_primeFactors_f_lt hodd h3 habund hcard7
    linarith
  have h52 : (5 : ℕ) ^ 2 ∣ n := (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hn0).mpr hfact
  have : (25 : ℕ) = 5 ^ 2 := by norm_num
  rw [this]; exact h52

/-- **`7² ∣ n`.**  An odd abundant number coprime to 3 with exactly seven distinct prime
factors is divisible by `49`: the second-smallest prime must also carry exponent at least
two.  (The `49/24` weight cutoff is exactly tight here at `q = 23`.) -/
theorem seven_sq_dvd {n : ℕ} (hodd : Odd n) (h3 : ¬ (3 ∣ n)) (habund : Nat.Abundant n)
    (hcard7 : n.primeFactors.card = 7) : 49 ∣ n := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hcard7
  have h7mem : (7 : ℕ) ∈ n.primeFactors := by
    rcases omega_seven_prime_support hodd h3 habund hcard7 with h | h | h | h <;> rw [h] <;> decide
  have hfact : 2 ≤ n.factorization 7 := by
    by_contra hlt
    push_neg at hlt
    have hge1 : 1 ≤ n.factorization 7 := by
      have hne : n.factorization 7 ≠ 0 := by
        rw [← Nat.support_factorization] at h7mem
        exact Finsupp.mem_support_iff.mp h7mem
      omega
    have hv : n.factorization 7 = 1 := by omega
    have hre := refined_euler habund h7mem
    have hf7 : f 7 = 7 / 6 := by simp only [f]; norm_num
    have hF7 : Ffac n 7 = 8 / 7 := by
      simp only [Ffac, hv]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
    rw [hf7, hF7] at hre
    have hb := prod_primeFactors_f_lt hodd h3 habund hcard7
    linarith
  have h72 : (7 : ℕ) ^ 2 ∣ n := (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hn0).mpr hfact
  have : (49 : ℕ) = 7 ^ 2 := by norm_num
  rw [this]; exact h72

/-- **The minimal exponent corner is impossible.**  For the `ω = 7` residual, the primes
`5, 7, 11` cannot all sit at the minimal exponents `(2, 2, 1)`: `v₅ ≥ 3 ∨ v₇ ≥ 3 ∨ v₁₁ ≥ 2`.

At `(2,2,1)` the three-prime refined Euler bound forces
`∏_{p∣n} p/(p−1) > 1037575/508896`, contradicting the sharp weight bound
`∏_{p∣n} p/(p−1) < 1037575/508896`. -/
lemma exp_not_all_minimal {n : ℕ} (hodd : Odd n) (h3 : ¬ (3 ∣ n)) (habund : Nat.Abundant n)
    (hcard7 : n.primeFactors.card = 7) :
    3 ≤ n.factorization 5 ∨ 3 ≤ n.factorization 7 ∨ 2 ≤ n.factorization 11 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hv5, hv7, hv11⟩ := hcon
  have hn0 : n ≠ 0 := by rintro rfl; simp at hcard7
  have h5mem : (5 : ℕ) ∈ n.primeFactors := by
    rcases omega_seven_prime_support hodd h3 habund hcard7 with h | h | h | h <;> rw [h] <;> decide
  have h7mem : (7 : ℕ) ∈ n.primeFactors := by
    rcases omega_seven_prime_support hodd h3 habund hcard7 with h | h | h | h <;> rw [h] <;> decide
  have h11mem : (11 : ℕ) ∈ n.primeFactors := by
    rcases omega_seven_prime_support hodd h3 habund hcard7 with h | h | h | h <;> rw [h] <;> decide
  have e5 : 2 ≤ n.factorization 5 := by
    have h25 := five_sq_dvd hodd h3 habund hcard7
    exact (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hn0).mp
      (by rw [show (5 : ℕ) ^ 2 = 25 from by norm_num]; exact h25)
  have e7 : 2 ≤ n.factorization 7 := by
    have h49 := seven_sq_dvd hodd h3 habund hcard7
    exact (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hn0).mp
      (by rw [show (7 : ℕ) ^ 2 = 49 from by norm_num]; exact h49)
  have e11 : 1 ≤ n.factorization 11 := by
    have hne : n.factorization 11 ≠ 0 := by
      rw [← Nat.support_factorization] at h11mem
      exact Finsupp.mem_support_iff.mp h11mem
    omega
  have hv5eq : n.factorization 5 = 2 := by omega
  have hv7eq : n.factorization 7 = 2 := by omega
  have hv11eq : n.factorization 11 = 1 := by omega
  have hsub : ({5, 7, 11} : Finset ℕ) ⊆ n.primeFactors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact h5mem
    · exact h7mem
    · exact h11mem
  have hre := refined_euler_set habund hsub
  have hTf : ∏ p ∈ ({5, 7, 11} : Finset ℕ), f p = f 5 * (f 7 * f 11) := by
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  have hTF : ∏ p ∈ ({5, 7, 11} : Finset ℕ), Ffac n p = Ffac n 5 * (Ffac n 7 * Ffac n 11) := by
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  have hF5 : Ffac n 5 = 31 / 25 := by
    simp only [Ffac, hv5eq]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  have hF7 : Ffac n 7 = 57 / 49 := by
    simp only [Ffac, hv7eq]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  have hF11 : Ffac n 11 = 12 / 11 := by
    simp only [Ffac, hv11eq]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hTf, hTF, hF5, hF7, hF11] at hre
  have hfvals : f 5 * (f 7 * f 11) = 77 / 48 := by simp only [f]; norm_num
  rw [hfvals] at hre
  set P := ∏ p ∈ n.primeFactors, f p with hP
  have hb := prod_primeFactors_f_lt_sharp hodd h3 habund hcard7
  rw [← hP] at hb
  have hcoef : (0 : ℚ) < 31 / 25 * (57 / 49 * (12 / 11)) := by norm_num
  have hmul := mul_lt_mul_of_pos_left hb hcoef
  have hval : (31 / 25 * (57 / 49 * (12 / 11)) : ℚ) * (1037575 / 508896) = 77 / 24 := by norm_num
  have hlhs : (2 : ℚ) * (77 / 48) = 77 / 24 := by norm_num
  rw [hlhs] at hre
  linarith [hre, hmul, hval]

/-- Magnitude bound from the explicit prime-power expansion: forcing `v₅ ≥ 2`, `v₇ ≥ 2`,
the six fixed primes `5,7,11,13,17,19` and a seventh prime `q ≥ 23`, *plus* one of the
exponent increments `v₅ ≥ 3`, `v₇ ≥ 3`, `v₁₁ ≥ 2`, drives the product past `5391411025`. -/
private lemma mag_bound {v5 v7 v11 v13 v17 v19 vq q : ℕ}
    (h5 : 2 ≤ v5) (h7 : 2 ≤ v7) (h11 : 1 ≤ v11)
    (h13 : 1 ≤ v13) (h17 : 1 ≤ v17) (h19 : 1 ≤ v19) (hvq : 1 ≤ vq) (hq : 23 ≤ q)
    (hdisj : 3 ≤ v5 ∨ 3 ≤ v7 ∨ 2 ≤ v11) :
    5391411025 ≤ 5 ^ v5 * (7 ^ v7 * (11 ^ v11 * (13 ^ v13 * (17 ^ v17 * (19 ^ v19 * q ^ vq))))) := by
  have p13 : 13 ≤ 13 ^ v13 := by
    calc (13 : ℕ) = 13 ^ 1 := (pow_one 13).symm
      _ ≤ 13 ^ v13 := Nat.pow_le_pow_right (by norm_num) h13
  have p17 : 17 ≤ 17 ^ v17 := by
    calc (17 : ℕ) = 17 ^ 1 := (pow_one 17).symm
      _ ≤ 17 ^ v17 := Nat.pow_le_pow_right (by norm_num) h17
  have p19 : 19 ≤ 19 ^ v19 := by
    calc (19 : ℕ) = 19 ^ 1 := (pow_one 19).symm
      _ ≤ 19 ^ v19 := Nat.pow_le_pow_right (by norm_num) h19
  have pq : 23 ≤ q ^ vq := by
    calc (23 : ℕ) ≤ q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ vq := Nat.pow_le_pow_right (by omega) hvq
  rcases hdisj with hd | hd | hd
  · have p5 : 125 ≤ 5 ^ v5 := by
      calc (125 : ℕ) = 5 ^ 3 := by norm_num
        _ ≤ 5 ^ v5 := Nat.pow_le_pow_right (by norm_num) hd
    have p7 : 49 ≤ 7 ^ v7 := by
      calc (49 : ℕ) = 7 ^ 2 := by norm_num
        _ ≤ 7 ^ v7 := Nat.pow_le_pow_right (by norm_num) h7
    have p11 : 11 ≤ 11 ^ v11 := by
      calc (11 : ℕ) = 11 ^ 1 := (pow_one 11).symm
        _ ≤ 11 ^ v11 := Nat.pow_le_pow_right (by norm_num) h11
    calc (5391411025 : ℕ) ≤ 125 * (49 * (11 * (13 * (17 * (19 * 23))))) := by norm_num
      _ ≤ 5 ^ v5 * (7 ^ v7 * (11 ^ v11 * (13 ^ v13 * (17 ^ v17 * (19 ^ v19 * q ^ vq))))) :=
          Nat.mul_le_mul p5 (Nat.mul_le_mul p7 (Nat.mul_le_mul p11
            (Nat.mul_le_mul p13 (Nat.mul_le_mul p17 (Nat.mul_le_mul p19 pq)))))
  · have p5 : 25 ≤ 5 ^ v5 := by
      calc (25 : ℕ) = 5 ^ 2 := by norm_num
        _ ≤ 5 ^ v5 := Nat.pow_le_pow_right (by norm_num) h5
    have p7 : 343 ≤ 7 ^ v7 := by
      calc (343 : ℕ) = 7 ^ 3 := by norm_num
        _ ≤ 7 ^ v7 := Nat.pow_le_pow_right (by norm_num) hd
    have p11 : 11 ≤ 11 ^ v11 := by
      calc (11 : ℕ) = 11 ^ 1 := (pow_one 11).symm
        _ ≤ 11 ^ v11 := Nat.pow_le_pow_right (by norm_num) h11
    calc (5391411025 : ℕ) ≤ 25 * (343 * (11 * (13 * (17 * (19 * 23))))) := by norm_num
      _ ≤ 5 ^ v5 * (7 ^ v7 * (11 ^ v11 * (13 ^ v13 * (17 ^ v17 * (19 ^ v19 * q ^ vq))))) :=
          Nat.mul_le_mul p5 (Nat.mul_le_mul p7 (Nat.mul_le_mul p11
            (Nat.mul_le_mul p13 (Nat.mul_le_mul p17 (Nat.mul_le_mul p19 pq)))))
  · have p5 : 25 ≤ 5 ^ v5 := by
      calc (25 : ℕ) = 5 ^ 2 := by norm_num
        _ ≤ 5 ^ v5 := Nat.pow_le_pow_right (by norm_num) h5
    have p7 : 49 ≤ 7 ^ v7 := by
      calc (49 : ℕ) = 7 ^ 2 := by norm_num
        _ ≤ 7 ^ v7 := Nat.pow_le_pow_right (by norm_num) h7
    have p11 : 121 ≤ 11 ^ v11 := by
      calc (121 : ℕ) = 11 ^ 2 := by norm_num
        _ ≤ 11 ^ v11 := Nat.pow_le_pow_right (by norm_num) hd
    calc (5391411025 : ℕ) ≤ 25 * (49 * (121 * (13 * (17 * (19 * 23))))) := by norm_num
      _ ≤ 5 ^ v5 * (7 ^ v7 * (11 ^ v11 * (13 ^ v13 * (17 ^ v17 * (19 ^ v19 * q ^ vq))))) :=
          Nat.mul_le_mul p5 (Nat.mul_le_mul p7 (Nat.mul_le_mul p11
            (Nat.mul_le_mul p13 (Nat.mul_le_mul p17 (Nat.mul_le_mul p19 pq)))))

/-- **Sharp residual magnitude bound — closes the `ω = 7` case.**  An odd abundant number
coprime to 3 with exactly seven distinct prime factors satisfies `n ≥ 5391411025`. -/
theorem omega_seven_residual_ge_sharp {n : ℕ} (hodd : Odd n) (h3 : ¬ (3 ∣ n))
    (habund : Nat.Abundant n) (hcard7 : n.primeFactors.card = 7) : 5391411025 ≤ n := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hcard7
  have hpow : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n :=
    Nat.factorization_prod_pow_eq_self hn0
  have hf1 : ∀ x : ℕ, x ∈ n.primeFactors → 1 ≤ n.factorization x := by
    intro x hx
    have hne : n.factorization x ≠ 0 := by
      rw [← Nat.support_factorization] at hx
      exact Finsupp.mem_support_iff.mp hx
    omega
  have e5 : 2 ≤ n.factorization 5 := by
    have h25 := five_sq_dvd hodd h3 habund hcard7
    exact (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hn0).mp
      (by rw [show (5 : ℕ) ^ 2 = 25 from by norm_num]; exact h25)
  have e7 : 2 ≤ n.factorization 7 := by
    have h49 := seven_sq_dvd hodd h3 habund hcard7
    exact (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) hn0).mp
      (by rw [show (7 : ℕ) ^ 2 = 49 from by norm_num]; exact h49)
  have hm11 : (11 : ℕ) ∈ n.primeFactors := by
    rcases omega_seven_prime_support hodd h3 habund hcard7 with h | h | h | h <;> rw [h] <;> decide
  have hm13 : (13 : ℕ) ∈ n.primeFactors := by
    rcases omega_seven_prime_support hodd h3 habund hcard7 with h | h | h | h <;> rw [h] <;> decide
  have hm17 : (17 : ℕ) ∈ n.primeFactors := by
    rcases omega_seven_prime_support hodd h3 habund hcard7 with h | h | h | h <;> rw [h] <;> decide
  have hm19 : (19 : ℕ) ∈ n.primeFactors := by
    rcases omega_seven_prime_support hodd h3 habund hcard7 with h | h | h | h <;> rw [h] <;> decide
  have e11 := hf1 11 hm11
  have e13 := hf1 13 hm13
  have e17 := hf1 17 hm17
  have e19 := hf1 19 hm19
  have hdisj := exp_not_all_minimal hodd h3 habund hcard7
  rcases omega_seven_prime_support hodd h3 habund hcard7 with h | h | h | h
  · have eq7 := hf1 23 (by rw [h]; decide)
    rw [← hpow, h, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
    exact mag_bound e5 e7 e11 e13 e17 e19 eq7 (by norm_num) hdisj
  · have eq7 := hf1 29 (by rw [h]; decide)
    rw [← hpow, h, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
    exact mag_bound e5 e7 e11 e13 e17 e19 eq7 (by norm_num) hdisj
  · have eq7 := hf1 31 (by rw [h]; decide)
    rw [← hpow, h, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
    exact mag_bound e5 e7 e11 e13 e17 e19 eq7 (by norm_num) hdisj
  · have eq7 := hf1 37 (by rw [h]; decide)
    rw [← hpow, h, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
    exact mag_bound e5 e7 e11 e13 e17 e19 eq7 (by norm_num) hdisj

/-- **Unconditional exact lower bound (resolves the lower-bound direction of the conjecture).**
Every odd abundant number coprime to 3 is at least `5391411025 = 5²·7·11·13·17·19·23·29`.

Assembled from three exhaustive shapes for an odd abundant `n` coprime to 3 lying below the
witness: the squarefree case is `≥ 33426748355`, the `ω ≥ 8` case is `≥ 5391411025`
(both `GeneralBound`), and the residual `ω = 7` case is `≥ 5391411025`
(`omega_seven_residual_ge_sharp`).  Since the witness `5391411025` is itself odd, abundant
and coprime to 3, the least such number is exactly `5391411025`. -/
theorem odd_abundant_coprime_three_ge_witness {n : ℕ} (hodd : Odd n) (h3 : ¬ (3 ∣ n))
    (habund : Nat.Abundant n) : 5391411025 ≤ n := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨_, hcard7⟩ :=
    odd_abundant_coprime_three_below_min_structure hodd h3 habund hlt
  have := omega_seven_residual_ge_sharp hodd h3 habund hcard7
  omega

#check @refined_euler_set
#check @exp_not_all_minimal
#check @omega_seven_residual_ge_sharp
#check @odd_abundant_coprime_three_ge_witness

-- Axiom audit: only the foundational axioms (`propext`, `Classical.choice`, `Quot.sound`);
-- in particular NO `Lean.ofReduceBool` (no `native_decide`) and NO `sorryAx`.
#print axioms five_sq_dvd
#print axioms seven_sq_dvd
#print axioms omega_seven_residual_ge_sharp
#print axioms odd_abundant_coprime_three_ge_witness

end AbundantNumberOQ02OQ01SevenPrimeExponents
