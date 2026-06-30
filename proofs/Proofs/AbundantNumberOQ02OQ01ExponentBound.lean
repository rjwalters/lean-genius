/-
  **First exponent bound for the open `ω = 7` residual case: `25 ∣ n`.**

  The exact-minimality problem "the smallest odd abundant number not divisible by 3 is
  `5391411025 = 5²·7·11·13·17·19·23·29`" has been reduced (companion files) to a single
  residual shape: an odd abundant number coprime to 3 strictly below `5391411025` must be
  **non-squarefree with exactly 7 distinct prime factors**, and
  `AbundantNumberOQ02OQ01OmegaSevenPrimes.lean` pinned its prime support to one of just four
  explicit sets `{5,7,11,13,17,19,q}` with `q ∈ {23,29,31,37}`.  The remaining task is to
  bound the prime-power *exponents* on each of these four supports.

  This file takes the first exponent step: **the prime `5` must occur to at least the
  second power**, i.e. `v₅(n) ≥ 2`, equivalently `25 ∣ n`.

  The mechanism is a *sharpened* Euler abundancy bound.  The companion `euler_f_gt_two`
  drops every exponent and only keeps the supremum weight `f p = p/(p−1)`.  Here we instead
  keep the `p = 5` factor **exact**: writing `σ(n)/n = ∏_{p∣n} σ(p^{a_p})/p^{a_p}` and using
  the per-prime-power bound `σ(p^a)/p^a < p/(p−1)` for the other six primes, an `a₅ = 1`
  would give the exact factor `σ(5)/5 = 6/5` and hence

      σ(n)/n  <  (6/5) · f(7)·f(11)·f(13)·f(17)·f(19)·f(q)
              ≤  (6/5) · f(7)·f(11)·f(13)·f(17)·f(19)·f(23)
              =  7436429 / 3801600  ≈ 1.9561  <  2,

  contradicting abundancy `σ(n)/n > 2`.  (The bound `f(q) ≤ f(23)` is just antitonicity of
  `f`; the displayed numeric witness is the worst case `q = 23`.)  Hence `a₅ ≥ 2`.

  The reusable engine is `abundant_two_lt_prod_g`: for *any* abundant `n`,
  `2 < ∏_{p∣n} σ(p^{a_p})/p^{a_p}` over ℚ — the exact rational abundancy product, the natural
  refinement of the integer Euler bound `abundant_imp_two_mul_prod_sub_one_lt`.  Future
  per-prime exponent bounds (`a₇`, `a₁₁`, …) can be read off the same product.

  Everything is axiom-free (only `propext`/`Classical.choice`/`Quot.sound`; no
  `Lean.ofReduceBool`, no `native_decide`, no `sorry`).
-/
import Mathlib
import Proofs.AbundantNumberOQ02OQ01OmegaSevenPrimes

namespace AbundantNumberOQ02OQ01ExponentBound

open Nat ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

open AbundantNumberOQ02OQ01Unconditional
open AbundantNumberOQ02OQ01Minimality
open AbundantNumberOQ02OQ01OmegaSevenPrimes

/-- The exact per-prime-power weight `g n p = σ(p^{vₚ(n)}) / p^{vₚ(n)}` over ℚ, written as the
geometric sum `∑_{i ≤ vₚ(n)} pⁱ` divided by `p^{vₚ(n)}`.  Its product over `n.primeFactors`
is exactly `σ(n)/n`. -/
noncomputable def g (n p : ℕ) : ℚ :=
  (∑ i ∈ Finset.range (n.factorization p + 1), (p : ℚ) ^ i) / (p : ℚ) ^ (n.factorization p)

/-- **Per-prime-power weight bound.**  `σ(p^a)/p^a < p/(p−1)` over ℚ, the rational shadow of
`geomSum_mul_pred_lt`.  Here as the `≤` form needed for the product comparison. -/
lemma geomSum_div_le_f {p : ℕ} (hp : 2 ≤ p) (a : ℕ) :
    (∑ i ∈ Finset.range (a + 1), (p : ℚ) ^ i) / (p : ℚ) ^ a ≤ f p := by
  have hp2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
  have hpa : (0 : ℚ) < (p : ℚ) ^ a := by positivity
  have hpm1 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  have hN := geomSum_mul_pred_lt hp a
  have hQ : (∑ i ∈ Finset.range (a + 1), (p : ℚ) ^ i) * ((p : ℚ) - 1) < (p : ℚ) ^ (a + 1) := by
    have h1le : 1 ≤ p := by omega
    have hcast :
        (∑ i ∈ Finset.range (a + 1), (p : ℚ) ^ i) * ((p : ℚ) - 1)
          = (((∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1) : ℕ) : ℚ) := by
      push_cast [Nat.cast_sub h1le]
      ring
    rw [hcast]
    calc (((∑ i ∈ Finset.range (a + 1), p ^ i) * (p - 1) : ℕ) : ℚ)
        < ((p ^ (a + 1) : ℕ) : ℚ) := by exact_mod_cast hN
      _ = (p : ℚ) ^ (a + 1) := by push_cast; ring
  rw [f, div_le_div_iff₀ hpa hpm1]
  have hps : (p : ℚ) ^ (a + 1) = (p : ℚ) * (p : ℚ) ^ a := by rw [pow_succ]; ring
  linarith [hQ, hps]

/-- `g n p ≤ f p` for any prime power `≥ 2`. -/
lemma g_le_f {n p : ℕ} (hp : 2 ≤ p) : g n p ≤ f p :=
  geomSum_div_le_f hp (n.factorization p)

/-- The weight `g n p` is nonnegative for `p ≥ 2`. -/
lemma g_nonneg {n p : ℕ} (hp : 2 ≤ p) : 0 ≤ g n p := by
  unfold g
  have hpa : (0 : ℚ) < (p : ℚ) ^ (n.factorization p) := by
    have : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (by omega : 0 < p)
    positivity
  apply div_nonneg _ (le_of_lt hpa)
  apply Finset.sum_nonneg
  intro i _
  positivity

/-- **Exact rational abundancy product.**  For any abundant `n`,
`2 < ∏_{p∣n} σ(p^{vₚ(n)})/p^{vₚ(n)}`.  This is the sharp refinement of the integer Euler
bound `abundant_imp_two_mul_prod_sub_one_lt`: instead of replacing each exponent by the
supremum weight `p/(p−1)`, it keeps the exact per-prime-power weight, so individual primes'
exponents can be analysed. -/
lemma abundant_two_lt_prod_g {n : ℕ} (habund : Nat.Abundant n) :
    2 < ∏ p ∈ n.primeFactors, g n p := by
  -- abundance forces `n > 1` and `σ(n) > 2n`
  have hn' : n < ∑ i ∈ n.properDivisors, i := habund
  have h1n : 1 < n := by
    rcases n with _ | _ | n
    · simp [Nat.properDivisors_zero] at hn'
    · simp [Nat.properDivisors_one] at hn'
    · omega
  have hn0 : n ≠ 0 := by omega
  have hσ : 2 * n < σ 1 n := by
    rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
    omega
  -- `n` and `σ 1 n` as rational products over the prime factors
  have hNpow : (n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ) ^ (n.factorization p) := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn0]
    push_cast
    rfl
  have hSigN : σ 1 n = ∏ p ∈ n.primeFactors, ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i := by
    rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn0]
    simp only [mul_one]
  have hSig : (σ 1 n : ℚ)
      = ∏ p ∈ n.primeFactors, ∑ i ∈ Finset.range (n.factorization p + 1), (p : ℚ) ^ i := by
    rw [hSigN]; push_cast; rfl
  have hnpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast (by omega : 0 < n)
  -- the product of weights equals σ(n)/n
  have hprod : ∏ p ∈ n.primeFactors, g n p = (σ 1 n : ℚ) / (n : ℚ) := by
    unfold g
    rw [Finset.prod_div_distrib, ← hSig, ← hNpow]
  rw [hprod, lt_div_iff₀ hnpos]
  have hσQ : (2 : ℚ) * n < (σ 1 n : ℚ) := by exact_mod_cast hσ
  linarith

/-- Worst-case numeric bound (worst case `q = 23`).  For `q ∈ {23,29,31,37}`,
`(6/5) · ∏_{p ∈ {7,11,13,17,19,q}} f p < 2`.  Stated over the support set with `5` erased. -/
private lemma erase5_prod_f_bound {q : ℕ} (hq : q = 23 ∨ q = 29 ∨ q = 31 ∨ q = 37) :
    (6 : ℚ) / 5 * ∏ p ∈ ({5, 7, 11, 13, 17, 19, q} : Finset ℕ).erase 5, f p < 2 := by
  rcases hq with rfl | rfl | rfl | rfl <;>
  · rw [Finset.erase_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_singleton]
    simp only [f]
    norm_num

/-- **First exponent bound for the `ω = 7` residual case: `v₅(n) ≥ 2`.**

An odd abundant number coprime to `3` with exactly seven distinct prime factors has `5` as a
prime factor to at least the *second* power: `25 ∣ n`.  Combined with
`omega_seven_prime_support`, this is the first of the per-support exponent bounds needed to
finish the exact-minimality theorem (it already rules out every squarefree-in-`5` candidate
on all four supports). -/
theorem omega_seven_imp_five_sq_dvd
    {n : ℕ} (hodd : Odd n) (h3 : ¬ (3 ∣ n)) (habund : Nat.Abundant n)
    (hcard7 : n.primeFactors.card = 7) :
    2 ≤ n.factorization 5 := by
  by_contra hlt
  push_neg at hlt
  -- prime support is one of the four explicit sets; in particular `5 ∈ primeFactors`
  have hsupp := omega_seven_prime_support hodd h3 habund hcard7
  have h5mem : 5 ∈ n.primeFactors := by
    rcases hsupp with h | h | h | h <;> rw [h] <;> decide
  -- `5 ∈ primeFactors` ⟹ `v₅(n) ≠ 0`; with `v₅(n) < 2` this pins `v₅(n) = 1`
  have hf5ne : n.factorization 5 ≠ 0 := by
    rw [← Nat.support_factorization] at h5mem
    exact Finsupp.mem_support_iff.mp h5mem
  have hf5 : n.factorization 5 = 1 := by omega
  -- the exact rational abundancy product, split off the `p = 5` factor
  have h2lt := abundant_two_lt_prod_g habund
  rw [← Finset.mul_prod_erase n.primeFactors (g n) h5mem] at h2lt
  -- the `5`-factor is exactly `6/5`
  have hg5 : g n 5 = 6 / 5 := by
    unfold g
    rw [hf5]
    norm_num [Finset.sum_range_succ]
  rw [hg5] at h2lt
  -- the remaining six weights are bounded above by the supremum weights `f`
  have hb : ∏ p ∈ n.primeFactors.erase 5, g n p ≤ ∏ p ∈ n.primeFactors.erase 5, f p := by
    apply Finset.prod_le_prod
    · intro p hp
      exact g_nonneg (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).two_le
    · intro p hp
      exact g_le_f (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).two_le
  have hmono : (6 : ℚ) / 5 * ∏ p ∈ n.primeFactors.erase 5, g n p
      ≤ 6 / 5 * ∏ p ∈ n.primeFactors.erase 5, f p :=
    mul_le_mul_of_nonneg_left hb (by norm_num)
  -- the supremum product is `< 2` on every one of the four supports
  have hfinal : (6 : ℚ) / 5 * ∏ p ∈ n.primeFactors.erase 5, f p < 2 := by
    rcases hsupp with h | h | h | h
    · rw [h]; exact erase5_prod_f_bound (Or.inl rfl)
    · rw [h]; exact erase5_prod_f_bound (Or.inr (Or.inl rfl))
    · rw [h]; exact erase5_prod_f_bound (Or.inr (Or.inr (Or.inl rfl)))
    · rw [h]; exact erase5_prod_f_bound (Or.inr (Or.inr (Or.inr rfl)))
  linarith [h2lt, hmono, hfinal]

#check @omega_seven_imp_five_sq_dvd

-- Axiom audit: only the foundational axioms (`propext`, `Classical.choice`, `Quot.sound`);
-- in particular NO `Lean.ofReduceBool` (no `native_decide`) and NO `sorryAx`.
#print axioms omega_seven_imp_five_sq_dvd

end AbundantNumberOQ02OQ01ExponentBound
