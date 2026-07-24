import Mathlib

/-
# Two primes in `(n, 2n]` — a Ramanujan-type strengthening of Bertrand's postulate

This file proves that for every natural number `n ≥ 6` the interval `(n, 2n]`
contains **two distinct primes**:

  `exists_two_primes_in_Ioc : ∀ n ≥ 6, ∃ p q, p.Prime ∧ q.Prime ∧ p < q ∧ n < p ∧ q ≤ 2 * n`

Mathlib's Bertrand postulate (`Nat.exists_prime_lt_and_le_two_mul`) gives ONE
prime in `(n, 2n]`; the two-prime refinement is the `k = 2` instance of
Ramanujan's 1919 generalization ("A proof of Bertrand's postulate", J. Indian
Math. Soc. 11, 181–182): `π(x) − π(x/2) ≥ k` for `x ≥ R_k`, where `R_2 = 11`
is the second Ramanujan prime.  In the dual interval form proved here the
sharp threshold is `n ≥ 6` (the interval `(5, 10]` contains only the prime 7,
so the bound is best possible).

The result was, at time of writing, absent from Mathlib, and is the single
missing ingredient (`exists_second_prime_in_Ioc`, proved at the bottom of this
file with the exact signature of the `sorry` it discharges) in the A054656
distinct-prime-partition engine (`Proofs/A054656DistinctPrimePartition.lean`):
the Richert-style induction there needs a prime `q ≠ p` in `(x, 2x]` even when
the forbidden prime `p` is itself the unique Bertrand witness.

## Proof strategy

We adapt the Erdős central-binomial-coefficient proof of Bertrand's postulate,
following Mathlib's `Mathlib/NumberTheory/Bertrand.lean` (Patrick Stevens,
Bolton Bailey) step by step, weakening the hypothesis "no prime lies in
`(n, 2n]`" to "at most ONE prime lies in `(n, 2n]`".

The point is quantitative: a prime `p ∈ (n, 2n]` divides `centralBinom n` at
most once (since `p² > 2n`), so a SINGLE permitted prime inflates the
factorization bound by a factor of at most `2n`:

  `centralBinom n ≤ (2n) · (2n)^√(2n) · 4^(2n/3)`   (one permitted prime)

versus Mathlib's `(2n)^√(2n) · 4^(2n/3)` (no permitted prime).  Coupled with
the exponential lower bound `4^n < n · centralBinom n`, the required real
inequality becomes

  `x · (2x) · (2x)^√(2x) · 4^(2x/3) ≤ 4^x`,

and the concavity argument used by Mathlib still closes at the SAME threshold
`x = 512`: at the right endpoint the comparison is `2^339 ≤ 2^(1024/3)`
(i.e. `1017 ≤ 1024`), one extra factor `2x = 2^10` having been absorbed by the
slack Mathlib's proof leaves unused (`2^329 ≤ 2^(1024/3)`).  Concavity of
`log x + log(2x) + √(2x)·log(2x) − (log 4/3)·x` on `(0.5, ∞)` follows from
the same three ingredients as in Mathlib plus concavity of one extra `log`.

For `6 ≤ n < 512` we use a descending chain of prime PAIRS, mirroring
Mathlib's descending prime list: for consecutive chain entries with
`b ≤ p < q ≤ 2c` every `n` with `c ≤ n < b` gets its two primes from the pair
`(p, q)`.  The chain

  (512) 521, 523 → (269) 269, 271 → (139) 139, 149 → (75) 79, 83 →
  (42) 43, 47 → (24) 29, 31 → (16) 17, 19 → (12)

reaches `n < 12`, and `6 ≤ n ≤ 11` is finished by explicit witnesses.

## Main results

* `Bertrand2.real_main_inequality` — the real inequality with the extra `2x`.
* `centralBinom_le_of_unique_bertrand_prime` — the inflated factorization bound.
* `exists_two_primes_eventually` — two primes in `(n, 2n]` for `512 ≤ n`.
* `exists_two_primes_in_Ioc` — two primes in `(n, 2n]` for all `n ≥ 6` (sharp).
* `exists_second_prime_in_Ioc` — drop-in replacement for the A054656 `sorry`:
  a second prime `q ≠ p` when a prime `p ∈ (x, 2x]` is forbidden, `x ≥ 11`.

This file is axiom-free and `sorry`-free: everything is machine-checked from
Mathlib.  No `native_decide` is used (kernel `decide`/`norm_num` only).

References:
* S. Ramanujan, "A proof of Bertrand's postulate", J. Indian Math. Soc. 11 (1919).
* J. Sondow, "Ramanujan primes and Bertrand's postulate", Amer. Math. Monthly 116 (2009).
* M. Aigner, G. M. Ziegler, "Proofs from THE BOOK", Chapter on Bertrand's postulate.
-/

namespace A054656

section Real

open Real

namespace Bertrand2

/-- **The real inequality with one extra factor `2x`.**  Analogue of
`Bertrand.real_main_inequality`: the concave function
`f x = log 2 + (log x + log x) + √(2x)·log(2x) − (log 4/3)·x`
(which equals `log (x·(2x)·(2x)^√(2x) / 4^(x/3))` for `x > 0`) is nonnegative
at `18` and nonpositive at `512`, hence nonpositive on `[512, ∞)`.
At `512` the comparison is `2^(9+10+320) = 2^339 ≤ 2^(1024/3)`. -/
theorem real_main_inequality {x : ℝ} (x_large : (512 : ℝ) ≤ x) :
    x * ((2 * x) * (2 * x) ^ √(2 * x)) * 4 ^ (2 * x / 3) ≤ 4 ^ x := by
  let f : ℝ → ℝ := fun x =>
    log 2 + (log x + log x) + √(2 * x) * log (2 * x) - log 4 / 3 * x
  have hf' : ∀ x : ℝ, 0 < x → 0 < x * ((2 * x) * (2 * x) ^ √(2 * x)) / 4 ^ (x / 3) := by
    intro x h
    positivity
  have hf : ∀ x : ℝ, 0 < x →
      f x = log (x * ((2 * x) * (2 * x) ^ √(2 * x)) / 4 ^ (x / 3)) := by
    intro x h5
    have h6 : (0 : ℝ) < 2 * x := mul_pos two_pos h5
    have h7 : (0 : ℝ) < (2 * x) ^ √(2 * x) := rpow_pos_of_pos h6 _
    show log 2 + (log x + log x) + √(2 * x) * log (2 * x) - log 4 / 3 * x
        = log (x * ((2 * x) * (2 * x) ^ √(2 * x)) / 4 ^ (x / 3))
    rw [log_div (by positivity) (by positivity), log_mul h5.ne' (by positivity),
      log_mul h6.ne' h7.ne', log_rpow h6, log_rpow zero_lt_four,
      log_mul (two_ne_zero (α := ℝ)) h5.ne']
    ring
  have h5 : 0 < x := lt_of_lt_of_le (by norm_num) x_large
  rw [← div_le_one (rpow_pos_of_pos four_pos x), ← div_div_eq_mul_div, ← rpow_sub four_pos, ←
    mul_div 2 x, mul_div_left_comm, ← mul_one_sub, (by norm_num : (1 : ℝ) - 2 / 3 = 1 / 3),
    mul_one_div, ← log_nonpos_iff (hf' x h5).le, ← hf x h5]
  -- Concavity of `f` on `(0.5, ∞)`: same pieces as Mathlib's proof, plus one
  -- extra concave `log` (from the additional factor `2x`).
  have h : ConcaveOn ℝ (Set.Ioi 0.5) f := by
    apply ConcaveOn.sub
    · apply ConcaveOn.add
      · apply ConcaveOn.add
        · exact concaveOn_const _ (convex_Ioi _)
        · exact (strictConcaveOn_log_Ioi.concaveOn.subset
            (Set.Ioi_subset_Ioi (by norm_num)) (convex_Ioi 0.5)).add
            (strictConcaveOn_log_Ioi.concaveOn.subset
            (Set.Ioi_subset_Ioi (by norm_num)) (convex_Ioi 0.5))
      · convert!
          ((strictConcaveOn_sqrt_mul_log_Ioi.concaveOn.comp_linearMap ((2 : ℝ) • LinearMap.id)))
          using 1
        ext x
        simp only [Set.mem_Ioi, Set.mem_preimage, LinearMap.smul_apply,
          LinearMap.id_coe, id_eq, smul_eq_mul]
        rw [← mul_lt_mul_iff_right₀ (two_pos)]
        norm_num1
        rfl
    · apply ConvexOn.smul
      · exact div_nonneg (log_nonneg (by norm_num)) (by norm_num)
      · exact convexOn_id (convex_Ioi (0.5 : ℝ))
  suffices ∃ x1 x2, 0.5 < x1 ∧ x1 < x2 ∧ x2 ≤ x ∧ 0 ≤ f x1 ∧ f x2 ≤ 0 by
    obtain ⟨x1, x2, h1, h2, h0, h3, h4⟩ := this
    exact (h.right_le_of_le_left'' h1 ((h1.trans h2).trans_le h0) h2 h0 (h4.trans h3)).trans h4
  refine ⟨18, 512, by norm_num, by norm_num, x_large, ?_, ?_⟩
  · -- `f 18 ≥ 0` ⟺ `4^6 ≤ 18·36·36^6`.
    have h36 : √(2 * (18 : ℝ)) = 6 :=
      (sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)).mpr (by norm_num)
    rw [hf _ (by norm_num), log_nonneg_iff (by positivity), h36,
      one_le_div (by positivity)]
    norm_num
  · -- `f 512 ≤ 0` ⟺ `512·1024·1024^32 = 2^339 ≤ 2^(1024/3) = 4^(512/3)`.
    have h32 : √(2 * (512 : ℝ)) = 32 :=
      (sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)).mpr (by norm_num)
    rw [hf _ (by norm_num), log_nonpos_iff (hf' _ (by norm_num)).le, h32,
      div_le_one (by positivity)]
    have e1 : ((2 : ℝ) * 512) ^ (32 : ℝ) = 2 ^ (320 : ℝ) := by
      rw [show (2 : ℝ) * 512 = 2 ^ (10 : ℝ) by
            rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, rpow_natCast]; norm_num,
        ← rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    calc (512 : ℝ) * ((2 * 512) * (2 * 512) ^ (32 : ℝ))
        = (512 * (2 * 512)) * (2 * 512) ^ (32 : ℝ) := by ring
      _ = 2 ^ (19 : ℝ) * 2 ^ (320 : ℝ) := by
          rw [e1, show (512 : ℝ) * (2 * 512) = 2 ^ (19 : ℝ) by
            rw [show (19 : ℝ) = ((19 : ℕ) : ℝ) by norm_num, rpow_natCast]; norm_num]
      _ = 2 ^ (339 : ℝ) := by
          rw [← rpow_add (by norm_num : (0 : ℝ) < 2)]; norm_num
      _ ≤ 2 ^ ((2 : ℝ) * (512 / 3)) := by
          apply rpow_le_rpow_of_exponent_le one_le_two
          norm_num
      _ = (2 ^ (2 : ℝ)) ^ ((512 : ℝ) / 3) := by
          rw [← rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = 4 ^ ((512 : ℝ) / 3) := by
          rw [show (2 : ℝ) ^ (2 : ℝ) = 4 by
            rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast]; norm_num]

end Bertrand2

end Real

section Nat

/-- Natural-number version of `Bertrand2.real_main_inequality`, analogue of
`Nat.bertrand_main_inequality`. -/
theorem two_primes_main_inequality {n : ℕ} (n_large : 512 ≤ n) :
    n * ((2 * n) * (2 * n) ^ Nat.sqrt (2 * n)) * 4 ^ (2 * n / 3) ≤ 4 ^ n := by
  rw [← @Nat.cast_le ℝ]
  push_cast
  simp only [← Real.rpow_natCast]
  refine le_trans ?_ (Bertrand2.real_main_inequality (by exact_mod_cast n_large))
  have n_pos : (512 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n_large
  gcongr
  · linarith
  · exact_mod_cast Real.nat_sqrt_le_real_sqrt
  · norm_num
  · exact Nat.cast_div_le.trans (by norm_cast)

/-- If `p₀` is the UNIQUE prime in `(n, 2n]`, then the prime factorization of
`centralBinom n` is supported on `[0, 2n/3] ∪ {p₀}`.  Analogue of
`centralBinom_factorization_small` with one permitted Bertrand prime. -/
theorem centralBinom_factorization_unique {n p₀ : ℕ} (n_large : 2 < n)
    (_hp₀ : p₀.Prime) (hl : n < p₀) (hu : p₀ ≤ 2 * n)
    (huniq : ∀ q : ℕ, q.Prime → n < q → q ≤ 2 * n → q = p₀) :
    Nat.centralBinom n = p₀ ^ (Nat.centralBinom n).factorization p₀ *
      ∏ p ∈ Finset.range (2 * n / 3 + 1), p ^ (Nat.centralBinom n).factorization p := by
  have hnotin : p₀ ∉ Finset.range (2 * n / 3 + 1) := by
    simp only [Finset.mem_range, not_lt]
    omega
  have hins : ∏ x ∈ insert p₀ (Finset.range (2 * n / 3 + 1)),
        x ^ (Nat.centralBinom n).factorization x
      = p₀ ^ (Nat.centralBinom n).factorization p₀ *
        ∏ p ∈ Finset.range (2 * n / 3 + 1), p ^ (Nat.centralBinom n).factorization p :=
    Finset.prod_insert hnotin
  rw [← hins]
  refine ((Finset.prod_subset ?_ ?_).trans n.prod_pow_factorization_centralBinom).symm
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact Finset.mem_range.mpr (by omega)
    · rw [Finset.mem_range] at hx' ⊢
      omega
  · intro x hx hxns
    rw [Finset.mem_range] at hx
    have hxp₀ : x ≠ p₀ := fun h => hxns (h ▸ Finset.mem_insert_self _ _)
    have hxlarge : 2 * n / 3 + 1 ≤ x := by
      by_contra hcon
      exact hxns (Finset.mem_insert_of_mem (Finset.mem_range.mpr (by omega)))
    by_cases hxp : x.Prime
    · rcases Nat.lt_or_ge n x with hnx | hxn
      · exact absurd (huniq x hxp hnx (by omega)) hxp₀
      · rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul n_large hxn (by omega),
          pow_zero]
    · rw [Nat.factorization_eq_zero_of_not_prime n.centralBinom hxp, pow_zero]

/-- The part of the central-binomial factorization supported on `[0, 2n/3]` is
at most `(2n)^√(2n) · 4^(2n/3)`.  This is the product bound implicit in
Mathlib's `centralBinom_le_of_no_bertrand_prime`, extracted so it can be
reused with a permitted prime; the proof is Mathlib's verbatim. -/
theorem prod_pow_factorization_le (n : ℕ) (n_pos : 0 < n) :
    ∏ p ∈ Finset.range (2 * n / 3 + 1), p ^ (Nat.centralBinom n).factorization p ≤
      (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) := by
  have n2_pos : 1 ≤ 2 * n := by omega
  let S := {p ∈ Finset.range (2 * n / 3 + 1) | Nat.Prime p}
  have hS : ∏ x ∈ S, x ^ (Nat.centralBinom n).factorization x
      = ∏ x ∈ Finset.range (2 * n / 3 + 1), x ^ (Nat.centralBinom n).factorization x := by
    refine Finset.prod_filter_of_ne fun p _ h => ?_
    contrapose h
    rw [Nat.factorization_eq_zero_of_not_prime n.centralBinom h, pow_zero]
  rw [← hS, ← Finset.prod_filter_mul_prod_filter_not S (· ≤ Nat.sqrt (2 * n))]
  apply Nat.mul_le_mul
  · -- Primes `≤ √(2n)`: each contributes at most `2n`, and there are at most
    -- `√(2n)` of them.
    refine (Finset.prod_le_prod' fun p _ =>
      (?_ : p ^ (Nat.centralBinom n).factorization p ≤ 2 * n)).trans ?_
    · exact Nat.pow_factorization_choose_le (by omega)
    have hcard : (Finset.Icc 1 (Nat.sqrt (2 * n))).card = Nat.sqrt (2 * n) := by
      rw [Nat.card_Icc, Nat.add_sub_cancel]
    rw [Finset.prod_const]
    refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun x hx => ?_).trans hcard.le)
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
  · -- Primes in `(√(2n), 2n/3]`: exponent at most 1, so the product is at most
    -- the primorial, which is at most `4^(2n/3)`.
    refine le_trans ?_ (primorial_le_four_pow (2 * n / 3))
    refine (Finset.prod_le_prod' fun p hp =>
      (?_ : p ^ (Nat.centralBinom n).factorization p ≤ p)).trans ?_
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
      refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp <| not_le.1 h2)
    refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
    exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le

/-- **Inflated central-binomial bound.**  If `p₀` is the unique prime in
`(n, 2n]` then `centralBinom n ≤ (2n) · (2n)^√(2n) · 4^(2n/3)`: the permitted
prime divides `centralBinom n` at most once (`p₀² > 2n`), contributing a
factor at most `2n` on top of Mathlib's no-prime bound. -/
theorem centralBinom_le_of_unique_bertrand_prime {n p₀ : ℕ} (n_large : 2 < n)
    (hp₀ : p₀.Prime) (hl : n < p₀) (hu : p₀ ≤ 2 * n)
    (huniq : ∀ q : ℕ, q.Prime → n < q → q ≤ 2 * n → q = p₀) :
    Nat.centralBinom n ≤ (2 * n) * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3)) := by
  have hν : (Nat.centralBinom n).factorization p₀ ≤ 1 := by
    refine Nat.factorization_choose_le_one ?_
    have h1 : (n + 1) * (n + 1) ≤ p₀ * p₀ := Nat.mul_le_mul hl hl
    nlinarith
  calc Nat.centralBinom n
      = p₀ ^ (Nat.centralBinom n).factorization p₀ *
        ∏ p ∈ Finset.range (2 * n / 3 + 1), p ^ (Nat.centralBinom n).factorization p :=
        centralBinom_factorization_unique n_large hp₀ hl hu huniq
    _ ≤ (2 * n) * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3)) := by
        refine Nat.mul_le_mul ?_ (prod_pow_factorization_le n (by omega))
        calc p₀ ^ (Nat.centralBinom n).factorization p₀
            ≤ p₀ ^ 1 := Nat.pow_le_pow_right hp₀.pos hν
          _ = p₀ := pow_one p₀
          _ ≤ 2 * n := hu

/-- **Two primes in `(n, 2n]`, eventual version.**  For `512 ≤ n` the interval
`(n, 2n]` contains two distinct primes: if it contained at most one, the
inflated factorization bound would force
`4^n < n·(2n)·(2n)^√(2n)·4^(2n/3) ≤ 4^n`. -/
theorem exists_two_primes_eventually (n : ℕ) (n_large : 512 ≤ n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n < p ∧ q ≤ 2 * n := by
  by_contra hcon
  obtain ⟨p₀, hp₀, hp₀l, hp₀u⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  have huniq : ∀ q : ℕ, q.Prime → n < q → q ≤ 2 * n → q = p₀ := by
    intro q hq hnq hq2n
    by_contra hne
    rcases Nat.lt_or_ge q p₀ with h | h
    · exact hcon ⟨q, p₀, hq, hp₀, h, hnq, hp₀u⟩
    · exact hcon ⟨p₀, q, hp₀, hq, h.lt_of_ne' hne, hp₀l, hq2n⟩
  have h1 : 4 ^ n < n * Nat.centralBinom n :=
    Nat.four_pow_lt_mul_centralBinom n (by omega)
  have h2 : Nat.centralBinom n ≤ (2 * n) * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3)) :=
    centralBinom_le_of_unique_bertrand_prime (by omega) hp₀ hp₀l hp₀u huniq
  have h3 : n * ((2 * n) * (2 * n) ^ Nat.sqrt (2 * n)) * 4 ^ (2 * n / 3) ≤ 4 ^ n :=
    two_primes_main_inequality n_large
  have : (4 : ℕ) ^ n < 4 ^ n := by
    calc 4 ^ n < n * Nat.centralBinom n := h1
      _ ≤ n * ((2 * n) * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3))) :=
          Nat.mul_le_mul_left n h2
      _ = n * ((2 * n) * (2 * n) ^ Nat.sqrt (2 * n)) * 4 ^ (2 * n / 3) := by ring
      _ ≤ 4 ^ n := h3
  exact absurd this (lt_irrefl _)

/-- Descending-chain step for the small cases, analogue of
`Nat.exists_prime_lt_and_le_two_mul_succ` but for prime PAIRS: if primes
`p < q` satisfy `b ≤ p` and `q ≤ 2c`, then every `n` with `c ≤ n < b` has both
`p` and `q` in `(n, 2n]`, so the covering obligation descends from `b` to `c`. -/
theorem exists_two_primes_succ {n : ℕ} (c p q : ℕ) {b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hbp : b ≤ p) (hqc : q ≤ 2 * c)
    (H : n < c → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n < p ∧ q ≤ 2 * n) :
    n < b → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n < p ∧ q ≤ 2 * n := by
  intro hnb
  rcases Nat.lt_or_ge n c with h | h
  · exact H h
  · exact ⟨p, q, hp, hq, hpq, lt_of_lt_of_le hnb hbp, hqc.trans (by omega)⟩

/-- **Two primes in `(n, 2n]` (Ramanujan-type; sharp threshold).**  For every
`n ≥ 6` the interval `(n, 2n]` contains two distinct primes.  The threshold is
sharp: `(5, 10]` contains only the prime 7.  This is the `k = 2` instance of
Ramanujan's quantitative Bertrand postulate (`R₂ = 11` in the `π(x) − π(x/2)`
formulation). -/
theorem exists_two_primes_in_Ioc (n : ℕ) (hn : 6 ≤ n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n < p ∧ q ≤ 2 * n := by
  rcases Nat.lt_or_ge n 512 with h | h
  · revert h
    refine exists_two_primes_succ 269 521 523
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine exists_two_primes_succ 139 269 271
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine exists_two_primes_succ 75 139 149
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine exists_two_primes_succ 42 79 83
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine exists_two_primes_succ 24 43 47
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine exists_two_primes_succ 16 29 31
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    refine exists_two_primes_succ 12 17 19
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
    intro h12
    interval_cases n
    · exact ⟨7, 11, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 13, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 13, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 13, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨11, 13, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨13, 17, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact exists_two_primes_eventually n h

/-- **Second prime in `(x, 2x]` avoiding a forbidden prime.**  Exact-signature
drop-in for the single remaining `sorry` of
`Proofs/A054656DistinctPrimePartition.lean` (`A054656.exists_second_prime_in_Ioc`):
when a prime `p` lies in `(x, 2x]` and `x ≥ 11`, the window contains another
prime `q ≠ p`. -/
theorem exists_second_prime_in_Ioc (x p : ℕ) (hx : 11 ≤ x) (_hp : Nat.Prime p)
    (_hpl : x < p) (_hpu : p ≤ 2 * x) :
    ∃ q, Nat.Prime q ∧ q ≠ p ∧ x < q ∧ q ≤ 2 * x := by
  obtain ⟨a, b, ha, hb, hab, hxa, hb2x⟩ := exists_two_primes_in_Ioc x (by omega)
  rcases eq_or_ne a p with rfl | hne
  · exact ⟨b, hb, by omega, by omega, hb2x⟩
  · exact ⟨a, ha, hne, hxa, by omega⟩

end Nat

end A054656
