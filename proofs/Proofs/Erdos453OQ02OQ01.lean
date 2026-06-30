/-
  Erdős 453 OQ-02 OQ-01: Eliminating the PNT axiom `log p_n / n → 0`

  Open Question: erdos-453-oq-02-oq-01
  Parent: Erdos453OQ02.lean  (which itself reduced Erdős #453 from 4 axioms to 2)

  Statement (parent OQ-02, open question 1):
    "Can `logPrime_ratio_tendsto_zero` be proved by connecting Mathlib's prime-counting
     machinery to the 1-indexed `nthPrime`? The missing step is extracting log(p_n)/n → 0."

  This file ANSWERS that question affirmatively, eliminating the axiom.

  Key point: `log p_n / n → 0` (equivalently `p_n^{1/n} → 1`, the n-th prime grows
  subexponentially) is FAR weaker than the full Prime Number Theorem. It needs only a
  Chebyshev-type LOWER bound on the prime-counting function `π`, which we derive here
  entirely from the central binomial coefficient `C(2n, n)`:

    * 4^n < n · C(2n,n)                      (Mathlib: `four_pow_lt_mul_centralBinom`)
    * C(2n,n) = ∏_{p ≤ 2n} p^{e_p},  p^{e_p} ≤ 2n   (Mathlib: `pow_factorization_choose_le`)
      hence  C(2n,n) ≤ (2n)^{π(2n)}.

  Combining: (2n)^{π(2n)} > 4^n / n, i.e. π(2n) ≳ n / log n. Inverting this bound gives the
  explicit estimate  p_k ≤ 2(k+1)^3  for the k-th prime (0-indexed), which is loose but more
  than enough: log p_k = O(log k) = o(k). A squeeze finishes `log p_n / n → 0`.

  RESULT: Parent OQ-02 had 2 axioms; this file removes `logPrime_ratio_tendsto_zero`,
  leaving exactly ONE axiom — Pomerance's discrete convex-hull lemma
  (`pomerance_convex_hull_lemma`), the genuine geometric core of the 1979 proof.

  The main consequence `pomerance_1979` (infinitely many n with p_n² > p_{n-i}·p_{n+i})
  is re-derived from that single remaining axiom.

  References:
  - Pomerance (1979): "The prime number graph", Math. Comp. 33, 399–408.
  - Chebyshev (1852): elementary bounds on π via central binomial coefficients.
  - Mathlib: `Nat.centralBinom`, `Nat.four_pow_lt_mul_centralBinom`,
    `Nat.pow_factorization_choose_le`, `Nat.nth`, `Real.isLittleO_log_id_atTop`.
-/

import Mathlib

open Nat Real Filter Finset
open scoped Nat.Prime BigOperators Topology

namespace Erdos453OQ02OQ01

/-!
## Part I: The prime sequence (axiom-free)

`p_n` is the n-th prime, 1-indexed (`p_1 = 2, p_2 = 3, …`). As in the parent files we set
`nthPrime n = Nat.nth Nat.Prime (n-1)` for `n ≥ 1`.
-/

/-- The n-th prime (1-indexed): `nthPrime 1 = 2`, `nthPrime 2 = 3`, … -/
noncomputable def nthPrime (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.nth Nat.Prime (n - 1)

/-- `p_n` is prime for `n ≥ 1` (proved, not axiomatized). -/
theorem nthPrime_is_prime (n : ℕ) (hn : n ≥ 1) : (nthPrime n).Prime := by
  unfold nthPrime
  rw [if_neg (by omega)]
  exact Nat.prime_nth_prime (n - 1)

/-!
## Part II: A Chebyshev lower bound for `π`, from the central binomial coefficient

The classical elementary estimate `π(x) ≳ x / log x`, in the explicit packaged form
`4^n < n · (2n)^{π(2n)}`, followed by its inversion into an upper bound on the n-th prime.
-/

/-- The `n`-th central binomial coefficient is at most `(2n)^{π(2n)}`: each prime power
dividing it is `≤ 2n`, and the number of distinct prime divisors is at most `π(2n)`. -/
theorem centralBinom_le_pow_primeCounting (n : ℕ) :
    n.centralBinom ≤ (2 * n) ^ (Nat.primeCounting (2 * n)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; norm_num [Nat.centralBinom, Nat.primeCounting_zero]
  have h2n : 0 < 2 * n := by omega
  have hne : n.centralBinom ≠ 0 := (Nat.centralBinom_pos n).ne'
  set S := (n.centralBinom).factorization.support with hS
  -- every prime in the support is `≤ 2n`, so `S ⊆ {primes < 2n+1}`
  have hsub : S ⊆ (Finset.range (2 * n + 1)).filter Nat.Prime := by
    intro p hp
    rw [hS, Nat.support_factorization, Nat.mem_primeFactors] at hp
    obtain ⟨hpprime, hpdvd, hcbne⟩ := hp
    have hpos : 0 < (n.centralBinom).factorization p :=
      hpprime.factorization_pos_of_dvd hcbne hpdvd
    have hple : p ≤ 2 * n := Nat.le_two_mul_of_factorization_centralBinom_pos hpos
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hpprime⟩
  -- hence `|S| ≤ π(2n)`
  have hcard : S.card ≤ Nat.primeCounting (2 * n) := by
    refine (Finset.card_le_card hsub).trans ?_
    rw [← Nat.count_eq_card_filter_range]
    have heq : Nat.primeCounting (2 * n) = Nat.count Nat.Prime (2 * n + 1) := by
      simp only [Nat.primeCounting, Nat.primeCounting']
    rw [heq]
  -- bound the product term by term, then by the cardinality
  calc n.centralBinom
      = n.centralBinom.factorization.prod (· ^ ·) := (Nat.factorization_prod_pow_eq_self hne).symm
    _ = ∏ p ∈ S, p ^ (n.centralBinom.factorization p) := by rw [Finsupp.prod]
    _ ≤ ∏ _p ∈ S, (2 * n) := by
        apply Finset.prod_le_prod'
        intro p _
        exact Nat.pow_factorization_choose_le h2n
    _ = (2 * n) ^ S.card := by rw [Finset.prod_const]
    _ ≤ (2 * n) ^ (Nat.primeCounting (2 * n)) := Nat.pow_le_pow_right h2n hcard

/-- **Chebyshev lower bound (packaged).** For `n ≥ 4`, `4^n < n · (2n)^{π(2n)}`.
Equivalently `π(2n) > (n log 4 − log n) / log(2n) ≳ n / log n`. -/
theorem four_pow_lt_mul_pow_primeCounting (n : ℕ) (hn : 4 ≤ n) :
    4 ^ n < n * (2 * n) ^ (Nat.primeCounting (2 * n)) :=
  lt_of_lt_of_le (Nat.four_pow_lt_mul_centralBinom n hn)
    (Nat.mul_le_mul_left n (centralBinom_le_pow_primeCounting n))

/-- **Inversion.** If `n ≥ 4` and the explicit inequality `n·(2n)^k ≤ 4^n` holds, then the
`k`-th prime (0-indexed) is at most `2n`. (Such an `n` exists with `2n` polynomial in `k`,
which is all we need below.) -/
theorem nth_prime_le_two_mul (k n : ℕ) (hn : 4 ≤ n)
    (hineq : n * (2 * n) ^ k ≤ 4 ^ n) :
    Nat.nth Nat.Prime k ≤ 2 * n := by
  -- the Chebyshev bound forces `π(2n) > k`
  have hk : k < Nat.primeCounting (2 * n) := by
    by_contra hcon
    push_neg at hcon
    have hmono : n * (2 * n) ^ (Nat.primeCounting (2 * n)) ≤ n * (2 * n) ^ k :=
      Nat.mul_le_mul_left n (Nat.pow_le_pow_right (by omega) hcon)
    have := four_pow_lt_mul_pow_primeCounting n hn
    omega
  -- and `π(2n) = #{primes ≤ 2n}`, so `nth Prime k < 2n+1`
  have heq : Nat.primeCounting (2 * n) = Nat.count Nat.Prime (2 * n + 1) := by
    simp only [Nat.primeCounting, Nat.primeCounting']
  rw [heq] at hk
  have := Nat.nth_lt_of_lt_count hk
  omega

/-- The explicit `ℕ` inequality that lets us take `n = (k+1)^3` in `nth_prime_le_two_mul`.
For `k ≥ 1`, `(k+1)^3 · (2(k+1)^3)^k ≤ 4^{(k+1)^3}`. Both sides reduce to powers of `2`;
the estimate `k+1 ≤ 2^{k+1}` closes the gap. -/
theorem nat_pow_ineq (k : ℕ) (hk : 1 ≤ k) :
    (k + 1) ^ 3 * (2 * (k + 1) ^ 3) ^ k ≤ 4 ^ ((k + 1) ^ 3) := by
  -- LHS = 2^k · (k+1)^(3k+3)
  have eLHS : (k + 1) ^ 3 * (2 * (k + 1) ^ 3) ^ k = 2 ^ k * (k + 1) ^ (3 * k + 3) := by
    rw [mul_pow, ← pow_mul, mul_comm ((k + 1) ^ 3) (2 ^ k * (k + 1) ^ (3 * k)),
      mul_assoc, ← pow_add]
  -- (k+1)^(3k+3) ≤ 2^(3(k+1)^2)
  have hb : (k + 1) ^ (3 * k + 3) ≤ 2 ^ (3 * (k + 1) ^ 2) := by
    calc (k + 1) ^ (3 * k + 3)
        ≤ (2 ^ (k + 1)) ^ (3 * k + 3) :=
          Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self)) _
      _ = 2 ^ ((k + 1) * (3 * k + 3)) := by rw [← pow_mul]
      _ = 2 ^ (3 * (k + 1) ^ 2) := by congr 1; ring
  -- RHS = 2^(2(k+1)^3)
  have eRHS : (4 : ℕ) ^ ((k + 1) ^ 3) = 2 ^ (2 * (k + 1) ^ 3) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
  rw [eLHS, eRHS]
  calc 2 ^ k * (k + 1) ^ (3 * k + 3)
      ≤ 2 ^ k * 2 ^ (3 * (k + 1) ^ 2) := Nat.mul_le_mul_left _ hb
    _ = 2 ^ (k + 3 * (k + 1) ^ 2) := by rw [← pow_add]
    _ ≤ 2 ^ (2 * (k + 1) ^ 3) := by
        apply Nat.pow_le_pow_right (by norm_num)
        nlinarith [hk]

/-- **Explicit prime upper bound.** For `k ≥ 1`, the `k`-th prime (0-indexed) satisfies
`nth Prime k ≤ 2(k+1)^3`. (The truth is `~ k log k`; the cubic bound is deliberately loose
but elementary and entirely sufficient for the asymptotics below.) -/
theorem nth_prime_le_cube (k : ℕ) (hk : 1 ≤ k) :
    Nat.nth Nat.Prime k ≤ 2 * (k + 1) ^ 3 := by
  refine nth_prime_le_two_mul k ((k + 1) ^ 3) ?_ (nat_pow_ineq k hk)
  calc (4 : ℕ) ≤ 2 ^ 3 := by norm_num
    _ ≤ (k + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3

/-- 1-indexed restatement: for `n ≥ 2`, `p_n ≤ 2 n^3`. -/
theorem nthPrime_le_cube {n : ℕ} (hn : 2 ≤ n) : nthPrime n ≤ 2 * n ^ 3 := by
  unfold nthPrime
  rw [if_neg (by omega)]
  have hk : 1 ≤ n - 1 := by omega
  have hb := nth_prime_le_cube (n - 1) hk
  have he : (n - 1) + 1 = n := by omega
  rwa [he] at hb

/-!
## Part III: `log p_n / n → 0` (the eliminated axiom)
-/

/-- The log-prime function `a_n = log p_n`, exactly as in the parent files. -/
noncomputable def logPrime (n : ℕ) : ℝ :=
  Real.log (nthPrime n)

/-- The upper envelope `log(2 n^3) / n → 0`, the squeeze majorant. -/
theorem upper_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (2 * (n : ℝ) ^ 3) / n) atTop (𝓝 0) := by
  -- `log n / n → 0` (Mathlib) and `log 2 / n → 0`, then split `log(2 n^3) = log 2 + 3 log n`
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun n : ℕ => Real.log 2 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
  have hsum : Tendsto
      (fun n : ℕ => Real.log 2 / (n : ℝ) + 3 * (Real.log (n : ℝ) / (n : ℝ)))
      atTop (𝓝 0) := by
    have := hconst.add (hlog.const_mul 3)
    simpa using this
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  field_simp
  ring

/-- **Axiom eliminated.** `log p_n / n → 0`, where `p_n` is the 1-indexed `n`-th prime.

This is the PNT consequence that the parent file `Erdos453OQ02.lean` axiomatized as
`logPrime_ratio_tendsto_zero`. It is proved here purely from the elementary Chebyshev lower
bound (via the central binomial coefficient), with no appeal to the full Prime Number
Theorem. -/
theorem logPrime_ratio_tendsto_zero :
    Tendsto (fun n => logPrime n / n) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ upper_tendsto_zero
  · -- `0 ≤ log p_n / n` eventually (in fact `p_n ≥ 2`, so `log p_n ≥ 0`)
    filter_upwards [eventually_ge_atTop 2] with n hn
    apply div_nonneg _ (by positivity)
    unfold logPrime
    apply Real.log_nonneg
    unfold nthPrime
    rw [if_neg (by omega)]
    have : Nat.Prime (Nat.nth Nat.Prime (n - 1)) := Nat.prime_nth_prime (n - 1)
    exact_mod_cast this.one_lt.le
  · -- `log p_n / n ≤ log(2 n^3) / n` eventually
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hle : logPrime n ≤ Real.log (2 * (n : ℝ) ^ 3) := by
      unfold logPrime
      apply Real.log_le_log
      · have : Nat.Prime (nthPrime n) := by
          unfold nthPrime; rw [if_neg (by omega)]; exact Nat.prime_nth_prime (n - 1)
        exact_mod_cast this.pos
      · have hb := nthPrime_le_cube hn
        have : ((nthPrime n : ℕ) : ℝ) ≤ ((2 * n ^ 3 : ℕ) : ℝ) := by exact_mod_cast hb
        push_cast at this ⊢
        linarith
    gcongr

/-!
## Part IV: The one remaining axiom (Pomerance's geometric lemma)

The PNT-consequence axiom is gone. What remains is the genuine mathematical core of
Pomerance's 1979 argument: a sublinear discrete curve has infinitely many upper convex-hull
vertices. Formalizing this requires discrete convex-hull theory not yet in Mathlib, so it
stays as the single remaining axiom.
-/

/-- `(n, a_n)` is an upper convex-hull vertex if `2 a_n > a_{n-i} + a_{n+i}` for all `0 < i < n`. -/
def IsConvexHullVertex (a : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ i : ℕ, 0 < i → i < n → 2 * a n > a (n - i) + a (n + i)

/-- **Axiom (Pomerance's key lemma).** Any sequence with `a_n = o(n)` has infinitely many
upper convex-hull vertices. The deep geometric result from Pomerance (1979); a full proof
needs discrete convex-hull theory for `ℕ → ℝ` sequences, not yet available in Mathlib. -/
axiom pomerance_convex_hull_lemma (a : ℕ → ℝ)
    (h : Filter.Tendsto (fun n => a n / n) Filter.atTop (nhds 0)) :
    ∀ N : ℕ, ∃ n ≥ N, IsConvexHullVertex a n

/-!
## Part V: Re-deriving Pomerance's theorem with a single axiom
-/

/-- If `(n, log p_n)` is an upper convex-hull vertex then `p_n² > p_{n-i}·p_{n+i}` for all `i`. -/
theorem convexity_implies_product_bound (n : ℕ) (hn : n ≥ 2)
    (hv : IsConvexHullVertex logPrime n) :
    ∀ i : ℕ, 0 < i → i < n →
      (nthPrime n : ℤ) ^ 2 > (nthPrime (n + i) : ℤ) * (nthPrime (n - i) : ℤ) := by
  intro i hi_pos hi_lt
  have hvi := hv i hi_pos hi_lt
  unfold logPrime at hvi
  have hp_n : (0 : ℝ) < nthPrime n :=
    Nat.cast_pos.mpr (Nat.Prime.pos (nthPrime_is_prime n (by omega)))
  have hp_ni : (0 : ℝ) < nthPrime (n - i) :=
    Nat.cast_pos.mpr (Nat.Prime.pos (nthPrime_is_prime (n - i) (by omega)))
  have hp_pi : (0 : ℝ) < nthPrime (n + i) :=
    Nat.cast_pos.mpr (Nat.Prime.pos (nthPrime_is_prime (n + i) (by omega)))
  have h_log : Real.log ((nthPrime (n - i) : ℝ) * nthPrime (n + i)) <
      Real.log ((nthPrime n : ℝ) ^ 2) := by
    calc Real.log ((nthPrime (n - i) : ℝ) * nthPrime (n + i))
        = Real.log (nthPrime (n - i)) + Real.log (nthPrime (n + i)) :=
          Real.log_mul (ne_of_gt hp_ni) (ne_of_gt hp_pi)
      _ < 2 * Real.log (nthPrime n) := by linarith
      _ = Real.log ((nthPrime n : ℝ) ^ 2) := by rw [Real.log_pow]; ring
  have h_real : (nthPrime (n - i) : ℝ) * nthPrime (n + i) < (nthPrime n : ℝ) ^ 2 :=
    (Real.log_lt_log_iff (mul_pos hp_ni hp_pi) (pow_pos hp_n 2)).mp h_log
  exact_mod_cast show nthPrime n ^ 2 > nthPrime (n + i) * nthPrime (n - i) by
    calc nthPrime n ^ 2
        > nthPrime (n - i) * nthPrime (n + i) := by exact_mod_cast h_real
      _ = nthPrime (n + i) * nthPrime (n - i) := Nat.mul_comm _ _

/-- **Pomerance (1979), with a single axiom.** There are infinitely many `n` such that
`p_n² > p_{n+i}·p_{n-i}` for all `0 < i < n`. Now depends only on
`pomerance_convex_hull_lemma`; the PNT-consequence axiom has been discharged. -/
theorem pomerance_1979 :
    ∀ N : ℕ, ∃ n ≥ N,
      ∀ i : ℕ, 0 < i → i < n →
        (nthPrime n : ℤ) ^ 2 > (nthPrime (n + i) : ℤ) * (nthPrime (n - i) : ℤ) := by
  intro N
  obtain ⟨n, hn, hv⟩ :=
    pomerance_convex_hull_lemma logPrime logPrime_ratio_tendsto_zero (max N 2)
  refine ⟨n, by omega, ?_⟩
  exact convexity_implies_product_bound n (by omega) hv

/-- **Consecutive-primes corollary (`i = 1`).** Infinitely many `n ≥ 2` with
`p_n² > p_{n-1}·p_{n+1}`. -/
theorem pomerance_consecutive_primes :
    ∀ N : ℕ, ∃ n ≥ max N 2,
      (nthPrime n : ℤ) ^ 2 > (nthPrime (n + 1) : ℤ) * (nthPrime (n - 1) : ℤ) := by
  intro N
  obtain ⟨n, hn_ge, hn_main⟩ := pomerance_1979 (max N 2)
  refine ⟨n, hn_ge, ?_⟩
  have hn2 : n ≥ 2 := le_trans (le_max_right N 2) hn_ge
  exact hn_main 1 (by omega) (by omega)

/-!
## Part VI: Summary of axiom elimination

| File                  | axioms | sorries |
|-----------------------|--------|---------|
| Erdos453Problem.lean  |   4    |   1     |
| Erdos453OQ02.lean     |   2    |   0     |
| Erdos453OQ02OQ01.lean |   1    |   0     |   ← this file

Eliminated here: `logPrime_ratio_tendsto_zero` (PNT consequence), proved from the
elementary Chebyshev lower bound `π(2n) ≳ n/log n` via the central binomial coefficient.

Remaining axiom: `pomerance_convex_hull_lemma` — the discrete convex-hull lemma that is the
true geometric heart of Pomerance's proof.
-/

theorem axiom_elimination_summary :
    ∀ N : ℕ, ∃ n ≥ N,
      ∀ i : ℕ, 0 < i → i < n →
        (nthPrime n : ℤ) ^ 2 > (nthPrime (n + i) : ℤ) * (nthPrime (n - i) : ℤ) :=
  pomerance_1979

end Erdos453OQ02OQ01
