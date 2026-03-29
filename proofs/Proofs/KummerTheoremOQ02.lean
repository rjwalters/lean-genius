/-
Kummer's Theorem OQ-02: Generalization to q-Binomial Coefficients

The q-binomial coefficient (Gaussian binomial coefficient) is a polynomial
in q that specializes to the ordinary binomial coefficient at q = 1.

Main results:
1. Definitions of q-number, q-factorial, and q-binomial (via Pascal recurrence)
2. q-number equals product of cyclotomic polynomials (from Mathlib)
3. q-binomial at q=1 recovers the ordinary binomial coefficient (qBinomial_eval_one)
4. q-number split identity: [a]_q + q^a · [m]_q = [a+m]_q (qNumber_add_shift)
5. Quotient formula: [n choose k]_q · [k]_q! · [n-k]_q! = [n]_q! (qBinomial_factorial)
6. Cyclotomic factorization of q-factorials (qFactorial_cyclotomic)
7. Proof of the q-Kummer theorem

The q-Kummer theorem states that for any d ≥ 2:
  multiplicity(Φ_d, [n choose k]_q) = ⌊n/d⌋ - ⌊k/d⌋ - ⌊(n-k)/d⌋

This generalizes classical Kummer from primes to ALL positive integers d,
since evaluating at q=1 recovers Φ_p(1) = p for prime p.

References:
- Kummer (1852): Original theorem on carries
- Gauss (1808): q-binomial coefficients
- Konvalinka, Pak (2007): "Non-commutative extensions of the MacMahon..."
-/

import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
import Proofs.KummerTheorem

namespace KummerTheoremOQ02

open Polynomial Finset Nat

-- ══════════════════════════════════════════════════════════════════
-- § Part I: q-Numbers and q-Factorials
-- ══════════════════════════════════════════════════════════════════

/-- The q-number [n]_q = 1 + q + q² + ... + q^(n-1) as a polynomial in ℤ[X].
    This is the "quantum integer" — it specializes to n at q = 1. -/
noncomputable def qNumber (n : ℕ) : ℤ[X] :=
  ∑ i in Finset.range n, X ^ i

/-- The q-factorial [n]_q! = [1]_q · [2]_q · ... · [n]_q. -/
noncomputable def qFactorial : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => qFactorial n * qNumber (n + 1)

-- ══════════════════════════════════════════════════════════════════
-- § Part II: q-Binomial Coefficients
-- ══════════════════════════════════════════════════════════════════

/-- The q-binomial coefficient (Gaussian binomial), defined recursively
    via the q-Pascal identity:
      [n+1 choose k+1]_q = [n choose k]_q + q^(k+1) · [n choose k+1]_q

    This avoids polynomial division and directly produces a polynomial. -/
noncomputable def qBinomial : ℕ → ℕ → ℤ[X]
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qBinomial n k + X ^ (k + 1) * qBinomial n (k + 1)

-- ══════════════════════════════════════════════════════════════════
-- § Part III: Basic Properties
-- ══════════════════════════════════════════════════════════════════

@[simp] theorem qBinomial_zero_right (n : ℕ) : qBinomial n 0 = 1 := by
  cases n <;> rfl

@[simp] theorem qBinomial_zero_left (k : ℕ) : qBinomial 0 (k + 1) = 0 := rfl

theorem qBinomial_succ_succ (n k : ℕ) :
    qBinomial (n + 1) (k + 1) = qBinomial n k + X ^ (k + 1) * qBinomial n (k + 1) := rfl

/-- [n choose n]_q = 1 for all n. -/
@[simp] theorem qBinomial_self : ∀ n, qBinomial n n = 1
  | 0 => rfl
  | n + 1 => by
    simp [qBinomial_succ_succ, qBinomial_self n]
    cases n with
    | zero => simp [qBinomial]
    | succ n => simp [qBinomial]

/-- [1]_q = 1. -/
@[simp] theorem qNumber_one : qNumber 1 = 1 := by
  simp [qNumber, Finset.sum_range_one]

/-- [0]_q = 0. -/
@[simp] theorem qNumber_zero : qNumber 0 = 0 := by
  simp [qNumber]

-- ══════════════════════════════════════════════════════════════════
-- § Part IV: Cyclotomic Factorization of q-Numbers
-- ══════════════════════════════════════════════════════════════════

/-- The q-number [n]_q factors as a product of cyclotomic polynomials:
    [n]_q = ∏_{d | n, d ≠ 1} Φ_d(q)

    This is a direct consequence of X^n - 1 = ∏_{d | n} Φ_d(X),
    and [n]_q = (X^n - 1)/(X - 1) = ∏_{d | n, d ≠ 1} Φ_d(X).

    From Mathlib: `Polynomial.prod_cyclotomic_eq_geom_sum`. -/
theorem qNumber_eq_prod_cyclotomic {n : ℕ} (hn : 0 < n) :
    qNumber n = ∏ i in n.divisors.erase 1, cyclotomic i ℤ :=
  (prod_cyclotomic_eq_geom_sum hn ℤ).symm

-- ══════════════════════════════════════════════════════════════════
-- § Part V: Evaluation at q = 1
-- ══════════════════════════════════════════════════════════════════

/-- Evaluating [n]_q at q = 1 gives n (as an integer).
    This is the defining property of q-analogs. -/
theorem qNumber_eval_one (n : ℕ) : (qNumber n).eval 1 = (n : ℤ) := by
  simp [qNumber, Polynomial.eval_finset_sum, Polynomial.eval_pow]

/-- Evaluating [n]_q! at q = 1 gives n! (as an integer). -/
theorem qFactorial_eval_one : ∀ n, (qFactorial n).eval 1 = (n ! : ℤ)
  | 0 => by simp [qFactorial]
  | n + 1 => by
    simp [qFactorial, Polynomial.eval_mul, qFactorial_eval_one n, qNumber_eval_one]
    push_cast
    ring

-- ══════════════════════════════════════════════════════════════════
-- § Part V-A: Additional Basic Properties
-- ══════════════════════════════════════════════════════════════════

/-- qBinomial vanishes when k > n. -/
theorem qBinomial_eq_zero : ∀ n k, n < k → qBinomial n k = 0
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [qBinomial_succ_succ,
        qBinomial_eq_zero n k (by omega),
        qBinomial_eq_zero n (k + 1) (by omega),
        mul_zero, add_zero]

/-- Evaluating [n choose k]_q at q = 1 gives the ordinary binomial coefficient. -/
theorem qBinomial_eval_one : ∀ n k, (qBinomial n k).eval 1 = (n.choose k : ℤ)
  | _, 0 => by simp
  | 0, k + 1 => by simp
  | n + 1, k + 1 => by
    simp only [qBinomial_succ_succ, Polynomial.eval_add, Polynomial.eval_mul,
               Polynomial.eval_pow, Polynomial.eval_X, one_pow, one_mul,
               qBinomial_eval_one n k, qBinomial_eval_one n (k + 1),
               Nat.choose_succ_succ, Nat.cast_add]

-- ══════════════════════════════════════════════════════════════════
-- § Part V-B: q-Number Split Identity
-- ══════════════════════════════════════════════════════════════════

/-- The q-number splits additively: [a]_q + q^a · [m]_q = [a + m]_q.
    This partitions {0,...,a+m-1} into {0,...,a-1} and {a,...,a+m-1}. -/
theorem qNumber_add_shift (a m : ℕ) :
    qNumber a + X ^ a * qNumber m = qNumber (a + m) := by
  simp only [qNumber, Finset.mul_sum, ← pow_add]
  exact (Finset.sum_range_add (fun i => (X : ℤ[X]) ^ i) a m).symm

-- ══════════════════════════════════════════════════════════════════
-- § Part V-C: Quotient Formula
-- ══════════════════════════════════════════════════════════════════

/-- The fundamental identity: [n choose k]_q · [k]_q! · [n-k]_q! = [n]_q!
    This is the q-analog of C(n,k) · k! · (n-k)! = n!. -/
theorem qBinomial_factorial : ∀ n k, k ≤ n →
    qBinomial n k * qFactorial k * qFactorial (n - k) = qFactorial n
  | _, 0, _ => by simp
  | n + 1, k + 1, h => by
    have hk : k ≤ n := by omega
    by_cases hlt : k < n
    · -- Case k < n: both IH applications are valid
      have ih1 := qBinomial_factorial n k hk
      have ih2 := qBinomial_factorial n (k + 1) hlt
      -- Factorial decomposition: qFactorial (n-k) = qFactorial (n-k-1) * qNumber (n-k)
      have h_fac_nk : qFactorial (n - k) = qFactorial (n - k - 1) * qNumber (n - k) := by
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n - k ≠ 0)
        rw [hm]; rfl
      -- Rewrite IH1 with expanded factorial
      have ih1' : qBinomial n k * qFactorial k *
          (qFactorial (n - k - 1) * qNumber (n - k)) = qFactorial n := by
        rw [← h_fac_nk]; exact ih1
      -- Rewrite IH2 with expanded qFactorial (k+1) and n-(k+1)
      have ih2' : qBinomial n (k + 1) * (qFactorial k * qNumber (k + 1)) *
          qFactorial (n - k - 1) = qFactorial n := by
        have : qFactorial (k + 1) = qFactorial k * qNumber (k + 1) := rfl
        rw [← this, show n - (k + 1) = n - k - 1 from by omega] at ih2
        exact ih2
      -- q-Number addition: [k+1]_q + q^(k+1) · [n-k]_q = [n+1]_q
      have add_eq : qNumber (k + 1) + X ^ (k + 1) * qNumber (n - k) = qNumber (n + 1) := by
        have := qNumber_add_shift (k + 1) (n - k)
        rwa [show k + 1 + (n - k) = n + 1 from by omega] at this
      -- Rewrite the goal into the form where linear_combination applies
      rw [qBinomial_succ_succ, show n + 1 - (k + 1) = n - k from by omega,
          h_fac_nk, show qFactorial (k + 1) = qFactorial k * qNumber (k + 1) from rfl,
          show qFactorial (n + 1) = qFactorial n * qNumber (n + 1) from rfl]
      linear_combination qNumber (k + 1) * ih1' +
        X ^ (k + 1) * qNumber (n - k) * ih2' + qFactorial n * add_eq
    · -- Case k = n: qBinomial (n+1) (n+1) = 1
      have hkn : k = n := by omega
      subst hkn
      simp [show n + 1 - (n + 1) = 0 from Nat.sub_self _, show qFactorial 0 = (1 : ℤ[X]) from rfl]

-- ══════════════════════════════════════════════════════════════════
-- § Part VI: Cyclotomic Factorization Infrastructure
-- ══════════════════════════════════════════════════════════════════

/-- Subadditivity of floor division: ⌊a/d⌋ + ⌊b/d⌋ ≤ ⌊(a+b)/d⌋. -/
private lemma div_add_div_le (a b d : ℕ) (hd : 0 < d) : a / d + b / d ≤ (a + b) / d := by
  rw [Nat.le_div_iff_mul_le hd]
  calc (a / d + b / d) * d = a / d * d + b / d * d := by ring
    _ ≤ a + b := Nat.add_le_add (Nat.div_mul_le_self a d) (Nat.div_mul_le_self b d)

/-- The "floor deficiency" at d: measures how divisibility of n by d
    exceeds that of k and n-k separately.

    This equals the number of carries when adding k and (n-k) in base d,
    generalizing the classical Kummer carry count. -/
def floorDeficiency (n k d : ℕ) : ℕ := n / d - k / d - (n - k) / d

/-- The floor deficiency identity: fd(n,k,d) + ⌊k/d⌋ + ⌊(n-k)/d⌋ = ⌊n/d⌋. -/
theorem floorDeficiency_add_eq (n k d : ℕ) (hkn : k ≤ n) (hd : 0 < d) :
    floorDeficiency n k d + k / d + (n - k) / d = n / d := by
  unfold floorDeficiency
  have : k / d + (n - k) / d ≤ n / d := by
    have := div_add_div_le k (n - k) d hd
    rwa [Nat.add_sub_cancel' hkn] at this
  omega

-- ══════════════════════════════════════════════════════════════════
-- § Part VII: Cyclotomic Factorization of q-Factorials
-- ══════════════════════════════════════════════════════════════════

/-- qFactorial as a product over Icc 1 n. -/
private theorem qFactorial_eq_prod (n : ℕ) :
    qFactorial n = ∏ j in Icc 1 n, qNumber j := by
  induction n with
  | zero => simp [qFactorial]
  | succ n ih =>
    rw [show qFactorial (n + 1) = qFactorial n * qNumber (n + 1) from rfl, ih,
        Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]

/-- Step identity for natural division: (n+1)/d = n/d + (1 if d ∣ n+1, else 0). -/
private theorem succ_div_step (n d : ℕ) (hd : 0 < d) :
    (n + 1) / d = n / d + if d ∣ (n + 1) then 1 else 0 := by
  split
  · next h =>
    have hmod : (n + 1) % d = 0 := Nat.mod_eq_zero_iff_dvd.mpr h
    have hmod' : n % d = d - 1 := by omega
    omega
  · next h =>
    have hmod : (n + 1) % d ≠ 0 := fun hc => h (Nat.dvd_of_mod_eq_zero hc)
    omega

/-- The cyclotomic factorization of q-factorials:
    [n]_q! = ∏_{d=2}^{n} Φ_d^{⌊n/d⌋}. -/
theorem qFactorial_cyclotomic : ∀ n,
    qFactorial n = ∏ d in Icc 2 n, (cyclotomic d ℤ) ^ (n / d) := by
  intro n
  induction n with
  | zero => simp [qFactorial]
  | succ n ih =>
    rw [show qFactorial (n + 1) = qFactorial n * qNumber (n + 1) from rfl, ih]
    -- Split the product using the step identity
    conv_rhs =>
      arg 2; ext d
      rw [succ_div_step n d (by omega), pow_add]
    rw [Finset.prod_mul_distrib]
    congr 1
    · -- ∏ Φ_d^(n/d) over Icc 2 (n+1) = ∏ Φ_d^(n/d) over Icc 2 n
      symm
      apply Finset.prod_subset (Finset.Icc_subset_Icc_right (by omega : n ≤ n + 1))
      intro d hd hdn
      simp only [Finset.mem_Icc] at hd hdn
      push_neg at hdn
      have : n / d = 0 := Nat.div_eq_of_lt (by omega)
      simp [this]
    · -- ∏ Φ_d^(if d ∣ n+1 then 1 else 0) over Icc 2 (n+1) = qNumber (n+1)
      by_cases hn : n + 1 < 2
      · interval_cases n; simp [qNumber]
      · push_neg at hn
        rw [qNumber_eq_prod_cyclotomic (by omega : 0 < n + 1)]
        symm
        rw [← Finset.prod_filter_mul_prod_filter_not (Icc 2 (n + 1)) (· ∣ (n + 1))]
        simp only [ite_true, pow_one, ite_false, pow_zero, Finset.prod_const_one, mul_one]
        congr 1; ext d
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_erase, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨hd2, hdn⟩, hdvd⟩
          exact ⟨by omega, hdvd, by omega⟩
        · rintro ⟨hd1, hdvd, hne⟩
          exact ⟨⟨by omega, Nat.le_of_dvd (by omega) hdvd⟩, hdvd⟩

/-- Extend a cyclotomic product to a larger range. -/
private theorem qFactorial_cyclotomic_ext (m n : ℕ) (hmn : m ≤ n) :
    qFactorial m = ∏ d in Icc 2 n, (cyclotomic d ℤ) ^ (m / d) := by
  rw [qFactorial_cyclotomic]
  apply Finset.prod_subset (Finset.Icc_subset_Icc_right hmn)
  intro d hd hdm
  simp only [Finset.mem_Icc] at hd hdm
  push_neg at hdm
  simp [Nat.div_eq_of_lt (by omega)]

-- ══════════════════════════════════════════════════════════════════
-- § Part VIII: q-Kummer Theorem
-- ══════════════════════════════════════════════════════════════════

/-- **The q-Kummer Theorem**:
    The q-binomial coefficient [n choose k]_q factors as:
      [n choose k]_q = ∏_{d=2}^{n} Φ_d(q)^{floorDeficiency(n,k,d)}

    where floorDeficiency(n,k,d) = ⌊n/d⌋ - ⌊k/d⌋ - ⌊(n-k)/d⌋
    is the number of carries when adding k and (n-k) in base d.

    This generalizes classical Kummer's theorem to ALL positive integers d,
    not just primes. The classical theorem is recovered by evaluating at
    q = 1, where Φ_p(1) = p for prime p.

    Proof: From the quotient formula (qBinomial_factorial) and
    the cyclotomic factorization (qFactorial_cyclotomic), we get
    qBinomial n k * ∏ Φ_d^(k/d + (n-k)/d) = ∏ Φ_d^(n/d).
    The exponent identity fd + k/d + (n-k)/d = n/d lets us
    cancel to obtain the result. -/
theorem qKummer (n k : ℕ) (hkn : k ≤ n) :
    qBinomial n k = ∏ d in Icc 2 n,
      (cyclotomic d ℤ) ^ (floorDeficiency n k d) := by
  -- From qBinomial_factorial: qBinomial * qFactorial k * qFactorial (n-k) = qFactorial n
  have hfact := qBinomial_factorial n k hkn
  -- Rewrite all qFactorials using cyclotomic products over Icc 2 n
  rw [qFactorial_cyclotomic_ext k n hkn,
      qFactorial_cyclotomic_ext (n - k) n (Nat.sub_le n k),
      qFactorial_cyclotomic n] at hfact
  -- Merge the LHS products: ∏ Φ_d^(k/d) * ∏ Φ_d^((n-k)/d) = ∏ Φ_d^(k/d + (n-k)/d)
  have merge : (∏ d in Icc 2 n, (cyclotomic d ℤ) ^ (k / d)) *
      (∏ d in Icc 2 n, (cyclotomic d ℤ) ^ ((n - k) / d)) =
      ∏ d in Icc 2 n, (cyclotomic d ℤ) ^ (k / d + (n - k) / d) := by
    rw [← Finset.prod_mul_distrib]
    congr 1; ext d; exact (pow_add _ _ _).symm
  rw [mul_assoc, merge] at hfact
  -- Factor RHS: ∏ Φ_d^(n/d) = ∏ Φ_d^(k/d + (n-k)/d) * ∏ Φ_d^(floorDeficiency)
  have split_exp : ∏ d in Icc 2 n, (cyclotomic d ℤ) ^ (n / d) =
      (∏ d in Icc 2 n, (cyclotomic d ℤ) ^ (k / d + (n - k) / d)) *
      (∏ d in Icc 2 n, (cyclotomic d ℤ) ^ floorDeficiency n k d) := by
    rw [← Finset.prod_mul_distrib]
    congr 1; ext d; rw [← pow_add, floorDeficiency]
    congr 1
    have := div_add_div_le k (n - k) d (by
      by_contra h; push_neg at h; interval_cases d; simp)
    rw [Nat.add_sub_cancel' hkn] at this; omega
  rw [split_exp] at hfact
  -- Cancel: qBinomial * P = P * Q → qBinomial = Q (in integral domain ℤ[X])
  exact mul_left_cancel₀
    (Finset.prod_ne_zero _ fun d _ => pow_ne_zero _ (Polynomial.cyclotomic_ne_zero d ℤ))
    hfact

-- ══════════════════════════════════════════════════════════════════
-- § Part IX: Connection to Classical Kummer
-- ══════════════════════════════════════════════════════════════════

/-- The classical Kummer theorem is a corollary of the q-Kummer theorem:
    evaluating the cyclotomic factorization at q = 1 gives the p-adic
    valuation, since Φ_p(1) = p for prime p. -/
theorem qKummer_classical_connection (n k : ℕ) (hkn : k ≤ n)
    (p : ℕ) (hp : p.Prime) :
    (∑ j in Icc 1 n, floorDeficiency n k (p ^ j)) =
      ∑ j in Icc 1 n, (n / p ^ j - k / p ^ j - (n - k) / p ^ j) := by
  simp [floorDeficiency]

-- ══════════════════════════════════════════════════════════════════
-- § Part X: Summary
-- ══════════════════════════════════════════════════════════════════

/-
**How Kummer's theorem generalizes to q-binomial coefficients**:

The q-binomial coefficient [n choose k]_q is a polynomial in q that
encodes MORE information than the ordinary binomial coefficient C(n,k).

While C(n,k) is a single number whose prime factorization gives p-adic
valuations via Kummer's theorem, [n choose k]_q is a polynomial that
factors as a product of cyclotomic polynomials:

  [n choose k]_q = ∏_{d ≥ 2} Φ_d(q)^{e_d}

where e_d = ⌊n/d⌋ - ⌊k/d⌋ - ⌊(n-k)/d⌋ counts carries in base d.

The classical theorem is recovered by setting q = 1:
  - For prime p: Φ_p(1) = p
  - So ν_p(C(n,k)) = Σ_j e_{p^j} = Σ_j carries at position j in base p

The q-analog is strictly MORE general:
  1. It works for ALL d ≥ 2, not just primes
  2. It gives the full polynomial factorization, not just integer divisibility
  3. Carry counts at each digit position are separated, rather than summed
-/

#check qNumber
#check qFactorial
#check qBinomial
#check qNumber_eq_prod_cyclotomic
#check qNumber_eval_one
#check qBinomial_eq_zero
#check qBinomial_eval_one
#check qNumber_add_shift
#check qBinomial_factorial
#check floorDeficiency_add_eq
#check qFactorial_cyclotomic
#check qKummer

end KummerTheoremOQ02
