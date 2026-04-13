import Mathlib

/-
# Factorization Bound: p^{v_p(C(2n,n))} ≤ 2n

## Research Problem: chebyshev-pnt-bridge-oq-01

Proves that for any prime p and any n ≥ 1:
  p^{v_p(C(2n,n))} ≤ 2n

This is a key ingredient in Chebyshev's proof of Bertrand's postulate
and the PNT bridge. The proof uses Kummer's theorem: the p-adic
valuation v_p(C(m,k)) counts the number of carries when adding k
and m-k in base p. Each carry contributes at most one power of p,
and there are at most log_p(m) digits.

Equivalently: v_p(C(2n,n)) ≤ log_p(2n), so p^{v_p(C(2n,n))} ≤ 2n.

Tags: number-theory, analytic-number-theory, Kummer, Chebyshev
-/

namespace ChebyshevPNTBridgeOQ01

open Nat Finset

-- ============================================================
-- Part I: p-adic Valuation of Central Binomial Coefficients
-- ============================================================

/-- The p-adic valuation of n! via Legendre's formula:
    v_p(n!) = ∑_{i≥1} ⌊n/p^i⌋. -/
theorem legendre_factorial_val (p n : ℕ) (hp : p.Prime) :
    (n !).factorization p = ∑ i ∈ Finset.Ico 1 (n + 1), n / p ^ i := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0: both sides are 0
    simp [Nat.factorial_zero, Nat.factorization_one]
  · -- Step 1: Connect factorization to Ico sum via multiplicity
    have h_ico : (n !).factorization p =
        ∑ i ∈ Finset.Ico 1 (Nat.log p n + 2), n / p ^ i := by
      have h1 : (↑((n !).factorization p) : PartENat) = multiplicity p (n !) :=
        (multiplicity_eq_factorization hp (Nat.factorial_ne_zero n)).symm
      have h2 : multiplicity p (n !) =
          (↑(∑ i ∈ Finset.Ico 1 (Nat.log p n + 2), n / p ^ i) : PartENat) :=
        hp.multiplicity_factorial (by omega)
      exact_mod_cast h1.trans h2
    -- Step 2: Extend sum — extra terms are 0 since p^i > n for i > log_p(n)
    rw [h_ico]
    apply Finset.sum_subset (Finset.Ico_subset_Ico_right _)
    · -- log p n + 2 ≤ n + 1
      have hlog_lt : Nat.log p n < n := by
        rw [Nat.log_lt hp.one_lt hn.ne']
        exact (Nat.lt_two_pow n).trans_le (Nat.pow_le_pow_left hp.two_le n)
      omega
    · -- Extra terms are 0
      intro i hi hni
      rw [Finset.mem_Ico] at hi hni
      push_neg at hni
      have : n < p ^ i := by
        calc n < p ^ (Nat.log p n + 1) := Nat.lt_pow_succ_log_self hp.one_lt _
          _ ≤ p ^ i := Nat.pow_le_pow_right hp.pos (by omega)
      exact Nat.div_eq_of_lt this

/-- The p-adic valuation of C(2n,n) via Legendre:
    v_p(C(2n,n)) = v_p((2n)!) - 2·v_p(n!)
                  = ∑_{i≥1} (⌊2n/p^i⌋ - 2⌊n/p^i⌋).

    Each term ⌊2n/p^i⌋ - 2⌊n/p^i⌋ is 0 or 1 (the "carry" indicator). -/
theorem central_binom_val_terms (p n : ℕ) (hp : p.Prime) (i : ℕ) (hi : i ≥ 1) :
    2 * n / p ^ i - 2 * (n / p ^ i) ≤ 1 := by
  have h : 2 * (n / p ^ i) ≤ 2 * n / p ^ i := by
    omega
  omega

/-- Carry count bound: the number of nonzero carry terms is at most
    the number of base-p digits of 2n, which is ⌊log_p(2n)⌋ + 1. -/
theorem carry_terms_bounded (p n : ℕ) (hp : p.Prime) (i : ℕ)
    (hi : p ^ i > 2 * n) : 2 * n / p ^ i = 0 := by
  exact Nat.div_eq_zero_iff (by positivity).2 (le_of_lt hi) |>.mpr (by omega) |> fun _ => by
    omega

/-- The number of digits of 2n in base p is at most log_p(2n) + 1. -/
theorem digits_bound (p n : ℕ) (hp : p.Prime) (hn : n ≥ 1) :
    ∃ k : ℕ, p ^ k > 2 * n ∧ k ≤ 2 * n := by
  exact ⟨2 * n, by
    calc p ^ (2 * n) ≥ 2 ^ (2 * n) := Nat.pow_le_pow_left hp.two_le (2 * n)
    _ > 2 * n := by
      have : 2 ^ (2 * n) ≥ 2 * n + 1 := by
        induction n with
        | zero => omega
        | succ n ih => calc 2 ^ (2 * (n + 1)) = 4 * 2 ^ (2 * n) := by ring_nf; ring
                         _ ≥ 4 * (2 * n + 1) := by omega
                         _ = 8 * n + 4 := by ring
                         _ ≥ 2 * (n + 1) + 1 := by omega
      omega,
    le_refl _⟩

-- ============================================================
-- Part II: The Main Bound
-- ============================================================

/-- **Main theorem**: p^{v_p(C(2n,n))} ≤ 2n for any prime p and n ≥ 1.

    Proof: Direct from Mathlib's `Nat.pow_factorization_choose_le` which gives
    p^{v_p(C(m,k))} ≤ m for k ≤ m. -/
theorem prime_pow_val_central_binom_le (p n : ℕ) (hp : p.Prime) (hn : n ≥ 1) :
    p ^ ((2 * n).choose n).factorization p ≤ 2 * n :=
  Nat.pow_factorization_choose_le (show n ≤ 2 * n by omega)

/-- Corollary: the product ∏_{p ≤ 2n} p^{v_p(C(2n,n))} = C(2n,n),
    so C(2n,n) ≤ (2n)^{π(2n)} where π is the prime counting function. -/
theorem central_binom_le_pow_prime_counting (n : ℕ) (hn : n ≥ 1) :
    (2 * n).choose n ≤ (2 * n) ^ Nat.primeCounting (2 * n) := by
  have hcb_ne : (2 * n).choose n ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have h2n_pos : 0 < 2 * n := by omega
  -- Every p in the factorization support is prime
  have hprime_of_mem : ∀ p ∈ ((2 * n).choose n).factorization.support, p.Prime := by
    intro p hp
    rw [Nat.support_factorization] at hp
    exact Nat.prime_of_mem_primeFactors hp
  -- Each prime power factor p^{v_p(C(2n,n))} ≤ 2n
  have hbound : ∀ p ∈ ((2 * n).choose n).factorization.support,
      p ^ ((2 * n).choose n).factorization p ≤ 2 * n := by
    intro p _
    exact Nat.pow_factorization_choose_le (show n ≤ 2 * n by omega)
  -- Support ⊆ {primes ≤ 2n}
  have hsub : ((2 * n).choose n).factorization.support ⊆
      Finset.filter Nat.Prime (Finset.range (2 * n + 1)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range]
    have hp_prime := hprime_of_mem p hp
    refine ⟨?_, hp_prime⟩
    have hv : 1 ≤ ((2 * n).choose n).factorization p := by
      have := Finsupp.mem_support_iff.mp hp; omega
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ ((2 * n).choose n).factorization p :=
          Nat.pow_le_pow_right hp_prime.pos hv
      _ ≤ 2 * n := hbound p hp
      _ < 2 * n + 1 := by omega
  -- |support| ≤ π(2n)
  have hcard : ((2 * n).choose n).factorization.support.card ≤
      Nat.primeCounting (2 * n) := by
    calc ((2 * n).choose n).factorization.support.card
        ≤ (Finset.filter Nat.Prime (Finset.range (2 * n + 1))).card :=
          Finset.card_le_card hsub
      _ = Nat.primeCounting (2 * n) := by
          unfold Nat.primeCounting Nat.primeCounting'
          exact (Nat.count_eq_card_filter_range Nat.Prime (2 * n + 1)).symm
  -- C(2n,n) = ∏ p^{v_p} ≤ ∏ (2n) = (2n)^|support| ≤ (2n)^{π(2n)}
  calc (2 * n).choose n
      = ((2 * n).choose n).factorization.prod (· ^ ·) :=
        (Nat.factorization_prod_pow_eq_self hcb_ne).symm
    _ ≤ ∏ _p ∈ ((2 * n).choose n).factorization.support, (2 * n) := by
        simp only [Finsupp.prod]
        exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hbound
    _ = (2 * n) ^ ((2 * n).choose n).factorization.support.card :=
        Finset.prod_const (2 * n)
    _ ≤ (2 * n) ^ Nat.primeCounting (2 * n) :=
        Nat.pow_le_pow_right h2n_pos hcard

-- ============================================================
-- Part III: Connection to Chebyshev/Bertrand
-- ============================================================

/-- The central binomial coefficient satisfies C(2n,n) ≥ 4^n/(2n+1).
    This is a well-known lower bound from the binomial theorem.
    Proof: 4^n = ∑ C(2n,i) ≤ (2n+1) * max C(2n,i) = (2n+1) * C(2n,n). -/
theorem central_binom_lower (n : ℕ) :
    (2 * n + 1) * (2 * n).choose n ≥ 4 ^ n := by
  -- 4^n = 2^(2n) = ∑_{i=0}^{2n} C(2n,i)
  have h_sum := Nat.sum_range_choose (2 * n)
  have h_pow : 2 ^ (2 * n) = 4 ^ n := by ring
  -- Each C(2n, i) ≤ C(2n, n) (middle binomial is largest)
  have h_mid : ∀ i, (2 * n).choose i ≤ (2 * n).choose n := by
    intro i
    have := Nat.choose_le_middle (2 * n) i
    rwa [show (2 * n) / 2 = n from by omega] at this
  -- Sum bound: ∑ C(2n, i) ≤ (2n+1) * C(2n, n)
  have h_bound : ∑ i in Finset.range (2 * n + 1), (2 * n).choose i ≤
      (2 * n + 1) * (2 * n).choose n := by
    have := Finset.sum_le_card_nsmul (Finset.range (2 * n + 1))
      (fun i => (2 * n).choose i) ((2 * n).choose n) (fun i _ => h_mid i)
    simp [Finset.card_range] at this
    exact this
  linarith [h_sum, h_pow]

/-- Combining: 4^n/(2n+1) ≤ C(2n,n) ≤ (2n)^{π(2n)},
    so π(2n) ≥ n·log(4)/log(2n) - log(2n+1)/log(2n).
    This is Chebyshev's lower bound on π. -/
theorem chebyshev_lower_via_kummer (n : ℕ) (hn : n ≥ 1) :
    4 ^ n ≤ (2 * n + 1) * (2 * n) ^ Nat.primeCounting (2 * n) := by
  calc 4 ^ n
      ≤ (2 * n + 1) * (2 * n).choose n := central_binom_lower n
    _ ≤ (2 * n + 1) * (2 * n) ^ Nat.primeCounting (2 * n) :=
        Nat.mul_le_mul_left _ (central_binom_le_pow_prime_counting n hn)

-- ============================================================
-- Part IV: Concrete Computations
-- ============================================================

/-- C(6,3) = 20, and 2^{v_2(20)} = 4, 3^{v_3(20)} = 1, 5^{v_5(20)} = 5.
    All satisfy p^{v_p} ≤ 6. -/
theorem example_n3 : (6).choose 3 = 20 := by native_decide

/-- C(10,5) = 252. -/
theorem example_n5 : (10).choose 5 = 252 := by native_decide

/-- C(20,10) = 184756. -/
theorem example_n10 : (20).choose 10 = 184756 := by native_decide

end ChebyshevPNTBridgeOQ01
