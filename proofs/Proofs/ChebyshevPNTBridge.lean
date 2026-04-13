/-
# Chebyshev–PNT Bridge: Explicit Bounds on π(x)

Connects ChebyshevBounds.lean results to explicit bounds on the prime counting
function, establishing that π(n) is between c₁·n/log(n) and c₂·n/log(n).

**Upper bound** (fully proved):
  (√n)^{π(n) - π(√n)} ≤ 4^n
  Equivalently: π(n) ≤ √n + n·log(4)/log(√n)

**Lower bound** (fully proved):
  4^n ≤ (2n+1) · (2n)^{π(2n)}
  Equivalently: π(2n) ≥ n·log(2)/log(2n) - o(1)

Together these give: log(2) ≤ liminf π(x)·log(x)/x ≤ limsup ≤ 2·log(4)
This is Chebyshev's 1852 result (with weaker constants than his 0.921, 1.106).

**Status**: COMPLETE (0 sorries, 0 axioms)
-/

import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Proofs.ChebyshevBounds

namespace ChebyshevPNTBridge

open Nat Finset

/-! ═══════════════════════════════════════════════════════════════════════════════
PART I: UPPER BOUND ON π(n) VIA θ(n) AND PRIMORIAL

Strategy: primes p in (√n, n] each exceed √n, so their product ≥ (√n)^k
where k = #{primes in (√n, n]}. But their product divides primorial(n) ≤ 4^n.
Hence (√n)^k ≤ 4^n, giving k ≤ n·log(4)/log(√n).
Since π(n) = k + π(√n) ≤ k + √n, this bounds π(n).
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Number of primes in the interval (m, n] -/
def numPrimesAbove (m n : ℕ) : ℕ :=
  (filter Nat.Prime (Ico (m + 1) (n + 1))).card

/-- The count of primes in (m, n] equals π(n) - π(m) -/
theorem numPrimesAbove_eq (m n : ℕ) (hmn : m ≤ n) :
    numPrimesAbove m n = Nat.primeCounting n - Nat.primeCounting m := by
  unfold numPrimesAbove primeCounting primeCounting'
  have h1 : count Nat.Prime (n + 1) = (filter Nat.Prime (range (n + 1))).card :=
    count_eq_card_filter_range Nat.Prime (n + 1)
  have h2 : count Nat.Prime (m + 1) = (filter Nat.Prime (range (m + 1))).card :=
    count_eq_card_filter_range Nat.Prime (m + 1)
  rw [h1, h2]
  have hunion : range (n + 1) = range (m + 1) ∪ Ico (m + 1) (n + 1) := by
    ext x; simp only [mem_range, mem_union, mem_Ico]; omega
  have hdisj : Disjoint (range (m + 1)) (Ico (m + 1) (n + 1)) := by
    rw [disjoint_iff_ne]
    intro a ha b hb
    simp only [mem_range] at ha
    simp only [mem_Ico] at hb
    omega
  rw [hunion, filter_union, card_union_of_disjoint (disjoint_filter_filter hdisj)]
  omega

/-- Product of primes in (m, n] -/
noncomputable def prodPrimesAbove (m n : ℕ) : ℕ :=
  ∏ p ∈ filter Nat.Prime (Ico (m + 1) (n + 1)), p

/-- Each prime in (m, n] divides primorial(n), since it appears as a factor -/
theorem prime_in_range_dvd_primorial {p m n : ℕ} (hp : Nat.Prime p)
    (hlo : m < p) (hhi : p ≤ n) : p ∣ primorial n := by
  unfold primorial
  apply dvd_prod_of_mem
  simp only [mem_filter, mem_range]
  exact ⟨by omega, hp⟩

/-- Product of primes in (m, n] divides primorial(n) -/
theorem prodPrimesAbove_dvd_primorial (m n : ℕ) (hmn : m ≤ n) :
    prodPrimesAbove m n ∣ primorial n := by
  unfold prodPrimesAbove
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (mem_filter.mp hp).2.prime
  · intro p hp
    have ⟨hIco, hprime⟩ := mem_filter.mp hp
    have ⟨hlo, hhi⟩ := mem_Ico.mp hIco
    exact prime_in_range_dvd_primorial hprime (Nat.lt_of_succ_le hlo) (Nat.lt_succ_iff.mp hhi)

/-- **Upper bound on primes above √n**: (√n)^{π(n) - π(√n)} ≤ 4^n

This is the key upper bound: primes in (√n, n] are each > √n, so their
product exceeds (√n)^k. But this product divides n# ≤ 4^n. -/
theorem pow_sqrt_primeCounting_le (n : ℕ) (hn : 4 ≤ n) :
    (Nat.sqrt n) ^ numPrimesAbove (Nat.sqrt n) n ≤ 4 ^ n := by
  have hsqrt_pos : 0 < Nat.sqrt n := by
    have : 2 ≤ Nat.sqrt n := by
      rw [Nat.le_sqrt]
      omega
    omega
  have hS : ∀ p ∈ filter Nat.Prime (Ico (Nat.sqrt n + 1) (n + 1)),
      Nat.Prime p ∧ Nat.sqrt n < p := by
    intro p hp
    have ⟨hIco, hprime⟩ := mem_filter.mp hp
    have ⟨hlo, _⟩ := mem_Ico.mp hIco
    exact ⟨hprime, Nat.lt_of_succ_le hlo⟩
  have hdvd := prodPrimesAbove_dvd_primorial (Nat.sqrt n) n (Nat.sqrt_le_self n)
  have hprim_pos : 0 < primorial n := primorial_pos n
  have hprim_le : primorial n ≤ 4 ^ n := primorial_le_4_pow n
  unfold numPrimesAbove prodPrimesAbove at *
  calc (Nat.sqrt n) ^ (filter Nat.Prime (Ico (Nat.sqrt n + 1) (n + 1))).card
      ≤ primorial n := ChebyshevBounds.pow_le_of_prod_primes_dvd hsqrt_pos _ hS hdvd hprim_pos
    _ ≤ 4 ^ n := hprim_le

/-- π(n) - π(√n) satisfies the power bound -/
theorem pow_sqrt_primeCounting_diff_le (n : ℕ) (hn : 4 ≤ n) :
    (Nat.sqrt n) ^ (Nat.primeCounting n - Nat.primeCounting (Nat.sqrt n)) ≤ 4 ^ n := by
  rw [← numPrimesAbove_eq (Nat.sqrt n) n (Nat.sqrt_le_self n)]
  exact pow_sqrt_primeCounting_le n hn

/-- Trivial bound: π(m) ≤ m (since 0 is not prime, at most m of {0,...,m} are prime) -/
theorem primeCounting_le (m : ℕ) : Nat.primeCounting m ≤ m := by
  unfold primeCounting primeCounting'
  -- filter Prime {0,...,m} = filter Prime ({0,...,m} \ {0}) since 0 is not prime
  -- |filter Prime S| ≤ |S| for any S, and |{0,...,m} \ {0}| = m
  calc count Nat.Prime (m + 1)
      = (filter Nat.Prime (range (m + 1))).card :=
        count_eq_card_filter_range Nat.Prime (m + 1)
    _ = (filter Nat.Prime ((range (m + 1)).erase 0)).card := by
        congr 1; ext p; constructor
        · intro hp; simp only [mem_filter, mem_range] at hp
          simp only [mem_filter, mem_erase, mem_range]
          exact ⟨⟨hp.2.ne_zero, hp.1⟩, hp.2⟩
        · intro hp; simp only [mem_filter, mem_erase, mem_range] at hp
          simp only [mem_filter, mem_range]
          exact ⟨hp.1.2, hp.2⟩
    _ ≤ ((range (m + 1)).erase 0).card := card_filter_le _ _
    _ ≤ m := by
        rw [card_erase_of_mem (mem_range.mpr (by omega)), card_range]
        omega

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II: FACTORIZATION BOUND (Key Lemma for Lower Bound)

For any prime p: p^{v_p(C(2n,n))} ≤ 2n.

Proof idea: By Legendre's formula, v_p(C(2n,n)) = Σ_j (⌊2n/p^j⌋ - 2⌊n/p^j⌋).
Each term is 0 or 1 (since ⌊2x⌋ - 2⌊x⌋ ∈ {0,1}). Terms with p^j > 2n are 0.
So v_p(C(2n,n)) ≤ ⌊log_p(2n)⌋, giving p^{v_p} ≤ 2n.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Key factorization bound: p^{v_p(C(2n,n))} ≤ 2n for any prime p.
This is the standard bound from Legendre's formula for binomial coefficients.
The p-adic valuation of C(2n,n) is at most log_p(2n). -/
theorem prime_pow_factorization_centralBinom_le (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (_hp : p.Prime) :
    p ^ (centralBinom n).factorization p ≤ 2 * n := by
  -- centralBinom n = choose (2*n) n, and for any choose m k:
  -- p^{v_p(choose m k)} ≤ m (standard result from Legendre's formula)
  rw [centralBinom_eq_two_mul_choose]
  exact Nat.pow_factorization_choose_le (by omega)

/-- C(2n,n) ≤ (2n)^{π(2n)} : the central binomial coefficient is bounded
by the prime counting function power.

Proof: C(2n,n) = ∏_p p^{v_p(C(2n,n))} where each factor p^{v_p} ≤ 2n.
The product has at most π(2n) terms (prime factors are all ≤ 2n). -/
theorem centralBinom_le_pow_primeCounting (n : ℕ) (hn : 1 ≤ n) :
    centralBinom n ≤ (2 * n) ^ Nat.primeCounting (2 * n) := by
  have hcb_ne : centralBinom n ≠ 0 := (centralBinom_pos n).ne'
  have h2n_pos : 0 < 2 * n := by omega
  -- Helper: every p in the factorization support is prime
  have hprime_of_mem : ∀ p ∈ (centralBinom n).factorization.support, p.Prime := by
    intro p hp
    rw [Nat.support_factorization] at hp
    exact Nat.prime_of_mem_primeFactors hp
  -- Step 1: Each prime power factor p^{v_p(C(2n,n))} ≤ 2n
  have hbound : ∀ p ∈ (centralBinom n).factorization.support,
      p ^ (centralBinom n).factorization p ≤ 2 * n := by
    intro p hp
    exact prime_pow_factorization_centralBinom_le n hn p (hprime_of_mem p hp)
  -- Step 2: The support is contained in {primes ≤ 2n}, so |support| ≤ π(2n)
  have hsub : (centralBinom n).factorization.support ⊆
      filter Nat.Prime (range (2 * n + 1)) := by
    intro p hp
    simp only [mem_filter, mem_range]
    have hp_prime := hprime_of_mem p hp
    refine ⟨?_, hp_prime⟩
    -- p ≤ p^{v_p} ≤ 2n, so p < 2n + 1
    have hv : 1 ≤ (centralBinom n).factorization p := by
      have := Finsupp.mem_support_iff.mp hp; omega
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ (centralBinom n).factorization p :=
          Nat.pow_le_pow_right hp_prime.pos hv
      _ ≤ 2 * n := hbound p hp
      _ < 2 * n + 1 := by omega
  have hcard : (centralBinom n).factorization.support.card ≤ Nat.primeCounting (2 * n) := by
    calc (centralBinom n).factorization.support.card
        ≤ (filter Nat.Prime (range (2 * n + 1))).card := card_le_card hsub
      _ = Nat.primeCounting (2 * n) := by
          unfold primeCounting primeCounting'
          exact (count_eq_card_filter_range Nat.Prime (2 * n + 1)).symm
  -- Step 3: C(2n,n) = ∏ p^{v_p} ≤ ∏ (2n) = (2n)^|support| ≤ (2n)^{π(2n)}
  calc centralBinom n
      = (centralBinom n).factorization.prod (· ^ ·) :=
        (Nat.factorization_prod_pow_eq_self hcb_ne).symm
    _ ≤ ∏ _p ∈ (centralBinom n).factorization.support, (2 * n) := by
        simp only [Finsupp.prod]
        exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) hbound
    _ = (2 * n) ^ (centralBinom n).factorization.support.card :=
        prod_const (2 * n)
    _ ≤ (2 * n) ^ Nat.primeCounting (2 * n) :=
        Nat.pow_le_pow_right h2n_pos hcard

/-! ═══════════════════════════════════════════════════════════════════════════════
PART III: LOWER BOUND ON π(n)

From the central binomial lower bound (ChebyshevBounds) and factorization bound:
  4^n ≤ (2n+1) · C(2n,n) ≤ (2n+1) · (2n)^{π(2n)}

Taking logarithms:
  π(2n) ≥ (n·log(4) - log(2n+1)) / log(2n) → log(2) ≈ 0.693

This proves π is at least order n/log(n).
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Lower bound on π(2n)**: 4^n ≤ (2n+1) · (2n)^{π(2n)}

Combined with the upper bound, this shows π(x) = Θ(x/log(x)). -/
theorem four_pow_le_mul_pow_primeCounting (n : ℕ) (hn : 1 ≤ n) :
    4 ^ n ≤ (2 * n + 1) * (2 * n) ^ Nat.primeCounting (2 * n) := by
  calc 4 ^ n
      ≤ (2 * n + 1) * centralBinom n := ChebyshevBounds.centralBinom_ge_four_pow_div n
    _ ≤ (2 * n + 1) * (2 * n) ^ Nat.primeCounting (2 * n) := by
        apply Nat.mul_le_mul_left
        exact centralBinom_le_pow_primeCounting n hn

/-! ═══════════════════════════════════════════════════════════════════════════════
PART IV: SUMMARY

We have established Chebyshev's 1852 bounds (with weaker explicit constants):

**Upper**: (√n)^{π(n) - π(√n)} ≤ 4^n
  → π(n)·log(n)/n ≤ 2·log(4) + o(1) ≈ 2.77 + o(1)

**Lower**: 4^n ≤ (2n+1)·(2n)^{π(2n)}
  → π(x)·log(x)/x ≥ log(2) - o(1) ≈ 0.69 - o(1)

These show that π(x) = Θ(x/log(x)), confirming the order of growth predicted
by the Prime Number Theorem, though with weaker constants than PNT's limit of 1.

Chebyshev's original analysis (1852) achieved 0.921 ≤ liminf ≤ limsup ≤ 1.106,
which our weak constants 0.693 ≤ ... ≤ 2.773 do not reach. The tighter bounds
require more careful analysis of the prime factorization of C(2n,n).

The Prime Number Theorem (Hadamard/de la Vallée Poussin, 1896) shows the limit
is exactly 1, but requires complex analysis of the Riemann zeta function.
═══════════════════════════════════════════════════════════════════════════════ -/

#check pow_sqrt_primeCounting_diff_le  -- Upper bound
#check four_pow_le_mul_pow_primeCounting  -- Lower bound
#check ChebyshevBounds.chebyshevTheta_le  -- θ(n) ≤ n·log(4)
#check ChebyshevBounds.centralBinom_ge_four_pow_div  -- 4^n ≤ (2n+1)·C(2n,n)

end ChebyshevPNTBridge
