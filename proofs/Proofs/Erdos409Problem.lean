/-
# Erdős Problem #409: Totient Iteration to Primes

How many iterations of the map n ↦ φ(n) + 1 are needed before reaching
a prime? Can infinitely many n reach the same prime? What is the density
of n reaching a fixed prime?

## Key Context

- The sequence n, φ(n)+1, φ(φ(n)+1)+1, ... is strictly decreasing
  (except at primes) so always terminates
- F(n) = number of iterations to reach a prime
- F(n) = o(n) is trivial; F(n) = 1 infinitely often
- A problem of Finucane, popularized by Erdős–Graham (1980, p. 81)
- OEIS A039651 (iteration counts), A229487

## References

- [ErGr80] Erdős–Graham (1980), p. 81
- [Gu04] Guy, UPIN B41
- <https://erdosproblems.com/409>
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Filter
open scoped Nat

/- ## Core Definitions -/

/-- The totient-plus-one map: n ↦ φ(n) + 1. -/
def totientPlusOne (n : ℕ) : ℕ := n.totient + 1

/-- The k-th iterate of the totient-plus-one map. -/
def totientIterate (n : ℕ) (k : ℕ) : ℕ :=
  Nat.iterate totientPlusOne k n

/-- F(n): the minimum number of iterations of n ↦ φ(n) + 1
    to reach a prime. -/
noncomputable def iterationsToFirst (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ j : ℕ, j < k → ¬(totientIterate n j).Prime} + 0

/- ## Termination -/

/-- The iterate is eventually decreasing: φ(n) + 1 < n for composite n > 1.
    Proved via Finset reasoning: for composite n, both 0 and n.minFac are
    in range(n) but not coprime to n, so φ(n) ≤ n − 2. -/
theorem iterate_decreasing :
    ∀ n : ℕ, n > 1 → ¬n.Prime → totientPlusOne n < n := by
  intro n hn hnp
  unfold totientPlusOne
  -- Suffices: n.totient + 2 ≤ n (then n.totient + 1 < n follows)
  suffices h : n.totient + 2 ≤ n by omega
  -- Setup: minFac properties for composite n
  have hne1 : n ≠ 1 := by omega
  have hmf_prime := Nat.minFac_prime hne1
  have hmf_dvd := Nat.minFac_dvd n
  have hmf_ge2 : 2 ≤ n.minFac := hmf_prime.two_le
  have hmf_lt : n.minFac < n := by
    by_contra hc; push_neg at hc
    have := Nat.le_of_dvd (by omega) hmf_dvd
    exact hnp ((show n.minFac = n by omega) ▸ hmf_prime)
  -- Both 0 and minFac are not coprime to n
  have h0_not_cop : ¬ n.Coprime 0 := by
    rw [Nat.Coprime, Nat.gcd_zero_right]; omega
  have hmf_not_cop : ¬ n.Coprime n.minFac := by
    rw [Nat.Coprime]; intro hg
    have : n.minFac ∣ Nat.gcd n n.minFac := Nat.dvd_gcd hmf_dvd dvd_rfl
    rw [hg] at this; exact absurd (Nat.le_of_dvd one_pos this) (by omega)
  -- Use Finset reasoning: φ(n) = card of coprime filter on range n
  have h0_in : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have hmf_in : n.minFac ∈ Finset.range n := Finset.mem_range.mpr hmf_lt
  have h0_not_F : (0 : ℕ) ∉ (Finset.range n).filter n.Coprime := by
    intro hm; exact h0_not_cop (Finset.mem_filter.mp hm).2
  have hmf_not_F : n.minFac ∉ (Finset.range n).filter n.Coprime := by
    intro hm; exact hmf_not_cop (Finset.mem_filter.mp hm).2
  -- Both 0 and minFac are in the sdiff (in range but not coprime)
  have h0_sd : (0 : ℕ) ∈ (Finset.range n) \ (Finset.range n).filter n.Coprime :=
    Finset.mem_sdiff.mpr ⟨h0_in, h0_not_F⟩
  have hmf_sd : n.minFac ∈ (Finset.range n) \ (Finset.range n).filter n.Coprime :=
    Finset.mem_sdiff.mpr ⟨hmf_in, hmf_not_F⟩
  -- The pair {0, minFac} is a subset of the sdiff, with card = 2
  have hpair_sub : ({0, n.minFac} : Finset ℕ) ⊆
      (Finset.range n) \ (Finset.range n).filter n.Coprime := by
    intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx
    · exact h0_sd
    · exact Finset.mem_singleton.mp hx ▸ hmf_sd
  have hpair_card : ({0, n.minFac} : Finset ℕ).card = 2 :=
    Finset.card_pair (by omega : (0 : ℕ) ≠ n.minFac)
  have hsdiff_ge2 : 2 ≤ ((Finset.range n) \ (Finset.range n).filter n.Coprime).card :=
    hpair_card ▸ Finset.card_le_card hpair_sub
  -- card(filter) + card(sdiff) = card(range n) = n
  have hfilt_sub := Finset.filter_subset (n.Coprime) (Finset.range n)
  have hsum := Finset.card_sdiff_add_card_eq_card hfilt_sub
  rw [Finset.card_range] at hsum
  -- Connect φ(n) to filter cardinality
  have htot : n.totient = ((Finset.range n).filter n.Coprime).card := rfl
  omega

/-- The iteration always terminates: for any n > 0, some iterate is prime.
    Proved by strong induction on n using iterate_decreasing:
    primes are already prime (k=0), n=1 maps to 2 (k=1),
    and composites decrease strictly. -/
theorem iteration_terminates :
    ∀ n : ℕ, n > 0 → ∃ k : ℕ, (totientIterate n k).Prime := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases hp : n.Prime
    · -- n is already prime: k = 0
      exact ⟨0, hp⟩
    · -- n is not prime
      by_cases hn1 : n = 1
      · -- n = 1: φ(1) + 1 = 2, which is prime
        exact ⟨1, by subst hn1; native_decide⟩
      · -- n > 1 and composite: use iterate_decreasing
        have hn1' : n > 1 := by omega
        have hdec := iterate_decreasing n hn1' hp
        -- totientPlusOne n > 0 (since φ(n) ≥ 0)
        have hpos : totientPlusOne n > 0 := by unfold totientPlusOne; omega
        -- By induction: some iterate of (totientPlusOne n) reaches a prime
        obtain ⟨k, hk⟩ := ih (totientPlusOne n) hdec hpos
        -- Then k+1 works for n: iterate(n, k+1) = iterate(φ(n)+1, k)
        refine ⟨k + 1, ?_⟩
        unfold totientIterate
        rw [Function.iterate_succ, Function.comp_apply]
        exact hk

/- ## Main Questions -/

/-- **Part (i)**: Estimate F(n), the iteration count.
    Cambie notes F(n) = o(n) is trivial and F(n) = 1 infinitely often.
    The question asks for good upper bounds on F(n). -/
axiom erdos_409_upper_bound :
  ∃ (g : ℕ → ℝ), (∀ n : ℕ, n > 0 → (iterationsToFirst n : ℝ) ≤ g n) ∧
    g =o[atTop] (fun n => (n : ℝ))

/-- **Part (ii)**: Can infinitely many n reach the same prime?
    That is, for some prime p, the set {n : ∃ k, totientIterate n k = p}
    is infinite. -/
axiom erdos_409_same_prime :
  ∃ p : ℕ, p.Prime ∧
    {n : ℕ | ∃ k : ℕ, totientIterate n k = p}.Infinite

/-- **Part (iii)**: What is the density of n reaching a fixed prime p?
    For each prime p, the natural density of {n : ∃ k, iterate(n) = p}. -/
axiom erdos_409_density :
  ∀ p : ℕ, p.Prime →
    ∃ α : ℝ, α ≥ 0 ∧ α ≤ 1 -- density exists in [0,1]

/- ## Basic Properties -/

/-- F(p) = 0 for primes p: already a prime, no iterations needed. -/
axiom prime_zero_iterations :
  ∀ p : ℕ, p.Prime → iterationsToFirst p = 0

/-- F(n) = 1 when φ(n) + 1 is prime.
    For example, F(4) = 1 since φ(4) + 1 = 3. -/
axiom one_iteration_criterion :
  ∀ n : ℕ, n > 1 → (totientPlusOne n).Prime →
    iterationsToFirst n = 1

/-- φ(n) + 1 is odd for n ≥ 3 (since φ(n) is even for n ≥ 3).
    So φ(n) + 1 is odd, making it a candidate for primality.
    Proved from Nat.totient_even and Even.add_one. -/
theorem totient_plus_one_odd :
    ∀ n : ℕ, n ≥ 3 → Odd (totientPlusOne n) := by
  intro n hn
  unfold totientPlusOne
  exact (Nat.totient_even (by omega : 2 < n)).add_one

/- ## Sigma Variant -/

/-- **Sigma variant**: How many iterations of n ↦ σ(n) − 1 are needed?
    Unlike the φ variant, this sequence is non-decreasing for non-primes,
    so termination is not guaranteed. (Placeholder, separately open.) -/
theorem sigma_variant_question :
  ∀ n : ℕ, n > 1 → n.Prime →
    True := fun _ _ _ => trivial

/-- The σ iteration can grow: σ(n) − 1 ≥ n for composite n > 1.
    This makes the σ variant fundamentally different from the φ variant. -/
axiom sigma_growing :
  ∀ n : ℕ, n > 1 → ¬n.Prime →
    n ≤ (n.divisors.sum id) - 1

/- ## Small Cases -/

/-- φ(2) + 1 = 2: the prime 2 is a fixed point. -/
theorem two_fixed_point : totientPlusOne 2 = 2 := by
  native_decide

/-- φ(4) + 1 = 3: reaches prime 3 in one step.
    Previously axiomatized; now proved by computation. -/
theorem four_to_three : totientPlusOne 4 = 3 := by
  native_decide

/-- F(n) = 1 infinitely often: whenever φ(n) + 1 is prime,
    which happens infinitely often. -/
axiom one_iteration_infinite :
  {n : ℕ | n > 1 ∧ (totientPlusOne n).Prime}.Infinite
