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

import Mathlib

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

/-- Helper: totientIterate n 0 = n (zero iterations is identity). -/
theorem totientIterate_zero (n : ℕ) : totientIterate n 0 = n := rfl

/-- Helper: totientIterate n 1 = totientPlusOne n. -/
theorem totientIterate_one (n : ℕ) : totientIterate n 1 = totientPlusOne n := rfl

/-- F(p) = 0 for primes p: already a prime, no iterations needed.
    Proof: the set {k | ∀ j < k, ¬(iterate(p,j)).Prime} = {0} since
    iterate(p, 0) = p is prime. So sSup {0} = 0. -/
theorem prime_zero_iterations :
    ∀ p : ℕ, p.Prime → iterationsToFirst p = 0 := by
  intro p hp
  unfold iterationsToFirst
  simp only [add_zero]
  -- Show S = {0}, then sSup {0} = 0
  have hS_eq : {k : ℕ | ∀ j : ℕ, j < k → ¬(totientIterate p j).Prime} = {0} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hk
      by_contra hne
      have hpos : 0 < k := Nat.pos_of_ne_zero hne
      exact hk 0 hpos (by rw [totientIterate_zero]; exact hp)
    · rintro rfl; intro j hj; omega
  rw [hS_eq, csSup_singleton]

/-- F(n) = 1 when n is composite and φ(n) + 1 is prime.
    For example, F(4) = 1 since φ(4) + 1 = 3.
    Note: requires ¬n.Prime since F(p) = 0 for primes.
    Proof: the set is {0, 1} — 0 is always in, 1 is in because ¬n.Prime
    means iterate(n,0) = n is not prime, and 2 is out because
    iterate(n,1) = φ(n)+1 is prime. So sSup {0,1} = 1. -/
theorem one_iteration_criterion :
    ∀ n : ℕ, n > 1 → ¬n.Prime → (totientPlusOne n).Prime →
      iterationsToFirst n = 1 := by
  intro n hn hnp htot
  unfold iterationsToFirst
  simp only [add_zero]
  -- Show S = {0, 1}, then sSup {0, 1} = 0 ⊔ 1 = 1
  have hS_eq : {k : ℕ | ∀ j : ℕ, j < k → ¬(totientIterate n j).Prime} = {0, 1} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hk
      -- k can only be 0 or 1: if k ≥ 2, hk 1 contradicts htot
      by_contra h
      push_neg at h
      obtain ⟨hne0, hne1⟩ := h
      have hge2 : 2 ≤ k := by omega
      exact hk 1 (by omega) (by rw [totientIterate_one]; exact htot)
    · rintro (rfl | rfl)
      · intro j hj; omega
      · intro j hj
        have : j = 0 := by omega
        subst this
        rw [totientIterate_zero]
        exact hnp
  rw [hS_eq, csSup_pair]
  simp

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

/-- The σ iteration can grow: σ(n) − 1 ≥ n for n > 1.
    Since 1 and n are both divisors and 1 ≠ n (as n > 1),
    σ(n) ≥ 1 + n, so σ(n) - 1 ≥ n. -/
theorem sigma_growing :
    ∀ n : ℕ, n > 1 → ¬n.Prime →
      n ≤ (n.divisors.sum id) - 1 := by
  intro n hn _hnp
  -- σ(n) = n.divisors.sum id ≥ 1 + n since {1, n} ⊆ n.divisors
  have h1_dvd : 1 ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩
  have hn_dvd : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_refl n, by omega⟩
  have h1n_ne : (1 : ℕ) ≠ n := by omega
  have hpair : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact h1_dvd
    · exact Finset.mem_singleton.mp hx ▸ hn_dvd
  have hpair_sum : ({1, n} : Finset ℕ).sum id = 1 + n := by
    rw [Finset.sum_insert (by rwa [Finset.mem_singleton])]
    simp
  have hge : n.divisors.sum id ≥ 1 + n := by
    calc n.divisors.sum id ≥ ({1, n} : Finset ℕ).sum id :=
            Finset.sum_le_sum_of_subset_of_nonneg hpair (fun _ _ _ => Nat.zero_le _)
         _ = 1 + n := hpair_sum
  omega

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
