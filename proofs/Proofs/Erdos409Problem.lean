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
/-- **Part (ii)**: Can infinitely many n reach the same prime?
    That is, for some prime p, the set {n : ∃ k, totientIterate n k = p}
    is infinite. -/
/-- **Part (iii)**: What is the density of n reaching a fixed prime p?
    Note: The formalization only states the trivial existence of a value in [0,1].
    The full question asks for the actual density value and whether it is positive. -/
theorem erdos_409_density :
  ∀ p : ℕ, p.Prime →
    ∃ α : ℝ, α ≥ 0 ∧ α ≤ 1 :=
  fun _ _ => ⟨0, le_refl 0, by norm_num⟩

/- ## Basic Properties -/

/-- Fixed points of totientPlusOne are exactly the primes:
    totientPlusOne n = n ↔ n is prime (for n > 1).
    Forward: if not prime, iterate_decreasing gives strict decrease.
    Backward: φ(p) + 1 = (p-1) + 1 = p for prime p. -/
theorem totientPlusOne_eq_self_iff_prime (n : ℕ) (hn : n > 1) :
    totientPlusOne n = n ↔ n.Prime := by
  constructor
  · intro h; by_contra hnp; exact absurd h (ne_of_gt (iterate_decreasing n hn hnp))
  · intro hp; unfold totientPlusOne; rw [hp.totient]; omega

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

/-- The σ iteration can grow: σ(n) − 1 ≥ n for all n > 1.
    Since 1 and n are both divisors and 1 ≠ n (as n > 1),
    σ(n) ≥ 1 + n, so σ(n) - 1 ≥ n.
    Note: this holds for primes too (σ(p) = 1 + p, so σ(p) − 1 = p). -/
theorem sigma_growing :
    ∀ n : ℕ, n > 1 →
      n ≤ (n.divisors.sum id) - 1 := by
  intro n hn
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

/- ## Quantitative Bound -/

/-- φ(n) ≥ 2 for n ≥ 3: φ(n) is even (Nat.totient_even) and positive
    (Nat.totient_pos), hence ≥ 2. -/
theorem totient_ge_two (n : ℕ) (hn : n ≥ 3) : n.totient ≥ 2 := by
  have hpos : 0 < n.totient := Nat.totient_pos (by omega)
  have heven : Even n.totient := Nat.totient_even (by omega : 2 < n)
  obtain ⟨k, hk⟩ := heven
  omega

/-- Any n > 1 reaches a prime in at most n − 2 iterations.
    This gives the bound F(n) ≤ n − 2, i.e., F(n) = O(n).
    Proof: strong induction. Primes need 0 steps. For composite n ≥ 4,
    T(n) < n (by iterate_decreasing) and T(n) > 1 (since φ(n) ≥ 2),
    so by IH, T(n) reaches prime in ≤ T(n) − 2 steps, giving
    n reaches prime in ≤ T(n) − 1 ≤ n − 2 steps. -/
theorem iteration_reaches_prime_in :
    ∀ n : ℕ, n > 1 → ∃ k : ℕ, k ≤ n - 2 ∧ (totientIterate n k).Prime := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases hp : n.Prime
    · exact ⟨0, by omega, hp⟩
    · -- n > 1 and not prime, so n ≥ 4
      have hn4 : n ≥ 4 := by
        by_contra h; push_neg at h
        interval_cases n <;> simp_all [Nat.Prime]
      have hdec := iterate_decreasing n (by omega) hp
      -- totientPlusOne n > 1: φ(n) ≥ 2 for n ≥ 3, so φ(n)+1 ≥ 3
      have hm_gt1 : totientPlusOne n > 1 := by
        unfold totientPlusOne
        have := totient_ge_two n (by omega)
        omega
      obtain ⟨k, hk_le, hk_prime⟩ := ih (totientPlusOne n) hdec hm_gt1
      refine ⟨k + 1, ?_, ?_⟩
      · -- k + 1 ≤ n - 2: k ≤ T(n) - 2 and T(n) ≤ n - 1
        omega
      · -- totientIterate n (k+1) = totientIterate (T(n)) k
        unfold totientIterate
        rw [Function.iterate_succ, Function.comp_apply]
        exact hk_prime

/- ## Small Cases -/

/-- φ(2) + 1 = 2: the prime 2 is a fixed point. -/
theorem two_fixed_point : totientPlusOne 2 = 2 := by
  native_decide

/-- φ(4) + 1 = 3: reaches prime 3 in one step.
    Previously axiomatized; now proved by computation. -/
theorem four_to_three : totientPlusOne 4 = 3 := by
  native_decide

/-- F(n) = 1 infinitely often: the set {n > 1 | φ(n)+1 prime} is infinite.
    Proof: for every odd prime p, φ(2p) = φ(2)·φ(p) = 1·(p−1), so
    φ(2p)+1 = p is prime. Since odd primes are infinite, so is this set. -/
theorem one_iteration_infinite :
    {n : ℕ | n > 1 ∧ (totientPlusOne n).Prime}.Infinite := by
  -- The set of odd primes {p prime | p ≠ 2} is infinite
  have h_odd_inf : (setOf Nat.Prime \ {2}).Infinite :=
    Nat.infinite_setOf_prime.diff (Set.finite_singleton 2)
  -- Map odd primes to our target set via p ↦ 2p (injective on ℕ)
  apply Set.Infinite.mono _
    (Set.Infinite.image (2 * ·) h_odd_inf (fun a _ b _ h => by omega))
  -- Show {2p | p odd prime} ⊆ {n > 1 | (totientPlusOne n).Prime}
  rintro n ⟨p, hp_mem, rfl⟩
  have hp : p.Prime := (Set.mem_diff _).mp hp_mem |>.1
  have hp2 : p ≠ 2 := fun h =>
    (Set.mem_diff _).mp hp_mem |>.2 (Set.mem_singleton_iff.mpr h)
  refine ⟨by omega, ?_⟩
  -- Key computation: totientPlusOne (2*p) = p
  suffices h : totientPlusOne (2 * p) = p from h ▸ hp
  unfold totientPlusOne
  have hcop : Nat.Coprime 2 p :=
    Nat.coprime_two_left.mpr (hp.odd_of_ne_two hp2)
  rw [Nat.totient_mul hcop, Nat.totient_prime Nat.prime_two, Nat.totient_prime hp]
  have := hp.two_le; omega
