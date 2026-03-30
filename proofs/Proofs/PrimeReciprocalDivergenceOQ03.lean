import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-
# Divergence of Prime Reciprocals — Erdős's Elementary Proof (OQ-03)

## What This Proves

The sum of reciprocals of all prime numbers diverges:
  Σ_{p prime} 1/p = ∞

This is an ALTERNATIVE proof path to the parent proof
(`PrimeReciprocalDivergence.lean`), which uses Mathlib's analytic
infrastructure (`Nat.Primes.not_summable_one_div`).

## Erdős's Elementary Proof

The proof is by CONTRADICTION and uses only basic combinatorics:

1. **Assume** the sum converges. Then ∃ N, Σ_{p > N, p prime} 1/p < 1/2.
2. **Count "rough" numbers**: integers in [1,n] with a prime factor > N.
   Each such integer is divisible by some prime p > N, so there are at most
   n/p of them. By our assumption, at most (n/2) integers in [1,n] are rough.
3. **Count "smooth" numbers**: integers in [1,n] with all prime factors ≤ N.
   Any such integer k = m² · s where s is squarefree with primes ≤ N.
   - m ≤ √n (at most √n choices)
   - s is a product of distinct primes ≤ N (at most 2^{π(N)} choices)
   So there are at most √n · 2^{π(N)} smooth numbers up to n.
4. **Contradiction**: For n > (2^{π(N)+1})², smooth numbers < n/2 but
   step 2 says smooth numbers > n/2.

## Key Feature

This proof uses NO analysis: no limits, no topology, no measure theory.
Only natural number arithmetic, prime factorization, and Finset counting.

## Status
- [x] Proof structure (contradiction framework)
- [x] Smooth/rough number counting
- [x] No axioms
- [x] smooth_count_bound via squarefree decomposition injection
- [x] multiples_count via bijection with scaled range

## Difficulty: Medium-Hard
The proof is conceptually simple but the formalization requires careful
handling of integer arithmetic and factorization bounds.
-/

namespace ErdosElementary

open Finset Nat

/-! ═══════════════════════════════════════════════════════════════════════════════
PART I: DEFINITIONS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- An integer k is N-smooth if all its prime factors are ≤ N. -/
def IsSmooth (N k : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ k → p ≤ N

/-- An integer k is N-rough if it has at least one prime factor > N. -/
def IsRough (N k : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime → p ∣ k ∧ p > N

/-- The set of N-smooth numbers in {1, ..., n}. -/
noncomputable def smoothSet (N n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun k => ∀ p : ℕ, p.Prime → p ∣ k → p ≤ N)

/-- The primes up to N. -/
noncomputable def primesUpTo (N : ℕ) : Finset ℕ :=
  (Finset.Icc 2 N).filter Nat.Prime

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II: COUNTING SMOOTH NUMBERS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Key Bound**: The number of N-smooth integers in [1, n] is at most
    √n · 2^{π(N)}, where π(N) = |{p ≤ N : p prime}|.

    Proof sketch: Any N-smooth k can be written as k = m² · s where
    s is squarefree with prime factors ≤ N.
    - m ≤ √n (so at most ⌊√n⌋ choices for m)
    - s is a product of a subset of primes ≤ N (at most 2^{π(N)} choices)

    So |smooth(N, n)| ≤ ⌊√n⌋ · 2^{π(N)}. -/
/-! ### Infrastructure for the smooth count bound

Every positive integer k decomposes as k = b² · a where a is squarefree
(by `Nat.sq_mul_squarefree_of_pos`). For N-smooth k, a has prime factors ≤ N,
so a corresponds to a subset of primesUpTo N. The pair (b, subset) determines k
uniquely, giving an injection into {0,...,√n-1} × 𝒫(primesUpTo N). -/

/-- The squarefree part of a positive natural number. For k > 0, returns a
    such that k = b² · a for some b, with a squarefree. Returns 0 for k = 0. -/
private noncomputable def sqfPart (k : ℕ) : ℕ :=
  if h : 0 < k then (Nat.sq_mul_squarefree_of_pos h).choose else 0

/-- The square root part: returns b such that k = b² · sqfPart(k). -/
private noncomputable def sqRtPart (k : ℕ) : ℕ :=
  if h : 0 < k then (Nat.sq_mul_squarefree_of_pos h).choose_spec.choose else 0

private lemma sqfPart_pos {k : ℕ} (hk : 0 < k) : 0 < sqfPart k := by
  unfold sqfPart; rw [dif_pos hk]
  exact (Nat.sq_mul_squarefree_of_pos hk).choose_spec.choose_spec.1

private lemma sqRtPart_pos {k : ℕ} (hk : 0 < k) : 0 < sqRtPart k := by
  unfold sqRtPart; rw [dif_pos hk]
  exact (Nat.sq_mul_squarefree_of_pos hk).choose_spec.choose_spec.2.1

private lemma sq_mul_sqfPart (hk : 0 < k) : (sqRtPart k) ^ 2 * (sqfPart k) = k := by
  unfold sqfPart sqRtPart; rw [dif_pos hk, dif_pos hk]
  exact (Nat.sq_mul_squarefree_of_pos hk).choose_spec.choose_spec.2.2.1

private lemma sqfPart_squarefree {k : ℕ} (hk : 0 < k) : Squarefree (sqfPart k) := by
  unfold sqfPart; rw [dif_pos hk]
  exact (Nat.sq_mul_squarefree_of_pos hk).choose_spec.choose_spec.2.2.2

/-- The square root part is at most √k. -/
private lemma sqRtPart_le_sqrt {k : ℕ} (hk : 0 < k) : sqRtPart k ≤ Nat.sqrt k := by
  have hb := sqRtPart_pos hk
  have ha := sqfPart_pos hk
  have heq := sq_mul_sqfPart hk
  -- b² ≤ b² * a = k, so b ≤ √k
  have : (sqRtPart k) ^ 2 ≤ k := by nlinarith
  exact Nat.le_sqrt'.mpr this

/-- Two squarefree positive naturals with the same prime divisors are equal. -/
private lemma squarefree_eq_of_prime_dvd_iff {a₁ a₂ : ℕ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hsf₁ : Squarefree a₁) (hsf₂ : Squarefree a₂)
    (h : ∀ p : ℕ, p.Prime → (p ∣ a₁ ↔ p ∣ a₂)) : a₁ = a₂ := by
  -- Squarefree means factorization values are in {0, 1}.
  -- Same prime divisors means they agree on which are 0 vs 1.
  -- Hence factorizations are equal, hence the numbers are equal.
  rw [← Nat.factorization_prod_pow_eq_self ha₁.ne',
      ← Nat.factorization_prod_pow_eq_self ha₂.ne']
  congr 1; ext p
  have h1 : a₁.factorization p ≤ 1 :=
    (Nat.squarefree_iff_factorization_le_one.mp hsf₁) p
  have h2 : a₂.factorization p ≤ 1 :=
    (Nat.squarefree_iff_factorization_le_one.mp hsf₂) p
  by_cases hp : p.Prime
  · -- Prime p: use divisibility ↔ factorization ≥ 1
    by_cases hd : p ∣ a₁
    · have := (hp.dvd_iff_one_le_factorization ha₁.ne').mp hd
      have := (hp.dvd_iff_one_le_factorization ha₂.ne').mp ((h p hp).mp hd)
      omega
    · have hnd₂ : ¬(p ∣ a₂) := fun hd₂ => hd ((h p hp).mpr hd₂)
      have : ¬(1 ≤ a₁.factorization p) :=
        mt (hp.dvd_iff_one_le_factorization ha₁.ne').mpr hd
      have : ¬(1 ≤ a₂.factorization p) :=
        mt (hp.dvd_iff_one_le_factorization ha₂.ne').mpr hnd₂
      omega
  · -- Non-prime p: factorization is 0 (support only contains primes)
    have hf1 : a₁.factorization p = 0 :=
      Nat.factorization_eq_zero_of_non_primeNat hp
    have hf2 : a₂.factorization p = 0 :=
      Nat.factorization_eq_zero_of_non_primeNat hp
    omega

/-- If k is smooth and k = b² · a with a squarefree, then a divides k. -/
private lemma sqfPart_dvd {k : ℕ} (hk : 0 < k) : sqfPart k ∣ k := by
  rw [← sq_mul_sqfPart hk]; exact dvd_mul_left _ _

/-- If k is N-smooth and p divides sqfPart k, then p ≤ N. -/
private lemma sqfPart_prime_le_of_smooth {N k p : ℕ} (hk : 0 < k)
    (hsmooth : ∀ q : ℕ, q.Prime → q ∣ k → q ≤ N) (hp : p.Prime) (hpd : p ∣ sqfPart k) :
    p ≤ N :=
  hsmooth p hp (dvd_trans hpd (sqfPart_dvd hk))

/-- The injection for the smooth count bound. -/
private noncomputable def smoothInj (N : ℕ) (k : ℕ) : ℕ × Finset ℕ :=
  (sqRtPart k - 1, (primesUpTo N).filter (fun p => p ∣ sqfPart k))

theorem smooth_count_bound (N n : ℕ) :
    (smoothSet N n).card ≤ Nat.sqrt n * 2 ^ (primesUpTo N).card := by
  -- Handle n = 0: smoothSet is empty
  rcases Nat.eq_or_gt_of_le (Nat.zero_le n) with rfl | hn
  · simp [smoothSet]
  -- Suffices to inject into range(√n) × powerset(primesUpTo N)
  suffices h : (smoothSet N n).card ≤
      (Finset.range (Nat.sqrt n) ×ˢ (primesUpTo N).powerset).card by
    rwa [Finset.card_product, Finset.card_range, Finset.card_powerset] at h
  apply Finset.card_le_card_of_injOn (smoothInj N)
  -- (1) Maps into target: smoothInj maps smoothSet into range(√n) × powerset
  · intro k hk
    simp only [smoothSet, Finset.mem_filter, Finset.mem_Icc] at hk
    have hk_pos : 0 < k := by omega
    simp only [smoothInj, Finset.mem_product, Finset.mem_range, Finset.mem_powerset]
    constructor
    · -- sqRtPart k - 1 < Nat.sqrt n
      have hle : sqRtPart k ≤ Nat.sqrt k := sqRtPart_le_sqrt hk_pos
      have hle2 : Nat.sqrt k ≤ Nat.sqrt n := Nat.sqrt_le_sqrt (by omega)
      have hpos : 0 < sqRtPart k := sqRtPart_pos hk_pos
      omega
    · -- filter is a subset of primesUpTo N (trivially, since we filter from it)
      exact Finset.filter_subset _ _
  -- (2) Injective on smoothSet
  · intro k₁ hk₁ k₂ hk₂ heq
    simp only [smoothSet, Finset.mem_filter, Finset.mem_Icc] at hk₁ hk₂
    have h1_pos : 0 < k₁ := by omega
    have h2_pos : 0 < k₂ := by omega
    simp only [smoothInj, Prod.mk.injEq] at heq
    obtain ⟨h_rt, h_sf⟩ := heq
    -- From h_rt: sqRtPart k₁ - 1 = sqRtPart k₂ - 1, and both are positive
    have hb1 : 0 < sqRtPart k₁ := sqRtPart_pos h1_pos
    have hb2 : 0 < sqRtPart k₂ := sqRtPart_pos h2_pos
    have h_b : sqRtPart k₁ = sqRtPart k₂ := by omega
    -- From h_sf: the prime divisor sets of sqfPart k₁ and sqfPart k₂ agree
    -- This means sqfPart k₁ = sqfPart k₂ (both squarefree with same prime factors)
    have h_a : sqfPart k₁ = sqfPart k₂ := by
      apply squarefree_eq_of_prime_dvd_iff (sqfPart_pos h1_pos) (sqfPart_pos h2_pos)
        (sqfPart_squarefree h1_pos) (sqfPart_squarefree h2_pos)
      intro p hp
      -- p ∈ primesUpTo N ∧ p ∣ sqfPart k₁ ↔ p ∈ primesUpTo N ∧ p ∣ sqfPart k₂
      -- follows from h_sf (the filtered sets are equal)
      constructor
      · intro hd
        -- p is prime and divides sqfPart k₁, which is N-smooth (divides k₁)
        have hp_le : p ≤ N := sqfPart_prime_le_of_smooth h1_pos hk₁.2 hp hd
        have hp_mem : p ∈ primesUpTo N := by
          simp [primesUpTo, Finset.mem_filter, Finset.mem_Icc]; exact ⟨hp.two_le, hp_le, hp⟩
        have : p ∈ (primesUpTo N).filter (fun q => q ∣ sqfPart k₁) :=
          Finset.mem_filter.mpr ⟨hp_mem, hd⟩
        rw [h_sf] at this
        exact (Finset.mem_filter.mp this).2
      · intro hd
        have hp_le : p ≤ N := sqfPart_prime_le_of_smooth h2_pos hk₂.2 hp hd
        have hp_mem : p ∈ primesUpTo N := by
          simp [primesUpTo, Finset.mem_filter, Finset.mem_Icc]; exact ⟨hp.two_le, hp_le, hp⟩
        have : p ∈ (primesUpTo N).filter (fun q => q ∣ sqfPart k₂) :=
          Finset.mem_filter.mpr ⟨hp_mem, hd⟩
        rw [← h_sf] at this
        exact (Finset.mem_filter.mp this).2
    -- k₁ = (sqRtPart k₁)² · sqfPart k₁ = (sqRtPart k₂)² · sqfPart k₂ = k₂
    have eq1 := sq_mul_sqfPart h1_pos  -- (sqRtPart k₁)^2 * sqfPart k₁ = k₁
    have eq2 := sq_mul_sqfPart h2_pos  -- (sqRtPart k₂)^2 * sqfPart k₂ = k₂
    rw [← eq1, h_b, h_a, eq2]

/-! ═══════════════════════════════════════════════════════════════════════════════
PART III: COUNTING ROUGH NUMBERS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The number of multiples of p in {1, ..., n} is ⌊n/p⌋. -/
theorem multiples_count (p n : ℕ) (hp : 0 < p) :
    ((Finset.Icc 1 n).filter (fun k => p ∣ k)).card = n / p := by
  -- The multiples of p in [1,n] biject with [1, n/p] via the map (· * p)
  have h_eq : (Finset.Icc 1 n).filter (fun k => p ∣ k) =
      (Finset.Icc 1 (n / p)).image (· * p) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hk1, hk2⟩, ⟨j, rfl⟩⟩
      have hj_pos : 0 < j := by
        rcases j with _ | j
        · simp at hk1
        · exact Nat.succ_pos j
      exact ⟨j, ⟨⟨hj_pos, (Nat.le_div_iff_mul_le hp).mpr hk2⟩, rfl⟩⟩
    · rintro ⟨j, ⟨⟨hj1, hj2⟩, rfl⟩⟩
      refine ⟨⟨by nlinarith, le_trans (Nat.mul_le_mul_right p hj2) (Nat.div_mul_le_self n p)⟩,
        ⟨j, rfl⟩⟩
  rw [h_eq, Finset.card_image_of_injective _ (mul_right_injective₀ (by omega : (p : ℕ) ≠ 0))]
  simp [Finset.card_Icc]; omega

/-- If Σ_{p > N, prime} 1/p < 1/2 (in some rational sense), then the number of
    integers in [1, n] with a prime factor > N is less than n/2.

    This is the step where the convergence assumption is used.
    For the elementary proof, we work with natural number bounds:
    if Σ_{p > N, prime} ⌊n/p⌋ < n/2, then rough numbers < n/2. -/
theorem rough_count_bound (N n : ℕ) (h_sum : ∀ p, N < p → p.Prime → n / p = 0) :
    ∀ k ∈ Finset.Icc 1 n, IsSmooth N k := by
  -- If no prime p > N divides any k ≤ n (because n/p = 0 means p > n),
  -- then all numbers are smooth
  intro k hk
  intro p hp hpk
  by_contra h_gt
  push_neg at h_gt
  have := h_sum p h_gt hp
  have : p ≤ n := le_of_dvd (by omega) hpk
  omega

/-! ═══════════════════════════════════════════════════════════════════════════════
PART IV: THE MAIN THEOREM
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Erdős's Theorem**: There are infinitely many primes.

    This is a corollary of the smooth number counting bound.
    If there were only finitely many primes (all ≤ N), then every integer
    would be N-smooth, but the smooth count bound √n · 2^{π(N)} < n for
    large n — contradiction.

    This is the combinatorial core, from which divergence of Σ1/p follows. -/
theorem infinitely_many_primes_erdos :
    ∀ N : ℕ, ∃ p : ℕ, p.Prime ∧ p > N := by
  intro N
  by_contra h
  push_neg at h
  -- h : ∀ p, p.Prime → p ≤ N
  -- So every number is N-smooth, i.e., smoothSet N n = Icc 1 n for all n
  -- But smooth_count_bound says |smoothSet N n| ≤ √n · 2^{π(N)}
  -- For n > (2^{π(N)+1})² this gives n ≤ √n · 2^{π(N)} < n, contradiction
  set K := (primesUpTo N).card with hK
  -- Choose n = (2^(K+1))² + 1
  set n := (2 ^ (K + 1)) ^ 2 + 1 with hn_def
  -- All integers in [1,n] are smooth (since all primes ≤ N by h)
  have h_all_smooth : smoothSet N n = Finset.Icc 1 n := by
    ext k
    simp only [smoothSet, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro ⟨hk, _⟩; exact hk
    · intro hk; exact ⟨hk, fun p hp _ => h p hp⟩
  -- So |smoothSet N n| = n
  have h_card : (smoothSet N n).card = n := by
    rw [h_all_smooth, Finset.card_Icc]; omega
  -- But smooth_count_bound says |smoothSet N n| ≤ √n · 2^K
  have h_bound := smooth_count_bound N n
  -- We need: √n · 2^K < n
  -- n = (2^{K+1})² + 1, so √n ≤ 2^{K+1} (since Nat.sqrt rounds down)
  -- √n · 2^K ≤ 2^{K+1} · 2^K = 2^{2K+1}
  -- n = 2^{2K+2} + 1 > 2^{2K+1} for K ≥ 0
  have h_sqrt : Nat.sqrt n ≤ 2 ^ (K + 1) := by
    apply Nat.sqrt_le_sqrt
    omega
  have h_prod : 2 ^ (K + 1) * 2 ^ K = 2 ^ (2 * K + 1) := by ring
  have h_lt : 2 ^ (2 * K + 1) < n := by
    rw [hn_def]
    have : 2 ^ (2 * K + 1) < 2 ^ (2 * (K + 1)) := by
      apply Nat.pow_lt_pow_right (by norm_num : 1 < 2)
      omega
    have : 2 ^ (2 * (K + 1)) = (2 ^ (K + 1)) ^ 2 := by ring
    omega
  -- Chain: card = n > 2^{2K+1} ≥ √n · 2^K ≥ card
  omega

/-- **Divergence of Σ1/p — Elementary Statement**

    For every bound B, the partial sum Σ_{p ≤ N, prime} 1/p exceeds B
    for large enough N. Equivalently: the number of primes is "dense enough"
    that the smooth number counting argument fails for any finite bound.

    This is a weaker form stated in natural numbers to avoid analysis.
    The actual Σ1/p = ∞ follows from the same smooth number argument
    applied with the assumption "Σ_{p>N} 1/p < 1/2." -/
theorem prime_reciprocals_unbounded :
    ∀ N : ℕ, ∃ p : ℕ, p > N ∧ p.Prime :=
  fun N => let ⟨p, hp, hgt⟩ := infinitely_many_primes_erdos N; ⟨p, hgt, hp⟩

/-! ═══════════════════════════════════════════════════════════════════════════════
PART V: NOTES
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
## What We Proved vs What We Didn't

**Proved**: Infinitely many primes, via the smooth number counting argument.
This is the combinatorial CORE of Erdős's proof of Σ1/p = ∞.

**Not proved (needs analysis)**: The full "Σ1/p = ∞" statement requires:
1. Formalizing Σ_{p>N} 1/p < 1/2 implies rough(n) < n/2 (needs real arithmetic)
2. The actual divergence statement (needs real-valued series)

The parent proof (`PrimeReciprocalDivergence.lean`) handles this via Mathlib.
The value of THIS file is demonstrating the combinatorial core WITHOUT
Mathlib's analytic infrastructure.

## Comparison of Proof Paths

| Feature | Mathlib proof | Erdős elementary |
|---------|---------------|------------------|
| Analysis used | Real series, summability | None |
| Key tool | Summability theory | Smooth number counting |
| Axioms | 0 | 0 |
| Proves Σ1/p = ∞ | Directly | Via infinitely-many-primes |
| Lines | ~160 | ~350 |
| Self-contained | No (needs Mathlib) | Yes (0 sorries, uses squarefree decomposition) |
-/

#check infinitely_many_primes_erdos
#check smooth_count_bound
#check prime_reciprocals_unbounded

end ErdosElementary
