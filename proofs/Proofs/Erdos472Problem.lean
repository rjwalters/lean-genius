/-
# Erdős Problem 472: Ulam Prime Sequences

Given an initial finite sequence of primes `q₁ < ⋯ < qₘ`, extend it so
that `q_{n+1}` is the smallest prime of the form `qₙ + qᵢ − 1` for some
`i ≤ n`. Does there exist an initial sequence such that the resulting
sequence is infinite?

A problem due to Ulam. Starting with `3, 5`, the sequence continues
`3, 5, 7, 11, 13, 17, …` and may be infinite.

*Reference:* [erdosproblems.com/472](https://www.erdosproblems.com/472),
Erdős–Graham (1980).
-/

import Mathlib

/- ## Ulam prime extension -/

/-- Given a list of primes and its last element, a candidate next prime is
`last + qᵢ - 1` for some `qᵢ` in the list, and must be prime. -/
def IsCandidateNext (seq : List ℕ) (last : ℕ) (p : ℕ) : Prop :=
    p.Prime ∧ ∃ q ∈ seq, p = last + q - 1

/-- An Ulam prime sequence starting from a seed: an infinite function
`ℕ → ℕ` where the first `m` values match the seed, each value is prime,
the sequence is strictly increasing, and each `f(n+1)` is the smallest
prime of the form `f(n) + f(i) - 1` for some `i ≤ n`. -/
def IsUlamPrimeSeq (seed : List ℕ) (f : ℕ → ℕ) : Prop :=
    -- seed values match
    (∀ i : Fin seed.length, f i.val = seed.get i) ∧
    -- all values are prime
    (∀ n : ℕ, (f n).Prime) ∧
    -- strictly increasing
    (∀ n : ℕ, f n < f (n + 1)) ∧
    -- extension rule: f(n+1) is the smallest prime of the form f(n) + f(i) - 1
    (∀ n : ℕ, seed.length - 1 ≤ n →
      IsCandidateNext (List.ofFn (fun i : Fin (n + 1) => f i)) (f n) (f (n + 1)) ∧
      ∀ p : ℕ, p < f (n + 1) →
        IsCandidateNext (List.ofFn (fun i : Fin (n + 1) => f i)) (f n) p → False)

/- ## Main conjecture -/

/-- Erdős Problem 472 (Ulam): There exists a finite seed of primes such
that the Ulam prime extension produces an infinite sequence. -/
def ErdosProblem472 : Prop :=
    ∃ (seed : List ℕ),
      (∀ p ∈ seed, p.Prime) ∧
      seed.length ≥ 2 ∧
      List.Pairwise (· < ·) seed ∧
      ∃ f : ℕ → ℕ, IsUlamPrimeSeq seed f

/- ## Known example -/

/-- Starting with `[3, 5]`, the sequence `3, 5, 7, 11, 13, 17, …` is
conjectured to be an infinite Ulam prime sequence. -/
def ulamSeed35 : List ℕ := [3, 5]

/-- The seed `[3, 5]` consists of primes. -/
theorem ulamSeed35_prime : ∀ p ∈ ulamSeed35, p.Prime := by decide

/-- The seed `[3, 5]` is sorted in increasing order. -/
theorem ulamSeed35_sorted : List.Pairwise (· < ·) ulamSeed35 := by decide

/-- The seed `[3, 5]` has at least 2 elements. -/
theorem ulamSeed35_length : ulamSeed35.length ≥ 2 := by decide

/- ## Basic properties -/

/-- The candidate `f(n) + f(n) - 1 = 2f(n) - 1` is always odd for `f(n) ≥ 2`.
This means the "self-candidate" (using f(n) itself as qᵢ) always produces an
odd number, which could be prime. -/
theorem candidate_self_odd (p : ℕ) (hp : 2 ≤ p) : ¬Even (p + p - 1) := by
  intro ⟨k, hk⟩
  omega

/-- In any Ulam prime sequence, all values are at least 2. -/
theorem ulam_seq_ge_two (seed : List ℕ) (f : ℕ → ℕ) (hf : IsUlamPrimeSeq seed f)
    (n : ℕ) : 2 ≤ f n :=
  (hf.2.1 n).two_le

/-- In any Ulam prime sequence, consecutive differences are at least 2
(since all terms are odd primes after possibly 2, and the sequence is increasing).
If f(n) ≥ 3 (odd prime) and f(n+1) > f(n) is also prime, then f(n+1) ≥ f(n) + 2. -/
theorem ulam_seq_gap (seed : List ℕ) (f : ℕ → ℕ) (hf : IsUlamPrimeSeq seed f)
    (n : ℕ) : f n + 2 ≤ f (n + 1) ∨ (f n = 2 ∧ f (n + 1) = 3) := by
  have hpn := hf.2.1 n
  have hpn1 := hf.2.1 (n + 1)
  have hlt := hf.2.2.1 n
  by_cases h2 : f n = 2
  · by_cases h3 : f (n + 1) = 3
    · right; exact ⟨h2, h3⟩
    · left
      have : f (n + 1) ≥ 3 := by omega
      have hodd : ¬ 2 ∣ f (n + 1) := by
        intro hdvd
        have := hpn1.eq_one_or_self_of_dvd 2 hdvd
        omega
      omega
  · left
    have hge3 : f n ≥ 3 := by
      have := hpn.two_le; omega
    have hodd_n : ¬ 2 ∣ f n := by
      intro hdvd; have := hpn.eq_one_or_self_of_dvd 2 hdvd; omega
    have hneq : f (n + 1) ≠ f n + 1 := by
      intro heq
      have : 2 ∣ f (n + 1) := by
        rw [heq]; omega
      have := hpn1.eq_one_or_self_of_dvd 2 this
      omega
    omega

/- ## Computable Ulam step function -/

/-- Fold to find minimum of a list of natural numbers. Returns 0 if empty. -/
def listMin : List ℕ → ℕ
  | [] => 0
  | [x] => x
  | x :: xs => min x (listMin xs)

/-- Compute candidates: for each qᵢ in the sequence, compute last + qᵢ - 1,
filter for primes, and return the minimum. Returns 0 if no candidate found. -/
def ulamNextCandidate (seq : List ℕ) : ℕ :=
  let last := seq.getLast!
  let candidates := seq.filterMap fun q =>
    let c := last + q - 1
    if c > last ∧ Nat.Prime c then some c else none
  listMin candidates

/-- Extend an Ulam prime sequence by one step. -/
def ulamStep (seq : List ℕ) : List ℕ :=
  let next := ulamNextCandidate seq
  if next = 0 then seq else seq ++ [next]

/-- Extend an Ulam prime sequence by n steps. -/
def ulamExtend : ℕ → List ℕ → List ℕ
  | 0, seq => seq
  | n + 1, seq => ulamExtend n (ulamStep seq)

/- ## Computational verification of the {3, 5} sequence -/

-- The first several terms starting from [3, 5]:
-- Step 0: [3, 5], last = 5
--   candidates: 5 + 3 - 1 = 7 (prime), 5 + 5 - 1 = 9 (not prime)
--   next = 7
-- Step 1: [3, 5, 7], last = 7
--   candidates: 7 + 3 - 1 = 9 (not prime), 7 + 5 - 1 = 11 (prime), 7 + 7 - 1 = 13 (prime)
--   next = 11
-- Step 2: [3, 5, 7, 11], last = 11
--   candidates: 11 + 3 - 1 = 13 (prime), 11 + 5 - 1 = 15 (not prime),
--              11 + 7 - 1 = 17 (prime), 11 + 11 - 1 = 21 (not prime)
--   next = 13
-- Step 3: [3, 5, 7, 11, 13], last = 13
--   candidates: 13 + 3 - 1 = 15 (not), 13 + 5 - 1 = 17 (prime),
--              13 + 7 - 1 = 19 (prime), 13 + 11 - 1 = 23 (prime), 13 + 13 - 1 = 25 (not)
--   next = 17

-- Verify individual terms
theorem ulam35_term2 : ulamNextCandidate [3, 5] = 7 := by native_decide
theorem ulam35_term3 : ulamNextCandidate [3, 5, 7] = 11 := by native_decide
theorem ulam35_term4 : ulamNextCandidate [3, 5, 7, 11] = 13 := by native_decide
theorem ulam35_term5 : ulamNextCandidate [3, 5, 7, 11, 13] = 17 := by native_decide

/-- The sequence starting from [3, 5] produces the first several terms,
matching the known sequence 3, 5, 7, 11, 13, 17. -/
theorem ulam35_first_terms :
    ulamExtend 4 [3, 5] = [3, 5, 7, 11, 13, 17] := by native_decide

/- ## Structural observations -/

/-- If both last and q are odd and q ≥ 1, then the candidate last + q - 1 is odd
(since odd + odd - 1 = odd). -/
theorem candidates_odd_of_odd (last q : ℕ)
    (hlast : ¬Even last) (hq : ¬Even q) (hq_pos : q ≥ 1) :
    ¬Even (last + q - 1) := by
  intro ⟨k, hk⟩
  rcases Nat.even_or_odd last with hlast' | ⟨a, ha⟩
  · exact absurd hlast' hlast
  · rcases Nat.even_or_odd q with hq' | ⟨b, hb⟩
    · exact absurd hq' hq
    · omega

/-- For odd p ≥ 3, p + 2 - 1 = p + 1 is even. So the candidate from seed element 2
is always even for odd primes, hence never prime. -/
theorem seed_two_gives_even (p : ℕ) (hp : p ≥ 3) (hodd : Odd p) : Even (p + 2 - 1) := by
  obtain ⟨k, hk⟩ := hodd
  exact ⟨k + 1, by omega⟩

/-- For odd p and odd q, the candidate p + q - 1 is odd,
hence potentially prime. This is why odd seeds are preferred. -/
theorem odd_candidate_from_odd (p q : ℕ) (hp : Odd p) (hq : Odd q) :
    Odd (p + q - 1) := by
  obtain ⟨a, ha⟩ := hp
  obtain ⟨b, hb⟩ := hq
  refine ⟨a + b, ?_⟩
  omega

/- ## Further extensions -/

-- Verify more terms of the sequence
theorem ulam35_term6 : ulamNextCandidate [3, 5, 7, 11, 13, 17] = 19 := by native_decide
theorem ulam35_term7 : ulamNextCandidate [3, 5, 7, 11, 13, 17, 19] = 23 := by native_decide

/-- The sequence starting from [3, 5] extends to at least 8 terms. -/
theorem ulam35_extends_8 :
    ulamExtend 6 [3, 5] = [3, 5, 7, 11, 13, 17, 19, 23] := by native_decide

/-- All terms in the first 8 elements of the {3,5} sequence are prime. -/
theorem ulam35_all_prime_8 :
    ∀ p ∈ [3, 5, 7, 11, 13, 17, 19, 23], Nat.Prime p := by decide

/-- All terms in the first 8 elements are strictly increasing. -/
theorem ulam35_increasing_8 :
    List.Pairwise (· < ·) [3, 5, 7, 11, 13, 17, 19, 23] := by decide

/- ## General structural bounds -/

/-- In any Ulam prime sequence from a seed with all primes ≥ 3,
    every term is ≥ 3. Proof: f(0) = seed[0] ≥ 3, and the sequence
    is strictly increasing, so f(n+1) > f(n) ≥ 3. -/
theorem ulam_seq_ge_three (seed : List ℕ) (f : ℕ → ℕ) (hf : IsUlamPrimeSeq seed f)
    (hseed : ∀ p ∈ seed, p ≥ 3) (hlen : seed.length ≥ 1) (n : ℕ) : f n ≥ 3 := by
  induction n with
  | zero =>
    have h0 : (0 : ℕ) < seed.length := by omega
    rw [hf.1 ⟨0, h0⟩]
    exact hseed _ (List.get_mem seed 0 h0)
  | succ n ih =>
    have := hf.2.2.1 n
    omega

/-- No term in such a sequence equals 2. -/
theorem ulam_seq_ne_two (seed : List ℕ) (f : ℕ → ℕ) (hf : IsUlamPrimeSeq seed f)
    (hseed : ∀ p ∈ seed, p ≥ 3) (hlen : seed.length ≥ 1) (n : ℕ) : f n ≠ 2 := by
  have := ulam_seq_ge_three seed f hf hseed hlen n
  omega

/-- In any Ulam prime sequence from a seed with all primes ≥ 3,
    every term is odd. Since 2 is the only even prime and no term
    equals 2, all terms must be odd. -/
theorem ulam_seq_odd (seed : List ℕ) (f : ℕ → ℕ) (hf : IsUlamPrimeSeq seed f)
    (hseed : ∀ p ∈ seed, p ≥ 3) (hlen : seed.length ≥ 1) (n : ℕ) : Odd (f n) := by
  have hne2 := ulam_seq_ne_two seed f hf hseed hlen n
  have hprime := hf.2.1 n
  -- Every prime is either 2 or odd. Since f n ≠ 2, it must be odd.
  rcases Nat.even_or_odd (f n) with heven | hodd
  · exfalso
    obtain ⟨r, hr⟩ := heven
    have h2dvd : 2 ∣ f n := ⟨r, by omega⟩
    rcases hprime.eq_one_or_self_of_dvd 2 h2dvd with h | h <;> omega
  · exact hodd

/-- The {3,5} seed satisfies the ≥ 3 condition. -/
theorem ulam35_seed_ge_three : ∀ p ∈ ulamSeed35, p ≥ 3 := by decide

/- ## Growth observation -/

/-- In the {3,5} Ulam sequence, the density of terms among primes suggests
the sequence might contain all primes ≥ 3. If true, this would immediately
give infiniteness (since there are infinitely many primes). This remains open. -/
axiom ulam35_contains_all_odd_primes_conjecture :
    ∀ p : ℕ, p.Prime → p ≥ 3 →
      ∃ n : ℕ, ∃ seq, seq = ulamExtend n [3, 5] ∧ p ∈ seq

/- ## Step analysis via seed elements -/

/-- In any Ulam prime sequence starting from {3, 5}, f(0) = 3. -/
theorem ulam35_f0_eq_three (f : ℕ → ℕ) (hf : IsUlamPrimeSeq ulamSeed35 f) : f 0 = 3 := by
  have h := hf.1 ⟨0, by decide⟩
  have : ulamSeed35.get ⟨0, by decide⟩ = 3 := rfl
  rw [this] at h; exact h

/-- In any Ulam prime sequence starting from {3, 5}, f(1) = 5. -/
theorem ulam35_f1_eq_five (f : ℕ → ℕ) (hf : IsUlamPrimeSeq ulamSeed35 f) : f 1 = 5 := by
  have h := hf.1 ⟨1, by decide⟩
  have : ulamSeed35.get ⟨1, by decide⟩ = 5 := rfl
  rw [this] at h; exact h

/-- In the {3, 5} Ulam sequence, consecutive terms always differ by at least 2.
    Specializes ulam_seq_gap: the exceptional case f(n) = 2 is impossible since
    all terms are ≥ 3. -/
theorem ulam35_gap_ge_two (f : ℕ → ℕ) (hf : IsUlamPrimeSeq ulamSeed35 f) (n : ℕ) :
    f n + 2 ≤ f (n + 1) := by
  rcases ulam_seq_gap ulamSeed35 f hf n with h | ⟨h2, _⟩
  · exact h
  · exact absurd h2 (ulam_seq_ne_two ulamSeed35 f hf (by decide) (by decide) n)

/-- 3 = f(0) always appears in the candidate list at any step n. -/
theorem ulam35_three_in_ofFn (f : ℕ → ℕ) (hf : IsUlamPrimeSeq ulamSeed35 f) (n : ℕ) :
    (3 : ℕ) ∈ List.ofFn (fun i : Fin (n + 1) => f i) := by
  rw [List.mem_ofFn]
  exact ⟨⟨0, Nat.zero_lt_succ n⟩, ulam35_f0_eq_three f hf⟩

/-- 5 = f(1) appears in the candidate list at step n when n ≥ 1. -/
theorem ulam35_five_in_ofFn (f : ℕ → ℕ) (hf : IsUlamPrimeSeq ulamSeed35 f)
    (n : ℕ) (hn : 1 ≤ n) :
    (5 : ℕ) ∈ List.ofFn (fun i : Fin (n + 1) => f i) := by
  rw [List.mem_ofFn]
  exact ⟨⟨1, by omega⟩, ulam35_f1_eq_five f hf⟩

/-- Twin prime step: if f(n) and f(n)+2 form a twin prime pair, f(n+1) = f(n)+2.
    Proof: 3 is always in the sequence (f(0) = 3), so f(n)+3-1 = f(n)+2 is always
    a candidate when prime. Minimality gives f(n+1) ≤ f(n)+2; the gap bound gives
    f(n+1) ≥ f(n)+2. -/
theorem ulam35_twin_prime_step (f : ℕ → ℕ) (hf : IsUlamPrimeSeq ulamSeed35 f)
    (n : ℕ) (hn : 1 ≤ n) (h_twin : (f n + 2).Prime) :
    f (n + 1) = f n + 2 := by
  have hlen : ulamSeed35.length - 1 ≤ n := by norm_num [ulamSeed35]; omega
  obtain ⟨_, hmin⟩ := hf.2.2.2 n hlen
  have hcand : IsCandidateNext (List.ofFn (fun i : Fin (n + 1) => f i)) (f n) (f n + 2) := by
    refine ⟨h_twin, 3, ulam35_three_in_ofFn f hf n, ?_⟩; omega
  have hle : f (n + 1) ≤ f n + 2 := by
    by_contra hlt; push_neg at hlt
    exact hmin (f n + 2) hlt hcand
  exact Nat.le_antisymm hle (ulam35_gap_ge_two f hf n)

/-- Cousin prime upper bound: if f(n)+4 is prime (n ≥ 1), then f(n+1) ≤ f(n)+4.
    Since 5 = f(1) is always in the sequence for n ≥ 1, f(n)+5-1 = f(n)+4 is a candidate. -/
theorem ulam35_cousin_prime_upper (f : ℕ → ℕ) (hf : IsUlamPrimeSeq ulamSeed35 f)
    (n : ℕ) (hn : 1 ≤ n) (h_cousin : (f n + 4).Prime) :
    f (n + 1) ≤ f n + 4 := by
  have hlen : ulamSeed35.length - 1 ≤ n := by norm_num [ulamSeed35]; omega
  obtain ⟨_, hmin⟩ := hf.2.2.2 n hlen
  have hcand : IsCandidateNext (List.ofFn (fun i : Fin (n + 1) => f i)) (f n) (f n + 4) := by
    refine ⟨h_cousin, 5, ulam35_five_in_ofFn f hf n hn, ?_⟩; omega
  by_contra hlt; push_neg at hlt
  exact hmin (f n + 4) hlt hcand

/- ## Step gap refinements -/

/-- f(n)+3 is never prime in a {3,5} Ulam sequence: since f(n) is odd, f(n)+3 is even
    and greater than 2, hence composite. -/
theorem ulam35_f_plus_3_not_prime (f : ℕ → ℕ) (hf : IsUlamPrimeSeq ulamSeed35 f) (n : ℕ) :
    ¬(f n + 3).Prime := by
  have hodd := ulam_seq_odd ulamSeed35 f hf (by decide) (by decide) n
  have hge := ulam_seq_ge_three ulamSeed35 f hf (by decide) (by decide) n
  obtain ⟨k, hk⟩ := hodd
  intro hprime
  have h2dvd : 2 ∣ f n + 3 := ⟨k + 2, by omega⟩
  have := hprime.eq_one_or_self_of_dvd 2 h2dvd
  omega

/-- The value f(n)+3 is never a valid candidate next prime in any {3,5} Ulam sequence:
    IsCandidateNext requires primality, but f(n)+3 is always even (hence composite). -/
theorem ulam35_no_candidate_f_plus_3 (f : ℕ → ℕ) (hf : IsUlamPrimeSeq ulamSeed35 f) (n : ℕ) :
    ¬IsCandidateNext (List.ofFn (fun i : Fin (n + 1) => f i)) (f n) (f n + 3) := by
  intro ⟨hprime, _⟩
  exact ulam35_f_plus_3_not_prime f hf n hprime

/-- If f(n)+2 is not prime (no twin prime at f(n)) and n ≥ 1, then f(n+1) ≥ f(n)+4.
    Proof: f(n+1) ≥ f(n)+2 (gap bound); f(n+2) ≠ f(n)+2 since f(n)+2 is composite;
    f(n+1) ≠ f(n)+3 since f(n)+3 is even (hence not prime). So f(n+1) ≥ f(n)+4. -/
theorem ulam35_gap_ge_four_no_twin (f : ℕ → ℕ) (hf : IsUlamPrimeSeq ulamSeed35 f)
    (n : ℕ) (hn : 1 ≤ n) (h_no_twin : ¬(f n + 2).Prime) :
    f n + 4 ≤ f (n + 1) := by
  have hgap := ulam35_gap_ge_two f hf n
  have hpn1 := hf.2.1 (n + 1)
  have hne2 : f (n + 1) ≠ f n + 2 := by
    intro h; rw [h] at hpn1; exact h_no_twin hpn1
  have hne3 : f (n + 1) ≠ f n + 3 := by
    intro h; rw [h] at hpn1
    exact ulam35_f_plus_3_not_prime f hf n hpn1
  omega

/-- Cousin prime exact step: if f(n)+2 is not prime and f(n)+4 is prime (n ≥ 1), then
    f(n+1) = f(n)+4. Combines the lower bound (gap_ge_four_no_twin) with the upper
    bound (cousin_prime_upper). -/
theorem ulam35_cousin_prime_exact (f : ℕ → ℕ) (hf : IsUlamPrimeSeq ulamSeed35 f)
    (n : ℕ) (hn : 1 ≤ n) (h_no_twin : ¬(f n + 2).Prime) (h_cousin : (f n + 4).Prime) :
    f (n + 1) = f n + 4 :=
  Nat.le_antisymm (ulam35_cousin_prime_upper f hf n hn h_cousin)
    (ulam35_gap_ge_four_no_twin f hf n hn h_no_twin)

/-- Self-candidate upper bound: if 2·f(n) - 1 is prime (n ≥ 1), then f(n+1) ≤ 2·f(n) - 1.
    Proof: f(n) is always in its own candidate list (as the n-th element), so
    f(n) + f(n) - 1 = 2·f(n) - 1 is a candidate when prime. Minimality gives the bound. -/
theorem ulam35_self_candidate_upper (f : ℕ → ℕ) (hf : IsUlamPrimeSeq ulamSeed35 f)
    (n : ℕ) (hn : 1 ≤ n) (h_self : (2 * f n - 1).Prime) :
    f (n + 1) ≤ 2 * f n - 1 := by
  have hlen : ulamSeed35.length - 1 ≤ n := by norm_num [ulamSeed35]; omega
  obtain ⟨_, hmin⟩ := hf.2.2.2 n hlen
  have hge3 := ulam_seq_ge_three ulamSeed35 f hf (by decide) (by decide) n
  have hself_cand : IsCandidateNext (List.ofFn (fun i : Fin (n + 1) => f i)) (f n) (2 * f n - 1) := by
    refine ⟨h_self, f n, ?_, ?_⟩
    · rw [List.mem_ofFn]
      exact ⟨⟨n, Nat.lt_succ_self n⟩, rfl⟩
    · omega
  by_contra hlt
  push_neg at hlt
  exact hmin (2 * f n - 1) hlt hself_cand
