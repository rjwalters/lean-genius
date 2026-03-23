/-
# Erdős Problem #1055: Prime Classification by p+1 Factorization

Classify primes by the factorization structure of p+1:
- Class 1: all prime factors of p+1 are 2 or 3 (i.e., p+1 is 3-smooth)
- Class r: all prime factors of p+1 are in class ≤ r-1, with at least one
  prime factor in class exactly r-1.

## Key Questions
1. Are there infinitely many primes in each class?
2. How does p_r^{1/r} behave, where p_r is the least prime in class r?
   - Erdős conjectured p_r^{1/r} → ∞
   - Selfridge conjectured p_r^{1/r} is bounded

## Known Data
- Least primes by class: p_1=2, p_2=13, p_3=37, p_4=73, p_5=1021 (OEIS A005113)
- The count of primes ≤ n in class r is at most n^{o(1)}

## Status: OPEN

Reference: https://erdosproblems.com/1055
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/- ## Termination Lemma -/

/-- Any prime factor q of (p+1) with q ∉ {2,3} satisfies q < p.
    Key termination argument for well-founded prime classification.
    Proof: q | (p+1) gives q ≤ p+1. q ≠ p+1 by parity (p odd ⟹ p+1 even ⟹
    p+1 not an odd prime). q ≠ p since p ∤ (p+1). So q < p. -/
theorem nonSmooth_factor_lt (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hdvd : q ∣ p + 1) (hq2 : q ≠ 2) (hq3 : q ≠ 3) :
    q < p := by
  -- q ≤ p+1 since q divides p+1 > 0
  have hle : q ≤ p + 1 := Nat.le_of_dvd (by omega) hdvd
  -- q ≠ p: if q = p then p | (p+1), but (p+1) % p = 1 ≠ 0
  have hne_p : q ≠ p := by
    intro heq
    have h1 : (p + 1) % p = 1 := by
      calc (p + 1) % p = (1 + p) % p := by rw [Nat.add_comm]
        _ = 1 % p := Nat.add_mod_right 1 p
        _ = 1 := Nat.mod_eq_of_lt hp.one_lt
    have h2 : (p + 1) % p = 0 := Nat.dvd_iff_mod_eq_zero.mp (heq ▸ hdvd)
    omega
  -- q ≠ p+1: for p = 2, q = 3 contradicts hq3; for p ≥ 3, p is odd so
  -- p+1 is even, and the only even prime is 2, giving p = 1, contradiction
  have hne_succ : q ≠ p + 1 := by
    intro heq
    by_cases h2 : p = 2
    · exact hq3 (by omega)
    · have hp_odd : Odd p := hp.odd_of_ne_two h2
      have hp1_even : Even (p + 1) := hp_odd.add_one
      have h2_dvd : 2 ∣ q := by
        rw [heq]; obtain ⟨k, hk⟩ := hp1_even; exact ⟨k, by omega⟩
      rcases hq.eq_one_or_self_of_dvd 2 h2_dvd with h | h
      · omega
      · omega
  omega

/- ## Core Definitions -/

/-- Well-founded Erdős–Selfridge class using structural recursion on p.
    Terminates because all nonSmooth prime factors q of (p+1) satisfy q < p
    (proved in nonSmooth_factor_lt).
    - Class 0: not a prime (sentinel)
    - Class 1: all prime factors of p+1 are in {2, 3} (3-smooth successor)
    - Class r ≥ 2: 1 + max class of non-{2,3} prime factors of p+1 -/
def primeClassWF (p : ℕ) : ℕ :=
    if ¬ Nat.Prime p then 0
    else
      let factors := (p + 1).primeFactorsList.dedup
      let nonSmooth := factors.filter (fun q => q != 2 && q != 3)
      if nonSmooth.isEmpty then 1
      else 1 + nonSmooth.foldl (fun acc q =>
        if _h : q < p then max acc (primeClassWF q) else acc) 0
termination_by p

/-- The Erdős–Selfridge class of a prime. Returns 0 for non-primes.
    Uses well-founded recursion for clean structural proofs. -/
def primeClass (p : ℕ) : ℕ := primeClassWF p

/-- A prime p is in class r if primeClass p = r and p is prime. -/
def IsInClass (p : ℕ) (r : ℕ) : Prop :=
  p.Prime ∧ primeClass p = r

/- ## Verified Class Values -/

-- Class 1 primes: p+1 is 3-smooth
theorem class_2 : primeClass 2 = 1 := by native_decide
theorem class_3 : primeClass 3 = 1 := by native_decide
theorem class_5 : primeClass 5 = 1 := by native_decide
theorem class_7 : primeClass 7 = 1 := by native_decide
theorem class_11 : primeClass 11 = 1 := by native_decide
theorem class_17 : primeClass 17 = 1 := by native_decide
theorem class_23 : primeClass 23 = 1 := by native_decide
theorem class_31 : primeClass 31 = 1 := by native_decide

-- Class 2 primes: p+1 has a class-1 prime factor beyond {2,3}
theorem class_13 : primeClass 13 = 2 := by native_decide
theorem class_19 : primeClass 19 = 2 := by native_decide
theorem class_29 : primeClass 29 = 2 := by native_decide
theorem class_41 : primeClass 41 = 2 := by native_decide
theorem class_43 : primeClass 43 = 2 := by native_decide

-- Class 3 primes
theorem class_37 : primeClass 37 = 3 := by native_decide
theorem class_103 : primeClass 103 = 3 := by native_decide
theorem class_113 : primeClass 113 = 3 := by native_decide

-- Class 4 primes
theorem class_73 : primeClass 73 = 4 := by native_decide

-- Class 5 primes (p_5 = 1021, OEIS A005113)
theorem class_1021 : primeClass 1021 = 5 := by native_decide

-- Non-primes return 0
theorem class_nonprime_4 : primeClass 4 = 0 := by native_decide
theorem class_nonprime_6 : primeClass 6 = 0 := by native_decide

/- ## Least Prime in Each Class -/

/-- Find the least prime in class r by searching up to bound. -/
def findLeastPrimeInClass (r : ℕ) (bound : ℕ) : Option ℕ :=
  (List.range bound).find? (fun p => primeClass p == r)

-- Verify least primes (OEIS A005113): 2, 13, 37, 73, 1021
theorem least_class_1 : findLeastPrimeInClass 1 10 = some 2 := by native_decide
theorem least_class_2 : findLeastPrimeInClass 2 20 = some 13 := by native_decide
theorem least_class_3 : findLeastPrimeInClass 3 50 = some 37 := by native_decide
theorem least_class_4 : findLeastPrimeInClass 4 100 = some 73 := by native_decide
theorem least_class_5 : findLeastPrimeInClass 5 1100 = some 1021 := by native_decide

/- ## Structural Properties -/

/-- Foldl with guarded max is monotone in the initial value. -/
private theorem foldl_guarded_max_mono (l : List ℕ) (f : ℕ → ℕ) (bound : ℕ) (init : ℕ) :
    l.foldl (fun acc q => if q < bound then max acc (f q) else acc) init ≥ init := by
  induction l generalizing init with
  | nil => simp
  | cons a tl ih =>
    simp only [List.foldl]
    have h1 : (if a < bound then max init (f a) else init) ≥ init := by split <;> omega
    exact le_trans h1 (ih _)

/-- Foldl with guarded max is at least as large as any element's image. -/
private theorem foldl_guarded_max_ge (l : List ℕ) (f : ℕ → ℕ) (bound : ℕ) (x : ℕ)
    (hx : x ∈ l) (hlt : x < bound) (init : ℕ) :
    l.foldl (fun acc q => if q < bound then max acc (f q) else acc) init ≥ f x := by
  induction l generalizing init with
  | nil => simp at hx
  | cons a tl ih =>
    simp only [List.foldl]
    rcases List.mem_cons.mp hx with rfl | h
    · -- x = a: the guard fires, giving max init (f x) as new accumulator
      have h1 : (if x < bound then max init (f x) else init) ≥ f x := by
        simp [hlt]
      exact le_trans h1 (foldl_guarded_max_mono tl f bound _)
    · -- x ∈ tl: use induction hypothesis
      exact ih h _

/-- A prime factor q of (p+1) with q ∉ {2,3} belongs to the nonSmooth list. -/
private theorem mem_nonSmooth_of_dvd (p q : ℕ) (hq : Nat.Prime q)
    (hdvd : q ∣ p + 1) (hq2 : q ≠ 2) (hq3 : q ≠ 3) :
    q ∈ ((p + 1).primeFactorsList.dedup).filter (fun r => r != 2 && r != 3) := by
  rw [List.mem_filter, List.mem_dedup]
  exact ⟨(Nat.mem_primeFactorsList (by omega : p + 1 ≠ 0)).mpr ⟨hq, hdvd⟩, by simp [hq2, hq3]⟩

/-- primeClass p ≥ 1 + primeClass q when q is a nonSmooth factor of p+1.
    This is the key lower bound; the proof unfolds the WF definition. -/
private theorem primeClass_ge_succ_factor (p q : ℕ) (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hdvd : q ∣ p + 1) (hq2 : q ≠ 2) (hq3 : q ≠ 3) :
    primeClass p ≥ 1 + primeClass q := by
  have hqlt := nonSmooth_factor_lt p q hp hq hdvd hq2 hq3
  have hq_mem := mem_nonSmooth_of_dvd p q hq hdvd hq2 hq3
  show primeClassWF p ≥ 1 + primeClassWF q
  rw [primeClassWF.eq_1]
  split
  · exact absurd hp ‹_›
  · -- In the else branch, unfold let bindings then split on isEmpty
    simp only []
    split
    · -- isEmpty = true → simp_all converts to "all non-2 prime factors are 3"
      -- This contradicts hq3 (q ≠ 3) since q is such a factor
      exfalso
      simp_all
      rename_i hall
      exact hq3 (hall q hq hdvd hq2)
    · -- Goal: 1 + foldl (dite) ... ≥ 1 + primeClassWF q
      -- Convert dite to ite (definitionally equal, congr closes it)
      have hconv : ∀ (l : List ℕ) (init : ℕ),
          l.foldl (fun acc r => if _ : r < p then max acc (primeClassWF r) else acc) init =
          l.foldl (fun acc r => if r < p then max acc (primeClassWF r) else acc) init := by
        intro l init; congr
      rw [hconv]
      have := foldl_guarded_max_ge _ primeClassWF p q hq_mem hqlt 0
      omega

/-- For nonSmooth prime factors, class strictly decreases.
    Proved directly from the well-founded definition without fuel convergence. -/
theorem class_of_factor_lt (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hdvd : q ∣ p + 1) (hq2 : q ≠ 2) (hq3 : q ≠ 3) :
    primeClass q < primeClass p := by
  have h := primeClass_ge_succ_factor p q hp hq hdvd hq2 hq3
  omega

/-- Class 1 primes are exactly those whose successor is 3-smooth. -/
theorem class_one_iff_smooth (p : ℕ) (hp : Nat.Prime p) :
    primeClass p = 1 ↔ ∀ q ∈ (p + 1).primeFactorsList, q = 2 ∨ q = 3 := by
  constructor
  · -- Forward: class = 1 → all factors smooth
    intro h
    -- If any nonSmooth factor q exists, class ≥ 2 by class_of_factor_lt + pos
    by_contra hc
    push_neg at hc
    obtain ⟨q, hq_mem, hq2, hq3⟩ := hc
    have hq_prime := Nat.prime_of_mem_primeFactorsList hq_mem
    have hq_dvd := Nat.dvd_of_mem_primeFactorsList hq_mem
    have hlt := class_of_factor_lt p q hp hq_prime hq_dvd hq2 hq3
    -- primeClass q ≥ 1 since q is prime
    have hpos : primeClass q ≥ 1 := by
      show primeClassWF q ≥ 1
      rw [primeClassWF.eq_1]
      split
      · exact absurd hq_prime ‹_›
      · simp only []; split <;> omega
    -- So primeClass p ≥ 2, contradicting h
    omega
  · -- Backward: all factors smooth → class = 1
    intro h
    -- The nonSmooth filter is empty, so primeClassWF returns 1
    show primeClassWF p = 1
    rw [primeClassWF.eq_1]
    split
    · exact absurd hp ‹_›
    · simp only []
      -- The filter of non-{2,3} factors is empty
      have hnil : ((p + 1).primeFactorsList.dedup.filter (fun q => q != 2 && q != 3)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro q hq
        have hq_mem := List.mem_dedup.mp hq
        rcases h q hq_mem with rfl | rfl <;> simp
      simp [hnil]

/-- If p is prime, then primeClass p ≥ 1. -/
theorem primeClass_pos_of_prime (p : ℕ) (hp : Nat.Prime p) :
    primeClass p ≥ 1 := by
  show primeClassWF p ≥ 1
  rw [primeClassWF.eq_1]
  split
  · exact absurd hp ‹_›
  · simp only []; split <;> omega

/- ## Concrete Evidence for Infinitude -/

-- Multiple class-1 primes in [0, 50)
theorem many_class1_primes :
    (Finset.filter (fun p => decide (primeClass p = 1)) (Finset.range 50)).card ≥ 8 := by
  native_decide

-- Multiple class-2 primes in [0, 100)
theorem many_class2_primes :
    (Finset.filter (fun p => decide (primeClass p = 2)) (Finset.range 100)).card ≥ 8 := by
  native_decide

-- Multiple class-3 primes in [0, 200)
theorem many_class3_primes :
    (Finset.filter (fun p => decide (primeClass p = 3)) (Finset.range 200)).card ≥ 3 := by
  native_decide

/- ## The Main Conjectures (OPEN) -/

/-- Erdős Problem #1055 (main): For each r ≥ 1, there are infinitely many
    primes in class r. -/
axiom infinitely_many_in_each_class (r : ℕ) (hr : r ≥ 1) :
    Set.Infinite {p : ℕ | p.Prime ∧ primeClass p = r}

/-- Erdős's conjecture: p_r^{1/r} → ∞ as r → ∞.
    Formulated as: for every M, there exists R such that for all r ≥ R,
    the least prime p in class r satisfies p^{1/r} ≥ M. -/
axiom erdos_growth_conjecture :
    ∀ M : ℝ, ∃ R : ℕ, ∀ r ≥ R,
      ∀ p : ℕ, p.Prime → primeClass p = r →
        (∀ q : ℕ, q.Prime → primeClass q = r → p ≤ q) →
        ((p : ℝ)) ^ ((1 : ℝ) / (r : ℝ)) ≥ M

/-- Selfridge's competing conjecture: p_r^{1/r} is bounded. -/
axiom selfridge_bounded_conjecture :
    ∃ M : ℝ, ∀ r : ℕ, r ≥ 1 →
      ∀ p : ℕ, p.Prime → primeClass p = r →
        (∀ q : ℕ, q.Prime → primeClass q = r → p ≤ q) →
        ((p : ℝ)) ^ ((1 : ℝ) / (r : ℝ)) ≤ M

/- ## Known Density Bound -/

/-- The number of primes ≤ n in class r is at most n^{o(1)}.
    This is stated as "easy to prove" by Erdős. -/
axiom class_density_subpolynomial (r : ℕ) (hr : r ≥ 1) :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ((Finset.filter (fun p => decide (Nat.Prime p ∧ primeClass p = r))
        (Finset.range (n + 1))).card : ℝ) ≤ (n : ℝ) ^ ε
