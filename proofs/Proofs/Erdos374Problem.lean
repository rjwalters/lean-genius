/-
# Erdős Problem #374: Factorial Products as Perfect Squares

For m ∈ ℕ, define F(m) as the minimal k ≥ 2 such that there exist
a₁ < a₂ < ⋯ < aₖ = m with a₁! · a₂! · ⋯ · aₖ! a perfect square.

Let Dₖ = { m : F(m) = k }. Study |Dₖ ∩ {1,...,n}| for 3 ≤ k ≤ 6.

Known:
- D₂ = { m : m is a perfect square, m > 1 }
- No Dₖ contains a prime
- Dₖ = ∅ for k > 6
- The smallest element of D₆ is 527
- D₃ grows slower than D₄

Status: OPEN.

Reference: https://erdosproblems.com/374
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Factorial.Basic

open Classical

/- ## Definitions -/

/-- A number is a perfect square. -/
def IsPerfectSquare (n : ℕ) : Prop :=
  ∃ k : ℕ, n = k * k

/-- The product of factorials a₁! · a₂! · ⋯ · aₖ! for a strictly
    increasing sequence ending at m. -/
def factorialProduct (seq : List ℕ) : ℕ :=
  seq.foldl (fun acc a => acc * Nat.factorial a) 1

/-- There exists a strictly increasing sequence a₁ < ⋯ < aₖ = m
    of length k whose factorial product is a perfect square. -/
def HasSquareFactorialProduct (m k : ℕ) : Prop :=
  ∃ seq : List ℕ, seq.length = k ∧
    seq.getLast? = some m ∧
    seq.Pairwise (· < ·) ∧
    IsPerfectSquare (factorialProduct seq)

/-- F(m) = min { k ≥ 2 : HasSquareFactorialProduct m k }.
    Returns 0 when F(m) is undefined (no such k exists). -/
noncomputable def bigF (m : ℕ) : ℕ :=
  if h : ∃ k, 2 ≤ k ∧ HasSquareFactorialProduct m k then
    Nat.find h
  else 0

/-- Dₖ = { m : F(m) = k }. -/
def inDk (k m : ℕ) : Prop := bigF m = k

/- ## Basic Properties (Proved) -/

/-- F(m) ≥ 2 whenever F(m) is defined (bigF m ≠ 0). -/
theorem bigF_ge_two (m : ℕ) (hdef : bigF m ≠ 0) : 2 ≤ bigF m := by
  unfold bigF at hdef ⊢
  split_ifs at hdef ⊢ with h
  · exact (Nat.find_spec h).1
  · exact absurd rfl hdef

/-- The product of factorials of a two-element list equals the product
    of the individual factorials. -/
theorem factorialProduct_pair (a b : ℕ) :
    factorialProduct [a, b] = a.factorial * b.factorial := by
  simp [factorialProduct, List.foldl]

/- ## Proved: Backward Direction of D₂ = Squares -/

/-- For any n ≥ 2, the sequence [n²−1, n²] witnesses that n² has a
    2-element factorial square product:
      (n²−1)! · (n²)! = (n²−1)! · n² · (n²−1)! = (n · (n²−1)!)².
    This proves every perfect square ≥ 4 belongs to D₂. -/
theorem squares_have_square_factorial_product (n : ℕ) (hn : 2 ≤ n) :
    HasSquareFactorialProduct (n * n) 2 := by
  refine ⟨[n * n - 1, n * n], rfl, ?_, ?_, ?_⟩
  · -- getLast? [n*n-1, n*n] = some (n*n)
    simp
  · -- Pairwise (· < ·) [n*n-1, n*n]
    apply List.Pairwise.cons
    · intro a ha
      simp at ha; subst ha
      exact Nat.sub_lt (Nat.mul_pos (by omega) (by omega)) (by omega)
    · exact List.Pairwise.cons (by simp) List.Pairwise.nil
  · -- IsPerfectSquare (factorialProduct [n*n-1, n*n])
    rw [factorialProduct_pair]
    have hfact : (n * n).factorial = n * n * (n * n - 1).factorial := by
      have h := Nat.factorial_succ (n * n - 1)
      rw [Nat.sub_add_cancel (show 1 ≤ n * n from by nlinarith)] at h
      exact h
    rw [hfact]
    exact ⟨n * (n * n - 1).factorial, by ring⟩

/-- Verified example: 4 ∈ D₂ via [3, 4], since 3! · 4! = 144 = 12². -/
example : HasSquareFactorialProduct 4 2 :=
  ⟨[3, 4], rfl, by decide, by decide, ⟨12, by native_decide⟩⟩

/-- F(n²) = 2 for n ≥ 2: the Nat.find gives 2 because:
    - k = 2 satisfies 2 ≤ k ∧ HasSquareFactorialProduct (proved above)
    - k = 0, 1 fail the 2 ≤ k condition -/
theorem bigF_eq_two_of_square (n : ℕ) (hn : 2 ≤ n) : bigF (n * n) = 2 := by
  unfold bigF
  have h : ∃ k, 2 ≤ k ∧ HasSquareFactorialProduct (n * n) k :=
    ⟨2, le_refl 2, squares_have_square_factorial_product n hn⟩
  rw [dif_pos h]
  exact Nat.find_eq_iff.mpr ⟨⟨le_refl 2, squares_have_square_factorial_product n hn⟩,
    fun k hk ⟨h1, _⟩ => by omega⟩

/-- Every perfect square n² with n ≥ 2 belongs to D₂. This is the
    backward direction of D2_eq_squares, now proved. -/
theorem square_in_D2 (n : ℕ) (hn : 2 ≤ n) : inDk 2 (n * n) :=
  bigF_eq_two_of_square n hn

/- ## Helper Lemmas for factorialProduct -/

/-- The foldl for factorialProduct satisfies `foldl f b xs = b * foldl f 1 xs`.
    This is the key property relating different starting accumulators. -/
private lemma factorialProduct_foldl_mul (b : ℕ) (seq : List ℕ) :
    List.foldl (fun acc a => acc * Nat.factorial a) b seq =
    b * List.foldl (fun acc a => acc * Nat.factorial a) 1 seq := by
  induction seq generalizing b with
  | nil => simp [List.foldl]
  | cons x xs ih =>
    simp only [List.foldl]
    rw [ih (b * x.factorial), ih (1 * x.factorial)]
    ring

/-- factorialProduct distributes over list concatenation. -/
theorem factorialProduct_append (xs ys : List ℕ) :
    factorialProduct (xs ++ ys) = factorialProduct xs * factorialProduct ys := by
  unfold factorialProduct
  rw [List.foldl_append]
  exact factorialProduct_foldl_mul _ _

/-- factorialProduct of a singleton is just the factorial. -/
private lemma factorialProduct_singleton (x : ℕ) :
    factorialProduct [x] = x.factorial := by
  simp [factorialProduct, List.foldl]

/-- factorialProduct of (x :: xs) splits as x! * factorialProduct xs. -/
private lemma factorialProduct_cons (x : ℕ) (xs : List ℕ) :
    factorialProduct (x :: xs) = x.factorial * factorialProduct xs := by
  rw [show x :: xs = [x] ++ xs from rfl, factorialProduct_append, factorialProduct_singleton]

/-- A prime p does not divide the product of factorials of numbers all < p.
    Each a! for a < p has all factors in {1,...,a} ⊂ {1,...,p-1}, so p ∤ a!.
    Since p is prime and doesn't divide any individual a!, it doesn't divide
    their product. -/
private theorem not_prime_dvd_factorialProduct {p : ℕ} (hp : p.Prime) (seq : List ℕ)
    (hlt : ∀ a ∈ seq, a < p) : ¬(p ∣ factorialProduct seq) := by
  induction seq with
  | nil =>
    simp [factorialProduct, List.foldl]
    exact fun h => absurd (Nat.le_of_dvd Nat.one_pos h) (by omega)
  | cons x xs ih =>
    rw [factorialProduct_cons]
    intro h
    rcases hp.dvd_mul.mp h with hx | hxs
    · -- p ∣ x! implies p ≤ x, contradicting x < p
      exact absurd (hp.dvd_factorial.mp hx)
        (not_le_of_lt (hlt x (List.mem_cons_self x xs)))
    · -- p ∣ factorialProduct xs contradicts induction hypothesis
      exact ih (fun a ha => hlt a (List.mem_cons_of_mem x ha)) hxs

/- ## Known Results -/

/-- For primes, no strictly increasing sequence ending at p has a
    factorial product that is a perfect square.
    Proof: v_p(product) = 1 (odd) since p! contributes one factor of p
    and all other terms a_i! with a_i < p contribute zero. -/
theorem no_square_factorial_product_for_primes (p : ℕ) (hp : p.Prime)
    (k : ℕ) (hk : 2 ≤ k) : ¬HasSquareFactorialProduct p k := by
  intro ⟨seq, hlen, hlast, hpw, n, hn⟩
  -- Decompose: seq = init ++ [p]
  have hne : seq ≠ [] := by intro h; simp [h] at hlast
  have hget : seq.getLast hne = p := by
    rwa [List.getLast?_eq_getLast hne, Option.some_inj] at hlast
  set init := seq.dropLast with hinit_def
  have hseq : seq = init ++ [p] := by
    rw [hinit_def, ← hget]; exact (List.dropLast_append_getLast hne).symm
  -- All elements of init are < p (from Pairwise strict increasing + last = p)
  have hlt : ∀ a ∈ init, a < p := by
    intro a ha
    have hpw' := hseq ▸ hpw
    rw [List.pairwise_append] at hpw'
    exact hpw'.2.2 a ha p (List.mem_singleton.mpr rfl)
  -- factorialProduct seq = factorialProduct init * p!
  have hprod : factorialProduct seq = factorialProduct init * p.factorial := by
    rw [hseq, factorialProduct_append]
  -- p! = p * (p-1)!
  have hfact : p.factorial = p * (p - 1).factorial := by
    have := Nat.factorial_succ (p - 1)
    rwa [Nat.succ_eq_add_one, Nat.sub_add_cancel hp.pos] at this
  -- p does not divide factorialProduct init (all elements < p)
  have hndvd_init : ¬(p ∣ factorialProduct init) :=
    not_prime_dvd_factorialProduct hp init hlt
  -- p does not divide (p-1)!
  have hndvd_prev : ¬(p ∣ (p - 1).factorial) := by
    intro h; exact absurd (hp.dvd_factorial.mp h) (by omega)
  -- Combine: factorialProduct seq = p * M where M = factorialProduct init * (p-1)!
  set M := factorialProduct init * (p - 1).factorial with hM_def
  have hprod2 : factorialProduct seq = p * M := by
    rw [hprod, hfact, hM_def]; ring
  -- p does not divide M
  have hndvd_M : ¬(p ∣ M) := by
    rw [hM_def]; intro h
    rcases hp.dvd_mul.mp h with h | h
    · exact hndvd_init h
    · exact hndvd_prev h
  -- From perfect square: product = n * n
  -- p divides n (since p | p * M = n * n, and p is prime)
  have hp_dvd_n : p ∣ n := by
    have h1 : n * n = p * M := hn.symm.trans hprod2
    have h2 : p ∣ n * n := ⟨M, h1⟩
    exact (hp.dvd_mul.mp h2).elim id id
  -- So p² divides n², but p² does not divide p * M
  obtain ⟨m, rfl⟩ := hp_dvd_n
  -- product = (p*m)² = p²m²; product = p*M; so M = p*m², hence p | M
  exfalso; apply hndvd_M
  have h_eq : p * M = p * m * (p * m) := by linarith [hprod2, hn]
  rw [show p * m * (p * m) = p * (p * (m * m)) from by ring] at h_eq
  exact ⟨m * m, mul_left_cancel₀ hp.ne_zero h_eq⟩

/- ## Derived Theorems -/

/-- For primes, F is undefined: bigF returns 0 (the sentinel value). -/
theorem bigF_prime_zero (p : ℕ) (hp : p.Prime) : bigF p = 0 := by
  unfold bigF
  split_ifs with h
  · exfalso
    have ⟨hk, hsp⟩ := Nat.find_spec h
    exact no_square_factorial_product_for_primes p hp _ hk hsp
  · rfl

/-- No prime belongs to any Dₖ for k ≥ 2. -/
theorem no_prime_in_Dk (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : 2 ≤ k) :
    ¬inDk k p := by
  unfold inDk
  rw [bigF_prime_zero p hp]
  omega

/- ## Edge Cases -/

/-- HasSquareFactorialProduct 1 2 via the sequence [0, 1]: 0! · 1! = 1 = 1².
    This shows 1 ∈ D₂, the smallest element. -/
theorem one_has_square_factorial_product : HasSquareFactorialProduct 1 2 :=
  ⟨[0, 1], rfl, by decide, by decide, ⟨1, by simp [factorialProduct, List.foldl]⟩⟩

/-- bigF(1) = 2: the sequence [0, 1] witnesses 0! · 1! = 1 = 1². -/
theorem bigF_one_eq_two : bigF 1 = 2 := by
  unfold bigF
  have h : ∃ k, 2 ≤ k ∧ HasSquareFactorialProduct 1 k :=
    ⟨2, le_refl 2, one_has_square_factorial_product⟩
  rw [dif_pos h]
  exact Nat.find_eq_iff.mpr ⟨⟨le_refl 2, one_has_square_factorial_product⟩,
    fun k hk ⟨h1, _⟩ => by omega⟩

/-- 1 ∈ D₂ (the smallest element of D₂). -/
theorem one_in_D2 : inDk 2 1 := bigF_one_eq_two

/- ## The Open Question -/

