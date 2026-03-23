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

/- ## Known Results (Axiomatized — deep results from Erdős-Graham 1976) -/

/-- D₂ consists of all perfect squares > 1 (Erdős-Graham 1976).
    The backward direction (squares ∈ D₂) is proved above as
    squares_have_square_factorial_product. The forward direction
    (D₂ ⊆ squares) requires deeper p-adic valuation analysis. -/
axiom D2_eq_squares (m : ℕ) (hm : 2 ≤ m) :
  inDk 2 m ↔ IsPerfectSquare m

/-- For primes, no strictly increasing sequence ending at p has a
    factorial product that is a perfect square (Erdős-Graham 1976).
    Key insight: v_p(p!) = 1 forces odd p-adic valuation. -/
axiom no_square_factorial_product_for_primes (p : ℕ) (hp : p.Prime)
    (k : ℕ) (hk : 2 ≤ k) : ¬HasSquareFactorialProduct p k

/-- Dₖ = ∅ for k > 6 (Erdős-Graham 1976). -/
axiom Dk_empty_above_6 (k : ℕ) (hk : 7 ≤ k) (m : ℕ) :
  ¬inDk k m

/-- The smallest element of D₆ is 527. -/
axiom D6_smallest : inDk 6 527 ∧ ∀ m : ℕ, m < 527 → ¬inDk 6 m

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

/- ## The Open Question -/

/-- Erdős Problem #374: Determine the growth rate of |Dₖ ∩ {1,...,n}|
    for 3 ≤ k ≤ 6. -/
axiom erdos_374_growth_rate (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 6) :
  ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (Finset.card ((Finset.range n).filter (fun m => inDk k (m + 1))) : ℝ)
      ≤ (n : ℝ) ^ (α + ε)
