import Mathlib.Tactic

/-!
# Semantics of the sequential cardinality counter

The order-49 SAT certificates use PySAT's `seqcounter` encoding for every
degree equality.  This file isolates the mathematical witness behind that
encoding.  The auxiliary bit `s(i,j)` means that at least `j+1` of the first
`i+1` input bits are true.

These lemmas are the semantic half of the graph-to-DIMACS bridge: whenever
the graph has the prescribed degree, its edge row admits values for every
sequential-counter auxiliary variable that satisfy the counter clauses.
-/

namespace Erdos85

/-- Number of true input bits among indices strictly below `m`.  Values at
indices beyond the input width are ignored. -/
def seqPrefixTrue {n : Nat} (x : Fin n → Bool) (m : Nat) : Nat :=
  ((Finset.range m).filter fun i => if h : i < n then x ⟨i, h⟩ else false).card

/-- Canonical value of sequential-counter auxiliary `s(i,j)`: at least
`j+1` of inputs `0,...,i` are true. -/
def seqCounterWitness {n : Nat} (x : Fin n → Bool) (i j : Nat) : Bool :=
  decide (j + 1 ≤ seqPrefixTrue x (i + 1))

/-- Pointwise Boolean complement of an input row. -/
def seqNeg {n : Nat} (x : Fin n → Bool) : Fin n → Bool := fun i => !x i

theorem seqPrefixTrue_succ {n : Nat} (x : Fin n → Bool)
    (i : Nat) (hi : i < n) :
    seqPrefixTrue x (i + 1) =
      seqPrefixTrue x i + if x ⟨i, hi⟩ then 1 else 0 := by
  unfold seqPrefixTrue
  have hrange : Finset.range (i + 1) = insert i (Finset.range i) := by
    ext k
    simp
    omega
  rw [hrange]
  rw [Finset.filter_insert]
  have hnot : i ∉ Finset.range i := Finset.notMem_range_self
  by_cases hx : x ⟨i, hi⟩ = true
  · have hpred : (if h : i < n then x ⟨i, h⟩ else false) = true := by
      simpa [hi] using hx
    simp only [hpred, if_true]
    have hnotFilter : i ∉ ((Finset.range i).filter fun q =>
        if h : q < n then x ⟨q, h⟩ else false) := by
      intro hmem
      exact hnot (Finset.mem_filter.mp hmem).1
    rw [Finset.card_insert_of_notMem hnotFilter]
    simp [hx]
  · simp [hi, hx]

theorem seqPrefixTrue_mono {n : Nat} (x : Fin n → Bool)
    {a b : Nat} (hab : a ≤ b) : seqPrefixTrue x a ≤ seqPrefixTrue x b := by
  unfold seqPrefixTrue
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  exact ⟨lt_of_lt_of_le hi.1 hab, hi.2⟩

theorem seqPrefixTrue_le_total {n : Nat} (x : Fin n → Bool)
    {m : Nat} (hm : m ≤ n) : seqPrefixTrue x m ≤ seqPrefixTrue x n :=
  seqPrefixTrue_mono x hm

/-- A row and its Boolean complement contain `n` true bits altogether. -/
theorem seqPrefixTrue_neg_add {n : Nat} (x : Fin n → Bool) :
    seqPrefixTrue x n + seqPrefixTrue (seqNeg x) n = n := by
  let p : Nat → Prop := fun i =>
    if h : i < n then x ⟨i, h⟩ = true else False
  have hp : seqPrefixTrue x n = ((Finset.range n).filter p).card := by
    unfold seqPrefixTrue p
    congr 1
    ext i
    by_cases hi : i < n <;> simp [hi]
  have hn : seqPrefixTrue (seqNeg x) n =
      ((Finset.range n).filter fun i => ¬p i).card := by
    unfold seqPrefixTrue seqNeg p
    congr 1
    ext i
    by_cases hi : i < n
    · have hproof : ∀ h : i < n, x ⟨i, h⟩ = x ⟨i, hi⟩ := by
        intro h
        rfl
      cases hx : x ⟨i, hi⟩ <;> simp [hi, hproof, hx]
    · simp [hi]
  rw [hp, hn, Finset.card_filter_add_card_filter_not]
  simp

/-- Exact cardinality splits into the two bounds consumed by PySAT's
`equals/seqcounter` encoding. -/
theorem seqPrefixTrue_bounds_of_eq {n k : Nat} (x : Fin n → Bool)
    (hcount : seqPrefixTrue x n = k) :
    seqPrefixTrue x n ≤ k ∧ seqPrefixTrue (seqNeg x) n ≤ n - k := by
  constructor
  · omega
  · have hsum := seqPrefixTrue_neg_add x
    omega

/-- First sequential-counter clause: a true first input raises the first
counter bit. -/
theorem seqCounterWitness_first {n : Nat} (x : Fin n → Bool)
    (hn : 0 < n) (hx : x ⟨0, hn⟩ = true) :
    seqCounterWitness x 0 0 = true := by
  simp [seqCounterWitness, seqPrefixTrue_succ, hn, hx]

/-- Horizontal propagation clause `s(i-1,j) → s(i,j)`. -/
theorem seqCounterWitness_propagate {n : Nat} (x : Fin n → Bool)
    (i j : Nat) (_hi : i < n)
    (hs : seqCounterWitness x (i - 1) j = true) :
    seqCounterWitness x i j = true := by
  simp only [seqCounterWitness, decide_eq_true_eq] at hs ⊢
  have hmono : seqPrefixTrue x ((i - 1) + 1) ≤ seqPrefixTrue x (i + 1) :=
    seqPrefixTrue_mono x (by omega)
  omega

/-- Input propagation clause `x(i) → s(i,0)`. -/
theorem seqCounterWitness_input {n : Nat} (x : Fin n → Bool)
    (i : Nat) (hi : i < n) (hx : x ⟨i, hi⟩ = true) :
    seqCounterWitness x i 0 = true := by
  simp only [seqCounterWitness, decide_eq_true_eq]
  rw [seqPrefixTrue_succ x i hi, hx]
  simp

/-- Diagonal propagation clause
`x(i) ∧ s(i-1,j-1) → s(i,j)`. -/
theorem seqCounterWitness_diagonal {n : Nat} (x : Fin n → Bool)
    (i j : Nat) (hi : i < n) (hik : 0 < i) (hj : 0 < j)
    (hx : x ⟨i, hi⟩ = true)
    (hs : seqCounterWitness x (i - 1) (j - 1) = true) :
    seqCounterWitness x i j = true := by
  simp only [seqCounterWitness, decide_eq_true_eq] at hs ⊢
  rw [seqPrefixTrue_succ x i hi, hx]
  simp only [if_true]
  have heq : (i - 1) + 1 = i := by omega
  rw [heq] at hs
  have hjeq : (j - 1) + 1 = j := by omega
  rw [hjeq] at hs
  omega

/-- Overflow-prevention clause.  If the whole row has at most `k` true
inputs, a true input `i` cannot follow a prefix that already contains `k`
true inputs. -/
theorem seqCounterWitness_no_overflow {n : Nat} (x : Fin n → Bool)
    (i k : Nat) (hi : i < n) (hik : 0 < i) (hk : 0 < k)
    (htotal : seqPrefixTrue x n ≤ k)
    (hx : x ⟨i, hi⟩ = true) :
    seqCounterWitness x (i - 1) (k - 1) = false := by
  simp only [seqCounterWitness, decide_eq_false_iff_not]
  intro hs
  have heq : (i - 1) + 1 = i := by omega
  rw [heq] at hs
  have hstep := seqPrefixTrue_succ x i hi
  rw [hx] at hstep
  simp only [if_true] at hstep
  have hle : seqPrefixTrue x (i + 1) ≤ seqPrefixTrue x n :=
    seqPrefixTrue_le_total x (by omega)
  omega

end Erdos85
