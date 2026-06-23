import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

-- Approach 1: ∀ k ∈ Finset, with native_decide
def testGood1 (n : ℕ) : Prop :=
  ∀ k ∈ Finset.range n, k ^ 2 < n → Nat.Coprime n k → (n - k ^ 2).Prime

example : testGood1 3 := by native_decide
example : ¬ testGood1 5 := by native_decide

-- Approach 2: reformulate with conjunction to make decidable for decide
def testGood2 (n : ℕ) : Prop :=
  ∀ k ∈ Finset.range n, ¬(k ^ 2 < n ∧ Nat.Coprime n k) ∨ (n - k ^ 2).Prime

-- Approach 3: Bool function + iff
def checkGood (n : ℕ) : Bool :=
  (Finset.range n).forall fun k =>
    if h : k ^ 2 < n ∧ Nat.Coprime n k then (n - k ^ 2).Prime else true

-- Approach 4: decidable via Finset.decidableBAllCongr
def testGood4 (n : ℕ) : Prop :=
  ∀ k ∈ Finset.range n, (k ^ 2 < n ∧ Nat.Coprime n k) → (n - k ^ 2).Prime

example : testGood4 3 := by native_decide
