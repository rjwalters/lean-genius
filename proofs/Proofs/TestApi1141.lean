import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

-- Approach 1: ∀ k ∈ Finset, with native_decide
-- (v4.31: native_decide no longer auto-unfolds the `def` to find the Decidable
--  instance; `unfold` first so the concrete DecidablePred is used, and drop the
--  `open scoped Classical` whose noncomputable instances broke native_decide.)
def testGood1 (n : ℕ) : Prop :=
  ∀ k ∈ Finset.range n, k ^ 2 < n → Nat.Coprime n k → (n - k ^ 2).Prime

example : testGood1 3 := by unfold testGood1; native_decide
example : ¬ testGood1 5 := by unfold testGood1; native_decide

-- Approach 2: reformulate with conjunction to make decidable for decide
def testGood2 (n : ℕ) : Prop :=
  ∀ k ∈ Finset.range n, ¬(k ^ 2 < n ∧ Nat.Coprime n k) ∨ (n - k ^ 2).Prime

-- Approach 3: Bool function via decide (Finset.forall was removed in v4.31)
def checkGood (n : ℕ) : Bool :=
  decide (∀ k ∈ Finset.range n,
    (k ^ 2 < n ∧ Nat.Coprime n k) → (n - k ^ 2).Prime)

-- Approach 4: decidable via bounded-forall
def testGood4 (n : ℕ) : Prop :=
  ∀ k ∈ Finset.range n, (k ^ 2 < n ∧ Nat.Coprime n k) → (n - k ^ 2).Prime

example : testGood4 3 := by unfold testGood4; native_decide
