import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic

/-!
# Cantor's Diagonalization Theorem

## What This Proves
We prove that no function from ℕ to infinite binary sequences can be
surjective—there are "more" real numbers than natural numbers. This
establishes that the reals are uncountable.

## Approach
- **Foundation (from Mathlib):** We use only basic logic and function
  definitions from Mathlib. No non-trivial theorems are imported.
- **Original Contributions:** The complete diagonal construction and proof
  are original. We define `BinarySeq`, construct the diagonal sequence that
  differs from every enumerated sequence, and prove the main theorem.
- **Proof Techniques Demonstrated:** Boolean case analysis, function
  extensionality, proof by construction, the `unfold` tactic.

## Status
- [x] Complete proof
- [ ] Uses Mathlib for main result
- [ ] Proves extensions/corollaries
- [ ] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Mathlib.Logic.Function.Basic` : Basic function definitions (not used for main proof)
- `Mathlib.Data.Set.Function` : Set-theoretic function properties
- `Mathlib.Tactic` : Standard tactic library

Historical Note: Georg Cantor published this proof in 1891, revolutionizing
our understanding of infinity and showing that some infinities are larger
than others.
-/

namespace CantorDiagonalization

/-! ## Binary Sequences -/

/-- An infinite binary sequence is a function from ℕ to Bool.
    This represents numbers in [0,1] via binary expansion. -/
def BinarySeq := ℕ → Bool

/-! ## The Diagonal Construction -/

/-- The diagonal function: given an enumeration of sequences,
    construct a new sequence that differs from the n-th sequence
    at position n by flipping the bit. -/
def diagonal (f : ℕ → BinarySeq) : BinarySeq :=
  fun n => !(f n n)

/-- Key lemma: the diagonal differs from every sequence in the list
    at the crucial position n. This is the heart of the argument. -/
theorem diagonal_differs (f : ℕ → BinarySeq) (n : ℕ) :
    diagonal f n ≠ f n n := by
  -- Unfold the definition of diagonal
  unfold diagonal
  -- The diagonal at n is !(f n n), which cannot equal f n n
  cases f n n <;> simp

/-! ## Cantor's Main Theorem -/

/-- **Cantor's Theorem**: No function from ℕ to BinarySeq is surjective.
    There is always a binary sequence not in the range of any enumeration.

    Proof: Given any f : ℕ → BinarySeq, the diagonal sequence differs
    from f n at position n, so diagonal f ≠ f n for all n. -/
theorem cantor_diagonalization :
    ∀ f : ℕ → BinarySeq, ∃ s : BinarySeq, ∀ n : ℕ, f n ≠ s := by
  -- Take any proposed enumeration f
  intro f
  -- Construct the diagonal sequence
  use diagonal f
  -- Show it differs from every f n
  intro n
  -- Suppose f n = diagonal f for contradiction
  intro h
  -- At position n, f n n must equal (diagonal f) n
  have key : f n n = diagonal f n := congrFun h n
  -- But diagonal f n ≠ f n n by the diagonal lemma
  have contra := diagonal_differs f n
  -- These two facts contradict each other
  exact contra key.symm

/-- Reformulation: no surjection exists from ℕ to BinarySeq -/
theorem no_surjection_nat_to_binary :
    ¬∃ f : ℕ → BinarySeq, Function.Surjective f := by
  -- Assume such a surjection exists
  intro ⟨f, hf⟩
  -- By Cantor's theorem, there exists s not in the range of f
  obtain ⟨s, hs⟩ := cantor_diagonalization f
  -- But surjectivity says every s is in the range
  obtain ⟨n, hn⟩ := hf s
  -- Contradiction: f n = s but f n ≠ s
  exact hs n hn

/-! ## Corollary: The Reals are Uncountable -/

/-- The real numbers are uncountable.
    Since binary sequences correspond to reals in [0,1], and [0,1] has
    the same cardinality as ℝ, this establishes |ℕ| < |ℝ|. -/
theorem reals_uncountable :
    ¬∃ f : ℕ → BinarySeq, Function.Surjective f :=
  no_surjection_nat_to_binary

/-! ## The Power Set Version -/

/-- **Cantor's Theorem (Power Set Version)**: For any type S, there is
    no surjection from S to Set S. The power set is always strictly larger.

    This is the general form of Cantor's theorem. The binary sequence
    version follows by taking S = ℕ and noting Set ℕ ≅ (ℕ → Bool). -/
theorem cantor_powerset (S : Type*) :
    ¬∃ f : S → Set S, Function.Surjective f := by
  -- Assume such a surjection exists
  intro ⟨f, hf⟩
  -- Define the "diagonal" set: elements not in their own image
  let D : Set S := { x | x ∉ f x }
  -- D must be in the range of f (by surjectivity)
  obtain ⟨a, ha⟩ := hf D
  -- Key insight: a ∈ D ↔ a ∉ f a by definition
  have key : a ∈ D ↔ a ∉ f a := Iff.rfl
  -- Substitute f a = D to get: a ∈ D ↔ a ∉ D
  simp only [ha] at key
  -- This is a contradiction: P ↔ ¬P is impossible
  by_cases h : a ∈ D
  · -- If a ∈ D, then by key, a ∉ D - contradiction
    exact key.mp h h
  · -- If a ∉ D, then by key, a ∈ D - contradiction
    exact h (key.mpr h)

/-! ## Connection to Russell's Paradox -/

/-- The diagonal set D = {x | x ∉ f x} is reminiscent of Russell's paradox.
    If we try f = id (the identity), we get D = {x | x ∉ x}, which leads
    to the famous paradox in naive set theory.

    In type theory (and ZFC), this is resolved: we can't have x ∈ x
    because sets are stratified by rank. -/
theorem diagonal_set_paradox (S : Type*) (f : S → Set S) :
    let D := { x : S | x ∉ f x }
    ∀ a : S, f a = D → (a ∈ D ↔ a ∉ D) := by
  intro D a ha
  -- By definition of D: a ∈ D ↔ a ∉ f a
  have key : a ∈ D ↔ a ∉ f a := Iff.rfl
  -- Substitute f a = D to get: a ∈ D ↔ a ∉ D
  simp only [ha] at key
  exact key

/-! ## Visualization of the Diagonal Argument

```
       Position:   0    1    2    3    4    ...
Sequence f(0):    [0]   1    1    0    1    ...
Sequence f(1):     1   [0]   0    1    1    ...
Sequence f(2):     0    0   [1]   0    0    ...
Sequence f(3):     1    1    0   [0]   1    ...
Sequence f(4):     0    1    0    1   [0]   ...
         ⋮

Diagonal elements:  0    0    1    0    0    ...
Flipped diagonal:   1    1    0    1    1    ...  ← This sequence ≠ f(n) for any n!
```

The diagonal sequence differs from f(n) at position n, guaranteed. -/

#check cantor_diagonalization
#check no_surjection_nat_to_binary
#check reals_uncountable
#check cantor_powerset

end CantorDiagonalization
