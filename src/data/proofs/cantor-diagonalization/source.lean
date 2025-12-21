/-
  Cantor's Diagonalization Theorem

  A formal proof in Lean 4 that the real numbers are uncountable.
  This follows Cantor's famous diagonal argument from 1891: no function
  from natural numbers to infinite binary sequences can be surjective.

  Historical context: Georg Cantor published this proof in 1891, building
  on his 1874 proof of uncountability. This elegant argument revolutionized
  our understanding of infinity, showing that some infinities are larger
  than others.

  We prove the theorem in terms of functions from Nat to Bool, which
  represent infinite binary sequences (equivalently, real numbers in [0,1]).
-/

-- An infinite binary sequence is a function from Nat to Bool
def BinarySeq := Nat → Bool

-- The diagonal function: given a sequence of sequences,
-- construct a new sequence that differs from each sequence at position n
def diagonal (f : Nat → BinarySeq) : BinarySeq :=
  fun n => !(f n n)

-- Key lemma: the diagonal differs from every sequence in the list
theorem diagonal_differs (f : Nat → BinarySeq) (n : Nat) :
    diagonal f n ≠ f n n := by
  unfold diagonal
  simp only [Bool.not_eq_self, not_false_eq_true]

-- Cantor's Theorem: No function from Nat to BinarySeq is surjective
-- (there is no bijection between N and the set of binary sequences)
theorem cantor_diagonalization :
    ∀ f : Nat → BinarySeq, ∃ s : BinarySeq, ∀ n : Nat, f n ≠ s := by
  intro f
  -- Construct the diagonal sequence
  use diagonal f
  -- Show it differs from every f n
  intro n
  -- Suppose f n = diagonal f for contradiction
  intro h
  -- At position n, f n n must equal (diagonal f) n
  have : f n n = diagonal f n := congrFun h n
  -- But diagonal f n = !(f n n) by definition
  have contra : f n n ≠ diagonal f n := fun heq => by
    have := diagonal_differs f n
    exact this heq.symm
  exact contra this

-- Corollary: The reals are uncountable
-- (stated as: binary sequences are uncountable)
theorem reals_uncountable :
    ¬∃ f : Nat → BinarySeq, Function.Surjective f := by
  intro ⟨f, hf⟩
  -- By Cantor's theorem, there exists s not in the range of f
  obtain ⟨s, hs⟩ := cantor_diagonalization f
  -- But surjectivity says every s is in the range
  obtain ⟨n, hn⟩ := hf s
  -- Contradiction: f n = s but f n ≠ s
  exact hs n hn

-- Alternative formulation: there is no injection from BinarySeq to Nat
-- (would require choice to prove the contrapositive)

-- The power set version: |P(S)| > |S| for any set S
-- For finite sets: |P(S)| = 2^|S|
-- For infinite sets: the power set is strictly larger

theorem cantor_powerset (S : Type) :
    ¬∃ f : S → Set S, Function.Surjective f := by
  intro ⟨f, hf⟩
  -- Define the "diagonal" set: elements not in their own image
  let D : Set S := { x | x ∉ f x }
  -- D must be in the range of f (by surjectivity)
  obtain ⟨a, ha⟩ := hf D
  -- Is a ∈ D?
  by_cases h : a ∈ D
  · -- If a ∈ D, then a ∉ f a = D, contradiction
    have : a ∉ f a := h
    rw [ha] at this
    exact this h
  · -- If a ∉ D, then a ∈ f a = D, so a ∈ D, contradiction
    have : a ∈ f a := by
      rw [ha]
      exact h
    rw [ha] at this
    exact h this

-- Visualization of the diagonal argument:
--
--        Sequence 0:  0  1  1  0  1  0  ...
--        Sequence 1:  1  0  0  1  1  1  ...
--        Sequence 2:  0  0  1  0  0  1  ...
--        Sequence 3:  1  1  0  0  1  0  ...
--        Sequence 4:  0  1  0  1  0  1  ...
--        ...
--
-- Diagonal elements: 0, 0, 1, 0, 0, ...
-- Flipped diagonal:  1, 1, 0, 1, 1, ...  <- This sequence is not in the list!

#check cantor_diagonalization
#check reals_uncountable
#check cantor_powerset
