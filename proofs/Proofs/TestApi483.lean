import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic

-- Test: basic Schur number concepts
-- A k-coloring of {1, ..., N} (using 0-indexed Fin)

-- Does a coloring have a monochromatic a + b = c?
def hasMonoSum (N k : ℕ) (χ : Fin N → Fin k) : Prop :=
  ∃ (a b c : Fin N), (a.val + 1) + (b.val + 1) = (c.val + 1) ∧ χ a = χ b ∧ χ a = χ c

-- The Schur property: every k-coloring of {1,...,N} has a monochromatic sum
def SchurProp (N k : ℕ) : Prop :=
  ∀ χ : Fin N → Fin k, hasMonoSum N k χ

-- Test basic API
#check @Fintype.decidableForallFintype
#check Nat.find
#check Nat.find_spec
