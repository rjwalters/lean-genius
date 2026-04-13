/-
  Aristotle targets for Erdős Problem #628 (Erdős-Lovász Tihany Conjecture)
  Routine supporting lemmas for automated proof search.
  See Stubs/Erdos628Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the open conjecture (TihanyConjecture)
  - NOT theorems depending on independenceNumber (def-sorry)
  - NOT theorems depending on IsLineGraph or IsQuasiLine (def-sorry)
  - Routine symmetry and monotonicity facts
  - No definition sorries
  - No axioms

  Included targets (5):
  - areDisjoint_symm: Disjoint S T ↔ Disjoint T S
  - isCliqueFree_mono: IsCliqueFree G k → IsCliqueFree G (k+1)
  - splittable_symm: IsSplittable G a b → IsSplittable G b a
  - hasDisjointHighChromatic_symm: HasDisjointHighChromatic G a b → ... G b a
  - tihanyForPair_symm: TihanyForPair a b → TihanyForPair b a
-/
import Mathlib
import Proofs.GraphCore

namespace Erdos628Aristotle

open SimpleGraph Finset GraphCore

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsCliqueFree (G : SimpleGraph V) (k : ℕ) : Prop :=
  cliqueNumber G < k

def IsSplittable (G : SimpleGraph V) (a b : ℕ) : Prop :=
  ∃ S T : Finset V,
    Disjoint S T ∧
    chromaticNumber (G.induce S) ≥ a ∧
    chromaticNumber (G.induce T) ≥ b

def HasDisjointHighChromatic (G : SimpleGraph V) (a b : ℕ) : Prop :=
  ∃ S T : Finset V,
    (S ∩ T = ∅) ∧
    chromaticNumber (G.induce S) ≥ a ∧
    chromaticNumber (G.induce T) ≥ b

def TihanyForPair (a b : ℕ) : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    let k := a + b - 1
    chromaticNumber G = k →
    IsCliqueFree G k →
    IsSplittable G a b

-- Routine: Disjoint is symmetric.
-- Disjoint.comm in Mathlib.
theorem areDisjoint_symm (S T : Finset V) (h : Disjoint S T) : Disjoint T S := by
  sorry

-- Routine: IsCliqueFree is monotone in k.
-- cliqueNumber G < k implies cliqueNumber G < k+1.
theorem isCliqueFree_mono (G : SimpleGraph V) (k : ℕ) (hG : IsCliqueFree G k) :
    IsCliqueFree G (k + 1) := by
  sorry

-- Routine: IsSplittable is symmetric.
-- Swapping S and T gives the symmetric case.
theorem splittable_symm (G : SimpleGraph V) (a b : ℕ)
    (h : IsSplittable G a b) : IsSplittable G b a := by
  sorry

-- Routine: HasDisjointHighChromatic is symmetric.
-- Swapping S and T gives the symmetric case.
theorem hasDisjointHighChromatic_symm (G : SimpleGraph V) (a b : ℕ)
    (h : HasDisjointHighChromatic G a b) : HasDisjointHighChromatic G b a := by
  sorry

-- Routine: TihanyForPair is symmetric in (a,b).
-- If TihanyForPair a b, then TihanyForPair b a (note a+b-1 = b+a-1).
theorem tihanyForPair_symm (a b : ℕ)
    (h : TihanyForPair a b) : TihanyForPair b a := by
  sorry

end Erdos628Aristotle
