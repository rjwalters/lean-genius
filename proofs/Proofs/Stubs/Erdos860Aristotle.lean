/-
  Aristotle targets for Erdős Problem #860
  Routine supporting lemmas for automated proof search.
  See Erdos860Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT linear_lower_bound (requires non-trivial application of erdos_selfridge axiom)
  - NOT subquadratic_upper_bound (requires non-trivial application of erdos_pomerance axiom)
  - NOT h(n) definition (definition sorry — Aristotle skips)
  - Routine: PrimeCovering structure properties, AdmitsCovering monotonicity, base cases
  - No definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos860Aristotle

/-- The n-th prime number (1-indexed, so nthPrime 1 = 2). -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- A prime covering assignment for the interval (m, m+L]:
    distinct integers a_i where p_i | a_i. -/
structure PrimeCovering (m : ℕ) (L : ℕ) (k : ℕ) where
  assignment : Fin k → ℕ
  in_interval : ∀ i, m < assignment i ∧ assignment i ≤ m + L
  distinct : ∀ i j, i ≠ j → assignment i ≠ assignment j
  divisibility : ∀ i, (nthPrime (i.val + 1)) ∣ assignment i

/-- The interval (m, m+L] admits a prime covering for the first k primes. -/
def AdmitsCovering (m L k : ℕ) : Prop :=
  Nonempty (PrimeCovering m L k)

-- Routine: Each assignment value is bounded above by m + L.
theorem covering_le_upper {m L k : ℕ} (c : PrimeCovering m L k) (i : Fin k) :
    c.assignment i ≤ m + L :=
  (c.in_interval i).2

-- Routine: Each assignment value strictly exceeds m.
theorem covering_gt_lower {m L k : ℕ} (c : PrimeCovering m L k) (i : Fin k) :
    m < c.assignment i :=
  (c.in_interval i).1

-- Routine: Each assignment value is positive when m = 0.
theorem covering_pos_of_zero_base {L k : ℕ} (c : PrimeCovering 0 L k) (i : Fin k) :
    0 < c.assignment i := by
  exact (c.in_interval i).1

-- Routine: The empty covering is admitted for any m and L (k = 0).
-- Fin 0 is empty so all conditions are vacuously satisfied.
theorem admits_covering_zero (m L : ℕ) : AdmitsCovering m L 0 :=
  ⟨{ assignment := fun i => i.elim0
     in_interval := fun i => i.elim0
     distinct := fun i => i.elim0
     divisibility := fun i => i.elim0 }⟩

-- Routine: AdmitsCovering is monotone in L.
-- If (m, m+L₁] can cover k primes and L₁ ≤ L₂, then (m, m+L₂] can too.
theorem admits_covering_mono {m L₁ L₂ k : ℕ} (hL : L₁ ≤ L₂)
    (hc : AdmitsCovering m L₁ k) : AdmitsCovering m L₂ k := by
  obtain ⟨c⟩ := hc
  exact ⟨⟨c.assignment,
    fun i => ⟨(c.in_interval i).1,
              (c.in_interval i).2.trans (Nat.add_le_add_left hL m)⟩,
    c.distinct,
    c.divisibility⟩⟩

-- Routine: For m ≥ 1, any covering assignment value is at least 2.
theorem covering_ge_two {m L k : ℕ} (hm : 1 ≤ m) (c : PrimeCovering m L k) (i : Fin k) :
    2 ≤ c.assignment i := by
  have h := (c.in_interval i).1
  omega

end Erdos860Aristotle
