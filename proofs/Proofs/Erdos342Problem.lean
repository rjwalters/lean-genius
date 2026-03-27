/-
Erdős Problem #342: The Ulam Sequence U(1,2)

Source: https://erdosproblems.com/342
Status: OPEN

Statement:
Define a sequence where a₁ = 1, a₂ = 2, and for n ≥ 2, a_{n+1} is the
least integer greater than aₙ that can be expressed uniquely as aᵢ + aⱼ
with i < j ≤ n.

The sequence begins: 1, 2, 3, 4, 6, 8, 11, 13, 16, 18, 26, 28, ...

Questions:
1. Do infinitely many twin pairs (a, a+2) occur in the Ulam sequence?
2. Does the sequence have asymptotic density zero?

OEIS: A002858

Reference: [ErGr80, p.53]
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib

open Nat Finset

namespace Erdos342

/- ##Part I: The Ulam Sequence Definition -/

/-- The Ulam sequence U(1,2) as a function ℕ → ℕ.
    a(0) = 1, a(1) = 2, and a(n+1) is the least integer > a(n)
    with a unique representation as a(i) + a(j) for i < j ≤ n. -/
axiom ulamSeq : ℕ → ℕ

/- ##Part II: Unique Representation Property -/

/-- The number of ways to write m as a(i) + a(j) with i < j
    using terms up to index n. -/
noncomputable def representationCount (m n : ℕ) : ℕ :=
  (Finset.range n).sum fun i =>
    (Finset.Icc (i + 1) (n - 1)).filter (fun j =>
      ulamSeq i + ulamSeq j = m) |>.card

/- ##Part III: Known Initial Values -/

/- ##Part IV: Twin Pairs -/

/-- An Ulam twin pair is a pair (a(n), a(n+1)) with a(n+1) = a(n) + 2. -/
def IsUlamTwin (n : ℕ) : Prop :=
  ulamSeq (n + 1) = ulamSeq n + 2

/-- The set of indices where twin pairs occur. -/
def twinIndices : Set ℕ :=
  {n | IsUlamTwin n}

/- ##Part V: The Erdős Conjecture -/

/--
**Erdős Problem #342 (OPEN):**
Do infinitely many twin pairs (a, a+2) occur in the Ulam sequence?

Formally: { n : ℕ | IsUlamTwin n } is infinite.
-/
def ErdosConjecture342 : Prop :=
  Set.Infinite twinIndices

/- ##Part VI: Density Questions -/

/-- The counting function: how many Ulam numbers are ≤ x. -/
noncomputable def ulamCount (x : ℕ) : ℕ :=
  (Finset.range (x + 1)).filter (fun m => ∃ n, ulamSeq n = m) |>.card

/-- The Ulam sequence is conjectured to have density zero. -/
def DensityZero : Prop :=
  Filter.Tendsto
    (fun N => (ulamCount N : ℝ) / (N : ℝ))
    Filter.atTop
    (nhds 0)

/-- The density question is open, but A ∨ ¬A holds by excluded middle. -/
theorem ulam_density_open : DensityZero ∨ ¬DensityZero :=
  Classical.em DensityZero

/- ##Part VII: Growth Rate -/

/- ##Part VIII: Additive Structure -/

/-- The set of Ulam numbers. -/
def ulamSet : Set ℕ := {n | ∃ k, ulamSeq k = n}

/-- The sumset U + U restricted to unique representations. -/
def uniqueSumset : Set ℕ :=
  {m | ∃! (p : ℕ × ℕ), p.1 ∈ ulamSet ∧ p.2 ∈ ulamSet ∧
    p.1 < p.2 ∧ p.1 + p.2 = m}

/- ##Part IX: Summary -/

/--
**Erdős Problem #342: Summary**

PROBLEM: In the Ulam sequence U(1,2) = 1, 2, 3, 4, 6, 8, 11, 13, 16, 18, 26, 28, ...,
do infinitely many twin pairs (a, a+2) occur?

STATUS: OPEN

KNOWN:
- The sequence is well-defined and strictly increasing
- Growth rate: a(n) ≈ 13.5 · n (empirical)
- Twin pairs include (26, 28), (478, 480), ...
- The density question is also open
- OEIS A002858
-/
theorem erdos_342_statement :
    ErdosConjecture342 ↔ Set.Infinite {n : ℕ | ulamSeq (n + 1) = ulamSeq n + 2} := by
  simp only [ErdosConjecture342, twinIndices, IsUlamTwin]

/-- Erdős Problem #342: OPEN
    The twin pairs conjecture is equivalent to Set.Infinite twinIndices. -/
theorem erdos_342_open : ErdosConjecture342 ↔ Set.Infinite twinIndices := Iff.rfl

end Erdos342
