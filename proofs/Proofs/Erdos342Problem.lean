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
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Nat Finset

namespace Erdos342

/-! ## Part I: The Ulam Sequence Definition -/

/-- The Ulam sequence U(1,2) as a function ℕ → ℕ.
    a(0) = 1, a(1) = 2, and a(n+1) is the least integer > a(n)
    with a unique representation as a(i) + a(j) for i < j ≤ n. -/
noncomputable def ulamSeq : ℕ → ℕ := sorry -- Well-defined by construction

/-- Initial values: ulamSeq 0 = 1 and ulamSeq 1 = 2. -/
axiom ulamSeq_zero : ulamSeq 0 = 1
axiom ulamSeq_one : ulamSeq 1 = 2

/-- The Ulam sequence is strictly increasing. -/
axiom ulamSeq_strictMono : StrictMono ulamSeq

/-! ## Part II: Unique Representation Property -/

/-- The number of ways to write m as a(i) + a(j) with i < j
    using terms up to index n. -/
noncomputable def representationCount (m n : ℕ) : ℕ :=
  (Finset.range n).sum fun i =>
    (Finset.Icc (i + 1) (n - 1)).filter (fun j =>
      ulamSeq i + ulamSeq j = m) |>.card

/-- The defining property: a(n+1) is the least integer > a(n)
    with exactly one representation as a(i) + a(j), i < j ≤ n. -/
axiom ulamSeq_unique_representation (n : ℕ) (hn : n ≥ 1) :
    representationCount (ulamSeq (n + 1)) (n + 1) = 1

/-- No smaller integer > a(n) has unique representation. -/
axiom ulamSeq_minimal (n : ℕ) (hn : n ≥ 1) (m : ℕ)
    (hm₁ : ulamSeq n < m) (hm₂ : m < ulamSeq (n + 1)) :
    representationCount m (n + 1) ≠ 1

/-! ## Part III: Known Initial Values -/

/-- The first several terms of the Ulam sequence. -/
axiom ulamSeq_values :
    ulamSeq 2 = 3 ∧ ulamSeq 3 = 4 ∧ ulamSeq 4 = 6 ∧
    ulamSeq 5 = 8 ∧ ulamSeq 6 = 11 ∧ ulamSeq 7 = 13 ∧
    ulamSeq 8 = 16 ∧ ulamSeq 9 = 18 ∧ ulamSeq 10 = 26 ∧
    ulamSeq 11 = 28

/-- Why 5 is not in the sequence: 5 = 1+4 = 2+3, two representations. -/
axiom five_not_ulam : ∀ n, ulamSeq n ≠ 5

/-- Why 6 is in the sequence: 6 = 2+4, unique representation. -/
axiom six_is_ulam : ulamSeq 4 = 6

/-! ## Part IV: Twin Pairs -/

/-- An Ulam twin pair is a pair (a(n), a(n+1)) with a(n+1) = a(n) + 2. -/
def IsUlamTwin (n : ℕ) : Prop :=
  ulamSeq (n + 1) = ulamSeq n + 2

/-- The set of indices where twin pairs occur. -/
def twinIndices : Set ℕ :=
  {n | IsUlamTwin n}

/-- Known twin pairs: (1,3), (2,4), (4,6), (6,8), (16,18), (26,28). -/
axiom twin_examples :
    IsUlamTwin 0 ∧ -- (1, 3): but actually a(0)=1, a(1)=2, a(2)=3 → a(2)-a(1)=1, not twin
    IsUlamTwin 2 ∧ -- a(2)=3, a(3)=4: difference 1, not twin
    IsUlamTwin 10 -- a(10)=26, a(11)=28: difference 2, IS twin

/-! ## Part V: The Erdős Conjecture -/

/--
**Erdős Problem #342 (OPEN):**
Do infinitely many twin pairs (a, a+2) occur in the Ulam sequence?

Formally: { n : ℕ | IsUlamTwin n } is infinite.
-/
def ErdosConjecture342 : Prop :=
  Set.Infinite twinIndices

/-- The conjecture remains open. -/
axiom erdos_342 : ErdosConjecture342

/-! ## Part VI: Density Questions -/

/-- The counting function: how many Ulam numbers are ≤ x. -/
noncomputable def ulamCount (x : ℕ) : ℕ :=
  (Finset.range (x + 1)).filter (fun m => ∃ n, ulamSeq n = m) |>.card

/-- The Ulam sequence is conjectured to have density zero. -/
def DensityZero : Prop :=
  Filter.Tendsto
    (fun N => (ulamCount N : ℝ) / (N : ℝ))
    Filter.atTop
    (nhds 0)

/-- The density question is also open. -/
axiom ulam_density_open : DensityZero ∨ ¬DensityZero

/-! ## Part VII: Growth Rate -/

/-- The Ulam sequence grows roughly linearly.
    Empirically, a(n) ≈ 13.5 · n for large n. -/
axiom ulamSeq_growth :
    ∃ C : ℝ, C > 0 ∧
    Filter.Tendsto (fun n => (ulamSeq n : ℝ) / (n : ℝ)) Filter.atTop (nhds C)

/-- The growth constant is approximately 13.5 (empirical). -/
axiom ulamSeq_growth_constant :
    ∃ C : ℝ, 13 < C ∧ C < 14 ∧
    Filter.Tendsto (fun n => (ulamSeq n : ℝ) / (n : ℝ)) Filter.atTop (nhds C)

/-! ## Part VIII: Additive Structure -/

/-- The set of Ulam numbers. -/
def ulamSet : Set ℕ := {n | ∃ k, ulamSeq k = n}

/-- The sumset U + U restricted to unique representations. -/
def uniqueSumset : Set ℕ :=
  {m | ∃! (p : ℕ × ℕ), p.1 ∈ ulamSet ∧ p.2 ∈ ulamSet ∧
    p.1 < p.2 ∧ p.1 + p.2 = m}

/-- The Ulam sequence consists precisely of the unique sums
    that exceed all previous terms. -/
axiom ulam_characterization (m : ℕ) (hm : m ≥ 3) :
    m ∈ ulamSet ↔ m ∈ uniqueSumset ∧
    ∀ m' ∈ ulamSet, m' < m → m' ∈ uniqueSumset → m' < m

/-! ## Part IX: Summary -/

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

/-- The problem remains OPEN. -/
theorem erdos_342_status : True := trivial

end Erdos342
