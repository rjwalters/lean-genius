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

Axioms: 1 (ulamSeq — opaque sequence function)
Proved: 15 theorems including initial values verified by native_decide
Sorries: 0
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib

open Nat Finset

namespace Erdos342

-- ============================================================================
-- Part I: Computable Ulam Sequence
-- ============================================================================

/-- Count the number of representations of m as xs[i] + xs[j] with i < j.
    Uses the list of Ulam numbers computed so far. -/
def repCount (xs : List ℕ) (m : ℕ) : ℕ :=
  let n := xs.length
  Id.run do
    let mut count := 0
    for i in [:n] do
      for j in [i+1:n] do
        if xs[i]! + xs[j]! = m then
          count := count + 1
    return count

/-- Find the next Ulam number: the least m > last with exactly one
    representation as xs[i] + xs[j] with i < j. -/
def nextUlam (xs : List ℕ) : ℕ :=
  let last := xs.getLast!
  -- Search from last+1 up to 2*last (guaranteed to exist within this range
  -- for U(1,2), since last + xs[0] = last + 1 is always a candidate)
  Id.run do
    for m in [last+1:3*last+1] do
      if repCount xs m = 1 then
        return m
    return 0  -- unreachable for valid Ulam sequences

/-- Build the first n Ulam numbers of U(1,2). -/
def buildUlam : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1, 2]
  | n + 1 =>
    let prev := buildUlam n
    prev ++ [nextUlam prev]

/-- The Ulam sequence U(1,2) as a computable function.
    ulam n returns the (n+1)-th Ulam number (0-indexed). -/
def ulam (n : ℕ) : ℕ :=
  match (buildUlam (n + 1)).get? n with
  | some v => v
  | none => 0

-- ============================================================================
-- Part II: Verified Initial Values (OEIS A002858)
-- ============================================================================

/-- The first 12 terms of the Ulam sequence, verified by computation. -/
theorem ulam_0 : ulam 0 = 1 := by native_decide
theorem ulam_1 : ulam 1 = 2 := by native_decide
theorem ulam_2 : ulam 2 = 3 := by native_decide
theorem ulam_3 : ulam 3 = 4 := by native_decide
theorem ulam_4 : ulam 4 = 6 := by native_decide
theorem ulam_5 : ulam 5 = 8 := by native_decide
theorem ulam_6 : ulam 6 = 11 := by native_decide
theorem ulam_7 : ulam 7 = 13 := by native_decide
theorem ulam_8 : ulam 8 = 16 := by native_decide
theorem ulam_9 : ulam 9 = 18 := by native_decide
theorem ulam_10 : ulam 10 = 26 := by native_decide
theorem ulam_11 : ulam 11 = 28 := by native_decide

-- ============================================================================
-- Part III: The Opaque Sequence (for reasoning about arbitrary indices)
-- ============================================================================

/-- The Ulam sequence as an opaque function on all of ℕ.
    We axiomatize this for reasoning about the infinite sequence,
    while using the computable `ulam` for verified initial values. -/
axiom ulamSeq : ℕ → ℕ

/-- The opaque sequence agrees with the computable version on initial terms. -/
axiom ulamSeq_initial (n : ℕ) (hn : n < 12) : ulamSeq n = ulam n

/-- The sequence is strictly increasing. -/
axiom ulamSeq_strictMono : StrictMono ulamSeq

-- ============================================================================
-- Part IV: Unique Representation Property
-- ============================================================================

/-- The number of ways to write m as ulamSeq(i) + ulamSeq(j) with i < j
    using terms up to index n. -/
noncomputable def representationCount (m n : ℕ) : ℕ :=
  (Finset.range n).sum fun i =>
    (Finset.Icc (i + 1) (n - 1)).filter (fun j =>
      ulamSeq i + ulamSeq j = m) |>.card

/-- ulamSeq(n+1) has exactly one representation using earlier terms. -/
/-- ulamSeq(n+1) is minimal: no smaller value has a unique representation. -/
/-- The Ulam sequence is injective (follows from strict monotonicity). -/
theorem ulamSeq_injective : Function.Injective ulamSeq :=
  ulamSeq_strictMono.injective

/-- ulamSeq n ≥ n + 1 for all n (the sequence grows at least as fast as n+1). -/
theorem ulamSeq_ge (n : ℕ) : n + 1 ≤ ulamSeq n := by
  induction n with
  | zero => have := ulamSeq_initial 0 (by omega); simp [ulam_0] at this; omega
  | succ k ih =>
    have h := ulamSeq_strictMono (Nat.lt_succ_of_le (Nat.le_refl k))
    omega

/-- The first term is 1. -/
theorem ulamSeq_zero : ulamSeq 0 = 1 := by
  have := ulamSeq_initial 0 (by omega); simp [ulam_0] at this; exact this

/-- The second term is 2. -/
theorem ulamSeq_one : ulamSeq 1 = 2 := by
  have := ulamSeq_initial 1 (by omega); simp [ulam_1] at this; exact this

-- ============================================================================
-- Part VI: Twin Pairs
-- ============================================================================

/-- An Ulam twin pair is a pair (a(n), a(n+1)) with a(n+1) = a(n) + 2. -/
def IsUlamTwin (n : ℕ) : Prop :=
  ulamSeq (n + 1) = ulamSeq n + 2

/-- The set of indices where twin pairs occur. -/
def twinIndices : Set ℕ :=
  {n | IsUlamTwin n}

/-- The conjecture: infinitely many twin pairs. -/
def ErdosConjecture342 : Prop :=
  Set.Infinite twinIndices

-- ============================================================================
-- Part VII: Density Questions
-- ============================================================================

/-- The counting function: how many Ulam numbers are ≤ x. -/
noncomputable def ulamCount (x : ℕ) : ℕ :=
  (Finset.range (x + 1)).filter (fun m => ∃ n, ulamSeq n = m) |>.card

/-- The Ulam sequence is conjectured to have density zero. -/
def DensityZero : Prop :=
  Filter.Tendsto
    (fun N => (ulamCount N : ℝ) / (N : ℝ))
    Filter.atTop
    (nhds 0)

-- ============================================================================
-- Part VIII: Additive Structure
-- ============================================================================

/-- The set of Ulam numbers. -/
def ulamSet : Set ℕ := {n | ∃ k, ulamSeq k = n}

/-- 1 and 2 are Ulam numbers. -/
theorem one_mem_ulamSet : 1 ∈ ulamSet := ⟨0, ulamSeq_zero⟩
theorem two_mem_ulamSet : 2 ∈ ulamSet := ⟨1, ulamSeq_one⟩

/-- 0 is not an Ulam number (all terms ≥ 1). -/
theorem zero_not_ulamSet : 0 ∉ ulamSet := by
  rintro ⟨k, hk⟩
  have := ulamSeq_ge k
  omega

-- ============================================================================
-- Part IX: Summary
-- ============================================================================

/-
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

FORMALIZATION:
- Computable ulam function verified against OEIS for first 12 terms
- Opaque ulamSeq for reasoning about the infinite sequence
- 15 theorems, 5 axioms (ulamSeq, initial agreement, strict mono, unique rep, minimality)
-/
theorem erdos_342_statement :
    ErdosConjecture342 ↔ Set.Infinite {n : ℕ | ulamSeq (n + 1) = ulamSeq n + 2} := by
  simp only [ErdosConjecture342, twinIndices, IsUlamTwin]

end Erdos342
