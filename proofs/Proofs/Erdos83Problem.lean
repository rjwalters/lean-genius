/-
Erdős Problem #83: Complete Intersection Theorem

Source: https://erdosproblems.com/83
Status: SOLVED (Ahlswede-Khachatrian 1997)
Prize: $500 Erdős prize

Statement:
Suppose we have a family F of subsets of [4n] such that |A| = 2n for all A ∈ F
and for every A, B ∈ F we have |A ∩ B| ≥ 2. Then:
|F| ≤ ½(C(4n,2n) - C(2n,n)²)

Background:
- Erdős-Ko-Rado (1961): foundational theorem on intersecting families
- This problem extends EKR to require |A ∩ B| ≥ 2 (t-intersecting)
- The bound is achieved by the 'majority family': all 2n-subsets containing
  at least n+1 elements from a fixed 2n-set

Answer: PROVED (Ahlswede-Khachatrian 1997)
- The Complete Intersection Theorem determines the maximum size of
  t-intersecting families of k-subsets of [m] for all valid parameters
- This specific case with m=4n, k=2n, t=2 follows as a corollary

References:
- Erdős, Ko, Rado (1961): "Intersection theorems for systems of finite sets"
- Ahlswede, Khachatrian (1997): "The complete intersection theorem for systems
  of finite sets" European J. Combin. 18, 125-136
-/

import Mathlib

open Finset Nat

namespace Erdos83

/-
## Part I: Basic Definitions
-/

/--
**The Ground Set [m]:**
We represent [m] = {1, 2, ..., m} as Fin m.
-/
def groundSet (m : ℕ) : Finset (Fin m) := Finset.univ

/--
**k-Uniform Family:**
A family F is k-uniform if every member has exactly k elements.
-/
def isKUniform {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (k : ℕ) : Prop :=
  ∀ A ∈ F, A.card = k

/--
**t-Intersecting Family:**
A family F is t-intersecting if every pair of members intersects in at least t elements.
-/
def isTIntersecting {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (t : ℕ) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≥ t

/--
**1-Intersecting (Classical Intersecting):**
The classical Erdős-Ko-Rado case: every pair intersects.
-/
def isIntersecting {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  isTIntersecting F 1

/-
## Part II: The Erdős-Ko-Rado Theorem (Background)
-/

/--
**Maximum Intersecting Family Size:**
For k-subsets of [n] with n ≥ 2k, the maximum 1-intersecting family has size C(n-1, k-1).
-/
axiom erdos_ko_rado_bound (n k : ℕ) (hn : n ≥ 2 * k) :
  ∀ (F : Finset (Finset (Fin n))),
    isKUniform F k → isIntersecting F →
    F.card ≤ Nat.choose (n - 1) (k - 1)

/--
**EKR Extremal Family:**
The extremal family consists of all k-sets containing a fixed element.
-/
def ekrStarFamily (n k : ℕ) (x : Fin n) : Finset (Finset (Fin n)) :=
  (Finset.univ.powerset).filter (fun S => S.card = k ∧ x ∈ S)

/--
**EKR is Achieved:**
The star family achieves the EKR bound.
-/
axiom ekr_achieved (n k : ℕ) (hn : n ≥ 2 * k) (hk : k ≥ 1) (x : Fin n) :
  (ekrStarFamily n k x).card = Nat.choose (n - 1) (k - 1)

/-
## Part III: The t-Intersecting Problem
-/

/--
**The Specific Problem Parameters:**
For Erdős #83: m = 4n, k = 2n, t = 2
-/
def erdos83Params (n : ℕ) : ℕ × ℕ × ℕ := (4 * n, 2 * n, 2)

/--
**Valid t-Intersecting Family for Erdős #83:**
A family of 2n-subsets of [4n] with pairwise 2-intersections.
-/
def isValidErdos83Family (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) : Prop :=
  isKUniform F (2 * n) ∧ isTIntersecting F 2

/-
## Part IV: The Conjectured Bound
-/

/--
**The Erdős-Ko-Rado Conjecture for t=2:**
The maximum is ½(C(4n,2n) - C(2n,n)²).
-/
def erdos83Bound (n : ℕ) : ℕ :=
  (Nat.choose (4 * n) (2 * n) - Nat.choose (2 * n) n ^ 2) / 2

/--
**The Formal Problem Statement:**
-/
def erdos83Question (n : ℕ) : Prop :=
  ∀ (F : Finset (Finset (Fin (4 * n)))),
    isValidErdos83Family n F →
    F.card ≤ erdos83Bound n

/-
## Part V: The Extremal Construction
-/

/--
**Star-Like Family (Majority Family):**
All 2n-subsets of [4n] containing at least n+1 elements from the first 2n elements.
Two such sets must share ≥ 2 elements by pigeonhole:
if |A ∩ [2n]| ≥ n+1 and |B ∩ [2n]| ≥ n+1, then |A ∩ B| ≥ (n+1)+(n+1)-2n = 2.
-/
def starLikeFamily (n : ℕ) : Finset (Finset (Fin (4 * n))) :=
  (Finset.univ : Finset (Fin (4 * n))).powerset.filter fun S =>
    S.card = 2 * n ∧ (S.filter fun x => x.val < 2 * n).card ≥ n + 1

/--
**Extremal Family Achieves Bound:**
-/
axiom starLikeFamily_achieves (n : ℕ) (hn : n ≥ 1) :
  (starLikeFamily n).card = erdos83Bound n

/--
**Extremal Family is Valid:**
-/
axiom starLikeFamily_valid (n : ℕ) (hn : n ≥ 1) :
  isValidErdos83Family n (starLikeFamily n)

/-
## Part VI: The Complete Intersection Theorem
-/

/--
**Critical Ratio r:**
For general (m, k, t), the optimal family is determined by the unique r satisfying:
1/(r+1) ≤ (m - 2k + 2t - 2) / ((t-1)(k-t+1)) < 1/r

Equivalently, r = floor(((t-1)(k-t+1) - 1) / (m - 2k + 2t - 2)).

For (m, k, t) = (4n, 2n, 2): critical ratio r = n - 1.
-/
def criticalRatio (m k t : ℕ) : ℕ :=
  let num := (m + 2 * t) - (2 * k + 2)  -- m - 2k + 2t - 2
  let den := (t - 1) * (k - t + 1)       -- (t-1)(k-t+1)
  if num = 0 then 0 else (den - 1) / num

/--
**AK-Family Structure:**
The family A(r) consists of all k-subsets containing at least (t + r) elements
from the first (t + 2r) elements of [m].
-/
def akFamily (m k t r : ℕ) : Finset (Finset (Fin m)) :=
  (Finset.univ : Finset (Fin m)).powerset.filter fun S =>
    S.card = k ∧ (S.filter fun x => x.val < t + 2 * r).card ≥ t + r

/--
**Complete Intersection Theorem (Ahlswede-Khachatrian 1997):**
The maximum t-intersecting family of k-subsets of [m] is A(r)
where r is the critical ratio.
-/
axiom ahlswede_khachatrian_theorem (m k t : ℕ)
    (hm : m ≥ 2 * k) (ht : 2 ≤ t) (htk : t ≤ k) :
  ∀ (F : Finset (Finset (Fin m))),
    isKUniform F k → isTIntersecting F t →
    F.card ≤ (akFamily m k t (criticalRatio m k t)).card

/-
## Part VII: Resolution of Erdős #83
-/

/--
**Erdős #83 as Special Case:**
With m = 4n, k = 2n, t = 2, the Complete Intersection Theorem gives
exactly the bound ½(C(4n,2n) - C(2n,n)²).
-/
axiom erdos83_from_ak (n : ℕ) (hn : n ≥ 1) :
  (akFamily (4*n) (2*n) 2 (criticalRatio (4*n) (2*n) 2)).card = erdos83Bound n

/--
**Affirmative Answer:**
Ahlswede-Khachatrian confirmed the Erdős-Ko-Rado conjecture for this case.
-/
theorem erdos83_answer (n : ℕ) (hn : n ≥ 1) : erdos83Question n := by
  intro F hF
  have h1 : isKUniform F (2 * n) := hF.1
  have h2 : isTIntersecting F 2 := hF.2
  have hbound := ahlswede_khachatrian_theorem (4*n) (2*n) 2
    (by omega) (by omega) (by omega) F h1 h2
  rw [erdos83_from_ak n hn] at hbound
  exact hbound

/-
## Part VIII: Bound Computation
-/

/--
**Bound for Small n:**
For n=1: C(4,2) = 6, C(2,1)² = 4, bound = (6-4)/2 = 1.
For n=2: C(8,4) = 70, C(4,2)² = 36, bound = (70-36)/2 = 17.
-/
theorem erdos83_bound_n1 : erdos83Bound 1 = 1 := by native_decide

theorem erdos83_bound_n2 : erdos83Bound 2 = 17 := by native_decide

/--
**Asymptotic Growth:**
The bound is approximately C(4n, 2n)/2 for large n,
since C(2n,n)² ≪ C(4n,2n) as n → ∞.
-/
axiom erdos83_bound_asymptotic (n : ℕ) (hn : n ≥ 10) :
  (erdos83Bound n : ℝ) ≥ Nat.choose (4*n) (2*n) / 2 - Nat.choose (2*n) n

/-
## Part IX: Implications and Generalizations
-/

/-
**Phase Transitions:**
The structure of optimal t-intersecting families changes at critical values of r.
As (m, k, t) vary, the optimal family A(r) changes structure discontinuously —
a discrete phase transition phenomenon analogous to statistical mechanics.
-/

/-
**Coding Theory Connection:**
t-intersecting k-uniform families on [m] correspond to constant-weight binary
codes of length m, weight k, and minimum 'agreement' t. The AK theorem
determines optimal code sizes for all parameters.
-/

/-
**Pushing-Pulling Technique:**
Ahlswede-Khachatrian introduced a two-element generalization of Frankl's shifting.
Classical shifting (replace element j with i < j) preserves 1-intersecting but
can destroy t-intersecting for t ≥ 2. Pushing-pulling modifies pairs simultaneously,
maintaining the stronger intersection requirement.
-/

/-
**Multipartite Extension:**
The theorem extends to families of multipartite sets and cross-intersecting
families {(A, B) : |A ∩ B| ≥ t}.
-/

/-
## Part X: Summary
-/

/--
**Summary of Results:**
Both the bound and its tightness (achieved by the star-like majority family).
-/
theorem erdos_83_summary (n : ℕ) (hn : n ≥ 1) :
    -- The problem asks for maximum size of 2-intersecting 2n-families on [4n]
    (∀ F, isValidErdos83Family n F → F.card ≤ erdos83Bound n) ∧
    -- The bound is achieved by the star-like family
    (starLikeFamily n).card = erdos83Bound n := by
  constructor
  · exact erdos83_answer n hn
  · exact starLikeFamily_achieves n hn

/--
**Erdős Problem #83: SOLVED**

For a family F of 2n-subsets of [4n] with |A ∩ B| ≥ 2 for all A, B ∈ F:
  |F| ≤ ½(C(4n,2n) - C(2n,n)²)

This bound is achieved by the majority family: all 2n-subsets containing
at least n+1 elements from a fixed 2n-set.

Proved by Ahlswede and Khachatrian (1997) via the Complete Intersection Theorem.
Prize: $500 Erdős prize.
-/
theorem erdos_83 (n : ℕ) (hn : n ≥ 1) : erdos83Question n := erdos83_answer n hn

end Erdos83
