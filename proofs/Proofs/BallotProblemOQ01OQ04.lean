/-
# Chung-Feller Theorem via the Cycle Lemma

## Research Problem: ballot-problem-oq-01-oq-04

The Chung-Feller theorem states that the number of lattice paths from (0,0)
to (2n,0) with steps +1 and -1, having exactly k upsteps above the x-axis,
equals C(2n,n)/(n+1) = Cₙ (the nth Catalan number), independent of k.

## Proof Strategy

1. A lattice path from (0,0) to (2n,0) has n upsteps (+1) and n downsteps (-1).
2. Prepend +1 to get a sequence of length 2n+1 with sum 1.
3. By the cycle lemma (proved in BallotProblemOQ01.lean), exactly 1 of the
   2n+1 cyclic rotations has all partial sums positive.
4. This creates a (2n+1)-to-1 map from rotation orbits to balanced paths,
   uniformly distributed over n+1 types, yielding C(2n,n)/(n+1) per type.

## Infrastructure

- cycle_lemma: proved in BallotProblemOQ01.lean (Dvoretzky-Motzkin 1947)
- Cn (Catalan number): defined in BallotProblemOQ03.lean
- catalan_formula: Cn n * (n+1) = C(2n,n), proved in BallotProblemOQ03.lean

## Proved in This File

- balanced_length, balanced_sum_zero: basic properties of balanced paths
- prepend_mem_kCountedSequence: key connection to the cycle lemma
- prepend_one_good_rotation: exactly 1 good rotation (from cycle lemma)
- prepend_unique_good_rotation: the good rotation is unique
- balanced_path_total: C(2n,n) = Cₙ × (n+1)
- cyclicRotation_isBalancedPath: rotations of balanced paths are balanced
- cutAtOnePosition: extraction of balanced path from rotation orbit
- upsteps_above_below_disjoint: upstep position partition

Axiom count: 1 (chung_feller_uniform — requires tracking how rotations change
upstep-above-axis counts; see Part VI proof strategy for details)
Sorry count: 0

## References

- Chung, K.L. and Feller, W. (1949). On fluctuations in coin-tossing.
- Dvoretzky, A. and Motzkin, Th. (1947). A problem of arrangements.
-/

import Proofs.BallotProblemOQ01
import Proofs.BallotProblemOQ03

namespace ChungFeller

open GeneralizedBallot LatticePathLGV

/- ## Part I: Balanced Paths -/

/-- A balanced lattice path: a list of n ones and n negative-ones. -/
def IsBalancedPath (l : List ℤ) (n : ℕ) : Prop :=
  l.count 1 = n ∧ l.count (-1 : ℤ) = n ∧ (∀ x ∈ l, x = 1 ∨ x = (-1 : ℤ))

/-- A balanced path has length 2n. -/
theorem balanced_length {l : List ℤ} {n : ℕ} (h : IsBalancedPath l n) :
    l.length = 2 * n := by
  obtain ⟨h1, h2, h3⟩ := h
  have hlen := length_eq_count_add_count (k := 1) h3
  simp only [h1, h2] at hlen
  omega

/-- A balanced path has sum 0. -/
theorem balanced_sum_zero {l : List ℤ} {n : ℕ} (h : IsBalancedPath l n) :
    l.sum = 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  have hsum := sum_eq_count_sub_mul_count (k := 1) h3
  simp only [h1, h2] at hsum
  omega

/- ## Part II: Connection to the Cycle Lemma -/

/-- Prepending +1 to a balanced path of length 2n gives a sequence in
    kCountedSequence 1 (n+1) n: it has (n+1) ones and n negative-ones. -/
theorem prepend_mem_kCountedSequence {l : List ℤ} {n : ℕ}
    (h : IsBalancedPath l n) :
    (1 :: l) ∈ kCountedSequence 1 (n + 1) n := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · -- count of 1 in (1 :: l) = n + 1
    simp [h1]
  · -- count of -1 in (1 :: l) = n
    simp [show (1 : ℤ) ≠ (-1 : ℤ) from by decide, h2]
  · -- all elements are ±1
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · left; rfl
    · exact h3 x hx

/-- **Key result**: The cycle lemma gives exactly 1 good rotation for
    the prepended sequence, since a - kb = (n+1) - 1·n = 1. -/
theorem prepend_one_good_rotation {l : List ℤ} {n : ℕ}
    (h : IsBalancedPath l n) :
    (goodRotations (1 :: l)).card = 1 := by
  have hmem := prepend_mem_kCountedSequence h
  have hab : 1 * n < n + 1 := by omega
  have hcl := cycle_lemma hmem hab
  omega

/-- The prepended sequence has length 2n+1. -/
theorem prepend_length {l : List ℤ} {n : ℕ}
    (h : IsBalancedPath l n) :
    (1 :: l).length = 2 * n + 1 := by
  simp [balanced_length h]

/-- The prepended sequence has sum 1 (positive). -/
theorem prepend_sum {l : List ℤ} {n : ℕ}
    (h : IsBalancedPath l n) :
    (1 :: l).sum = 1 := by
  simp [List.sum_cons, balanced_sum_zero h]

/-- The good rotation is unique: there is exactly one good rotation index. -/
theorem prepend_unique_good_rotation {l : List ℤ} {n : ℕ}
    (h : IsBalancedPath l n) :
    ∃ i, goodRotations (1 :: l) = {i} :=
  Finset.card_eq_one.mp (prepend_one_good_rotation h)

/- ## Part III: Counting Identity -/

/-- **Balanced path total**: C(2n,n) = Cₙ × (n+1).
    This identity, combined with the Chung-Feller uniform distribution,
    gives that each path type has exactly Cₙ members. -/
theorem balanced_path_total (n : ℕ) :
    Nat.choose (2 * n) n = Cn n * (n + 1) :=
  (catalan_formula n).symm

/-- Catalan number verification. -/
example : Cn 0 = 1 := by native_decide
example : Cn 1 = 1 := by native_decide
example : Cn 2 = 2 := by native_decide
example : Cn 3 = 5 := by native_decide

/- ## Part IV: The Chung-Feller Theorem -/

/-- Height of a lattice path at position i (the i-th prefix sum). -/
def pathHeight (l : List ℤ) (i : ℕ) : ℤ := (l.take i).sum

/-- Count of upsteps (+1 steps) that occur at non-negative height. -/
noncomputable def upstepsAboveAxis (l : List ℤ) : ℕ :=
  ((Finset.range l.length).filter (fun i =>
    l.get? i = some 1 ∧ (0 : ℤ) ≤ (l.take i).sum)).card

/-- The set of balanced paths of length 2n with exactly k upsteps above the axis. -/
def balancedPathsOfType (n k : ℕ) : Set (List ℤ) :=
  {l | IsBalancedPath l n ∧ upstepsAboveAxis l = k}

/-- Computable version of `upstepsAboveAxis` for `native_decide` proofs. -/
def upstepsAboveAxisC (l : List ℤ) : ℕ :=
  ((Finset.range l.length).filter (fun i =>
    l.get? i = some 1 ∧ (0 : ℤ) ≤ (l.take i).sum)).card

/-- `upstepsAboveAxisC` agrees with `upstepsAboveAxis`. -/
theorem upstepsAboveAxisC_eq (l : List ℤ) :
    upstepsAboveAxisC l = upstepsAboveAxis l := rfl

/-- Computational verification of Chung-Feller for n=2:
    Types 0, 1, 2 each have exactly 2 = C₂ balanced paths. -/
example : upstepsAboveAxisC [1, 1, -1, -1] = 2 := by native_decide
example : upstepsAboveAxisC [1, -1, 1, -1] = 2 := by native_decide
example : upstepsAboveAxisC [1, -1, -1, 1] = 1 := by native_decide
example : upstepsAboveAxisC [-1, 1, 1, -1] = 1 := by native_decide
example : upstepsAboveAxisC [-1, 1, -1, 1] = 0 := by native_decide
example : upstepsAboveAxisC [-1, -1, 1, 1] = 0 := by native_decide

/- ## Part V: Structural Infrastructure for Chung-Feller -/

/-- Cyclic rotations of balanced paths are balanced paths.
    This is fundamental: the rotation orbit of a balanced path consists of balanced paths. -/
theorem cyclicRotation_isBalancedPath {l : List ℤ} {n : ℕ} (h : IsBalancedPath l n)
    {i : ℕ} (hi : i ≤ l.length) : IsBalancedPath (cyclicRotation l i) n := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · -- count 1 preserved: rotation just reorders elements
    simp only [cyclicRotation, List.count_append]
    have := congr_arg (List.count 1) (List.take_append_drop i l)
    rw [List.count_append] at this; omega
  · -- count (-1) preserved
    simp only [cyclicRotation, List.count_append]
    have := congr_arg (List.count (-1 : ℤ)) (List.take_append_drop i l)
    rw [List.count_append] at this; omega
  · -- all elements still ±1
    intro x hx
    rw [cyclicRotation, List.mem_append] at hx
    rcases hx with hx | hx
    · exact h3 x (List.drop_subset i l hx)
    · exact h3 x (List.take_subset i l hx)

/-- The balanced path obtained by cutting a prepended sequence at position i.
    Given a good sequence s = (1 :: l) of length 2n+1, cutting at a 1-position
    and removing the leading 1 yields a balanced path. -/
def cutAtOnePosition (s : List ℤ) (i : ℕ) : List ℤ :=
  (cyclicRotation s i).tail

/-- Height at position 0 is always 0. -/
theorem pathHeight_zero (l : List ℤ) : pathHeight l 0 = 0 := by
  simp [pathHeight]

/-- Count of upsteps (+1 steps) that occur at strictly negative height. -/
noncomputable def upstepsBelowAxis (l : List ℤ) : ℕ :=
  ((Finset.range l.length).filter (fun i =>
    l.get? i = some 1 ∧ (l.take i).sum < 0)).card

/-- Computable version of upstepsBelowAxis. -/
def upstepsBelowAxisC (l : List ℤ) : ℕ :=
  ((Finset.range l.length).filter (fun i =>
    l.get? i = some 1 ∧ (l.take i).sum < 0)).card

/-- The above-axis and below-axis upstep filters partition all upstep positions.
    Every upstep occurs at either non-negative or negative height. -/
theorem upsteps_above_below_disjoint (l : List ℤ) :
    Disjoint
      ((Finset.range l.length).filter (fun i =>
        l.get? i = some 1 ∧ (0 : ℤ) ≤ (l.take i).sum))
      ((Finset.range l.length).filter (fun i =>
        l.get? i = some 1 ∧ (l.take i).sum < 0)) := by
  apply Finset.disjoint_left.mpr
  intro i hi1 hi2
  simp only [Finset.mem_filter] at hi1 hi2
  omega

/-- Computational verification: upsteps partition for n=2 paths. -/
example : upstepsAboveAxisC [1, 1, -1, -1] + upstepsBelowAxisC [1, 1, -1, -1] = 2 := by
  native_decide
example : upstepsAboveAxisC [1, -1, -1, 1] + upstepsBelowAxisC [1, -1, -1, 1] = 2 := by
  native_decide
example : upstepsAboveAxisC [-1, -1, 1, 1] + upstepsBelowAxisC [-1, -1, 1, 1] = 2 := by
  native_decide

/- ## Part VI: The Chung-Feller Theorem -/

/-- **Chung-Feller Theorem (uniform distribution)**:

    For each k ∈ {0, 1, ..., n}, the number of balanced paths from (0,0) to (2n,0)
    with exactly k upsteps above the x-axis equals the number with j upsteps above
    the x-axis — the distribution is uniform across the n+1 types.

    Combined with `balanced_path_total` (C(2n,n) = Cₙ × (n+1)), this implies
    each type has exactly Cₙ paths.

    **Proof strategy** (from cycle lemma):
    1. For each balanced path l, form s = (1 :: l) of length 2n+1.
    2. By cycle_lemma, s has exactly 1 good rotation (all prefix sums > 0).
    3. Map φ: l ↦ good rotation of (1 :: l). This is (n+1)-to-1.
    4. Each fiber of φ consists of n+1 balanced paths obtained by cutting
       the rotation orbit at each 1-position and removing the leading 1.
    5. These n+1 paths have types 0, 1, ..., n (each exactly once).
    6. Steps 3-5 yield a partition of all C(2n,n) balanced paths into
       groups of n+1, one per type, proving uniform distribution.

    **Remaining work**: Step 5 requires showing that different cut positions
    in the rotation orbit yield different upstep-above-axis counts.
    This involves tracking how the prefix sum structure changes as the
    cut point moves through the sequence. -/
axiom chung_feller_uniform (n : ℕ) (j k : ℕ) (hj : j ≤ n) (hk : k ≤ n) :
    Set.ncard (balancedPathsOfType n j) = Set.ncard (balancedPathsOfType n k)

end ChungFeller
