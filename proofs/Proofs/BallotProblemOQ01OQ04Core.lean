/-
# Chung-Feller Setup: Definitions and Cycle-Lemma Bridge (Core)

## Role in the proof family

This Core file holds the structural definitions and supporting lemmas shared
between the gallery face `BallotProblemOQ01OQ04.lean` and the bijection
proof `BallotProblemOQ01OQ04OQ01.lean`.

The split exists so that the bijection proof can supply the Chung-Feller
uniform-distribution theorem (`chung_feller_uniform'`) that the gallery face
re-exports as `chung_feller_uniform`, eliminating what was previously stated
as an axiom.

## Provided here

- `IsBalancedPath`, `balanced_length`, `balanced_sum_zero`
- `prepend_mem_kCountedSequence`, `prepend_one_good_rotation`,
  `prepend_unique_good_rotation`, `prepend_length`, `prepend_sum`
- `balanced_path_total`: C(2n,n) = Cₙ × (n+1)
- `pathHeight`, `upstepsAboveAxis`, `upstepsAboveAxisC`,
  `balancedPathsOfType`
- `isBalancedPath_nil`, `balanced_zero_eq_nil`
- Catalan-number sanity examples and small computational checks

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

/- ## Part IV: Path Type Definitions -/

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

/-- Computational verification of Chung-Feller for n=1:
    Each of types 0 and 1 has exactly 1 = C₁ balanced path. -/
example : upstepsAboveAxisC [1, -1] = 1 := by native_decide
example : upstepsAboveAxisC [-1, 1] = 0 := by native_decide

/-- Computational verification of Chung-Feller for n=2:
    Types 0, 1, 2 each have exactly 2 = C₂ balanced paths. -/
example : upstepsAboveAxisC [1, 1, -1, -1] = 2 := by native_decide
example : upstepsAboveAxisC [1, -1, 1, -1] = 2 := by native_decide
example : upstepsAboveAxisC [1, -1, -1, 1] = 1 := by native_decide
example : upstepsAboveAxisC [-1, 1, 1, -1] = 1 := by native_decide
example : upstepsAboveAxisC [-1, 1, -1, 1] = 0 := by native_decide
example : upstepsAboveAxisC [-1, -1, 1, 1] = 0 := by native_decide

/-- The empty list is the unique balanced path with n = 0. -/
theorem isBalancedPath_nil : IsBalancedPath ([] : List ℤ) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · simp
  · intro x hx
    simp at hx

/-- A balanced path with n = 0 is the empty list. -/
theorem balanced_zero_eq_nil {l : List ℤ} (h : IsBalancedPath l 0) : l = [] := by
  have hlen : l.length = 0 := by
    have := balanced_length h
    omega
  rcases l with _ | ⟨x, rest⟩
  · rfl
  · simp at hlen

end ChungFeller
