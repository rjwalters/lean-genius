/-
# Chung-Feller Bijection: Rotation Index to Path Type

## Research Problem: ballot-problem-oq-01-oq-04-oq-01

Constructs an explicit bijection between balanced paths of different "types"
(paths of type k have exactly k upsteps starting at non-negative height),
proving the Chung-Feller uniform distribution theorem.

## Relation to BallotProblemOQ01OQ04

This file extends BallotProblemOQ01OQ04 by making the bijection explicit.
We import only BallotProblemOQ01 (the cycle lemma) to avoid a broken
dependency chain through BallotProblemOQ03. The definitions of IsBalancedPath,
upstepsAboveAxis, and balancedPathsOfType are reproduced here from OQ04.

## Proof Approach (Two-Stage Bijection)

**The Chung-Feller Rotation Map**: For a balanced path l of length 2n,
define R(l) = l.rotate (rightmostMinPos l) where rightmostMinPos gives
the last position where the prefix sum achieves its minimum.

Key mathematical fact: After rotating by the last-minimum position:
- All prefix sums of R(l) are ≥ 0 (measured from the global minimum)
- Therefore R(l) is a Dyck path (all upsteps above the x-axis)

The bijection: Each Dyck path d has exactly n+1 "fiber paths" (one per type):
the paths {d.rotate j | j is a "return to zero" position of d}.
Swapping between fibers gives the type bijection.

## Status
- rotation_preserves_balanced: proved
- rotation_maps_to_dyck: sorry (prefix sum tracking after rotation)
- fiber_distinct_types: sorry (orbit analysis)
- chung_feller_uniform_proved: sorry (derives from the two sorry lemmas above)

## References
- Chung, K.L. and Feller, W. (1949). On fluctuations in coin-tossing. PNAS 35.
- Dvoretzky, A. and Motzkin, Th. (1947). A problem of arrangements. Duke Math. J.
-/

import Proofs.BallotProblemOQ01
import Mathlib

open GeneralizedBallot List Set Finset Nat

namespace ChungFellerOQ01

/-!
## Section I: Balanced Path Definitions
(These match the definitions in BallotProblemOQ01OQ04 — reproduced here
to avoid importing BallotProblemOQ03 transitively.)
-/

/-- A balanced path of length 2n: a list of n upsteps (+1) and n downsteps (-1). -/
def IsBalancedPath (l : List ℤ) (n : ℕ) : Prop :=
  l.count 1 = n ∧ l.count (-1 : ℤ) = n ∧ (∀ x ∈ l, x = 1 ∨ x = (-1 : ℤ))

/-- Auxiliary: count upsteps starting at non-negative height, tracking current height. -/
def countUpstepsAux (height : ℤ) : List ℤ → ℕ
  | [] => 0
  | x :: xs =>
    let inc := if x = 1 ∧ 0 ≤ height then 1 else 0
    inc + countUpstepsAux (height + x) xs

/-- Count of upsteps (+1 steps) that start at non-negative height.
    Defined recursively to avoid deprecated/missing List.get? or List.enumFrom. -/
def upstepsAboveAxisC (l : List ℤ) : ℕ := countUpstepsAux 0 l

noncomputable def upstepsAboveAxis (l : List ℤ) : ℕ := countUpstepsAux 0 l

theorem upstepsAboveAxisC_eq (l : List ℤ) :
    upstepsAboveAxisC l = upstepsAboveAxis l := rfl

/-- The set of balanced paths of length 2n with exactly k upsteps above axis. -/
def balancedPathsOfType (n k : ℕ) : Set (List ℤ) :=
  {l | IsBalancedPath l n ∧ upstepsAboveAxis l = k}

/-!
## Section II: Computational Verifications for n = 1, 2, 3
-/

/-- n=1: Dyck path [1,-1] has type 1. -/
example : upstepsAboveAxisC [1, -1] = 1 := by native_decide
/-- n=1: Anti-Dyck path [-1,1] has type 0. -/
example : upstepsAboveAxisC [-1, 1] = 0 := by native_decide

/-- n=2: Exactly 2 paths of each type (2, 1, 0). -/
example : upstepsAboveAxisC [1, 1, -1, -1] = 2 := by native_decide
example : upstepsAboveAxisC [1, -1, 1, -1] = 2 := by native_decide
example : upstepsAboveAxisC [1, -1, -1, 1] = 1 := by native_decide
example : upstepsAboveAxisC [-1, 1, 1, -1] = 1 := by native_decide
example : upstepsAboveAxisC [-1, 1, -1, 1] = 0 := by native_decide
example : upstepsAboveAxisC [-1, -1, 1, 1] = 0 := by native_decide

-- n=2: Verify the rotation map sends type-1 and type-0 paths to Dyck (type-2).
-- [1,-1,-1,1] (type 1): height profile 0,1,0,-1,0; min at pos 3; rotate by 3.
example : ([1, -1, -1, 1] : List ℤ).rotate 3 = [1, 1, -1, -1] := by native_decide
example : upstepsAboveAxisC (([1, -1, -1, 1] : List ℤ).rotate 3) = 2 := by native_decide
/-- [-1,1,1,-1] (type 1): min at pos 1; rotate by 1. -/
example : ([-1, 1, 1, -1] : List ℤ).rotate 1 = [1, 1, -1, -1] := by native_decide
example : upstepsAboveAxisC (([-1, 1, 1, -1] : List ℤ).rotate 1) = 2 := by native_decide
/-- [-1,1,-1,1] (type 0): min at pos 3; rotate by 3. -/
example : ([-1, 1, -1, 1] : List ℤ).rotate 3 = [1, -1, 1, -1] := by native_decide
example : upstepsAboveAxisC (([-1, 1, -1, 1] : List ℤ).rotate 3) = 2 := by native_decide
/-- [-1,-1,1,1] (type 0): min at pos 2; rotate by 2. -/
example : ([-1, -1, 1, 1] : List ℤ).rotate 2 = [1, 1, -1, -1] := by native_decide
example : upstepsAboveAxisC (([-1, -1, 1, 1] : List ℤ).rotate 2) = 2 := by native_decide

/-- n=2: Rotating Dyck paths [1,1,-1,-1] and [1,-1,1,-1] by their min pos (= 4 = full rotation)
    gives back themselves — confirming Dyck paths are fixed points of the map. -/
example : ([1, 1, -1, -1] : List ℤ).rotate 4 = [1, 1, -1, -1] := by native_decide
example : ([1, -1, 1, -1] : List ℤ).rotate 4 = [1, -1, 1, -1] := by native_decide

/-!
## Section III: Rotation Preserves Balanced Paths
-/

/-- Cyclic rotation is a permutation. -/
private lemma rotate_perm_self (l : List ℤ) (r : ℕ) : l.rotate r ~ l :=
  List.rotate_perm l r

/-- Rotating preserves the count of +1s. -/
lemma rotate_count_one (l : List ℤ) (r : ℕ) :
    (l.rotate r).count 1 = l.count 1 :=
  (rotate_perm_self l r).count_eq 1

/-- Rotating preserves the count of -1s. -/
lemma rotate_count_neg_one (l : List ℤ) (r : ℕ) :
    (l.rotate r).count (-1 : ℤ) = l.count (-1 : ℤ) :=
  (rotate_perm_self l r).count_eq (-1 : ℤ)

/-- Rotation preserves element membership. -/
lemma rotate_mem (l : List ℤ) (r : ℕ) (x : ℤ) :
    x ∈ l.rotate r ↔ x ∈ l :=
  List.mem_rotate

/-- **Proved**: Rotating a balanced path gives a balanced path. -/
theorem rotation_preserves_balanced {l : List ℤ} {n : ℕ} (h : IsBalancedPath l n) (r : ℕ) :
    IsBalancedPath (l.rotate r) n :=
  ⟨by rw [rotate_count_one]; exact h.1,
   by rw [rotate_count_neg_one]; exact h.2.1,
   fun x hx => h.2.2 x ((rotate_mem l r x).mp hx)⟩


/-!
## Section IV: The Chung-Feller Rotation Map
-/

/-- The Chung-Feller rotation: rotate by the position of the last prefix-sum minimum.
    This sends each balanced path to a Dyck path (all prefix sums ≥ 0). -/
noncomputable def chungFellerRot (l : List ℤ) : List ℤ :=
  l.rotate (rightmostMinPos l)

/-- Rotating preserves the balanced path property. -/
theorem chungFellerRot_balanced {l : List ℤ} {n : ℕ} (h : IsBalancedPath l n) :
    IsBalancedPath (chungFellerRot l) n :=
  rotation_preserves_balanced h (rightmostMinPos l)

/-- **Key Lemma (HARD)**: The Chung-Feller rotation sends every balanced path to a Dyck path
    (one where all n upsteps start at non-negative height, i.e., type n).

    **Proof sketch**: Let h(i) = prefixSum l i (height at position i). Since
    r = rightmostMinPos l satisfies h(r) = min_{j≤2n} h(j), after rotating by r,
    the new height at position j is:
      h'(j) = h((r + j) mod 2n) - h(r)
    This is ≥ 0 for all j, since h(r) is the global minimum. Hence every upstep
    of chungFellerRot l starts at non-negative height.

    **Formal gap**: Proving h'(j) = h((r+j) mod 2n) - h(r) requires showing that
    prefixSum (l.rotate r) j = prefixSum l (r+j) - prefixSum l r (for j ≤ 2n-r)
    and the wrap-around case. This involves careful case analysis on List.rotate. -/
theorem rotation_maps_to_dyck {l : List ℤ} {n : ℕ} (h : IsBalancedPath l n)
    (hn : 1 ≤ n) :
    upstepsAboveAxis (chungFellerRot l) = n := by
  sorry

/-!
## Section V: Fiber Analysis — Preimages Under the Rotation Map
-/

/-- The preimage of a Dyck path d under chungFellerRot, within balanced paths of type n. -/
noncomputable def rotFiber (n : ℕ) (d : List ℤ) : Set (List ℤ) :=
  {l | IsBalancedPath l n ∧ chungFellerRot l = d}

/-- **Fiber Lemma (HARD)**: Each Dyck path d of length 2n has exactly n+1 preimages
    under chungFellerRot, one of each type 0, 1, ..., n.

    **Proof sketch**: A Dyck path d of length 2n returns to height 0 at exactly n+1
    positions: 0 = p_0 < p_1 < ... < p_n = 2n (the n "valley" positions plus the
    endpoints). For each k ∈ {0, ..., n}, define:
      l_k = d.rotate (2*n - p_k)   (rotate by the complement of the k-th return)
    Then:
    1. l_k is a balanced path (by rotation_preserves_balanced)
    2. rightmostMinPos(l_k) = 2*n - p_k, so chungFellerRot(l_k) = d (fixed point check)
    3. upstepsAboveAxis(l_k) = k (the type shifts by rotation amount)
    The l_k are distinct since p_k are distinct. Conversely, any preimage is some l_k.

    **Formal gap**: Identifying the return-to-zero positions and proving properties (2,3). -/
theorem fiber_has_all_types {d : List ℤ} {n : ℕ}
    (hd : IsBalancedPath d n) (hDyck : upstepsAboveAxis d = n)
    (hn : 1 ≤ n) :
    ∀ k ≤ n, ∃ l ∈ rotFiber n d, upstepsAboveAxis l = k := by
  sorry

/-!
## Section VI: Chung-Feller Uniform Distribution
-/

/-- **Chung-Feller Theorem (proved from fiber bijection)**:
    For any j, k ≤ n, the balanced paths of type j and type k have the same cardinality.

    **Proof**:
    - The map l ↦ chungFellerRot l is a surjection from all balanced paths to Dyck paths.
    - Each Dyck path d has exactly n+1 fibers (one per type) by fiber_has_all_types.
    - This induces an explicit bijection: type j → (Dyck path) → type k.
    - Formally: for each l of type j, find d = chungFellerRot l, then use
      fiber_has_all_types to get the unique preimage of type k. -/
theorem chung_feller_uniform (n : ℕ) (j k : ℕ) (hj : j ≤ n) (hk : k ≤ n) :
    Set.ncard (balancedPathsOfType n j) = Set.ncard (balancedPathsOfType n k) := by
  by_cases hn : n = 0
  · subst hn; simp at hj hk; subst hj; subst hk; rfl
  · -- For n ≥ 1, apply the fiber bijection
    -- (depends on rotation_maps_to_dyck and fiber_has_all_types, both sorry'd)
    sorry

/-!
## Section VII: Consequences

These theorems follow from chung_feller_uniform, giving the full picture.
-/

/-- The uniform distribution implies all types have the same count. -/
theorem all_types_equal_count (n : ℕ) (k : ℕ) (hk : k ≤ n) :
    Set.ncard (balancedPathsOfType n k) = Set.ncard (balancedPathsOfType n 0) :=
  chung_feller_uniform n k 0 hk (Nat.zero_le n)

/-- Balanced paths partition into n+1 equal-size classes by type. -/
theorem type_classes_partition_balanced (n : ℕ) :
    ∀ l, IsBalancedPath l n ↔ ∃ k ≤ n, l ∈ balancedPathsOfType n k := by
  intro l
  constructor
  · intro hl
    exact ⟨upstepsAboveAxis l, by
      -- upstepsAboveAxis l ≤ n since there are only n upsteps
      sorry,
    hl, rfl⟩
  · rintro ⟨k, _, hl, _⟩
    exact hl

end ChungFellerOQ01
