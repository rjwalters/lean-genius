/-
# Erdős Problem #954 — Rosen's Greedy Additive Sequence

Let 0 = a₀ < a₁ < a₂ < ⋯ be defined by a₀ = 0, a₁ = 1, and a_{k+1} is
the smallest integer n such that the number of representations
a_i + a_j ≤ n (0 ≤ i ≤ j ≤ k, j ≥ 1) is less than n.

**Conjecture**: The representation count R(x) = |{(i,j) : a_i + a_j ≤ x, i ≤ j, j ≥ 1}|
satisfies R(x) = x + O(x^{1/4+o(1)}).

**Status: OPEN.** Erdős and Rosen could not even prove R(x) ≤ (1+o(1))x.

The sequence begins: 0, 1, 3, 5, 9, 13, 17, 24, 31, 38, 45, ...
OEIS: A390642

Reference: https://erdosproblems.com/954
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/- ## Core Definitions -/

/-- The representation count: number of pairs (i,j) with
    i ≤ j, j ≥ 1, and a(i) + a(j) ≤ n for a given sequence a. -/
def repCount (a : ℕ → ℕ) (k : ℕ) (n : ℕ) : ℕ :=
  (Finset.Icc 1 k).sum fun j =>
    (Finset.Icc 0 j).filter (fun i => a i + a j ≤ n) |>.card

/-- The greedy condition: a(k+1) is the smallest n such that
    repCount a k n < n. This ensures the sequence grows as slowly
    as possible while keeping R(n) < n at each new element. -/
def IsGreedyNext (a : ℕ → ℕ) (k : ℕ) : Prop :=
  repCount a k (a (k + 1)) < a (k + 1) ∧
  ∀ m, a k < m → m < a (k + 1) → repCount a k m ≥ m

/-- Rosen's greedy sequence satisfies the greedy condition at every step. -/
def IsRosenSequence (a : ℕ → ℕ) : Prop :=
  a 0 = 0 ∧ a 1 = 1 ∧ StrictMono a ∧ ∀ k ≥ 1, IsGreedyNext a k

/- ## Computable Sequence Construction -/

/-- Compute repCount for a list-based sequence. The list stores values
    in order: xs[0] = a(0), xs[1] = a(1), etc. -/
def repCountList (xs : List ℕ) (n : ℕ) : ℕ :=
  let k := xs.length - 1
  (List.range k).foldl (fun acc j' =>
    let j := j' + 1
    acc + (List.range (j + 1)).countP (fun i =>
      match xs[i]?, xs[j]? with
      | some ai, some aj => ai + aj ≤ n
      | _, _ => false)
  ) 0

/-- Find the next greedy element: smallest n > last such that
    repCount xs n < n. Uses a fuel parameter to ensure termination. -/
def findNextRosen (xs : List ℕ) (last : ℕ) : ℕ → ℕ
  | 0 => last + 1
  | fuel + 1 =>
    let candidate := last + 1
    if repCountList xs candidate < candidate then candidate
    else findNextRosen xs candidate fuel

/-- Build the Rosen sequence as (list, last_element) pair. -/
def buildRosen : ℕ → List ℕ × ℕ
  | 0 => ([0], 0)
  | 1 => ([0, 1], 1)
  | n + 2 =>
    let (prev, last) := buildRosen (n + 1)
    let next := findNextRosen prev last 200
    (prev ++ [next], next)

/-- Extract the k-th term from the computed Rosen sequence. -/
def rosenTerm (k : ℕ) : ℕ :=
  match (buildRosen k).1[k]? with
  | some v => v
  | none => 0

/- ## Verified Initial Values -/

-- Verify via computation that our greedy algorithm produces the expected values
-- (0, 1, 3, 5, 9, 13, 17, 24, 31, 38, 45)
theorem rosen_term_0 : rosenTerm 0 = 0 := by native_decide
theorem rosen_term_1 : rosenTerm 1 = 1 := by native_decide
theorem rosen_term_2 : rosenTerm 2 = 3 := by native_decide
theorem rosen_term_3 : rosenTerm 3 = 5 := by native_decide
theorem rosen_term_4 : rosenTerm 4 = 9 := by native_decide
theorem rosen_term_5 : rosenTerm 5 = 13 := by native_decide
theorem rosen_term_6 : rosenTerm 6 = 17 := by native_decide
theorem rosen_term_7 : rosenTerm 7 = 24 := by native_decide
theorem rosen_term_8 : rosenTerm 8 = 31 := by native_decide
theorem rosen_term_9 : rosenTerm 9 = 38 := by native_decide
theorem rosen_term_10 : rosenTerm 10 = 45 := by native_decide

/- ## Basic Properties (proved from definitions) -/

/-- By construction, R(n) < n at each new element of the sequence. -/
theorem repcount_below_at_elements (a : ℕ → ℕ) (h : IsRosenSequence a) (k : ℕ) (hk : 1 ≤ k) :
    repCount a k (a (k + 1)) < a (k + 1) :=
  (h.2.2.2 k hk).1

/-- By construction, R(x) ≥ x for all x between consecutive elements. -/
theorem repcount_above_between (a : ℕ → ℕ) (h : IsRosenSequence a) (k : ℕ) (hk : 1 ≤ k)
    (m : ℕ) (hm1 : a k < m) (hm2 : m < a (k + 1)) :
    repCount a k m ≥ m :=
  (h.2.2.2 k hk).2 m hm1 hm2

/-- The Rosen sequence is strictly monotone by definition. -/
theorem rosen_strictMono (a : ℕ → ℕ) (h : IsRosenSequence a) : StrictMono a :=
  h.2.2.1

/-- The sequence elements grow: a(k) ≥ k for a Rosen sequence. -/
theorem rosen_growth (a : ℕ → ℕ) (h : IsRosenSequence a) (k : ℕ) :
    a k ≥ k := by
  induction k with
  | zero => simp [h.1]
  | succ n ih =>
    have hlt : a n < a (n + 1) := h.2.2.1 (Nat.lt_succ_of_le le_rfl)
    omega

/-- For a Rosen sequence, the representation count satisfies R(m) ≥ m
    for every m strictly between a(k) and a(k+1). -/
theorem repcount_lower_bound_pre_element (a : ℕ → ℕ) (h : IsRosenSequence a) (k : ℕ)
    (hk : 1 ≤ k) (hgap : a k + 1 < a (k + 1)) :
    repCount a k (a (k + 1) - 1) ≥ a (k + 1) - 1 := by
  have hgreedy := h.2.2.2 k hk
  apply hgreedy.2
  · omega
  · omega

/- ## The Main Conjecture (OPEN) -/

/-- The full representation count over the infinite sequence. -/
def fullRepCount (a : ℕ → ℕ) (x : ℕ) : ℕ :=
  (Finset.range (x + 1)).sum fun j =>
    if j = 0 then 0 else
    (Finset.Icc 0 j).filter (fun i => a i + a j ≤ x) |>.card

/-- Weak conjecture: R(x) = (1 + o(1))x. Erdős and Rosen
    could not even prove this. -/
/-- Strong conjecture: R(x) = x + O(x^{1/4 + o(1)}).
    The error term x^{1/4} is the natural guess from Sidon set theory. -/
/- ## Connection to Sidon Sets and B₂ Sequences -/

/-- A B₂ sequence (Sidon set): all pairwise sums are distinct. -/
def IsB2Sequence (a : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ i₁ j₁ i₂ j₂, i₁ ≤ j₁ → j₁ ≤ k → i₂ ≤ j₂ → j₂ ≤ k →
    a i₁ + a j₁ = a i₂ + a j₂ → (i₁ = i₂ ∧ j₁ = j₂)

/-- The Rosen sequence is a relaxation of B₂: it allows repeated sums
    to achieve higher density. This is an open structural claim about
    any sequence satisfying the greedy property. -/
/-- The cumulative representation count fullRepCount is unbounded
    for any infinite sequence. This is trivially true: for any B,
    take x large enough that at least B+1 values j ∈ {1,...,B+1}
    satisfy a(0)+a(j) ≤ x; each such j contributes ≥ 1 to the count.
    (The B₂ hypothesis is not needed for this particular statement.) -/
theorem erdos_turan_context :
    ∀ a : ℕ → ℕ, (∀ k, IsB2Sequence a k) →
    ∀ B, ∃ n, fullRepCount a n > B := by
  intro a _ B
  -- Choose x = max(B+1, max_{j=1..B+1} (a 0 + a j))
  -- Each j ∈ {1,...,B+1} then contributes ≥ 1 via pair (0,j)
  let M := (Finset.Icc 1 (B + 1)).sup (fun j => a 0 + a j)
  let x := max M (B + 1)
  use x
  unfold fullRepCount
  -- Step 1: Σ over Icc 1 (B+1) of f(j) ≤ Σ over range(x+1) of g(j)
  -- where f(j) = filter.card and g(j) = if j=0 then 0 else filter.card
  -- Step 2: |Icc 1 (B+1)| ≤ Σ over Icc 1 (B+1) of f(j), since each f(j) ≥ 1
  -- Step 3: |Icc 1 (B+1)| = B+1
  suffices h : B + 1 ≤
      (Finset.range (x + 1)).sum (fun j =>
        if j = 0 then 0 else
        ((Finset.Icc 0 j).filter fun i => a i + a j ≤ x).card) by omega
  -- Each j ∈ {1,...,B+1} contributes ≥ 1 via i=0
  have h_each : ∀ j ∈ Finset.Icc 1 (B + 1),
      1 ≤ ((Finset.Icc 0 j).filter fun i => a i + a j ≤ x).card := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    apply Finset.card_pos.mpr
    exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩,
      le_trans (Finset.le_sup (f := fun j => a 0 + a j)
        (Finset.mem_Icc.mpr ⟨hj.1, hj.2⟩)) (le_max_left _ _)⟩⟩
  -- card(Icc 1 (B+1)) = B+1 ≤ sum over Icc of f ≤ sum over range of g
  calc B + 1
      = (Finset.Icc 1 (B + 1)).card := by rw [Nat.card_Icc]; omega
    _ = (Finset.Icc 1 (B + 1)).sum (fun _ => 1) := by simp
    _ ≤ (Finset.Icc 1 (B + 1)).sum (fun j =>
          ((Finset.Icc 0 j).filter fun i => a i + a j ≤ x).card) :=
        Finset.sum_le_sum (fun j hj => h_each j hj)
    _ ≤ (Finset.Icc 1 (B + 1)).sum (fun j =>
          if j = 0 then 0 else
          ((Finset.Icc 0 j).filter fun i => a i + a j ≤ x).card) := by
        apply Finset.sum_le_sum; intro j hj
        rw [Finset.mem_Icc] at hj; simp [show j ≠ 0 by omega]
    _ ≤ (Finset.range (x + 1)).sum (fun j =>
          if j = 0 then 0 else
          ((Finset.Icc 0 j).filter fun i => a i + a j ≤ x).card) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun j hj => Finset.mem_range.mpr (by rw [Finset.mem_Icc] at hj; omega))
          (fun _ _ _ => Nat.zero_le _)

/- ## Representation Count Monotonicity -/

/-- Adding more elements to the sequence can only increase the rep count.
    If we extend the sequence from k to k+1 elements, any pair counted
    in repCount a k n is still counted in repCount a (k+1) n, plus
    new pairs involving a(k+1). -/
theorem repCount_mono_k (a : ℕ → ℕ) (k n : ℕ) :
    repCount a k n ≤ repCount a (k + 1) n := by
  unfold repCount
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  · intros; exact Nat.zero_le _
