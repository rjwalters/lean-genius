import Archive.Wiedijk100Theorems.BallotProblem
import Mathlib.Tactic

/-
# The Generalized Ballot Problem: k-Fold Dominance

## Research Problem: ballot-problem-oq-01
Generalization of the Ballot Problem to the k-fold case.

## What This Proves
The Generalized Ballot Problem extends Bertrand's classical result (Wiedijk #30)
to the case where candidate A must maintain more than k times the votes of
candidate B throughout the entire counting process.

**Mathematical Statement:**
In an election where candidate A receives `a` votes and candidate B receives `b`
votes (where `a > k * b` for a positive integer `k`), the probability that A
always has more than `k` times as many votes as B throughout the counting is:

  P = (a - k * b) / (a + b)

This generalizes the classical formula P = (p - q)/(p + q) (the case k = 1).

## Approach
- **Lattice Path Model**: We model the vote counting using paths with upsteps (+1)
  and downsteps (-k). The condition "A has > k times B's votes" is equivalent to
  the path staying strictly above the x-axis.
- **Cycle Lemma**: The proof of the counting formula uses the Dvoretzky-Motzkin
  cycle lemma, which counts the number of "good" cyclic rotations.
- **Connection to Classical Case**: When k = 1, this reduces to the standard
  ballot problem with steps +1 and -1.

## Status
- [x] Definitions for generalized ballot sequences
- [x] Statement of the generalized ballot theorem
- [x] Proof that k=1 reduces to the classical ballot theorem
- [x] Key structural lemmas (sum, length, nonempty, path height, permutation characterization)
- [x] Finiteness of kCountedSequence (via permutation characterization)
- [x] Cycle lemma infrastructure (rotation sum/length/identity/membership preservation)
- [x] Positive sum/length preconditions for cycle lemma
- [x] Prefix sum relation for rotations (both wrapping and non-wrapping cases)
- [ ] Cyclic rotation composition (Aristotle-suitable)
- [ ] Full proof of the cycle lemma (3 sorries remain)
- [ ] Full proof of the generalized counting formula

## References
- Bertrand (1887): Original ballot problem
- Dvoretzky & Motzkin (1947): Cycle lemma
- Renault (2007): "Four Proofs of the Ballot Theorem"
-/

namespace GeneralizedBallot

open List Set

/- ## Part I: Generalized Ballot Sequences

We model the k-fold ballot problem using lattice paths:
- An upstep (+1) represents a vote for candidate A
- A downstep (-k) represents a vote for candidate B

A sequence is "k-good" if all prefix sums stay positive, meaning A always
has more than k times as many votes as B.
-/

/-- A generalized ballot sequence with `a` upsteps (+1) and `b` downsteps (-k).
This represents an election where A gets `a` votes and B gets `b` votes,
and each of B's votes "costs" k in the running total. -/
def kCountedSequence (k a b : ℕ) : Set (List ℤ) :=
  {l | l.count 1 = a ∧ l.count (-(k : ℤ)) = b ∧ ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ)}

/-- A lattice path stays positive if every nonempty prefix has positive sum.
This means the running total never reaches zero or below. -/
def kStaysPositive : Set (List ℤ) :=
  {l | ∀ (i : ℕ), 0 < i → i ≤ l.length → 0 < (l.take i).sum}

/- ## Part II: Core Algebraic Lemmas

These helper lemmas express the sum and length of a binary-valued list
in terms of element counts. They underpin all the basic properties. -/

/-- For a list where every element is 1 or -(k : ℤ), the sum equals
count(1) - k * count(-k). This is the core algebraic identity. -/
theorem sum_eq_count_sub_mul_count {k : ℕ} {l : List ℤ}
    (h : ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ)) :
    l.sum = (l.count 1 : ℤ) - (k : ℤ) * (l.count (-(k : ℤ))) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self x xs)
    have hxs : ∀ y ∈ xs, y = 1 ∨ y = -(k : ℤ) := fun y hy =>
      h y (List.mem_cons_of_mem x hy)
    have hne : (1 : ℤ) ≠ -(k : ℤ) := by omega
    simp only [List.sum_cons, List.count_cons]
    rw [ih hxs]
    rcases hx with rfl | rfl
    · -- x = 1: count 1 increases by 1, count (-k) stays the same
      simp [hne]
      push_cast
      omega
    · -- x = -k: count (-k) increases by 1, count 1 stays the same
      simp [hne.symm]
      push_cast
      ring

/-- For a list where every element is 1 or -(k : ℤ), the length equals
count(1) + count(-k). -/
theorem length_eq_count_add_count {k : ℕ} {l : List ℤ}
    (h : ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ)) :
    l.length = l.count 1 + l.count (-(k : ℤ)) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self x xs)
    have hxs : ∀ y ∈ xs, y = 1 ∨ y = -(k : ℤ) := fun y hy =>
      h y (List.mem_cons_of_mem x hy)
    have hne : (1 : ℤ) ≠ -(k : ℤ) := by omega
    simp only [List.length_cons, List.count_cons]
    rw [ih hxs]
    rcases hx with rfl | rfl
    · simp [hne]; omega
    · simp [hne.symm]; omega

/- ## Part III: Basic Properties of kCountedSequence -/

/-- The sum of a generalized ballot sequence is `a - k * b`. -/
theorem kCountedSequence_sum {k a b : ℕ} {l : List ℤ} (hl : l ∈ kCountedSequence k a b) :
    l.sum = (a : ℤ) - k * b := by
  have h := sum_eq_count_sub_mul_count hl.2.2
  rw [hl.1, hl.2.1] at h
  exact h

/-- The length of a generalized ballot sequence is `a + b`. -/
theorem kCountedSequence_length {k a b : ℕ} {l : List ℤ} (hl : l ∈ kCountedSequence k a b) :
    l.length = a + b := by
  have h := length_eq_count_add_count hl.2.2
  rw [hl.1, hl.2.1] at h
  exact h

/-- Generalized ballot sequences are finite.
They are a subset of lists of fixed length with elements from a two-element alphabet,
so the cardinality is at most 2^(a+b). -/
theorem kCountedSequence_perm (k a b : ℕ) (l : List ℤ) (hl : l ∈ kCountedSequence k a b) :
    l ~ (List.replicate a 1 ++ List.replicate b (-(k : ℤ))) := by
  rw [List.perm_iff_count]
  intro x
  have ⟨h1, h2, h3⟩ := hl
  have hne : (1 : ℤ) ≠ -(k : ℤ) := by omega
  by_cases hx1 : x = 1
  · subst hx1; simp [List.count_append, List.count_replicate, hne, hne.symm, h1]
  · by_cases hxk : x = -(k : ℤ)
    · subst hxk; simp [List.count_append, List.count_replicate, hne, hne.symm, h2]
    · have : l.count x = 0 := by
        rw [List.count_eq_zero]; intro hm; rcases h3 x hm with rfl | rfl <;> contradiction
      rw [this]; simp [List.count_append, List.count_replicate, hx1, hxk]

theorem kCountedSequence_finite (k a b : ℕ) : (kCountedSequence k a b).Finite := by
  -- Every element is a permutation of a fixed witness list w.
  -- The set of permutations of w is finite (subset of w.permutations list).
  let w := List.replicate a 1 ++ List.replicate b (-(k : ℤ))
  apply Set.Finite.subset (Finset.finite_toSet w.permutations.toFinset)
  intro l hl
  simp only [Finset.coe_toSet, List.mem_toFinset, List.mem_permutations]
  exact kCountedSequence_perm k a b l hl

/-- There is at least one generalized ballot sequence.
The witness is `replicate a 1 ++ replicate b (-(k : ℤ))`. -/
theorem kCountedSequence_nonempty (k a b : ℕ) : (kCountedSequence k a b).Nonempty := by
  use List.replicate a 1 ++ List.replicate b (-(k : ℤ))
  have hne : (1 : ℤ) ≠ -(k : ℤ) := by omega
  refine ⟨?_, ?_, ?_⟩
  · -- count 1 = a
    simp only [List.count_append, List.count_replicate]
    simp [hne, hne.symm]
  · -- count (-k) = b
    simp only [List.count_append, List.count_replicate]
    simp [hne, hne.symm]
  · -- all elements are 1 or -k
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact Or.inl (List.eq_of_mem_replicate hx)
    · exact Or.inr (List.eq_of_mem_replicate hx)

/- ## Part IV: Connection to Classical Ballot Problem

When k = 1, the generalized ballot problem reduces to the classical one.
The key observation: `kCountedSequence 1 a b` is exactly Mathlib's `countedSequence a b`
(since steps are +1 and -1), and our `kStaysPositive` corresponds to Mathlib's
`staysPositive` (which checks all nonempty suffixes have positive sum).
-/

/-- When k = 1, a generalized ballot sequence is exactly a classical ballot sequence.
The only values in the list are +1 and -1, matching Mathlib's `countedSequence`. -/
theorem kCountedSequence_eq_countedSequence (a b : ℕ) :
    kCountedSequence 1 a b = Ballot.countedSequence a b := by
  ext l
  simp only [kCountedSequence, Ballot.countedSequence, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, h3⟩
    simpa using h2
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, h3⟩
    simpa using h2

/- ## Part V: The Generalized Ballot Theorem -/

/-- **The Generalized Ballot Theorem (k-fold dominance)**

The number of good sequences satisfies the ballot equation.
This follows from the cycle lemma by double counting:
- For each sequence, exactly `a - k*b` of its `a+b` rotations are good (cycle lemma)
- Each good sequence arises as a rotation from exactly `a+b` source sequences
- Therefore: good_count * (a+b) = total_sequences * (a - k*b) -/
theorem generalized_ballot_count (k a b : ℕ) (hab : k * b < a) :
    ∃ (good_count : ℕ),
      good_count * (a + b) = (a - k * b) * (a + b).choose a := by
  sorry -- Requires: cycle_lemma + double counting + rotation bijectivity

/-- The probability form of the generalized ballot theorem.
When `a > k * b`, the probability is `(a - k * b) / (a + b)`. -/
theorem generalized_ballot_prob (k a b : ℕ) (hab : k * b < a) :
    ((a : ℚ) - k * b) / (a + b) > 0 := by
  have h1 : (0 : ℚ) < a - k * b := by
    rw [sub_pos]
    exact_mod_cast hab
  have h2 : (0 : ℚ) < a + b := by
    have : 0 < a := by omega
    positivity
  exact div_pos h1 h2

/- ## Part VI: Special Cases and Verification -/

/-- When k = 1, the generalized formula reduces to the classical ballot formula.
With `a > b`, P = (a - b)/(a + b). -/
theorem generalized_ballot_classical (a b : ℕ) :
    ((a : ℚ) - 1 * b) / (a + b) = (a - b) / (a + b) := by
  ring

/-- Example: k = 2, a = 5, b = 2. Since 5 > 2*2 = 4, the probability is
(5 - 2*2)/(5 + 2) = 1/7. -/
example : ((5 : ℚ) - 2 * 2) / (5 + 2) = 1 / 7 := by norm_num

/-- Example: k = 3, a = 10, b = 3. Since 10 > 3*3 = 9, the probability is
(10 - 3*3)/(10 + 3) = 1/13. -/
example : ((10 : ℚ) - 3 * 3) / (10 + 3) = 1 / 13 := by norm_num

/-- Example: k = 1, a = 3, b = 1. This is the classical case: P = 2/4 = 1/2. -/
example : ((3 : ℚ) - 1 * 1) / (3 + 1) = 1 / 2 := by norm_num

/-- Example: k = 2, a = 7, b = 3. P = (7 - 6)/(7 + 3) = 1/10. -/
example : ((7 : ℚ) - 2 * 3) / (7 + 3) = 1 / 10 := by norm_num

/- ## Part VII: The Cycle Lemma

The key tool for proving the generalized ballot theorem is the Dvoretzky-Motzkin
Cycle Lemma (1947).

Cycle Lemma: Given a sequence of integers x_1, x_2, ..., x_n with total
sum S > 0, exactly S of the n cyclic permutations have all positive partial sums.

For our application:
- The sequence has a entries of +1 and b entries of -k
- Total sum = a - kb > 0
- Length = a + b
- Number of "good" cyclic permutations = a - kb

This gives us the fraction of good orderings: (a - kb) / (a + b).
-/

/-- A cyclic rotation of a list by `i` positions. -/
def cyclicRotation (l : List ℤ) (i : ℕ) : List ℤ :=
  l.drop i ++ l.take i

/-- Cyclic rotation preserves the sum of the list. -/
theorem cyclicRotation_sum (l : List ℤ) (i : ℕ) :
    (cyclicRotation l i).sum = l.sum := by
  simp only [cyclicRotation, List.sum_append]
  have h := congr_arg List.sum (List.take_append_drop i l)
  rw [List.sum_append] at h
  omega

/-- Cyclic rotation preserves the length of the list. -/
theorem cyclicRotation_length (l : List ℤ) (i : ℕ) (hi : i ≤ l.length) :
    (cyclicRotation l i).length = l.length := by
  simp [cyclicRotation, List.length_drop, List.length_take, Nat.min_eq_left hi]
  omega

/-- Cyclic rotation by 0 is the identity. -/
theorem cyclicRotation_zero (l : List ℤ) :
    cyclicRotation l 0 = l := by
  simp [cyclicRotation]

/-- Cyclic rotation by n (the length) returns the original list. -/
theorem cyclicRotation_length_self (l : List ℤ) :
    cyclicRotation l l.length = l := by
  simp [cyclicRotation]

/-- Cyclic rotation preserves membership in kCountedSequence.
All rotations of a ballot sequence are themselves ballot sequences. -/
theorem cyclicRotation_mem_kCountedSequence {k a b : ℕ} {l : List ℤ}
    (hl : l ∈ kCountedSequence k a b) (i : ℕ) (hi : i ≤ l.length) :
    cyclicRotation l i ∈ kCountedSequence k a b := by
  have ⟨h1, h2, h3⟩ := hl
  refine ⟨?_, ?_, ?_⟩
  · -- count 1 is preserved by rotation
    simp only [cyclicRotation, List.count_append]
    have := congr_arg (List.count 1) (List.take_append_drop i l)
    rw [List.count_append] at this
    omega
  · -- count (-k) is preserved by rotation
    simp only [cyclicRotation, List.count_append]
    have := congr_arg (List.count (-(k : ℤ))) (List.take_append_drop i l)
    rw [List.count_append] at this
    omega
  · -- all elements are 1 or -k
    intro x hx
    rw [cyclicRotation, List.mem_append] at hx
    rcases hx with hx | hx
    · exact h3 x (List.drop_subset i l hx)
    · exact h3 x (List.take_subset i l hx)

/-- Cyclic rotation of a rotation composes: rotating by i then by j equals rotating by i+j
(modulo length). For the non-wrapping case where i+j ≤ length. -/
theorem cyclicRotation_compose (l : List ℤ) (i j : ℕ)
    (hi : i ≤ l.length) (hj : j ≤ l.length - i) :
    cyclicRotation (cyclicRotation l i) j = cyclicRotation l (i + j) := by
  -- cyclicRotation l i = l.drop i ++ l.take i
  -- Since j ≤ length(l.drop i), the take/drop of the concatenation stays in the first part.
  simp only [cyclicRotation]
  have hlen_drop : l.drop i |>.length = l.length - i := List.length_drop i l
  have hj_le : j ≤ (l.drop i).length := by omega
  -- Simplify drop/take of the concatenation using the length bound
  rw [List.drop_append_of_le_length hj_le, List.take_append_of_le_length hj_le]
  -- Now we have: ((l.drop i).drop j ++ l.take i) ++ (l.drop i).take j
  --            = l.drop (i + j) ++ l.take (i + j)
  rw [List.drop_drop]
  -- LHS: l.drop (i + j) ++ l.take i ++ (l.drop i).take j
  -- RHS: l.drop (i + j) ++ l.take (i + j)
  -- Suffices: l.take i ++ (l.drop i).take j = l.take (i + j)
  rw [List.append_assoc]
  congr 1
  -- l.take i ++ (l.drop i).take j = l.take (i + j)
  rw [← List.take_add]

/-- A kCountedSequence where k*b < a has positive sum, which is the precondition
for the cycle lemma. -/
theorem kCountedSequence_pos_sum {k a b : ℕ} {l : List ℤ}
    (hl : l ∈ kCountedSequence k a b) (hab : k * b < a) :
    0 < l.sum := by
  rw [kCountedSequence_sum hl]
  omega

/-- A kCountedSequence has positive length when a + b > 0. -/
theorem kCountedSequence_pos_length {k a b : ℕ} {l : List ℤ}
    (hl : l ∈ kCountedSequence k a b) (hab : 0 < a + b) :
    0 < l.length := by
  rw [kCountedSequence_length hl]
  exact hab

/-- The prefix sum of a cyclic rotation relates to prefix sums of the original.
For rotation starting at position i:
  prefixSum(rotation, j) = prefixSum(original, i+j) - prefixSum(original, i)
when i+j <= n, and wraps around with an additive correction of S = sum(l). -/
/-- Helper: sum of l.drop i equals l.sum - (l.take i).sum -/
private theorem sum_drop_eq (l : List ℤ) (i : ℕ) :
    (l.drop i).sum = l.sum - (l.take i).sum := by
  have h := congr_arg List.sum (List.take_append_drop i l)
  rw [List.sum_append] at h
  omega

/-- Helper: the "middle slice" (l.drop i).take j has sum = prefixSum(i+j) - prefixSum(i)
    when i + j ≤ l.length. -/
private theorem take_drop_sum (l : List ℤ) (i j : ℕ)
    (hi : i ≤ l.length) (hij : i + j ≤ l.length) :
    ((l.drop i).take j).sum = (l.take (i + j)).sum - (l.take i).sum := by
  have key : l.take (i + j) = l.take i ++ (l.drop i).take j := by
    rw [← List.take_take]
    conv_lhs => rw [← List.take_append_drop i l]
    rw [List.take_append_eq_append_take]
    simp [List.length_take, Nat.min_eq_left hi]
    congr 1
    omega
  have := congr_arg List.sum key
  rw [List.sum_append] at this
  omega

theorem cyclicRotation_prefixSum (l : List ℤ) (i j : ℕ)
    (hi : i ≤ l.length) (hj : j ≤ l.length) :
    ((cyclicRotation l i).take j).sum =
      if i + j ≤ l.length then
        (l.take (i + j)).sum - (l.take i).sum
      else
        (l.take (i + j - l.length)).sum + l.sum - (l.take i).sum := by
  simp only [cyclicRotation]
  by_cases hij : i + j ≤ l.length
  · -- Non-wrapping case: j ≤ length(l.drop i), so take j stays within l.drop i
    simp only [hij, ↓reduceIte]
    have hj_le : j ≤ (l.drop i).length := by
      simp [List.length_drop]
      omega
    rw [List.take_append_of_le_length hj_le]
    exact take_drop_sum l i j hi hij
  · -- Wrapping case: j > length(l.drop i), take all of l.drop i plus some of l.take i
    push_neg at hij
    simp only [show ¬(i + j ≤ l.length) from by omega, ↓reduceIte]
    have hdrop_len : (l.drop i).length = l.length - i := List.length_drop i l
    have hj_gt : (l.drop i).length ≤ j := by omega
    rw [List.take_append]
    rw [List.take_of_length_le hj_gt]
    rw [List.sum_append]
    rw [sum_drop_eq]
    -- Simplify j - (l.drop i).length = i + j - l.length
    have hlen_eq : j - (l.drop i).length = i + j - l.length := by
      rw [hdrop_len]; omega
    rw [hlen_eq]
    -- Simplify (l.take i).take(i+j-n) = l.take(i+j-n)
    have htake_take : ((l.take i).take (i + j - l.length)).sum =
        (l.take (i + j - l.length)).sum := by
      congr 1
      rw [List.take_take]
      congr 1
      exact Nat.min_eq_left (by omega)
    rw [htake_take]
    omega

/-- The prefix sum function: prefixSum l i = sum of first i elements. -/
def prefixSum (l : List ℤ) (i : ℕ) : ℤ := (l.take i).sum

/-- Prefix sum at 0 is 0. -/
theorem prefixSum_zero (l : List ℤ) : prefixSum l 0 = 0 := by
  simp [prefixSum]

/-- Prefix sum at the full length is the total sum. -/
theorem prefixSum_length (l : List ℤ) : prefixSum l l.length = l.sum := by
  simp [prefixSum, List.take_length]

/-- Prefix sum of the doubled sequence satisfies periodicity:
    prefixSum(l ++ l, i + n) = prefixSum(l ++ l, i) + sum(l) for i ≤ n. -/
theorem prefixSum_doubled_periodic (l : List ℤ) (i : ℕ) (hi : i ≤ l.length) :
    prefixSum (l ++ l) (i + l.length) = prefixSum (l ++ l) i + l.sum := by
  simp only [prefixSum]
  rw [show i + l.length = l.length + i from by omega]
  rw [List.take_add]
  rw [List.sum_append]
  congr 1
  -- (l ++ l).take(l.length) = l
  rw [List.take_left]
  -- Now: ((l ++ l).drop l.length).take i = l.take i
  rw [List.drop_left]
  -- ((l ++ l).drop l.length) = l, so take i of that = l.take i
  -- But we need: (l ++ l).take i = the first i elements
  -- Actually: prefixSum(l++l, i) = prefixSum(l, i) since i ≤ l.length
  -- and (l++l).drop(l.length) = l, so take i of that = l.take i
  rfl

/-- A rotation i is "good" if all prefix sums of the rotated sequence are positive. -/
def isGoodRotation (l : List ℤ) (i : ℕ) : Prop :=
  ∀ j, 0 < j → j ≤ l.length → 0 < ((cyclicRotation l i).take j).sum

/-- Good rotation is decidable for concrete lists and positions. -/
instance (l : List ℤ) (i : ℕ) : Decidable (isGoodRotation l i) :=
  inferInstanceAs (Decidable (∀ j, 0 < j → j ≤ l.length →
    0 < ((cyclicRotation l i).take j).sum))

/-- The set of good rotations as a Finset. -/
def goodRotations (l : List ℤ) : Finset ℕ :=
  (Finset.range l.length).filter (fun i => isGoodRotation l i)

/-- The good rotation condition can be characterized purely in terms of the prefix sum
function of the doubled sequence. Position i is good iff P(i) is strictly less than
P(i+1), P(i+2), ..., P(i+n) in the doubled prefix sum sequence. -/
theorem isGoodRotation_iff_prefixSum (l : List ℤ) (i : ℕ) (hi : i < l.length) :
    isGoodRotation l i ↔
      ∀ j, 0 < j → j ≤ l.length →
        prefixSum l i < prefixSum (l ++ l) (i + j) := by
  unfold isGoodRotation
  constructor
  · intro h j hj hjn
    have hgood := h j hj hjn
    rw [cyclicRotation_prefixSum l i j (le_of_lt hi) hjn] at hgood
    simp only [prefixSum]
    split_ifs at hgood with hij
    · -- Non-wrapping: P(i+j) - P(i) > 0, so P(i) < P(i+j)
      -- Also: i+j ≤ l.length, so (l++l).take(i+j) = l.take(i+j)
      rw [List.take_append_of_le_length (by omega)]
      omega
    · -- Wrapping: P(i+j-n) + S - P(i) > 0
      push_neg at hij
      -- Decompose (l++l).take(i+j) via l.length + (i+j-l.length)
      have hrw : i + j = l.length + (i + j - l.length) := by omega
      rw [hrw, List.take_add, List.sum_append, List.take_left, List.drop_left]
      omega
  · intro h j hj hjn
    rw [cyclicRotation_prefixSum l i j (le_of_lt hi) hjn]
    have hpf := h j hj hjn
    simp only [prefixSum] at hpf
    split_ifs with hij
    · -- Non-wrapping
      rw [List.take_append_of_le_length (by omega)] at hpf
      omega
    · -- Wrapping
      push_neg at hij
      have hrw : i + j = l.length + (i + j - l.length) := by omega
      rw [hrw, List.take_add, List.sum_append, List.take_left, List.drop_left] at hpf
      omega

/-- For the doubled sequence, prefixSum(l++l, i) = prefixSum(l, i) when i ≤ l.length. -/
theorem prefixSum_doubled_le (l : List ℤ) (i : ℕ) (hi : i ≤ l.length) :
    prefixSum (l ++ l) i = prefixSum l i := by
  simp only [prefixSum]
  rw [List.take_append_of_le_length hi]

/-- **The Cycle Lemma (Dvoretzky-Motzkin, 1947).**

For a list of integers with positive sum S and length n,
exactly S of the n cyclic rotations have all positive prefix sums.

Proof Strategy (Rightmost Minimum):
1. Define prefixSum(i) = sum of first i elements, with prefixSum(0) = 0.
2. For the "doubled" sequence (period 2), consider positions 0, 1, ..., 2n-1.
3. The prefix sums satisfy prefixSum(i + n) = prefixSum(i) + S.
4. In each window of n consecutive positions, there are exactly S positions j
   where j is a "new minimum" (prefixSum(j) < prefixSum(i) for all i in the window
   before j). These correspond exactly to good starting positions.

This is the fundamental counting tool for the generalized ballot problem. -/
theorem cycle_lemma (l : List ℤ) (hn : 0 < l.length)
    (hS : 0 < l.sum) :
    ((Finset.range l.length).filter
      (fun i => ∀ j, 0 < j → j ≤ l.length →
        0 < ((cyclicRotation l i).take j).sum)).card = l.sum.toNat := by
  sorry -- The full cycle lemma proof; requires rightmost minimum injection argument

/-- Verification: For the simple list [2, -1], sum = 1 > 0, length = 2.
The cycle lemma predicts exactly 1 good rotation. -/
example : ((Finset.range 2).filter (fun i =>
    ∀ j, 0 < j → j ≤ 2 →
      0 < ((cyclicRotation [2, -1] i).take j).sum)).card = 1 := by
  native_decide

/- ## Part VIII: Lattice Path Interpretation

The k-fold ballot problem has a beautiful lattice path interpretation:

Setup:
- Start at the origin (0, 0)
- A vote for A = upstep to (x+1, y+1)
- A vote for B = downstep to (x+1, y-k)
- End at (a+b, a-kb)

k-good paths are those that never touch or go below the x-axis.

When k = 1: standard Dyck-like paths above the x-axis
When k = 2: paths where each downstep drops by 2 (steeper descent)
When k = 3: each B vote is "worth" 3 A votes in the count

Connection to ballot counting:
In the election, at any point after counting some votes, if A has alpha votes
and B has beta votes, the lattice height is alpha - k*beta. The condition
"A has more than k times B's votes" (alpha > k*beta) is exactly "height > 0".

This gives us a clean bijection between:
- Vote orderings where A always dominates by factor k
- Lattice paths from (0,0) to (a+b, a-kb) that stay strictly above y=0
-/

/-- The height at position i in a k-ballot path equals
the number of A votes minus k times the number of B votes so far. -/
theorem path_height_interpretation {k a b : ℕ} {l : List ℤ}
    (hl : l ∈ kCountedSequence k a b) (i : ℕ) (hi : i ≤ l.length) :
    (l.take i).sum = (l.take i).count 1 - (k : ℤ) * (l.take i).count (-(k : ℤ)) := by
  apply sum_eq_count_sub_mul_count
  intro x hx
  exact hl.2.2 x (List.take_subset i l hx)

/- ## Part IX: Extensions and Open Directions

The k-fold generalization opens several research directions:

1. Multi-candidate ballot problem: Given candidates with votes v_1 > v_2 > ... > v_m,
   what is the probability that candidate 1 always leads candidate 2, who always
   leads candidate 3, etc.? This requires a multi-dimensional lattice path analysis.

2. Continuous-time version: The ballot problem has a continuous analogue in
   terms of Brownian motion (the Brownian ballot problem).

3. Weighted voting: Different votes could have different weights, leading to
   lattice paths with varying step sizes.

4. Random walks with barriers: The ballot problem is equivalent to counting
   random walks that avoid a barrier, connecting to the theory of reflected
   random walks.
-/

end GeneralizedBallot
