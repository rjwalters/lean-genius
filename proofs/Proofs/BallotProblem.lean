import Archive.Wiedijk100Theorems.BallotProblem
import Mathlib.Tactic

/-!
# The Ballot Problem

## What This Proves
The Ballot Problem (Wiedijk's 100 Theorems #30) computes the probability that in an
election, candidate A is strictly ahead of candidate B throughout the entire counting
process.

**Mathematical Statement:**
In an election where candidate A receives p votes and candidate B receives q votes
(where p > q), the probability that A leads B throughout the counting is:

$$P = \frac{p - q}{p + q}$$

This elegant formula was first proven by Bertrand in 1887.

## Approach
- **Foundation (from Mathlib):** We use `Archive.Wiedijk100Theorems.BallotProblem` which
  provides the complete proof using conditional counting on finite sets. The proof models
  vote sequences as lists of +1 (vote for A) and -1 (vote for B), then counts sequences
  where all suffix sums are positive.
- **Original Contributions:** This file provides a pedagogical wrapper with:
  1. Clear explanation of the lattice path interpretation
  2. Connection to the reflection principle
  3. Historical context and applications
- **Proof Techniques Demonstrated:** Conditional probability on finite sets, induction
  on vote totals, counting arguments.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main results
- [x] Proves the ballot theorem formula
- [x] Pedagogical commentary
- [x] Complete (no sorries)

## Mathlib Dependencies
- `Ballot.countedSequence` : Set of vote sequences with p votes for A and q for B
- `Ballot.staysPositive` : Set of sequences where A leads throughout
- `Ballot.ballot_problem` : The main ballot theorem

## Historical Note
This theorem is named after Joseph Bertrand who posed it in 1887. It has a beautiful
proof using the "reflection principle" - we count unfavorable paths by reflecting them
across a boundary. The result appears throughout probability theory and combinatorics,
with connections to random walks, Catalan numbers, and financial mathematics.

## The Reflection Principle (Intuitive Explanation)

Consider the vote counting as a path in a lattice:
- Start at origin (0, 0)
- Each +1 vote moves right and up (to (x+1, y+1))
- Each -1 vote moves right and down (to (x+1, y-1))
- End at (p+q, p-q)

"A leads throughout" means the path never touches or crosses the x-axis after time 0.

To count paths that DO touch the axis:
1. Take any path from (0,0) to (p+q, p-q) that touches y=0
2. Find the first point where it touches y=0
3. Reflect all steps before that point (flip +1 ↔ -1)
4. This creates a bijection with paths from (0,0) to (p+q, q-p)

The number of bad paths = C(p+q, q) (paths ending at (p+q, q-p))
Total paths = C(p+q, p)
Good paths = C(p+q, p) - C(p+q, q)
Probability = Good/Total = (p-q)/(p+q)

## Why This Works

The key insight is that any path touching the x-axis can be uniquely paired with
a path to the "wrong" endpoint by the reflection. This bijection immediately gives
us the count of unfavorable outcomes.

## Wiedijk's 100 Theorems: #30
-/

namespace BallotProblem

open Ballot Set ProbabilityTheory MeasureTheory

-- The MeasurableSpace instance for List ℤ is defined locally in Mathlib's Ballot module.
-- We need to recreate it here to use condCount.
private def measurableSpace_list_int : MeasurableSpace (List ℤ) := ⊤
attribute [local instance] measurableSpace_list_int

private theorem measurableSingletonClass_list_int : MeasurableSingletonClass (List ℤ) :=
  { measurableSet_singleton := fun _ => trivial }
attribute [local instance] measurableSingletonClass_list_int

/-! ## Part I: The Setting

We model vote counting as a sequence of +1s and -1s:
- +1 represents a vote for candidate A
- -1 represents a vote for candidate B
- The sequence represents the order in which votes are counted
- Candidate A is "ahead" at any point if the partial sum is positive
-/

/-- A vote sequence is a list of +1s and -1s where:
- There are exactly p occurrences of +1 (votes for A)
- There are exactly q occurrences of -1 (votes for B)

This is formalized in Mathlib as `countedSequence p q`. -/
example (p q : ℕ) : Set (List ℤ) := countedSequence p q

/-- A sequence "stays positive" if every nonempty suffix has positive sum.
This means candidate A is strictly ahead after counting each vote. -/
example : Set (List ℤ) := staysPositive

/-! ## Part II: Key Properties

The countedSequence has well-defined cardinality given by binomial coefficients. -/

/-- The number of distinct vote sequences with p votes for A and q for B
equals the binomial coefficient C(p+q, p). -/
theorem count_vote_sequences (p q : ℕ) :
    Measure.count (countedSequence p q) = (p + q).choose p :=
  count_countedSequence p q

/-- Vote sequences are finite - there are only finitely many ways to arrange p votes
for A and q votes for B. -/
theorem vote_sequences_finite (p q : ℕ) : (countedSequence p q).Finite :=
  countedSequence_finite p q

/-- There is always at least one vote sequence (unless both p and q are 0). -/
theorem vote_sequences_nonempty (p q : ℕ) : (countedSequence p q).Nonempty :=
  countedSequence_nonempty p q

/-! ## Part III: The Ballot Theorem

The main result: the probability that A leads throughout equals (p-q)/(p+q). -/

/-- **The Ballot Problem (Wiedijk #30)**

If candidate A receives p votes and candidate B receives q votes, with p > q,
then the probability that A is ahead of B throughout the counting is (p-q)/(p+q).

This is proved by:
1. Modeling votes as sequences of +1 and -1
2. "Staying positive" means all suffix sums are positive
3. Using induction on p and q with the reflection principle -/
theorem ballot_theorem (p q : ℕ) (h : q < p) :
    condCount (countedSequence p q) staysPositive = (p - q) / (p + q) :=
  ballot_problem q p h

/-- The real-valued version of the ballot theorem. -/
theorem ballot_theorem_real (p q : ℕ) (h : q < p) :
    (condCount (countedSequence p q) staysPositive).toReal = (p - q) / (p + q) :=
  ballot_problem' q p h

/-! ## Part IV: Edge Cases and Special Values -/

/-- When q = 0 (A receives all votes), the probability is 1.
This makes sense: if B gets no votes, A is always ahead! -/
theorem ballot_unanimous (p : ℕ) :
    condCount (countedSequence (p + 1) 0) staysPositive = 1 :=
  ballot_edge p

/-- When p = q (a tie), the probability that A leads throughout is 0.
This is because at some point the running totals must be equal. -/
theorem ballot_tie (p : ℕ) :
    condCount (countedSequence (p + 1) (p + 1)) staysPositive = 0 :=
  ballot_same p

/-! ## Part V: Concrete Probability Values

Let's verify some specific cases by computing the formula (p-q)/(p+q). -/

/-- With 2 votes for A and 1 for B: P = (2-1)/(2+1) = 1/3.

There are C(3,2) = 3 possible sequences: [+1,+1,-1], [+1,-1,+1], [-1,+1,+1]
Only [+1,+1,-1] keeps A ahead throughout (sum after each step: 1, 2, 1)
So probability = 1/3 ✓ -/
example : (2 - 1 : ℚ) / (2 + 1) = 1 / 3 := by norm_num

/-- With 3 votes for A and 1 for B: P = (3-1)/(3+1) = 1/2. -/
example : (3 - 1 : ℚ) / (3 + 1) = 1 / 2 := by norm_num

/-- With 4 votes for A and 2 for B: P = (4-2)/(4+2) = 1/3. -/
example : (4 - 2 : ℚ) / (4 + 2) = 1 / 3 := by norm_num

/-- With 5 votes for A and 2 for B: P = (5-2)/(5+2) = 3/7. -/
example : (5 - 2 : ℚ) / (5 + 2) = 3 / 7 := by norm_num

/-- With 10 votes for A and 4 for B: P = (10-4)/(10+4) = 3/7. -/
example : (10 - 4 : ℚ) / (10 + 4) = 3 / 7 := by norm_num

/-! ## Part VI: Connection to Lattice Paths and Catalan Numbers

The ballot problem is closely related to Catalan numbers and lattice path counting.

**Catalan Connection:**
The number of ways to count ballots such that A is never behind (weakly ahead)
is given by the Catalan number when p = q = n:

  Cₙ = (1/(n+1)) × C(2n, n)

The ballot problem gives us the count of strictly ahead paths, which differs
slightly but uses similar counting techniques.

**Random Walk Interpretation:**
The vote counting is equivalent to a simple random walk on the integers:
- Start at 0
- Each step is +1 (probability p/(p+q)) or -1 (probability q/(p+q))
- We want the walk to always stay positive

This has applications in:
- Financial mathematics (stock prices staying above a barrier)
- Queueing theory (queue never emptying)
- Branching processes
-/

/-! ## Part VII: The Reflection Principle in Detail

The proof uses the elegant reflection principle. Here's how it works:

**Setup:**
- We have p votes for A and q votes for B, with p > q
- A path is "bad" if A ever ties with B during counting
- We want to count "good" paths where A always leads

**The Reflection Bijection:**
For any "bad" path (one that touches the x-axis):
1. Find the FIRST time the partial sum equals 0
2. Reflect all votes before that point: swap +1 ↔ -1
3. This creates a unique path from 0 to (q-p) instead of (p-q)

**Why It's a Bijection:**
- Every bad path maps to exactly one reflected path
- Every path ending at (q-p) comes from exactly one bad path
- The mapping is invertible: reflect the prefix back

**Counting:**
- Total paths: C(p+q, p)
- Bad paths = paths to (q-p) = C(p+q, q)
- Good paths = C(p+q, p) - C(p+q, q)

**Probability:**
P(good) = [C(p+q,p) - C(p+q,q)] / C(p+q,p)
        = 1 - C(p+q,q)/C(p+q,p)
        = 1 - [p!q!/((p-q+q)!(p+q-p)!)] / [p!q!/((p+q-p)!(p+q-q)!)]
        = 1 - q!/(p-q)! × (p-q)!/p!... [simplifies to]
        = (p-q)/(p+q)

This elegant simplification is the heart of the ballot problem!
-/

#check ballot_theorem
#check ballot_unanimous
#check ballot_tie

end BallotProblem
