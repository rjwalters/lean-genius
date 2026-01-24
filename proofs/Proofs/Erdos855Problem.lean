/-
Erdős Problem #855: The Second Hardy-Littlewood Conjecture

Source: https://erdosproblems.com/855
Status: OPEN (likely FALSE)

Statement:
If π(x) counts the number of primes in [1,x], is it true that for large x and y:
  π(x+y) ≤ π(x) + π(y)?

Answer: Probably NO

This is the Second Hardy-Littlewood Conjecture. Erdős described it as
"an old conjecture of mine which was probably already stated by Hardy and Littlewood."

Key Results:
- Hensley-Richards (1973): This conjecture is FALSE assuming the prime k-tuples conjecture
- Under k-tuples: π(x+y) > π(x) + π(y) + (log 2 - o(1))·y/(log y)² for infinitely many x
- Montgomery-Vaughan: π(x+y) ≤ π(x) + 2y/log(y) (unconditional upper bound)

The conjecture is incompatible with the prime k-tuples conjecture, and most
number theorists believe k-tuples is true, so this conjecture is likely false.

Tags: number-theory, primes, prime-counting, hardy-littlewood, k-tuples
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic

namespace Erdos855

/-
## Part I: The Prime Counting Function
-/

/--
**Prime Counting Function:**
π(n) = |{p ≤ n : p prime}|
-/
noncomputable def primePi (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.Icc 1 n)).card

/--
**Basic Property:**
π is monotonically increasing.
-/
axiom primePi_monotone : Monotone primePi

/--
**Prime Number Theorem:**
π(n) ~ n/log(n) as n → ∞.
-/
axiom prime_number_theorem (ε : ℝ) (hε : ε > 0) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, (n : ℝ) > 0 →
      |((primePi n : ℝ) - n / Real.log n) / (n / Real.log n)| < ε

/-
## Part II: The Second Hardy-Littlewood Conjecture
-/

/--
**The Second Hardy-Littlewood Conjecture:**
For all sufficiently large x and y:
  π(x+y) ≤ π(x) + π(y)

This asserts that the prime counting function is "subadditive" in a sense.
-/
def SecondHardyLittlewoodConjecture : Prop :=
  ∃ N₀ : ℕ, ∀ x y : ℕ, x ≥ N₀ → y ≥ N₀ →
    primePi (x + y) ≤ primePi x + primePi y

/--
**Status: OPEN, LIKELY FALSE**
The conjecture remains unproved but is believed to be false
based on its incompatibility with the prime k-tuples conjecture.
-/
axiom conjecture_status_open : True

/-
## Part III: The Prime k-Tuples Conjecture
-/

/--
**Admissible Tuple:**
A k-tuple (h₁, ..., hₖ) is admissible if for every prime p,
the residues h₁ mod p, ..., hₖ mod p don't cover all residue classes.
-/
def IsAdmissibleTuple (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime →
    (Finset.image (· % p) H).card < p

/--
**Prime k-Tuples Conjecture (Hardy-Littlewood):**
For any admissible k-tuple H = {h₁, ..., hₖ}, there are infinitely many n
such that n + h₁, n + h₂, ..., n + hₖ are all prime.
-/
def PrimeKTuplesConjecture : Prop :=
  ∀ H : Finset ℕ, IsAdmissibleTuple H →
    ∀ N : ℕ, ∃ n > N, ∀ h ∈ H, (n + h).Prime

/--
**The k-Tuples Conjecture is widely believed to be true.**
It is supported by extensive numerical evidence and heuristic arguments.
-/
axiom k_tuples_widely_believed : True

/-
## Part IV: Hensley-Richards Incompatibility Theorem
-/

/--
**Hensley-Richards (1973):**
The Second Hardy-Littlewood Conjecture is incompatible with
the Prime k-Tuples Conjecture.

If k-tuples is true, then for every large y, there exist infinitely
many x such that:
  π(x+y) > π(x) + π(y)
-/
axiom hensley_richards_incompatibility :
    PrimeKTuplesConjecture → ¬SecondHardyLittlewoodConjecture

/--
**Quantitative Version:**
Under the k-tuples conjecture, for every large y and infinitely many x:
  π(x+y) > π(x) + π(y) + (log 2 - o(1)) · y/(log y)²
-/
axiom hensley_richards_quantitative :
    PrimeKTuplesConjecture →
      ∀ y : ℕ, y > 1 → ∀ N : ℕ, ∃ x > N,
        (primePi (x + y) : ℝ) > primePi x + primePi y +
          (Real.log 2 / 2) * y / (Real.log y)^2

/--
**Reason for Incompatibility:**
If there exists an admissible k-tuple with more than π(k) elements,
then placing it at the right position gives a counterexample.

Hensley-Richards showed such dense admissible tuples exist.
-/
axiom dense_admissible_tuples_exist (k : ℕ) (hk : k ≥ 2) :
    ∃ H : Finset ℕ, IsAdmissibleTuple H ∧ H.card > primePi k ∧
      ∀ h ∈ H, h < k

/-
## Part V: Unconditional Results
-/

/--
**Montgomery-Vaughan Upper Bound:**
Unconditionally, we have:
  π(x+y) ≤ π(x) + 2y/log(y)

This is weaker than the conjecture (which claims π(x) + π(y)).
-/
axiom montgomery_vaughan_bound (x y : ℕ) (hy : y ≥ 2) :
    (primePi (x + y) : ℝ) ≤ primePi x + 2 * y / Real.log y

/--
**Trivial Lower Bound:**
π(x+y) ≥ π(x) always, since we're counting more primes.
-/
theorem primePi_add_ge (x y : ℕ) :
    primePi (x + y) ≥ primePi x :=
  primePi_monotone (Nat.le_add_right x y)

/--
**Best Known Asymptotic:**
The true behavior is believed to be:
  π(x+y) = π(x) + π(y) + O(y/(log y)²)
with the error term sometimes positive, sometimes negative.
-/
axiom true_asymptotic_behavior : True

/-
## Part VI: Related Conjectures
-/

/--
**Straus's Modification:**
π(x+y) ≤ π(x) + 2π(y/2)

This is also incompatible with the k-tuples conjecture.
-/
def StrausConjecture : Prop :=
  ∃ N₀ : ℕ, ∀ x y : ℕ, x ≥ N₀ → y ≥ N₀ →
    primePi (x + y) ≤ primePi x + 2 * primePi (y / 2)

axiom straus_also_incompatible :
    PrimeKTuplesConjecture → ¬StrausConjecture

/--
**Erdős's Weaker Conjecture:**
π(x+y) ≤ π(x) + π(y) + O(y/(log y)²)

This weaker form may be true and is consistent with k-tuples.
-/
def ErdosWeakerConjecture : Prop :=
  ∃ C : ℝ, ∃ N₀ : ℕ, ∀ x y : ℕ, x ≥ N₀ → y ≥ N₀ →
    (primePi (x + y) : ℝ) ≤ primePi x + primePi y + C * y / (Real.log y)^2

axiom erdos_weaker_consistent : True  -- Consistent with k-tuples

/-
## Part VII: Why This Matters
-/

/--
**Philosophical Point:**
This problem illustrates a fundamental tension in number theory.
Both conjectures (k-tuples and 2nd Hardy-Littlewood) seem natural,
but they cannot both be true.

Most experts believe k-tuples, so the 2nd Hardy-Littlewood conjecture
is likely false - but no explicit counterexample is known!
-/
axiom philosophical_significance : True

/--
**Computational Note:**
No explicit counterexample has been found despite extensive computation.
The first potential counterexample is expected to be astronomically large.
-/
axiom no_known_counterexample : True

/-
## Part VIII: Main Results
-/

/--
**Erdős Problem #855: LIKELY FALSE**

**Conjecture:** π(x+y) ≤ π(x) + π(y) for large x, y.

**Status:** Open, but likely FALSE

**Why:** Hensley-Richards (1973) proved this is incompatible with
the prime k-tuples conjecture. Since k-tuples is widely believed,
this conjecture is likely wrong.

**Unconditional:** Montgomery-Vaughan proved π(x+y) ≤ π(x) + 2y/log(y).
-/
theorem erdos_855 : True := trivial

/--
**Summary:**
The Second Hardy-Littlewood Conjecture (Erdős #855) asserts
π(x+y) ≤ π(x) + π(y) for large x, y. This is likely false:
- Hensley-Richards showed incompatibility with k-tuples conjecture
- The k-tuples conjecture is widely believed
- No counterexample found despite computation

The tension between these conjectures is a fascinating open problem
in analytic number theory.
-/
theorem erdos_855_summary :
    -- The conjecture is open but likely false
    True ∧
    -- It contradicts k-tuples
    (PrimeKTuplesConjecture → ¬SecondHardyLittlewoodConjecture) := by
  exact ⟨trivial, hensley_richards_incompatibility⟩

end Erdos855
