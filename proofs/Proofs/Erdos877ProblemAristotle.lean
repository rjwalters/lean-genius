/-
  Aristotle targets for Erdos877Problem (Erdős #877: Maximal Sum-Free Subsets)
  Routine supporting lemmas for automated proof search.
  See Erdos877Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open problem (f_m(n) asymptotics)
  - NOT results depending on deep axioms (Łuczak-Schoen, Cameron-Erdős)
  - Structural/constructive results provable by elementary finite combinatorics
  - No definition sorries, no axioms

  Targets:
  1. maximal_criterion': Logical consequence of isMaximalSumFree definition.
     Every x ∉ A in a maximal sum-free set must be "covered" by A:
     either x = a+b, or a = x+b, or x+x = a for some a,b ∈ A.
     Proof strategy:
     - From isMaximalSumFree: ¬isSumFree (insert x A)
     - Unpack: ∃ p q r ∈ insert x A with p = q + r
     - Since A is sum-free, x must appear among p,q,r
     - Case p = x: x = q + r with q,r ∈ A → first disjunct
     - Case q = x: p = x + r with p,r ∈ A → second disjunct
     - Case r = x: p = q + x → a = x + b for a=p,b=q; or x+x=a if q=x too

  2. odds_construction': Existence of a sum-free set of size ≥ n/2 in {0,...,n}.
     Witness: (Finset.range (n+1)).filter (fun x => x % 2 = 1)  [odd numbers]
     Sum-free proof: if a%2=1 and b%2=1, then (a+b)%2=0, so a+b not in filter.
     Size proof: count of odd numbers in {0,...,n} equals (n+1)/2 ≥ n/2 (Nat div).
     Tactic hint: induction on n; the filter size for Finset.range (n+2) is
     1 + (filter size for range (n+1)) when n is even, or same when n is odd.

  Excluded (deep results, not Aristotle targets):
  - maximal_vs_all: requires Cameron-Erdős + Łuczak-Schoen axioms
  - erdos_877: main theorem, assembles the axioms
  - f_m_le_f: already sorry-free in the main file
-/
import Mathlib
import Proofs.Erdos877Problem

namespace Erdos877.Aristotle

open Erdos877 Finset Nat

-- ============================================================
-- Aristotle Target 1: Maximal criterion
-- ============================================================

/-- **Maximal criterion** (Aristotle target):
    For a maximal sum-free A ⊆ {0,...,n} and x ∈ {0,...,n} with x ∉ A,
    x is covered by A in one of three ways:
    - x = a + b (x is a sum of A-elements)
    - a = x + b (x is a summand for an A-element)
    - x + x = a (x is the double source of an A-element)

    Proof sketch:
    1. hmax.2.2 gives ¬isSumFree (insert x A)
    2. push_neg yields ∃ p q r ∈ insert x A, p = q + r
    3. Since A is sum-free (hmax.2.1), not all of p,q,r are in A; so x ∈ {p,q,r}
    4. Cases on which of p,q,r equals x:
       · p = x: then x = q + r; if q,r ∈ A: first disjunct. Otherwise recurse.
       · q = x: then p = x + r; if p,r ∈ A: second disjunct.
       · r = x: then p = q + x; if p,q ∈ A: second disjunct (a=p,b=q from heq).
         If q = x also: x + x = p → third disjunct. -/
theorem maximal_criterion' (n : ℕ) (A : Finset ℕ)
    (hmax : isMaximalSumFree n A) (x : ℕ) (hx : x ∈ Finset.range (n + 1))
    (hxA : x ∉ A) :
    (∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ x = a + b) ∨
    (∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ a = x + b) ∨
    (∃ a : ℕ, a ∈ A ∧ x + x = a) := by
  sorry

-- ============================================================
-- Aristotle Target 2: Odds construction
-- ============================================================

/-- **Odds construction** (Aristotle target):
    For any n, the odd numbers in {0,...,n} form a sum-free set with ≥ n/2 elements.
    Witness: (Finset.range (n+1)).filter (· % 2 = 1)

    Sum-free proof:
    Suppose a, b, c are in the odd-filter (a%2=1, b%2=1, c%2=1) and a = b + c.
    Then a % 2 = (b + c) % 2 = (1 + 1) % 2 = 0. But a % 2 = 1. Contradiction. omega.

    Size ≥ n/2 proof:
    The count of odd numbers in {0,...,n} equals (n+1)/2 (Nat division).
    Since (n+1)/2 ≥ n/2 for all n : ℕ (one is at least as large as the other), done.
    Alternatively: (n+1)/2 ≥ n/2 follows from omega after establishing the count. -/
theorem odds_construction' (n : ℕ) :
    ∃ A : Finset ℕ,
      A ⊆ Finset.range (n + 1) ∧
      isSumFree A ∧
      A.card ≥ n / 2 := by
  refine ⟨(Finset.range (n + 1)).filter (· % 2 = 1), Finset.filter_subset _ _, ?_, ?_⟩
  · -- sum-free: odd + odd = even, never odd
    intro a b c ha hb hc habc
    simp only [Finset.mem_filter] at ha hb hc
    omega
  · -- card: count of odds in {0,...,n} equals (n+1)/2 ≥ n/2
    have key : ∀ m, ((Finset.range m).filter (· % 2 = 1)).card = m / 2 := by
      intro m
      induction m with
      | zero => simp
      | succ k ih =>
        rw [Finset.range_succ, Finset.filter_insert]
        split_ifs with hmod
        · rw [Finset.card_insert_of_not_mem (by simp [Finset.mem_filter, Finset.mem_range])]
          omega
        · omega
    have := key (n + 1)
    omega

end Erdos877.Aristotle
