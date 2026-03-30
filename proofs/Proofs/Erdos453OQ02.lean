/-
  Erdős 453 OQ-02: Axiom Elimination for Prime Product Bound

  Open Question: erdos-453-oq-02
  Parent: Erdos453Problem.lean

  Statement:
  Can the axioms in Erdős Problem #453 be proved from Mathlib?
  The parent file axiomatizes nthPrime_is_prime, nthPrime_strictMono,
  and leaves nthPrime_values as sorry.

  This file proves all three from Mathlib's Nat.nth API:
  - nthPrime_is_prime: via Nat.nth_mem_of_infinite
  - nthPrime_strictMono: via Nat.nth_strictMono
  - nthPrime_values: via Nat.nth_prime_{zero,one,two}_eq_{two,three,five}
    and Nat.nth_count + decide for the 4th prime

  The remaining 2 axioms (logPrime_ratio_tendsto_zero, pomerance_convex_hull_lemma)
  require PNT and convex hull theory; they remain axiomatized.

  Result: Axiom count reduced from 4 to 2, sorry count from 1 to 0.

  References:
  - Pomerance (1979): "The prime number graph", Math. Comp.
  - Mathlib: Nat.nth, Nat.nth_mem_of_infinite, Nat.nth_strictMono
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Basic

open Nat Real

namespace Erdos453OQ02

/-
## Part I: The Prime Sequence (Axiom-Free)

Same definitions as the parent file, but with proved theorems
replacing axioms.
-/

/--
**The n-th Prime (1-indexed):**
p_n denotes the n-th prime number (1-indexed: p_1 = 2, p_2 = 3, ...).
-/
noncomputable def nthPrime (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.nth Nat.Prime (n - 1)

/--
**Previously axiomatized; now proved.**
All nthPrime values for n ≥ 1 are prime.

Proof: nthPrime n = Nat.nth Nat.Prime (n-1), and Nat.nth_mem_of_infinite
gives that elements of Nat.nth over an infinite set satisfy the predicate.
-/
theorem nthPrime_is_prime (n : ℕ) (hn : n ≥ 1) : (nthPrime n).Prime := by
  unfold nthPrime
  simp [Nat.not_eq_zero_of_lt (by omega : 0 < n)]
  exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (n - 1)

/--
**Previously axiomatized; now proved.**
The prime sequence (shifted) is strictly monotone.

Proof: fun n => nthPrime (n + 1) = fun n => Nat.nth Nat.Prime n,
and Nat.nth_strictMono gives strict monotonicity for infinite sets.
-/
theorem nthPrime_strictMono : StrictMono (fun n => nthPrime (n + 1)) := by
  intro a b hab
  unfold nthPrime
  simp
  exact Nat.nth_strictMono Nat.infinite_setOf_prime hab

/--
Helper: Nat.nth Nat.Prime 3 = 7.
Proved via Nat.count + decide, following the pattern in Erdos1137Problem.lean.
-/
private theorem nth_prime_three_eq_seven : Nat.nth Nat.Prime 3 = 7 := by
  have h_count : Nat.count Nat.Prime 7 = 3 := by decide
  have h_prime : Nat.Prime 7 := by decide
  rw [← h_count]
  exact Nat.nth_count h_prime

/--
**Previously sorry; now proved.**
The first four primes: p_1 = 2, p_2 = 3, p_3 = 5, p_4 = 7.

Proof uses Mathlib's nth_prime lemmas for indices 0-2 and
the Nat.count/Nat.nth_count technique for index 3.
-/
theorem nthPrime_values :
    nthPrime 1 = 2 ∧ nthPrime 2 = 3 ∧ nthPrime 3 = 5 ∧ nthPrime 4 = 7 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- nthPrime 1 = Nat.nth Nat.Prime 0 = 2
    unfold nthPrime; simp; exact Nat.nth_prime_zero_eq_two
  · -- nthPrime 2 = Nat.nth Nat.Prime 1 = 3
    unfold nthPrime; simp; exact Nat.nth_prime_one_eq_three
  · -- nthPrime 3 = Nat.nth Nat.Prime 2 = 5
    unfold nthPrime; simp; exact Nat.nth_prime_two_eq_five
  · -- nthPrime 4 = Nat.nth Nat.Prime 3 = 7
    unfold nthPrime; simp; exact nth_prime_three_eq_seven

/-
## Part II: Remaining Axioms (Deep Results)

These two axioms require substantial mathematical machinery
and remain axiomatized.
-/

/--
**Log-Prime Function:**
a_n = log p_n for the n-th prime.
-/
noncomputable def logPrime (n : ℕ) : ℝ :=
  log (nthPrime n)

/--
**Axiom (PNT consequence):**
log p_n / n → 0 as n → ∞.
Proving this requires the Prime Number Theorem, which is available
in Mathlib but connecting it to our 1-indexed nthPrime requires
additional infrastructure.
-/
axiom logPrime_ratio_tendsto_zero :
    Filter.Tendsto (fun n => logPrime n / n) Filter.atTop (nhds 0)

/--
**Convex Hull Vertex:**
A point (n, a_n) is on the upper boundary of the convex hull if
2·a_n > a_{n-i} + a_{n+i} for all 0 < i < n.
-/
def IsConvexHullVertex (a : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ i : ℕ, 0 < i → i < n → 2 * a n > a (n - i) + a (n + i)

/--
**Axiom (Pomerance's Key Lemma):**
For any sequence with a_n = o(n), there are infinitely many convex hull vertices.
This is the deep geometric result from Pomerance (1979). A full proof
would require formalizing convex hull theory for discrete sequences.
-/
axiom pomerance_convex_hull_lemma (a : ℕ → ℝ)
    (h : Filter.Tendsto (fun n => a n / n) Filter.atTop (nhds 0)) :
    ∀ N : ℕ, ∃ n ≥ N, IsConvexHullVertex a n

/-
## Part III: Re-deriving Main Results with Proved Axioms

The key chain of reasoning from the parent file, now with 2 fewer axioms.
-/

/--
**From Convexity to Inequality:**
If (n, log p_n) is a convex hull vertex, then p_n² > p_{n-i}·p_{n+i} for all i.
-/
theorem convexity_implies_product_bound (n : ℕ) (hn : n ≥ 2)
    (hv : IsConvexHullVertex logPrime n) :
    ∀ i : ℕ, 0 < i → i < n →
      (nthPrime n : ℤ) ^ 2 > (nthPrime (n + i) : ℤ) * (nthPrime (n - i) : ℤ) := by
  intro i hi_pos hi_lt
  have hvi := hv i hi_pos hi_lt
  unfold logPrime at hvi
  -- Primes are positive
  have hp_n : (0 : ℝ) < nthPrime n :=
    Nat.cast_pos.mpr (Nat.Prime.pos (nthPrime_is_prime n (by omega)))
  have hp_ni : (0 : ℝ) < nthPrime (n - i) :=
    Nat.cast_pos.mpr (Nat.Prime.pos (nthPrime_is_prime (n - i) (by omega)))
  have hp_pi : (0 : ℝ) < nthPrime (n + i) :=
    Nat.cast_pos.mpr (Nat.Prime.pos (nthPrime_is_prime (n + i) (by omega)))
  -- Convert log inequality to product inequality
  have h_log : Real.log ((nthPrime (n - i) : ℝ) * nthPrime (n + i)) <
      Real.log ((nthPrime n : ℝ) ^ 2) := by
    calc Real.log ((nthPrime (n - i) : ℝ) * nthPrime (n + i))
        = Real.log (nthPrime (n - i)) + Real.log (nthPrime (n + i)) :=
          Real.log_mul (ne_of_gt hp_ni) (ne_of_gt hp_pi)
      _ < 2 * Real.log (nthPrime n) := by linarith
      _ = Real.log ((nthPrime n : ℝ) ^ 2) := by rw [Real.log_pow]; ring
  have h_real : (nthPrime (n - i) : ℝ) * nthPrime (n + i) < (nthPrime n : ℝ) ^ 2 :=
    (Real.log_lt_log_iff (mul_pos hp_ni hp_pi) (pow_pos hp_n 2)).mp h_log
  exact_mod_cast show nthPrime n ^ 2 > nthPrime (n + i) * nthPrime (n - i) by
    calc nthPrime n ^ 2
        > nthPrime (n - i) * nthPrime (n + i) := by exact_mod_cast h_real
      _ = nthPrime (n + i) * nthPrime (n - i) := Nat.mul_comm _ _

/--
**Pomerance (1979):**
There are infinitely many n such that p_n² > p_{n+i}·p_{n-i} for all 0 < i < n.
-/
theorem pomerance_1979 :
    ∀ N : ℕ, ∃ n ≥ N,
      ∀ i : ℕ, 0 < i → i < n →
        (nthPrime n : ℤ) ^ 2 > (nthPrime (n + i) : ℤ) * (nthPrime (n - i) : ℤ) := by
  intro N
  obtain ⟨n, hn, hv⟩ := pomerance_convex_hull_lemma logPrime logPrime_ratio_tendsto_zero (max N 2)
  refine ⟨n, by omega, ?_⟩
  exact convexity_implies_product_bound n (by omega) hv

/-
## Part IV: Summary of Axiom Elimination
-/

/--
**Axiom Elimination Summary:**

Parent file (Erdos453Problem.lean): 4 axioms, 1 sorry
This file (Erdos453OQ02.lean):      2 axioms, 0 sorries

Eliminated:
- nthPrime_is_prime: proved via Nat.nth_mem_of_infinite
- nthPrime_strictMono: proved via Nat.nth_strictMono
- nthPrime_values: proved via Nat.nth_prime_*_eq_* + Nat.nth_count

Remaining (require deep mathematical infrastructure):
- logPrime_ratio_tendsto_zero: needs PNT connection
- pomerance_convex_hull_lemma: needs convex hull theory for discrete sequences
-/
theorem axiom_elimination_summary :
    -- The main result still holds with fewer axioms
    ∀ N : ℕ, ∃ n ≥ N,
      ∀ i : ℕ, 0 < i → i < n →
        (nthPrime n : ℤ) ^ 2 > (nthPrime (n + i) : ℤ) * (nthPrime (n - i) : ℤ) :=
  pomerance_1979

end Erdos453OQ02
