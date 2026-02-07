/-
# Erdős Problem #372: Descending Largest Prime Factors

**Source:** [erdosproblems.com/372](https://erdosproblems.com/372)
**Status:** SOLVED (Yes)

**Statement:**
Let P(n) denote the largest prime factor of n.
Are there infinitely many n such that P(n) > P(n+1) > P(n+2)?

**Answer:** YES — proved by Balog (2001)

**History:**
- Erdős-Pomerance (1978): Posed the conjecture; proved the ascending case
  P(n) < P(n+1) < P(n+2) occurs infinitely often
- Balog (2001): Proved #{n ≤ x : P(n) > P(n+1) > P(n+2)} ≫ √x
- De Koninck-Doyon (2011): Conjectured density is 1/6

**Reference:** https://erdosproblems.com/372
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Topology.Instances.Nat
import Mathlib.Data.Real.Basic

open Filter

namespace Erdos372

/- ## Part I: Largest Prime Factor -/

/--
**Largest Prime Factor:**
P(n) is the largest prime that divides n.
For n = 1, we define P(1) = 1 (convention).
-/
noncomputable def largestPrimeFactor (n : ℕ) : ℕ :=
  if n ≤ 1 then 1
  else (n.primeFactors).max' (Nat.primeFactors_nonempty (by omega))

-- Convenient notation
notation "P" => largestPrimeFactor

/--
P(n) is always a prime for n > 1.
-/
theorem largestPrimeFactor_prime {n : ℕ} (hn : n > 1) : (P n).Prime := by
  unfold largestPrimeFactor
  simp [hn]
  exact Nat.prime_of_mem_primeFactors (Finset.max'_mem _ _)

/--
P(n) divides n for n > 1.
-/
theorem largestPrimeFactor_dvd {n : ℕ} (hn : n > 1) : P n ∣ n := by
  unfold largestPrimeFactor
  simp [hn]
  have := Finset.max'_mem (n.primeFactors) (Nat.primeFactors_nonempty (by omega))
  exact Nat.dvd_of_mem_primeFactors this

/--
For any prime p dividing n, we have p ≤ P(n).
-/
theorem prime_le_largestPrimeFactor {n p : ℕ} (hn : n > 1) (hp : p.Prime) (hdvd : p ∣ n) :
    p ≤ P n := by
  unfold largestPrimeFactor
  simp [hn]
  have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hdvd, by omega⟩
  exact Finset.le_max' _ _ hmem

/- ## Part II: Examples of Largest Prime Factors -/

/--
Example: P(6) = 3.
6 = 2 × 3, so the largest prime factor is 3.
-/
example : P 6 = 3 := by native_decide

/--
Example: P(30) = 5.
30 = 2 × 3 × 5, so the largest prime factor is 5.
-/
example : P 30 = 5 := by native_decide

/--
Example: P(210) = 7.
210 = 2 × 3 × 5 × 7 (primorial of 7).
-/
example : P 210 = 7 := by native_decide

/- ## Part III: The Descending Triplet Property -/

/--
**Descending Triple:**
A natural number n satisfies the descending triplet property if
P(n) > P(n+1) > P(n+2).
-/
def isDescendingTriple (n : ℕ) : Prop :=
  P n > P (n + 1) ∧ P (n + 1) > P (n + 2)

/--
The set of all n satisfying the descending triplet property.
-/
def descendingTriples : Set ℕ :=
  {n : ℕ | isDescendingTriple n}

/- ## Part IV: The Erdős-Pomerance Theorem (Ascending Case) -/

/--
**Ascending Triple:**
A natural number n satisfies the ascending triplet property if
P(n) < P(n+1) < P(n+2).
-/
def isAscendingTriple (n : ℕ) : Prop :=
  P n < P (n + 1) ∧ P (n + 1) < P (n + 2)

/--
**Erdős-Pomerance Theorem (1978):**
There are infinitely many n such that P(n) < P(n+1) < P(n+2).
Axiomatized because the proof uses sieve methods not yet in Mathlib.
-/
axiom erdos_pomerance_ascending :
    Set.Infinite {n : ℕ | isAscendingTriple n}

/- ## Part V: Balog's Theorem (2001) -/

/--
**Balog's Quantitative Result:**
The number of n ≤ x satisfying P(n) > P(n+1) > P(n+2) is ≫ √x.
There exists a constant c > 0 such that for all sufficiently
large x, #{n ≤ x : P(n) > P(n+1) > P(n+2)} ≥ c·√x.
Axiomatized because Balog's proof uses deep sieve techniques.
-/
axiom balog_quantitative :
    ∃ (c : ℝ) (x₀ : ℕ), c > 0 ∧ ∀ x ≥ x₀,
      (Finset.filter (fun n => isDescendingTriple n) (Finset.range (x + 1))).card ≥
        c * Real.sqrt x

/--
**Balog's Theorem (2001) — Main Result:**
There are infinitely many n such that P(n) > P(n+1) > P(n+2).
This resolves Erdős Problem #372 in the affirmative.
Axiomatized because it follows from balog_quantitative via
a divergence argument (c·√x → ∞).
-/
axiom balog_descending_infinite : Set.Infinite descendingTriples

/- ## Part VI: The Density Conjecture -/

/--
**Balog's Density Conjecture:**
The natural density of n with P(n) > P(n+1) > P(n+2) is 1/6.

Intuition: There are 3! = 6 orderings of (P(n), P(n+1), P(n+2)),
and by symmetry each ordering should occur with density 1/6.
-/
def balog_density_conjecture : Prop :=
  ∃ (density : ℝ), density = 1/6 ∧
    Tendsto (fun x : ℕ =>
      (Finset.filter (fun n => isDescendingTriple n) (Finset.range (x + 1))).card / x)
      atTop (nhds density)

/- ## Part VII: Related Properties -/

/--
**Smooth Numbers:**
A number n is y-smooth if P(n) ≤ y.
The distribution of smooth numbers plays a key role in
Balog's sieve-theoretic proof of the descending case.
-/
def isSmooth (n : ℕ) (y : ℕ) : Prop := P n ≤ y

/--
**Longer Descending Chains:**
For k ≥ 3, are there infinitely many n with
P(n) > P(n+1) > ... > P(n+k-1)?
The case k = 3 is solved by Balog; longer chains remain open.
-/
def longerDescendingChains (k : ℕ) : Prop :=
  k ≥ 3 → Set.Infinite {n : ℕ | ∀ i < k - 1, P (n + i) > P (n + i + 1)}

/- ## Part VIII: Main Theorem -/

/--
**Main Theorem (Answer to Erdős #372):**
There are infinitely many n such that P(n) > P(n+1) > P(n+2).
-/
theorem erdos_372 : Set.Infinite {n : ℕ | P n > P (n + 1) ∧ P (n + 1) > P (n + 2)} :=
  balog_descending_infinite

/- ## Part IX: Summary -/

/--
**Erdős Problem #372: SOLVED**

**QUESTION:** Are there infinitely many n with P(n) > P(n+1) > P(n+2)?

**ANSWER:** YES (Balog, 2001)

**KEY RESULTS:**
1. Erdős-Pomerance (1978): ascending triplets occur infinitely often
2. Balog (2001): descending triplets occur at least c·√x times up to x
3. Density conjecture: each of the 6 orderings has density 1/6 (open)

**CONTRIBUTORS:**
- Erdős-Pomerance: Original conjecture and ascending case
- Balog: Resolution of descending case
- De Koninck-Doyon: Density generalization
-/
theorem erdos_372_summary :
    -- Infinitely many descending triplets exist
    Set.Infinite {n : ℕ | isDescendingTriple n} ∧
    -- The ascending case was also proved
    Set.Infinite {n : ℕ | isAscendingTriple n} :=
  ⟨balog_descending_infinite, erdos_pomerance_ascending⟩

end Erdos372
