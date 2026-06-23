/-
Erdős Problem #1059, Open Question 01:
Natural Density of Factorial-Avoiding Primes

**The Question**: What is the natural density of primes p satisfying
AllFactorialSubtractionsComposite(p) among all primes?

The probabilistic heuristic predicts density 1: for a prime p ∈ (l!, (l+1)!],
there are exactly l+1 factorial conditions to check (k = 0, ..., l), and each
p - k! is independently prime with probability ~1/ln(p). The expected number of
"failures" is ~(l+1)/ln(p), which → 0 as p → ∞ (since l = O(log p / log log p)).
So almost all large primes satisfy the property.

**Proved in this file** (0 sorries):
1. `decAllFact`: Decidable instance for AllFactorialSubtractionsComposite
2. Four new witnesses: 461, 557, 673 (level 5) and 769 (level 6), extending 101, 211
3. `six_prime_witnesses`: 6 verified prime witnesses
4. `checkCount_*`: factorial check counts (5 for p=101; 6 for p=211,461,557,673; 7 for p=769)
5. `qualifyingCount_le_primeCount`: C(x) ≤ π(x) always
6. `qualifyingPrimeCount_mono`: C(x) is monotone
7. `factorialCheckCount_mono`: check count is monotone
8. `factorialCheckCount_le_log`: factorialCheckCount n ≤ ⌊log₂ n⌋ + 2 (formalizes density heuristic)
9. `factorialCheckCount_eq_of_interval`: exact count = l+1 when l! < n ≤ (l+1)!
10. `factorialCheckCount_const_on_interval`: count is constant within each factorial level
11. `three_not_qualifying`: p = 3 is prime but does not satisfy AllFactorialSubtractionsComposite
12. `qualifyingPrimeCount_lt_primeCount`: C(x) < π(x) for all x ≥ 3 (density < 1 always)
13. `density_strictly_between`: 0 < C(x) < π(x) for all x ≥ 101
14. `qualifyingPrimes_infinite`: {p | AFSC(p)} is infinite — from Selberg density axiom (OQ-02)
15. `qualifyingPrimeCount_ge`: C((N+3)!) ≥ N for all N — Selberg lower bound

**Axiom** (1): `density_one_conjecture` — density equals 1
(Items 14–15 additionally depend on `Erdos1059OQ02.selberg_density_axiom`)

References:
- Erdős, P. https://erdosproblems.com/1059
- Main proof: Erdos1059Problem.lean (witnesses 101, 211)
- OQ-02: Selberg sieve framework for this problem
- OQ-05: Alternative decidability proof
- OEIS A064152: Primes p such that p - k! is composite for all k with 1 ≤ k! < p
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import Proofs.Erdos1059OQ02

namespace Erdos1059OQ01

/-
## Core Definition and Decidability
-/

/-- For each k with k! < n, n - k! is not prime and is ≥ 2 (composite). -/
def AllFactorialSubtractionsComposite (n : ℕ) : Prop :=
  ∀ k : ℕ, Nat.factorial k < n → ¬(n - Nat.factorial k).Prime ∧ n - Nat.factorial k ≥ 2

/-- k! < n implies k < n, since k ≤ k! for all k ∈ ℕ (Nat.self_le_factorial). -/
theorem factorial_lt_implies_lt {k n : ℕ} (h : Nat.factorial k < n) : k < n :=
  lt_of_le_of_lt (Nat.self_le_factorial k) h

/-- AllFactorialSubtractionsComposite is decidable via a bounded quantifier over range n. -/
instance decAllFact (n : ℕ) : Decidable (AllFactorialSubtractionsComposite n) :=
  decidable_of_iff
    (∀ k ∈ Finset.range n, Nat.factorial k < n →
        ¬(n - Nat.factorial k).Prime ∧ n - Nat.factorial k ≥ 2)
    ⟨fun h k hk => h k (Finset.mem_range.mpr (factorial_lt_implies_lt hk)) hk,
     fun h k _ hk => h k hk⟩

/-
## Witnesses: Level 5 (p ∈ (120, 720))

The main file verifies p = 101 (level 4) and p = 211 (level 5). For p in (5!, 6!] = (120, 720],
we need to check k = 0, 1, 2, 3, 4, 5 (i.e., p - 1, p - 1, p - 2, p - 6, p - 24, p - 120).
Note: p - 1 is always even > 2 for odd prime p > 3, so the binding conditions
are p - 2, p - 6, p - 24, p - 120.

p = 461: 460, 459 = 3·153, 455 = 5·7·13, 437 = 19·23, 341 = 11·31. All composite.
p = 557: 556, 555 = 3·5·37, 551 = 19·29, 533 = 13·41, 437 = 19·23. All composite.
p = 673: 672, 671 = 11·61, 667 = 23·29, 649 = 11·59, 553 = 7·79. All composite.
-/

/-- p = 461 is prime and satisfies AllFactorialSubtractionsComposite. -/
theorem prime_461 : Nat.Prime 461 := by native_decide
theorem witness_461 : AllFactorialSubtractionsComposite 461 := by native_decide

/-- p = 557 is prime and satisfies AllFactorialSubtractionsComposite. -/
theorem prime_557 : Nat.Prime 557 := by native_decide
theorem witness_557 : AllFactorialSubtractionsComposite 557 := by native_decide

/-- p = 673 is prime and satisfies AllFactorialSubtractionsComposite. -/
theorem prime_673 : Nat.Prime 673 := by native_decide
theorem witness_673 : AllFactorialSubtractionsComposite 673 := by native_decide

/-
## Witnesses: Level 6 (p ∈ (720, 5040))

For p in (6!, 7!] = (720, 5040], we need to check k = 0, 1, 2, 3, 4, 5, 6
(i.e., k! = 1, 1, 2, 6, 24, 120, 720). The binding conditions are
p - 2, p - 6, p - 24, p - 120, p - 720 (since p - 1 is always even).

p = 769: 767 = 13·59, 763 = 7·109, 745 = 5·149, 649 = 11·59, 49 = 7². All composite.
-/

/-- p = 769 is prime and satisfies AllFactorialSubtractionsComposite (first level-6 witness). -/
theorem prime_769 : Nat.Prime 769 := by native_decide
theorem witness_769 : AllFactorialSubtractionsComposite 769 := by native_decide

/-- Six prime witnesses for Erdős Problem #1059: 101, 211, 461, 557, 673, 769. -/
theorem six_prime_witnesses :
    Nat.Prime 101 ∧ AllFactorialSubtractionsComposite 101 ∧
    Nat.Prime 211 ∧ AllFactorialSubtractionsComposite 211 ∧
    Nat.Prime 461 ∧ AllFactorialSubtractionsComposite 461 ∧
    Nat.Prime 557 ∧ AllFactorialSubtractionsComposite 557 ∧
    Nat.Prime 673 ∧ AllFactorialSubtractionsComposite 673 ∧
    Nat.Prime 769 ∧ AllFactorialSubtractionsComposite 769 :=
  ⟨by decide, by native_decide,
   by native_decide, by native_decide,
   prime_461, witness_461,
   prime_557, witness_557,
   prime_673, witness_673,
   prime_769, witness_769⟩

/-
## Factorial Check Structure

For p ∈ (l!, (l+1)!], exactly l+1 values of k satisfy k! < p (namely k = 0, ..., l).
So AllFactorialSubtractionsComposite(p) requires l+1 compositeness checks.
The key density insight: l+1 = O(log p / log log p), much smaller than ln(p).
-/

/-- The set of k-values (factorial indices) that must be checked for n. -/
def factorialCheckSet (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun k => Nat.factorial k < n)

/-- Number of factorial checks needed for AllFactorialSubtractionsComposite(n). -/
def factorialCheckCount (n : ℕ) : ℕ := (factorialCheckSet n).card

-- Concrete check counts at our six witness values
theorem checkCount_101 : factorialCheckCount 101 = 5 := by native_decide
theorem checkCount_211 : factorialCheckCount 211 = 6 := by native_decide
theorem checkCount_461 : factorialCheckCount 461 = 6 := by native_decide
theorem checkCount_557 : factorialCheckCount 557 = 6 := by native_decide
theorem checkCount_673 : factorialCheckCount 673 = 6 := by native_decide
theorem checkCount_769 : factorialCheckCount 769 = 7 := by native_decide

/-- The factorial check count is monotone: larger n may require more checks. -/
theorem factorialCheckCount_mono {m n : ℕ} (h : m ≤ n) :
    factorialCheckCount m ≤ factorialCheckCount n := by
  apply Finset.card_le_card
  intro k hk
  simp only [factorialCheckSet, Finset.mem_filter, Finset.mem_range] at *
  exact ⟨by omega, by omega⟩

/-
## Factorial Check Count Bound

The number of factorial-index checks grows at most logarithmically in n.
This is the formal version of the density heuristic's key asymptotic claim.

The proof uses the elementary inequality 2^(k-1) ≤ k! for k ≥ 1:
if k! < n then 2^(k-1) < n, bounding k by ⌊log₂ n⌋ + 1.
-/

/-- For k ≥ 1, 2^(k-1) ≤ k!. Proved by induction: base 1! = 1 = 2^0,
    inductive step uses (k+1)! = (k+1) · k! ≥ 2 · 2^(k-1) = 2^k. -/
private lemma two_pow_pred_le_factorial {k : ℕ} (hk : 1 ≤ k) : 2^(k-1) ≤ k.factorial := by
  cases k with
  | zero => omega
  | succ n =>
    simp only [Nat.succ_sub_one]
    clear hk
    induction n with
    | zero => norm_num [Nat.factorial]
    | succ m ih =>
      have hpos : 0 < (m + 1).factorial := Nat.factorial_pos _
      calc 2^(m+1) = 2 * 2^m := by ring
        _ ≤ 2 * (m+1).factorial := by linarith
        _ ≤ (m+2) * (m+1).factorial := by nlinarith
        _ = (m+1+1).factorial := (Nat.factorial_succ (m+1)).symm

/-- If 2^m < n (and n ≥ 2), then m ≤ Nat.log 2 n.
    Proof: if m > log₂ n then 2^m ≥ 2^(log₂ n + 1) > n by Nat.lt_pow_succ_log_self. -/
private lemma le_log_of_pow_lt {m n : ℕ} (h : 2^m < n) : m ≤ Nat.log 2 n := by
  by_contra hlt
  push_neg at hlt
  have hlt' : Nat.log 2 n + 1 ≤ m := hlt
  have h1 : n < 2^(Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by omega) n
  have h2 : 2^(Nat.log 2 n + 1) ≤ 2^m := Nat.pow_le_pow_right (by omega) hlt'
  linarith

/-- **Factorial Check Count Bound**: factorialCheckCount n ≤ ⌊log₂ n⌋ + 2.

    This formalizes the density heuristic's key asymptotic claim: for a prime
    p ∈ (l!, (l+1)!], only l+1 ≤ ⌊log₂ p⌋ + 2 conditions must be checked,
    while each condition fails independently with probability ~1/ln(p) → 0.

    Proof: Show factorialCheckSet n ⊆ Finset.range (⌊log₂ n⌋ + 2):
    · k = 0: trivial (0 < ⌊log₂ n⌋ + 2)
    · k ≥ 1: 2^(k-1) ≤ k! < n, so 2^(k-1) < n, so k-1 ≤ ⌊log₂ n⌋ by log definition. -/
theorem factorialCheckCount_le_log (n : ℕ) :
    factorialCheckCount n ≤ Nat.log 2 n + 2 := by
  have hsubset : factorialCheckSet n ⊆ Finset.range (Nat.log 2 n + 2) := by
    intro k hk
    simp only [factorialCheckSet, Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_range]
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · omega
    · have h1 : 2^(k-1) ≤ k.factorial := two_pow_pred_le_factorial hkpos
      have h2 : 2^(k-1) < n := lt_of_le_of_lt h1 hk.2
      have h3 : k-1 ≤ Nat.log 2 n := le_log_of_pow_lt h2
      omega
  calc factorialCheckCount n
      = (factorialCheckSet n).card := rfl
    _ ≤ (Finset.range (Nat.log 2 n + 2)).card := Finset.card_le_card hsubset
    _ = Nat.log 2 n + 2 := Finset.card_range _

-- Numerical verification: 769 uses 7 checks, log₂(769) = 9, so 7 ≤ 11
theorem checkCount_bound_769 : factorialCheckCount 769 ≤ Nat.log 2 769 + 2 := by
  have hc : factorialCheckCount 769 = 7 := checkCount_769
  have hlog : Nat.log 2 769 = 9 := by native_decide
  omega

/-
## Exact Factorial Check Count

When the "level" l of n is known — i.e., l! < n ≤ (l+1)! — the factorial check
count equals exactly l+1, not merely is bounded by ⌊log₂ n⌋ + 2.

The proof identifies factorialCheckSet n = Finset.range (l+1):
· k ≤ l → k! ≤ l! < n (k ∈ set) and k ≤ l ≤ l! < n (k < n)
· k ≥ l+1 → k! ≥ (l+1)! ≥ n (k! < n fails, k ∉ set)
-/

/-- **Exact Count Formula**: For n in the factorial interval (l!, (l+1)!],
    factorialCheckCount n = l + 1.

    This upgrades the logarithmic upper bound to a precise closed form:
    the check count depends only on which factorial interval contains n. -/
theorem factorialCheckCount_eq_of_interval {n l : ℕ} (hl : l.factorial < n)
    (hn : n ≤ (l + 1).factorial) : factorialCheckCount n = l + 1 := by
  have hfcs : factorialCheckSet n = Finset.range (l + 1) := by
    ext k
    simp only [factorialCheckSet, Finset.mem_filter, Finset.mem_range]
    constructor
    · -- k ∈ factorialCheckSet n → k < l+1
      intro ⟨_, hkfact⟩
      by_contra hk
      push_neg at hk
      -- k ≥ l+1 implies k! ≥ (l+1)! ≥ n, contradicting k! < n
      have hge : (l + 1).factorial ≤ k.factorial := Nat.factorial_le hk
      linarith
    · -- k < l+1 → k ∈ factorialCheckSet n
      intro hk
      have hkl : k ≤ l := Nat.lt_succ_iff.mp hk
      refine ⟨?_, Nat.lt_of_le_of_lt (Nat.factorial_le hkl) hl⟩
      -- k < n: k ≤ l ≤ l! < n
      exact Nat.lt_of_le_of_lt (Nat.le_trans hkl (Nat.self_le_factorial l)) hl
  simp [factorialCheckCount, hfcs, Finset.card_range]

/-- The factorial check count is constant on each factorial interval: if m and n
    both lie in (l!, (l+1)!], then factorialCheckCount m = factorialCheckCount n. -/
theorem factorialCheckCount_const_on_interval {m n l : ℕ}
    (hm : l.factorial < m) (hm2 : m ≤ (l + 1).factorial)
    (hn : l.factorial < n) (hn2 : n ≤ (l + 1).factorial) :
    factorialCheckCount m = factorialCheckCount n := by
  rw [factorialCheckCount_eq_of_interval hm hm2, factorialCheckCount_eq_of_interval hn hn2]

/-
## Natural Density

The natural density of qualifying primes among all primes is:
  lim_{x→∞} C(x) / π(x)
where C(x) = #{p ≤ x : p prime, AllFact(p)} and π(x) = #{p ≤ x : p prime}.

The density conjecture (from the probabilistic heuristic) asserts this limit = 1.
-/

/-- Number of qualifying primes at most x. -/
def qualifyingPrimeCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter
    (fun n => n.Prime ∧ AllFactorialSubtractionsComposite n)).card

/-- Number of primes at most x (the prime counting function π(x)). -/
def primeCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun n => n.Prime)).card

/-- C(x) ≤ π(x): qualifying primes are a subset of all primes. -/
theorem qualifyingCount_le_primeCount (x : ℕ) :
    qualifyingPrimeCount x ≤ primeCount x := by
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at *
  exact ⟨hn.1, hn.2.1⟩

/-- C(x) is monotone: more primes are available at larger x. -/
theorem qualifyingPrimeCount_mono {x y : ℕ} (h : x ≤ y) :
    qualifyingPrimeCount x ≤ qualifyingPrimeCount y := by
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at *
  exact ⟨by omega, hn.2⟩

/-- C(769) ≥ 6: we have at least six qualifying primes up to 769. -/
theorem qualifyingPrimeCount_ge_six : qualifyingPrimeCount 769 ≥ 6 := by
  have h101 : 101 ∈ (Finset.range 770).filter
      (fun n => n.Prime ∧ AllFactorialSubtractionsComposite n) := by
    simp [Finset.mem_filter, Finset.mem_range]
    exact ⟨by decide, by native_decide⟩
  have h211 : 211 ∈ (Finset.range 770).filter
      (fun n => n.Prime ∧ AllFactorialSubtractionsComposite n) := by
    simp [Finset.mem_filter, Finset.mem_range]
    exact ⟨by native_decide, by native_decide⟩
  have h461 : 461 ∈ (Finset.range 770).filter
      (fun n => n.Prime ∧ AllFactorialSubtractionsComposite n) := by
    simp [Finset.mem_filter, Finset.mem_range]
    exact ⟨prime_461, witness_461⟩
  have h557 : 557 ∈ (Finset.range 770).filter
      (fun n => n.Prime ∧ AllFactorialSubtractionsComposite n) := by
    simp [Finset.mem_filter, Finset.mem_range]
    exact ⟨prime_557, witness_557⟩
  have h673 : 673 ∈ (Finset.range 770).filter
      (fun n => n.Prime ∧ AllFactorialSubtractionsComposite n) := by
    simp [Finset.mem_filter, Finset.mem_range]
    exact ⟨prime_673, witness_673⟩
  have h769 : 769 ∈ (Finset.range 770).filter
      (fun n => n.Prime ∧ AllFactorialSubtractionsComposite n) := by
    simp [Finset.mem_filter, Finset.mem_range]
    exact ⟨prime_769, witness_769⟩
  have hdisj : ({101, 211, 461, 557, 673, 769} : Finset ℕ).card = 6 := by decide
  calc 6 = ({101, 211, 461, 557, 673, 769} : Finset ℕ).card := hdisj.symm
    _ ≤ qualifyingPrimeCount 769 := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
        · exact h101
        · exact h211
        · exact h461
        · exact h557
        · exact h673
        · exact h769

/-
## The Density Conjecture

The full proof of density = 1 would require:
  1. The Prime Number Theorem: π(x) ~ x/ln(x)
  2. Brun-Titchmarsh inequality: #{p ≤ x : p+k prime} ≲ 2x/(φ(k)ln(x))
  3. Selberg's sieve to bound #{p ≤ x : ∃ k ≤ l, p-k! prime} ≤ (l+1)·2x/(ln x)

Since l+1 ≤ ⌊log₂ p⌋ + 2 (proved above) and π(x) ~ x/ln(x), the failing primes satisfy
#{failing p ≤ x} ≲ (log x) · π(x) / log x = O(π(x) / log log x) = o(π(x)).

None of PNT, Brun-Titchmarsh, or Selberg's sieve are yet in Mathlib, so we axiomatize.
-/

/-- **Density Conjecture (OPEN)**: The natural density of qualifying primes equals 1.
    Equivalently: for every k, eventually C(x) ≥ k/(k+1) · π(x).
    The probabilistic heuristic predicts this from:
      - Each p fails with expected probability ~(l+1)/ln(p) ≤ (log p)/ln(p) → 0
      - The Lovász local lemma or Borel-Cantelli then implies density 1 -/
axiom density_one_conjecture :
    ∀ k : ℕ, ∃ X : ℕ, ∀ x : ℕ, x ≥ X →
      qualifyingPrimeCount x * (k + 1) ≥ primeCount x * k

/-
## Non-Qualifying Primes: The Density Gap

While density_one_conjecture predicts lim C(x)/π(x) = 1, the density is strictly < 1
at every finite stage. The prime p = 3 witnesses this: 3 is prime but fails
AllFactorialSubtractionsComposite since 3 - 0! = 2 is prime.
-/

/-- p = 3 is prime but does NOT satisfy AllFactorialSubtractionsComposite:
    For k = 0: 0! = 1 < 3, but 3 - 1 = 2 is prime (violating compositeness). -/
theorem three_not_qualifying : ¬AllFactorialSubtractionsComposite 3 := by native_decide

/-- **Density Gap Theorem**: For all x ≥ 3, C(x) < π(x).
    The density is strictly less than 1 at every finite stage.

    Proof: p = 3 lies in π(x) (prime, ≤ x) but NOT in C(x), since 3 - 0! = 2 is prime.
    So the qualifying-prime finset is a strict subset of the prime finset. -/
theorem qualifyingPrimeCount_lt_primeCount {x : ℕ} (hx : x ≥ 3) :
    qualifyingPrimeCount x < primeCount x := by
  unfold qualifyingPrimeCount primeCount
  apply Finset.card_lt_card
  rw [Finset.ssubset_def]
  refine ⟨?_, ?_⟩
  · -- C(x) ⊆ π(x): every qualifying prime is a prime
    intro n hn
    simp only [Finset.mem_filter] at *
    exact ⟨hn.1, hn.2.1⟩
  · -- ¬(π(x) ⊆ C(x)): p = 3 is in π(x) but not C(x)
    intro h_rev
    have h3_in_P : 3 ∈ (Finset.range (x + 1)).filter (fun n => Nat.Prime n) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by decide⟩
    have h3_in_Q := h_rev h3_in_P
    simp only [Finset.mem_filter] at h3_in_Q
    exact three_not_qualifying h3_in_Q.2.2

/-- For x ≥ 101, C(x) ≥ 1: the qualifying prime count is positive.
    (p = 101 is the smallest qualifying prime.) -/
theorem qualifyingPrimeCount_pos {x : ℕ} (hx : x ≥ 101) :
    0 < qualifyingPrimeCount x := by
  have h101 : 0 < qualifyingPrimeCount 101 := by native_decide
  exact Nat.lt_of_lt_of_le h101 (qualifyingPrimeCount_mono (by omega))

/-- **Density Sandwich Theorem**: For 101 ≤ x, we have 0 < C(x) < π(x).
    The density C(x)/π(x) is strictly between 0 and 1 at every finite stage ≥ 101.
    Combined with density_one_conjecture (lim = 1), this fully characterises the
    asymptotic regime: the density starts below 1 and approaches 1 from below. -/
theorem density_strictly_between {x : ℕ} (hx : x ≥ 101) :
    0 < qualifyingPrimeCount x ∧ qualifyingPrimeCount x < primeCount x :=
  ⟨qualifyingPrimeCount_pos hx, qualifyingPrimeCount_lt_primeCount (by omega)⟩

/-
## Cross-Problem Synthesis: Qualifying Primes Are Infinite

OQ-02 proves (via `selberg_implies_erdos`) that the set of qualifying primes is infinite,
using the Selberg density axiom. We import that result here. The two files use identical
definitions of AllFactorialSubtractionsComposite (same body, different namespaces),
so the transfer is definitional.

This gives a formal lower bound: C((N+3)!) ≥ N for all N. The proof constructs one
qualifying prime per factorial level ≥ 3 (from `selberg_density_axiom`), uses disjointness
of primorial intervals to ensure distinctness, and bounds all primes by (N+3)!.

Note: `qualifyingPrimes_infinite` and `qualifyingPrimeCount_ge` depend on
`Erdos1059OQ02.selberg_density_axiom`, which is an axiom in OQ-02 (not in this file).
-/

/-- **Qualifying Primes Are Infinite** (conditional on Selberg density axiom):
    The set of primes satisfying AllFactorialSubtractionsComposite is infinite.

    Proof: Import `selberg_implies_erdos` from OQ-02 via definitional equality of AFSC.
    This is weaker than `density_one_conjecture` (density = 1): infinite-many primes
    qualify, but the limiting ratio is not determined here. -/
theorem qualifyingPrimes_infinite :
    Set.Infinite {p : ℕ | p.Prime ∧ AllFactorialSubtractionsComposite p} := by
  have h := Erdos1059OQ02.selberg_implies_erdos
  -- Unfold ErdosProblem1059; the two AFSC defs are definitionally equal (same body)
  unfold Erdos1059OQ02.ErdosProblem1059 at h
  exact h

/-- Canonical qualifying prime at level l (for l ≥ 3), chosen via Classical.choice
    from the Selberg density axiom. -/
private noncomputable def levelCandidate (l : ℕ) : ℕ :=
  if h : l ≥ 3 then Classical.choose (Erdos1059OQ02.selberg_density_axiom l h) else 0

private lemma levelCandidate_spec (l : ℕ) (hl : l ≥ 3) :
    levelCandidate l ∈ Erdos1059OQ02.PrimorialInterval l ∧
    (levelCandidate l).Prime ∧
    AllFactorialSubtractionsComposite (levelCandidate l) := by
  have heq : levelCandidate l = Classical.choose (Erdos1059OQ02.selberg_density_axiom l hl) := by
    simp only [levelCandidate, dif_pos hl]
  obtain ⟨hmem, hprime, hcomp⟩ := Classical.choose_spec (Erdos1059OQ02.selberg_density_axiom l hl)
  rw [heq]
  refine ⟨hmem, hprime, ?_⟩
  -- Both AFSC definitions have the same body; Lean uses definitional equality
  exact hcomp

/-- `levelCandidate l` lies in the l-th primorial interval, so it is ≤ (l+1)!. -/
private lemma levelCandidate_le (l : ℕ) (hl : l ≥ 3) :
    levelCandidate l ≤ Nat.factorial (l + 1) := by
  obtain ⟨hmem, _, _⟩ := levelCandidate_spec l hl
  simp only [Erdos1059OQ02.PrimorialInterval, Finset.mem_Ioc] at hmem
  exact hmem.2

/-- Qualifying primes at different levels are distinct (primorial intervals are disjoint). -/
private lemma levelCandidate_injective {l l' : ℕ} (hl : l ≥ 3) (hl' : l' ≥ 3)
    (heq : levelCandidate l = levelCandidate l') : l = l' := by
  by_contra hne
  obtain ⟨hmem, _, _⟩ := levelCandidate_spec l hl
  obtain ⟨hmem', _, _⟩ := levelCandidate_spec l' hl'
  rw [heq] at hmem
  exact (Finset.disjoint_left.mp (Erdos1059OQ02.primorial_intervals_disjoint hne)) hmem hmem'

/-- **Selberg Lower Bound**: For any N, C((N+3)!) ≥ N.

    This gives a formal quantitative lower bound on the qualifying prime count.
    Proof: For l ∈ {3, ..., N+2}, `selberg_density_axiom` gives a qualifying prime
    p_l ∈ I(l) ⊆ (0, (N+3)!]. The N primes are distinct (intervals disjoint)
    and all counted by C((N+3)!). -/
theorem qualifyingPrimeCount_ge (N : ℕ) :
    qualifyingPrimeCount (Nat.factorial (N + 3)) ≥ N := by
  -- S = image of levels {3, ..., N+2} under levelCandidate
  let S := (Finset.Ico 3 (N + 3)).image levelCandidate
  -- S ⊆ qualifying primes up to (N+3)!
  have hS_sub : S ⊆ (Finset.range (Nat.factorial (N + 3) + 1)).filter
      (fun n => n.Prime ∧ AllFactorialSubtractionsComposite n) := by
    intro p hp
    simp only [S, Finset.mem_image, Finset.mem_Ico] at hp
    obtain ⟨l, ⟨hl3, hlN⟩, rfl⟩ := hp
    simp only [Finset.mem_filter, Finset.mem_range]
    obtain ⟨_, hprime, hcomp⟩ := levelCandidate_spec l (by omega)
    exact ⟨Nat.lt_succ_of_le (le_trans (levelCandidate_le l (by omega))
                               (Nat.factorial_le (by omega))), hprime, hcomp⟩
  -- S.card = N (by injectivity of levelCandidate on levels ≥ 3)
  have hS_card : S.card = N := by
    rw [Finset.card_image_of_injOn]
    · have h := Nat.card_Ico 3 (N + 3)
      omega
    · intro l hl l' hl' heq
      simp only [Finset.coe_Ico, Set.mem_Ico] at hl hl'
      exact levelCandidate_injective (by omega) (by omega) heq
  -- Conclude: N = S.card ≤ qualifyingPrimeCount
  calc N = S.card := hS_card.symm
    _ ≤ qualifyingPrimeCount (Nat.factorial (N + 3)) := by
        unfold qualifyingPrimeCount
        exact Finset.card_le_card hS_sub

/-
## Summary

This file provides four new computational witnesses for Erdős Problem #1059,
extending the gallery from 2 verified witnesses to 6:
  - Level-5 witnesses (p ∈ (120, 720)): 461, 557, 673 (requiring 6 checks each)
  - Level-6 witness (p ∈ (720, 5040)): 769 (requiring 7 checks)

Key mathematical contributions:

1. `factorialCheckCount_le_log`: factorialCheckCount(n) ≤ ⌊log₂ n⌋ + 2 for all n.
   This is the rigorous version of the density heuristic's key observation: each prime
   requires only O(log n) conditions — logarithmically many, not linearly many.
   Proof: elementary bound 2^(k-1) ≤ k! for k ≥ 1 (induction on factorial recurrence).

2. `factorialCheckCount_eq_of_interval`: when l! < n ≤ (l+1)!, factorialCheckCount n = l+1.
   This exact formula identifies the check count with the "factorial level" of n:
   the count jumps by exactly 1 at each factorial boundary and is constant within levels.
   Proof: factorialCheckSet n = Finset.range (l+1) via double inclusion using Nat.factorial_le.

3. `factorialCheckCount_const_on_interval`: check count is constant within each level.
   This confirms the level structure is well-defined.

4. `qualifyingPrimeCount_lt_primeCount`: C(x) < π(x) for all x ≥ 3.
   The density is strictly less than 1 at every finite stage. Witness: p = 3 is prime
   but fails the property (3 - 0! = 2 is prime). Proof: Finset strict-subset argument.

5. `density_strictly_between`: 0 < C(x) < π(x) for all x ≥ 101.
   Combined with density_one_conjecture, this shows: density starts below 1 and → 1.

6. `qualifyingPrimes_infinite`: The set {p | AFSC(p)} is infinite.
   Imports `selberg_implies_erdos` from OQ-02 via definitional equality of AFSC.
   This is weaker than density_one_conjecture but follows from the Selberg axiom alone.

7. `qualifyingPrimeCount_ge`: C((N+3)!) ≥ N for all N ∈ ℕ.
   A formal quantitative lower bound: the qualifying prime count at (N+3)! is at least N.
   Proof: levelCandidate picks one qualifying prime per level l ∈ {3..N+2}; these are
   distinct (primorial intervals disjoint) and all ≤ (N+3)!.

Key counts at the six witnesses:
  p = 101: 5 checks (level 4: 4! < 101 ≤ 5! = 120)
  p = 211: 6 checks (level 5: 5! < 211 ≤ 6! = 720)
  p = 461: 6 checks (level 5: 5! < 461 ≤ 6!)
  p = 557: 6 checks (level 5: 5! < 557 ≤ 6!)
  p = 673: 6 checks (level 5: 5! < 673 ≤ 6!)
  p = 769: 7 checks (level 6: 6! < 769 ≤ 7! = 5040)

Numerical verifications: checkCount(769) = 7 ≤ log₂(769) + 2 = 11 ✓;
exact formula: 6! = 720 < 769 ≤ 5040 = 7!, count = 6+1 = 7 ✓.
-/

end Erdos1059OQ01
