/-
Erdős Problem #240: Gaps Between P-Smooth Numbers

Source: https://erdosproblems.com/240
Status: SOLVED (Tijdeman 1973)

Statement:
Is there an infinite set of primes P such that if {a₁ < a₂ < ···} is the
set of integers divisible only by primes in P, then lim(aᵢ₊₁ - aᵢ) = ∞?

Background:
- P-smooth numbers: integers whose prime factors all lie in P
- For finite P: gaps → ∞ (follows from Pólya's theorem)
- Question: Can this happen for INFINITE P?

Answer: YES (Tijdeman 1973)

Key Results:
- Pólya (1918): For quadratic f(n) without repeated roots, largest prime factor → ∞
- This implies for finite P: gaps are unbounded
- Tijdeman (1973): For finite P, gaps ≫ aᵢ/(log aᵢ)^C
- Tijdeman (1973): For any ε > 0, exists infinite P with gaps ≫ aᵢ^{1-ε}

Origin: Asked to Erdős by Wintner

References:
- Pólya (1918): "Zur arithmetischen Untersuchung der Polynome"
- Tijdeman (1973): "On integers with many small prime factors"
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Set

namespace Erdos240

/-
## Part I: P-Smooth Numbers
-/

/--
**P-Smooth Number:**
A positive integer n is P-smooth if all its prime factors are in P.
Equivalently, n is divisible only by primes in P.
-/
def isPSmooth (P : Set ℕ) (n : ℕ) : Prop :=
  n > 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ∈ P

/--
**The set of P-smooth numbers:**
-/
def smoothNumbers (P : Set ℕ) : Set ℕ :=
  {n : ℕ | isPSmooth P n}

/--
**1 is P-smooth for any P:**
-/
theorem one_isPSmooth (P : Set ℕ) : isPSmooth P 1 := by
  constructor
  · exact Nat.one_pos
  · intro p _ hdiv
    exact absurd (Nat.eq_one_of_dvd_one hdiv) (Nat.Prime.ne_one ‹p.Prime›)

/-
## Part II: Enumeration and Gaps
-/

/--
**Ordered enumeration:**
Let (aᵢ) be the P-smooth numbers in increasing order.
We axiomatize this enumeration.
-/
axiom smoothEnum (P : Set ℕ) : ℕ → ℕ

/--
**Enumeration is strictly increasing:**
By definition, an enumeration of the P-smooth numbers in increasing order
is strictly monotone. In particular the values are unbounded
(`StrictMono` on `ℕ → ℕ` gives `i ≤ smoothEnum P i`), which is the
property the limit argument below relies on.
-/
axiom smoothEnum_strictMono (P : Set ℕ) : StrictMono (smoothEnum P)

/-
**Enumeration properties:**
-/

/--
**Gap function:**
The gap between consecutive P-smooth numbers.
-/
noncomputable def gap (P : Set ℕ) (i : ℕ) : ℕ :=
  smoothEnum P (i + 1) - smoothEnum P i

/-
## Part III: The Main Question
-/

/--
**Gaps tend to infinity:**
The sequence of gaps is unbounded.
-/
def gapsTendToInfinity (P : Set ℕ) : Prop :=
  ∀ M : ℕ, ∃ i : ℕ, gap P i > M

/--
**The Erdős-Wintner Question:**
Is there an infinite set of primes P such that gaps → ∞?
-/
def erdos240Question : Prop :=
  ∃ P : Set ℕ, (∀ p ∈ P, Nat.Prime p) ∧ P.Infinite ∧ gapsTendToInfinity P

/-
## Part IV: Pólya's Theorem (1918)
-/

/-
**Pólya's Theorem:**
If f(n) is a quadratic integer polynomial without repeated roots,
then the largest prime factor of f(n) → ∞ as n → ∞.
-/

/-
**Corollary: f(n) = n(n+k) has large prime factors:**
-/

/-
## Part V: Finite P Case
-/

/--
**Finite P implies unbounded gaps:**
If P is a finite set of primes, then gaps → ∞.

Proof idea: If gaps were bounded by some k, then aᵢ₊₁ = aᵢ + k
infinitely often. This means n and n + k are both P-smooth
infinitely often. But n(n+k) has arbitrarily large prime factors
by Pólya's theorem, contradiction.
-/
axiom finite_P_unbounded_gaps (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
  gapsTendToInfinity (↑P : Set ℕ)

/-
**Tijdeman's quantitative bound for finite P (1973):**
For finite P, the gaps satisfy:
aᵢ₊₁ - aᵢ ≫ aᵢ / (log aᵢ)^C
for some constant C depending on P.
-/

/-
## Part VI: Tijdeman's Main Theorem (1973)
-/

/--
**Tijdeman's Theorem:**
For any ε > 0, there exists an infinite set of primes P such that
the gaps between consecutive P-smooth numbers satisfy:
aᵢ₊₁ - aᵢ ≫ aᵢ^{1-ε}

This answers Erdős-Wintner's question affirmatively.
-/
axiom tijdeman_main_theorem :
  ∀ ε : ℝ, ε > 0 → ∃ P : Set ℕ,
    (∀ p ∈ P, Nat.Prime p) ∧
    P.Infinite ∧
    ∃ c : ℝ, c > 0 ∧ ∀ i : ℕ, smoothEnum P i > 1 →
      (gap P i : ℝ) ≥ c * (smoothEnum P i : ℝ)^(1 - ε)

/--
**Answer to Erdős-Wintner:**
Yes, such an infinite P exists.
-/
theorem erdos240_answer : erdos240Question := by
  obtain ⟨P, hPrime, hInf, c, hc, hgap⟩ := tijdeman_main_theorem (1/2) (by norm_num)
  refine ⟨P, hPrime, hInf, ?_⟩
  intro M
  -- The enumeration is strictly increasing, hence `i ≤ smoothEnum P i`.
  have hmono : StrictMono (smoothEnum P) := smoothEnum_strictMono P
  have hle : ∀ j, j ≤ smoothEnum P j := by
    intro j
    induction j with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hlt : smoothEnum P k < smoothEnum P (k + 1) := hmono (Nat.lt_succ_self k)
      omega
  -- Pick `i` with `smoothEnum P i > (M/c)²`, so that `c · √(smoothEnum P i) > M`.
  obtain ⟨n, hn⟩ := exists_nat_gt (((M : ℝ) / c) ^ 2)
  set i : ℕ := max n 2 with hi_def
  have hi2 : 2 ≤ i := le_max_right _ _
  have hin : n ≤ i := le_max_left _ _
  -- `smoothEnum P i ≥ i ≥ 2`, so it is `> 1` and Tijdeman's bound applies.
  have ha_ge : i ≤ smoothEnum P i := hle i
  have ha_gt_one : smoothEnum P i > 1 := by omega
  have hgapi := hgap i ha_gt_one
  -- Real-analytic core: `(M/c)² < smoothEnum P i`.
  have hcpos : (0 : ℝ) < c := hc
  have hMc_nonneg : 0 ≤ (M : ℝ) / c := by positivity
  have hB : ((M : ℝ) / c) ^ 2 < (smoothEnum P i : ℝ) := by
    have h1 : ((M : ℝ) / c) ^ 2 < (n : ℝ) := hn
    have h2 : (n : ℝ) ≤ (i : ℝ) := by exact_mod_cast hin
    have h3 : (i : ℝ) ≤ (smoothEnum P i : ℝ) := by exact_mod_cast ha_ge
    linarith
  -- `M/c < √(smoothEnum P i)`.
  have hsqrt : (M : ℝ) / c < Real.sqrt (smoothEnum P i : ℝ) := by
    rw [show (M : ℝ) / c = Real.sqrt (((M : ℝ) / c) ^ 2) from (Real.sqrt_sq hMc_nonneg).symm]
    exact Real.sqrt_lt_sqrt (by positivity) hB
  -- Hence `M < c · √(smoothEnum P i) = c · (smoothEnum P i)^{1-1/2}`.
  have hMeq : c * ((M : ℝ) / c) = (M : ℝ) := by field_simp
  have hlt : (M : ℝ) < c * Real.sqrt (smoothEnum P i : ℝ) := by
    have := mul_lt_mul_of_pos_left hsqrt hcpos
    rwa [hMeq] at this
  have hrw : (smoothEnum P i : ℝ) ^ (1 - 1 / 2 : ℝ) = Real.sqrt (smoothEnum P i : ℝ) := by
    rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  -- Combine with Tijdeman's lower bound on the gap.
  have hfinal : (M : ℝ) < (gap P i : ℝ) := by
    have : (M : ℝ) < c * (smoothEnum P i : ℝ) ^ (1 - 1 / 2 : ℝ) := by rw [hrw]; exact hlt
    linarith [hgapi]
  exact ⟨i, by exact_mod_cast hfinal⟩

/-
## Part VII: Construction Ideas
-/

/-
**Tijdeman's Construction:**
The infinite set P is constructed so that the primes are
sufficiently "sparse" - they grow fast enough that consecutive
P-smooth numbers can't be too close.

Key insight: If P contains all primes up to some bound,
P-smooth numbers are dense. But if P is sparse (like powers
of 2, or primes along a fast-growing sequence), gaps grow.
-/

/--
**Example: Powers of 2**
If P = {2}, then P-smooth numbers are {1, 2, 4, 8, 16, ...}.
Gaps: 1, 2, 4, 8, ... which grow like aᵢ/2.

More generally, for P = {p} a singleton, P-smooth numbers are
{1, p, p², p³, ...} with gaps growing exponentially.
-/
theorem singleton_large_gaps (p : ℕ) (hp : p.Prime) :
    gapsTendToInfinity {p} := by
  -- `{p}` is a finite set of primes, so the finite-`P` result applies directly.
  have h : gapsTendToInfinity (↑({p} : Finset ℕ) : Set ℕ) :=
    finite_P_unbounded_gaps {p} (by
      intro q hq
      rw [Finset.mem_singleton] at hq
      subst hq
      exact hp)
  simpa using h

/-
## Part VIII: Related Results
-/

/-
**Størmer's Theorem:**
For any finite P, only finitely many consecutive integers
can both be P-smooth.

This is another consequence of Pólya-type results.
-/

/-
**Connection to ABC Conjecture:**
Better bounds on gaps would follow from the ABC conjecture.
The ABC conjecture implies: for coprime a, b, c with a + b = c,
c < rad(abc)^{1+ε} where rad is the radical (product of distinct primes).
-/

/-
**Smooth numbers in arithmetic progressions:**
How are P-smooth numbers distributed in arithmetic progressions?
This is related to Linnik-type problems.
-/

/-
## Part IX: Summary
-/

/--
**Summary of Known Results:**
-/
theorem erdos_240_summary :
    -- Finite P: gaps → ∞
    (∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) → gapsTendToInfinity (↑P : Set ℕ)) ∧
    -- Tijdeman's main theorem (infinite P)
    (∀ ε : ℝ, ε > 0 → ∃ P : Set ℕ, (∀ p ∈ P, Nat.Prime p) ∧ P.Infinite ∧
      ∃ c : ℝ, c > 0 ∧ ∀ i : ℕ, smoothEnum P i > 1 →
        (gap P i : ℝ) ≥ c * (smoothEnum P i : ℝ)^(1 - ε)) ∧
    -- Answer is YES
    erdos240Question := by
  refine ⟨finite_P_unbounded_gaps, ?_, erdos240_answer⟩
  intro ε hε
  exact tijdeman_main_theorem ε hε

/--
**Erdős Problem #240: SOLVED**

Is there an infinite set of primes P such that gaps between
consecutive P-smooth numbers tend to infinity?

Answer: YES (Tijdeman 1973)

For any ε > 0, there exists infinite P with gaps ≫ aᵢ^{1-ε}.
-/
theorem erdos_240 : erdos240Question := erdos240_answer

end Erdos240
