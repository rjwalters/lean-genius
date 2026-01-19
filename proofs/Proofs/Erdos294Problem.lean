/-
Erdős Problem #294: Egyptian Fractions and the t(N) Function

Source: https://erdosproblems.com/294
Status: SOLVED (Liu-Sawhney 2024)

Statement:
Let N ≥ 1 and t(N) be the least integer t such that there is NO solution to
  1 = 1/n₁ + 1/n₂ + ⋯ + 1/nₖ
with t = n₁ < n₂ < ⋯ < nₖ ≤ N.

In other words, t(N) is the smallest starting denominator from which we
cannot build an Egyptian fraction representation of 1 using only
denominators from {t, t+1, ..., N}.

Estimate t(N).

Background:
- Egyptian fractions: sums of distinct unit fractions
- Every positive rational has an Egyptian fraction representation
- The question is about the "density" of such representations

Known Results:
- Erdős-Graham (1980): t(N) ≪ N/log N (upper bound)
- Liu-Sawhney (2024): N/((log N)(log log N)³(log log log N)^O(1)) ≪ t(N) ≪ N/log N

References:
- Erdős, P. and Graham, R. (1980): Old and new problems and results in
  combinatorial number theory. Monographies de L'Enseignement Mathematique.
- Liu, Y. and Sawhney, M. (2024): On further questions regarding unit fractions.
  arXiv:2404.07113
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset BigOperators Nat Real

namespace Erdos294

/-
## Part I: Egyptian Fractions
-/

/--
**Unit fraction:**
The reciprocal 1/n for positive n.
-/
def unitFraction (n : ℕ) : ℚ := 1 / n

/--
**Egyptian fraction sum:**
Sum of reciprocals over a finite set of positive integers.
-/
def egyptianSum (S : Finset ℕ) : ℚ :=
  ∑ n ∈ S, unitFraction n

/--
**Valid Egyptian representation of 1:**
A finite set S of distinct positive integers with ∑_{n ∈ S} 1/n = 1.
-/
def isEgyptianRepresentationOf1 (S : Finset ℕ) : Prop :=
  S.Nonempty ∧ (∀ n ∈ S, n ≥ 1) ∧ egyptianSum S = 1

/--
**Example: {2, 3, 6} represents 1**
1/2 + 1/3 + 1/6 = 3/6 + 2/6 + 1/6 = 6/6 = 1.
-/
example : isEgyptianRepresentationOf1 {2, 3, 6} := by
  sorry

/-
## Part II: The t(N) Function
-/

/--
**Constrained Egyptian representation:**
An Egyptian representation of 1 using only denominators in [t, N].
-/
def hasConstrainedRepresentation (t N : ℕ) : Prop :=
  ∃ S : Finset ℕ, S.Nonempty ∧
    (∀ n ∈ S, t ≤ n ∧ n ≤ N) ∧
    egyptianSum S = 1

/--
**The t(N) function:**
t(N) = min{t ≥ 1 : there is NO Egyptian representation of 1 with denominators in [t, N]}.

Equivalently, t(N)-1 is the largest t such that 1 CAN be represented.
-/
noncomputable def t_func (N : ℕ) : ℕ :=
  Nat.find (⟨N + 1, by
    intro S hS
    sorry -- If t > N, no valid denominators exist
  ⟩ : ∃ t, ¬hasConstrainedRepresentation t N)

/--
**Key property: t(N) is where representations stop being possible.**
-/
theorem t_func_characterization (N : ℕ) (hN : N ≥ 2) :
    (∀ t < t_func N, hasConstrainedRepresentation t N) ∧
    ¬hasConstrainedRepresentation (t_func N) N := by
  sorry

/-
## Part III: Small Values
-/

/--
**t(2) = 2:**
Only {2} gives 1/2, not 1. So t(2) = 2.
-/
theorem t_2 : t_func 2 = 2 := by
  sorry

/--
**t(6) analysis:**
{2, 3, 6} gives 1/2 + 1/3 + 1/6 = 1, so t(6) > 2.
{3, 4, 5, 6} gives 1/3 + 1/4 + 1/5 + 1/6 = 20/60 + 15/60 + 12/60 + 10/60 = 57/60 ≠ 1.
-/
theorem t_6_lower : t_func 6 > 2 := by
  sorry

/--
**The harmonic sum:**
H_N = ∑_{k=1}^N 1/k.
-/
noncomputable def harmonicSum (N : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (N + 1), if k ≥ 1 then unitFraction k else 0

/--
**Harmonic sum bounds:**
H_N ≈ log(N) + γ where γ ≈ 0.577 is Euler's constant.
-/
axiom harmonic_asymptotic (N : ℕ) (hN : N ≥ 2) :
    |(harmonicSum N : ℝ) - Real.log N| < 1

/-
## Part IV: Erdős-Graham Upper Bound
-/

/--
**Erdős-Graham Upper Bound (1980):**
t(N) ≪ N/log(N).

For sufficiently large N, t(N) ≤ C · N/log(N) for some constant C.
-/
def erdosGrahamUpperBound : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    (t_func N : ℝ) ≤ C * N / Real.log N

axiom erdos_graham_1980 : erdosGrahamUpperBound

/--
**Interpretation:**
t(N) grows slower than N, essentially like N/log(N).
This means "most" starting points allow Egyptian representations of 1.
-/
def interpretation1 : String :=
  "For large N, only about N/log(N) starting points block representations"

/-
## Part V: The Liu-Sawhney Theorem
-/

/--
**Liu-Sawhney Lower Bound (2024):**
t(N) ≫ N/((log N)(log log N)³(log log log N)^O(1)).
-/
def liuSawhneyLowerBound : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∃ C : ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    (t_func N : ℝ) ≥ c * N / ((Real.log N) * (Real.log (Real.log N))^3 *
      (Real.log (Real.log (Real.log N)))^C)

/--
**Liu-Sawhney Theorem (2024):**
The full result, pinning down t(N) up to polylogarithmic factors.
-/
def liuSawhneyTheorem : Prop :=
  liuSawhneyLowerBound ∧ erdosGrahamUpperBound

axiom liu_sawhney_2024 : liuSawhneyTheorem

/--
**Erdős Problem #294: Main Theorem**
t(N) ≍ N/((log N)(log log N)^O(1)).
-/
theorem erdos_294 : liuSawhneyTheorem :=
  liu_sawhney_2024

/-
## Part VI: Implications
-/

/--
**Density interpretation:**
The set of t ∈ [1, N] allowing Egyptian representations has size ≈ N(1 - 1/log N).
So "almost all" starting points work.
-/
def densityInterpretation : Prop :=
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    (N - t_func N : ℝ) / N > 1 - ε

theorem almost_all_work : densityInterpretation := by
  sorry

/--
**The harmonic sum connection:**
t(N) is related to where the partial harmonic sums exceed certain thresholds.
-/
def harmonicConnection (t N : ℕ) : Prop :=
  hasConstrainedRepresentation t N → (harmonicSum N : ℝ) - (harmonicSum (t - 1) : ℝ) ≥ 1

/-
## Part VII: Related Functions
-/

/--
**The f(n) function:**
f(n) = minimum k such that 1 can be written as sum of k distinct unit fractions
with largest denominator n.
-/
noncomputable def f_func (n : ℕ) : ℕ :=
  Nat.find (⟨n, sorry⟩ : ∃ k, ∃ S : Finset ℕ, S.card = k ∧ n ∈ S ∧
    (∀ m ∈ S, m ≤ n) ∧ egyptianSum S = 1)

/--
**Relationship between t and f:**
If f(N) exists, then t(N) > 1.
-/
theorem t_f_relationship (N : ℕ) (hN : N ≥ 6) :
    ∃ S : Finset ℕ, isEgyptianRepresentationOf1 S ∧ (∀ n ∈ S, n ≤ N) →
    t_func N > 1 := by
  sorry

/-
## Part VIII: The Greedy Algorithm
-/

/--
**Greedy Egyptian fraction:**
The greedy algorithm for representing q as Egyptian fractions:
repeatedly subtract the largest unit fraction ≤ q.
-/
def greedyStep (q : ℚ) : ℕ := sorry  -- ceiling of 1/q when q > 0

/--
**Greedy algorithm property:**
The greedy algorithm always terminates but may produce long representations.
-/
axiom greedy_terminates (q : ℚ) (hq : 0 < q ∧ q < 1) :
    ∃ S : Finset ℕ, egyptianSum S = q

/--
**Relationship to t(N):**
The greedy algorithm's behavior affects whether constrained representations exist.
-/
def greedyRelation (t N : ℕ) : Prop :=
  hasConstrainedRepresentation t N ↔
    ∃ strategy : ℕ → ℕ, -- a selection strategy
      True -- complicated condition on the strategy

/-
## Part IX: Computational Aspects
-/

/--
**Computing t(N) is hard:**
There's no known efficient algorithm for computing t(N) exactly.
-/
axiom t_computation_hard : True

/--
**Small computed values:**
Some verified values of t(N).
-/
def knownValues : List (ℕ × ℕ) :=
  [(2, 2), (3, 2), (4, 2), (5, 2), (6, 3)]  -- t(N) values

/-
## Part X: Main Results Summary
-/

/--
**Erdős Problem #294: Summary**

1. **Definition:** t(N) = min t with no Egyptian rep of 1 in [t, N]
2. **Erdős-Graham (1980):** t(N) ≤ C·N/log(N) for some C
3. **Liu-Sawhney (2024):** t(N) ≥ c·N/((log N)(log log N)³...)
4. **Conclusion:** t(N) ≍ N/((log N)(log log N)^O(1))

Status: SOLVED
-/
theorem erdos_294_summary :
    -- Erdős-Graham upper bound
    erdosGrahamUpperBound ∧
    -- Liu-Sawhney lower bound
    liuSawhneyLowerBound := by
  exact liu_sawhney_2024

/--
**Key insight:**
The density of "bad" starting points is about log(N)/N,
so they form a sparse set.
-/
axiom key_insight : True

/--
**Problem Status:**
- Upper bound: PROVED (Erdős-Graham 1980)
- Lower bound: PROVED (Liu-Sawhney 2024)
- Full asymptotic: SOLVED up to (log log N)^O(1) factors
-/
axiom erdos_294_status : True

end Erdos294
