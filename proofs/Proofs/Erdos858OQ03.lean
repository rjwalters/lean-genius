/-
Erdős Problem #858 — OQ-03 leaf: a concrete primitive interval family whose
reciprocal sum stays bounded below by a constant.

Source: https://erdosproblems.com/858

Parent (`Proofs/Erdos858Problem.lean`): for A ⊆ {1,…,N} avoiding a·t = b with
a, b ∈ A and smallest prime factor of t exceeding a, the *weighted* reciprocal
sum (1/log N)·Σ_{n∈A} 1/n is o(1) as N → ∞ (Alexander 1966; the deep estimate is
axiomatized in the parent as `alexander_1966`).

Open question OQ-03 asks for the *structure of extremal sets achieving
near-maximum sums*. This file makes a concrete, fully verified (0-axiom)
contribution toward that question by exhibiting an explicit valid family and
quantifying its reciprocal sum.

We restate the parent's definitions (`smallestPrimeFactor`, `SatisfiesCondition`,
`IsPrimitive`, `InRange`, `reciprocalSum`) — the parent file does not compile
against the pinned Mathlib v4.26 because it imports the now-split module
`Mathlib.Algebra.BigOperators.Group.Finset`, so we keep this leaf self-contained
and re-export `import Mathlib`.

We take the "top half" interval A = (⌊N/2⌋, N] = `Finset.Ioc (N/2) N` and prove:

* `topHalf_primitive` : it is primitive (no element divides another) — because
  a ∣ b with a < b would force b ≥ 2a > N.
* `topHalf_satisfies` : being primitive, it satisfies #858's multiplicative
  condition (`primitive_satisfies_condition`).
* `topHalf_in_range`  : it lies in {1,…,N}.
* `reciprocalSum_topHalf_ge_half` : Σ_{n∈A} 1/n ≥ 1/2 for every N ≥ 1.

The last point is the mathematically interesting one: it shows the o(1) decay of
the *weighted* sum is due *entirely* to the 1/log N normalization. The bare
reciprocal sum of a valid (condition-satisfying) set need not vanish — here it is
uniformly bounded below by 1/2 — so any quantitative refinement of #858 must come
from the logarithmic denominator, not from the reciprocal sum shrinking.

Verified with no axioms beyond Lean's foundational
`propext`/`Classical.choice`/`Quot.sound`.
-/

import Mathlib

open Nat Real Finset BigOperators

namespace Erdos858OQ03

/-!
## Restated parent definitions (Erdős #858)
-/

/-- The smallest prime factor of `n > 1`, or `0` if `n ≤ 1`. -/
noncomputable def smallestPrimeFactor (n : ℕ) : ℕ :=
  if 1 < n then n.minFac else 0

/--
**Multiplicative condition.** `A` satisfies the condition if there is no solution
to `a·t = b` with `a, b ∈ A`, `t > 1`, and `smallestPrimeFactor t > a`.
-/
def SatisfiesCondition (A : Finset ℕ) : Prop :=
  ∀ a b t : ℕ, a ∈ A → b ∈ A → t > 1 → a * t = b →
    smallestPrimeFactor t ≤ a

/-- **Primitive set.** No element divides another. -/
def IsPrimitive (A : Finset ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ A → b ∈ A → a ∣ b → a = b

/--
Primitive sets of positive integers satisfy the multiplicative condition.

(Positivity is genuinely needed: `{0}` is primitive but fails the condition,
since `0·t = 0` would require `smallestPrimeFactor t ≤ 0`, impossible for `t > 1`.
The parent file's lemma omits this hypothesis and is therefore false at `0 ∈ A`.)
-/
theorem primitive_satisfies_condition (A : Finset ℕ) (hpos : ∀ a ∈ A, 0 < a)
    (hA : IsPrimitive A) : SatisfiesCondition A := by
  intro a b t ha hb ht heq
  by_contra _
  have hdvd : a ∣ b := ⟨t, heq.symm⟩
  have hab := hA a b ha hb hdvd
  rw [hab] at heq
  have hbpos := hpos b hb
  nlinarith

/-- **Range constraint.** `A ⊆ {1,…,N}`. -/
def InRange (A : Finset ℕ) (N : ℕ) : Prop :=
  ∀ n ∈ A, 1 ≤ n ∧ n ≤ N

/-- **Reciprocal sum** `Σ_{n ∈ A, n > 0} 1/n`. -/
noncomputable def reciprocalSum (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A.filter (· > 0), (1 : ℝ) / n

/-!
## The top-half interval family
-/

/--
**The top-half interval** A = (⌊N/2⌋, N], i.e. the integers n with
⌊N/2⌋ < n ≤ N. This is a clean, explicitly described set satisfying #858's
multiplicative condition.
-/
def topHalf (N : ℕ) : Finset ℕ := Finset.Ioc (N / 2) N

/--
The top-half interval is **primitive**: no element divides another.

If `a ∣ b` with `a, b ∈ (⌊N/2⌋, N]` and `a ≠ b`, then `b = a·k` with `k ≥ 2`,
so `b ≥ 2a > N`, contradicting `b ≤ N`.
-/
theorem topHalf_primitive (N : ℕ) : IsPrimitive (topHalf N) := by
  intro a b ha hb hab
  rw [topHalf, Finset.mem_Ioc] at ha hb
  obtain ⟨ha_gt, _⟩ := ha
  obtain ⟨hb_gt, hb_le⟩ := hb
  obtain ⟨k, hk⟩ := hab
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k <;> omega
  · have h2a : 2 * a ≤ b := by nlinarith
    omega

/--
The top-half interval **satisfies #858's multiplicative condition**, since it is
primitive.
-/
theorem topHalf_satisfies (N : ℕ) : SatisfiesCondition (topHalf N) :=
  primitive_satisfies_condition _
    (fun a ha => by rw [topHalf, Finset.mem_Ioc] at ha; omega)
    (topHalf_primitive N)

/-- The top-half interval **lies in {1,…,N}**. -/
theorem topHalf_in_range (N : ℕ) : InRange (topHalf N) N := by
  intro n hn
  rw [topHalf, Finset.mem_Ioc] at hn
  omega

/--
**Reciprocal-sum lower bound.** For every `N ≥ 1`,
  Σ_{n ∈ (⌊N/2⌋, N]} 1/n ≥ 1/2.

The interval has `N - ⌊N/2⌋ = ⌈N/2⌉` elements, each at most `N`, so each
reciprocal is at least `1/N` and the sum is at least `⌈N/2⌉ / N ≥ 1/2`.
-/
theorem reciprocalSum_topHalf_ge_half (N : ℕ) (hN : 1 ≤ N) :
    reciprocalSum (topHalf N) ≥ 1 / 2 := by
  have hfilter : (topHalf N).filter (· > 0) = topHalf N := by
    apply Finset.filter_true_of_mem
    intro n hn
    rw [topHalf, Finset.mem_Ioc] at hn
    omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hcard : (topHalf N).card = N - N / 2 := by
    rw [topHalf]; exact Nat.card_Ioc _ _
  have key : ∑ _n ∈ topHalf N, (1 : ℝ) / N ≤ ∑ n ∈ topHalf N, (1 : ℝ) / n := by
    apply Finset.sum_le_sum
    intro n hn
    rw [topHalf, Finset.mem_Ioc] at hn
    have hn1 : 1 ≤ n := by omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn.2
    exact one_div_le_one_div_of_le hnpos hnN
  have h2c : N ≤ 2 * (N - N / 2) := by omega
  calc (1 : ℝ) / 2
      ≤ ↑(N - N / 2) * (1 / N) := by
        rw [mul_one_div, le_div_iff₀ hNpos]
        have : (N : ℝ) ≤ 2 * ↑(N - N / 2) := by exact_mod_cast h2c
        linarith
    _ = ∑ _n ∈ topHalf N, (1 : ℝ) / N := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one_div]
    _ ≤ ∑ n ∈ topHalf N, (1 : ℝ) / n := key
    _ = reciprocalSum (topHalf N) := by unfold reciprocalSum; rw [hfilter]

/--
**Summary (OQ-03 contribution).** The explicit family `topHalf N = (⌊N/2⌋, N]`
is, for every `N ≥ 1`, a set that satisfies #858's multiplicative condition,
lies in {1,…,N}, and has reciprocal sum at least `1/2`.

Hence the o(1) decay of the *weighted* sum is forced entirely by the `1/log N`
normalization, not by any decay of the reciprocal sum itself.
-/
theorem topHalf_valid_with_large_reciprocal_sum (N : ℕ) (hN : 1 ≤ N) :
    SatisfiesCondition (topHalf N) ∧
      InRange (topHalf N) N ∧
      reciprocalSum (topHalf N) ≥ 1 / 2 :=
  ⟨topHalf_satisfies N, topHalf_in_range N, reciprocalSum_topHalf_ge_half N hN⟩

end Erdos858OQ03
