/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 53ad8a5a-cb79-424d-a474-eb6a05318d2c

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem boundedGaps_implies_positiveDensity (a : ℕ → ℕ) (C : ℕ) (hC : C > 0)
    (hmono : StrictMono a) (hpos : ∀ n, a n > 0) (hgap : HasUniformBoundedGaps a C) :
    HasPositiveUpperDensity (Set.range a)
-/

/-
Erdős Problem #299: Bounded Gap Sequences and Unit Fractions

Source: https://erdosproblems.com/299
Status: SOLVED (Bloom 2021) - Answer is NO

Statement:
Is there an infinite sequence a₁ < a₂ < ... such that:
  1. The gaps are bounded: a_{i+1} - a_i = O(1)
  2. No finite sum of 1/a_i equals 1

Answer: NO. Such a sequence does not exist.

This follows from Bloom's 2021 result on Problem #298, which shows that every set
of positive upper density contains a finite subset whose reciprocals sum to 1.
Since a sequence with bounded gaps has positive density, it must contain such a subset.

Key Results:
- Bloom (2021): If A ⊆ ℕ has positive upper density and 0 ∉ A, then there exists
  a finite S ⊆ A with ∑_{n ∈ S} 1/n = 1.
- Corollary: No bounded-gap sequence avoids having a unit fraction sum.

References:
- [Bl21] Bloom, T. F., "On a density conjecture about unit fractions" arXiv:2112.03726 (2021)
- [ErGr80] Erdős-Graham, "Old and new problems and results in combinatorial number theory"
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic


open Filter Asymptotics Finset

namespace Erdos299

/-!
## Part I: Definitions

We define the key concepts: bounded-gap sequences, Egyptian fractions, and density.
-/

/-- A sequence has bounded gaps if consecutive differences are O(1) as n → ∞.
    This means there exists a constant C such that a_{n+1} - a_n ≤ C for large n. -/
def HasBoundedGaps (a : ℕ → ℕ) : Prop :=
  (fun n => (a (n + 1) : ℝ) - a n) =O[atTop] (1 : ℕ → ℝ)

/-- A simpler characterization: gaps are bounded by some constant. -/
def HasUniformBoundedGaps (a : ℕ → ℕ) (C : ℕ) : Prop :=
  ∀ n, a (n + 1) - a n ≤ C

/-- A set of positive integers whose reciprocals sum to exactly 1.
    This is an Egyptian fraction decomposition.
    We use ℚ for decidability of equality. -/
def HasUnitFractionSum (S : Finset ℕ) : Prop :=
  (∀ n ∈ S, n > 0) ∧ ∑ n ∈ S, (1 : ℚ) / n = 1

/-- A sequence avoids unit fraction sums if no finite subset sums to 1. -/
def AvoidsUnitFractionSum (a : ℕ → ℕ) : Prop :=
  ∀ S : Finset ℕ, ∑ i ∈ S, (1 : ℝ) / a i ≠ 1

/-!
## Part II: Upper Density

The upper density of a set measures what fraction of integers it contains "in the limit".
-/

/-- The counting function: how many elements of a set are ≤ N. -/
noncomputable def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  (A ∩ Set.Iic N).ncard

/-- Upper density of a set A ⊆ ℕ.
    This is limsup_{N → ∞} |A ∩ [1,N]| / N. -/
noncomputable def upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup (fun N => (countingFunction A N : ℝ) / N) atTop

/-- A set has positive upper density if upperDensity A > 0. -/
def HasPositiveUpperDensity (A : Set ℕ) : Prop :=
  upperDensity A > 0

/-!
## Part III: Key Lemma - Bounded Gaps Imply Positive Density

If a strictly increasing sequence has bounded gaps, its range has positive density.
This is the crucial connection between Problems #298 and #299.
-/

/- A strictly increasing sequence with gaps bounded by C has density at least 1/C.
    Intuition: Every C consecutive integers contains at least one element of the sequence. -/
noncomputable section AristotleLemmas

/-
If a sequence has gaps bounded by C, then a_n is bounded by a_0 + n*C.
-/
lemma Erdos299.bounded_gaps_growth {a : ℕ → ℕ} {C : ℕ} (h : Erdos299.HasUniformBoundedGaps a C) (n : ℕ) :
    a n ≤ a 0 + n * C := by
      -- By definition of HasUniformBoundedGaps, we have \( a(n + 1) - a(n) ≤ C \).
      have h_diff : ∀ n, a (n + 1) ≤ a n + C := by
        intro n; specialize h n; omega;
      induction' n with n ih <;> [ norm_num; linarith [ h_diff n ] ]

end AristotleLemmas

theorem boundedGaps_implies_positiveDensity (a : ℕ → ℕ) (C : ℕ) (hC : C > 0)
    (hmono : StrictMono a) (hpos : ∀ n, a n > 0) (hgap : HasUniformBoundedGaps a C) :
    HasPositiveUpperDensity (Set.range a) := by
  -- The proof requires showing that |{a_i : a_i ≤ N}| / N ≥ 1/C eventually.
  -- This is because the gaps being ≤ C means a_n ≤ a_0 + n·C, so n ≥ (a_n - a_0)/C.
  -- Thus there are at least N/C elements below N (approximately).
  -- We claim that for large N, countingFunction (Set.range a) N ≥ (N - a 0) / C.
  have h_counting : ∀ N ≥ a 0 + C, (countingFunction (Set.range a) N : ℝ) ≥ (N - a 0) / C := by
    -- Let $k$ be the largest index such that $a k \leq N$.
    intro N hN
    obtain ⟨k, hk⟩ : ∃ k, a k ≤ N ∧ a (k + 1) > N := by
      -- Since $a$ is strictly increasing and unbounded, there exists some $k$ such that $a k > N$.
      obtain ⟨k, hk⟩ : ∃ k, a k > N := by
        exact ⟨ _, hmono.id_le _ ⟩;
      contrapose! hk;
      exact Nat.recOn k ( by linarith ) hk;
    -- Then $A \cap [0, N]$ contains $\{a 0, ..., a k\}$, so countingFunction A N ≥ k + 1.
    have h_counting_ge_k : (countingFunction (Set.range a) N : ℝ) ≥ k + 1 := by
      have h_counting_ge_k : (Set.range a ∩ Set.Iic N).ncard ≥ (Finset.image a (Finset.range (k + 1))).card := by
        rw [ ← Set.ncard_coe_finset ];
        apply Set.ncard_le_ncard;
        · exact fun x hx => by rcases Finset.mem_image.mp hx with ⟨ i, hi, rfl ⟩ ; exact ⟨ Set.mem_range_self _, by simpa using by linarith [ hmono.monotone ( show i ≤ k from Finset.mem_range_succ_iff.mp hi ) ] ⟩ ;
        · exact Set.finite_iff_bddAbove.mpr ⟨ N, fun x hx => hx.2 ⟩;
      exact_mod_cast h_counting_ge_k.trans' ( by rw [ Finset.card_image_of_injective _ hmono.injective ] ; norm_num );
    -- By the helper lemma `Erdos299.bounded_gaps_growth`, $a k \leq a 0 + k * C$.
    have h_ak_le : (a k : ℝ) ≤ a 0 + k * C := by
      exact_mod_cast Erdos299.bounded_gaps_growth hgap k;
    -- Since $k$ is maximal, $a (k+1) > N$. By bounded gaps, $a (k+1) \leq a k + C$.
    have h_ak1_le : (a (k + 1) : ℝ) ≤ a k + C := by
      exact_mod_cast by linarith [ hgap k, Nat.sub_add_cancel ( hmono.monotone ( Nat.le_succ k ) ) ] ;
    rw [ ge_iff_le, div_le_iff₀ ] <;> norm_num <;> nlinarith [ ( by norm_cast : ( a k : ℝ ) ≤ N ∧ ( a ( k + 1 ) : ℝ ) > N ) ];
  -- Dividing both sides of the inequality by N, we get (countingFunction (Set.range a) N : ℝ) / N ≥ (N - a 0) / (C * N).
  have h_dividing : ∀ N ≥ a 0 + C, (countingFunction (Set.range a) N : ℝ) / N ≥ (1 - a 0 / N) / C := by
    -- By dividing both sides of the inequality from h_counting by N, we obtain the desired result.
    intros N hN
    have := h_counting N hN
    field_simp [hN] at this ⊢;
    rw [ sub_div', div_le_div_iff_of_pos_right ] <;> linarith [ show ( N : ℝ ) > 0 by norm_cast; linarith [ hpos 0 ] ];
  -- As N → ∞, (1 - a 0 / N) / C converges to 1 / C.
  have h_limit : Filter.Tendsto (fun N : ℕ => (1 - a 0 / (N : ℝ)) / C) Filter.atTop (nhds (1 / C)) := by
    exact le_trans ( Filter.Tendsto.div_const ( tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop <| tendsto_natCast_atTop_atTop ) _ ) <| by norm_num;
  refine' lt_of_lt_of_le _ ( le_csInf _ _ ) <;> norm_num;
  exact one_div_pos.mpr ( Nat.cast_pos.mpr hC );
  · exact ⟨ 1, ⟨ a 0 + C, fun n hn => div_le_one_of_le₀ ( mod_cast by
      exact le_trans ( Set.ncard_le_ncard ( show Set.range a ∩ Set.Iic n ⊆ Set.Icc 1 n from fun x hx => ⟨ by obtain ⟨ k, rfl ⟩ := hx.1; exact hpos k, hx.2 ⟩ ) ) ( by simp +decide [ Set.ncard_eq_toFinset_card' ] ) ) ( Nat.cast_nonneg _ ) ⟩ ⟩;
  · exact fun b x hx => le_of_tendsto h_limit ( Filter.eventually_atTop.mpr ⟨ x + a 0 + C, fun N hN => le_trans ( h_dividing N ( by linarith ) ) ( hx N ( by linarith ) ) ⟩ )

/-!
## Part IV: Bloom's Theorem (Problem #298)

This is the key result: positive density sets contain Egyptian fractions.
-/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['Erdos299.bloom_theorem', 'harmonicSorry177575']-/
/-- **Bloom's Theorem (2021)** - Erdős Problem #298

    If A ⊆ ℕ has positive upper density and contains no zero,
    then A contains a finite subset S with ∑_{n ∈ S} 1/n = 1.

    This resolved a long-standing conjecture of Erdős and Graham.
    The proof uses sophisticated techniques from additive combinatorics. -/
axiom bloom_theorem (A : Set ℕ) (h0 : 0 ∉ A) (hdens : HasPositiveUpperDensity A) :
    ∃ S : Finset ℕ, ↑S ⊆ A ∧ HasUnitFractionSum S

/-!
## Part V: The Main Result - Erdős Problem #299
-/

/- Aristotle took a wrong turn (reason code: 0). Please try again. -/
/-- **Erdős Problem #299** (SOLVED - Answer: NO)

    There does NOT exist an infinite sequence a₁ < a₂ < ... such that:
    1. The gaps are bounded (a_{i+1} - a_i = O(1))
    2. No finite sum of 1/a_i equals 1

    This follows directly from Bloom's theorem (Problem #298):
    - Bounded-gap sequences have positive density (Part III)
    - Positive density sets contain unit fraction sums (Bloom's theorem)
    - Therefore, bounded-gap sequences must contain unit fraction sums -/
theorem erdos_299_no_such_sequence :
    ¬∃ (a : ℕ → ℕ),
      StrictMono a ∧
      (∀ n, 0 < a n) ∧
      HasBoundedGaps a ∧
      AvoidsUnitFractionSum a := by
  -- Proof sketch:
  -- 1. Assume such a sequence exists
  -- 2. Bounded gaps → positive density (boundedGaps_implies_positiveDensity)
  -- 3. Positive density → contains unit fraction sum (bloom_theorem)
  -- 4. This contradicts AvoidsUnitFractionSum
  intro ⟨a, hmono, hpos, hgaps, havoid⟩
  -- The full proof requires extracting the uniform bound from the O(1) condition
  -- and applying bloom_theorem to the range of a.
  sorry

/-- Alternative formulation matching formal-conjectures style.
    The answer is FALSE: no such sequence exists. -/
theorem erdos_299 : ¬∃ (a : ℕ → ℕ),
    StrictMono a ∧ (∀ n, 0 < a n) ∧
    (fun n => (a (n + 1) : ℝ) - a n) =O[atTop] (1 : ℕ → ℝ) ∧
    ∀ S : Finset ℕ, ∑ i ∈ S, (1 : ℝ) / a i ≠ 1 :=
  erdos_299_no_such_sequence

/-!
## Part VI: The Density Variant

Bloom's result is even stronger: positive density alone suffices.
-/

/-- **Density Variant of Problem #299**

    If A ⊆ ℕ has positive upper density (and contains no zero),
    then there exists a finite S ⊆ A with ∑_{n ∈ S} 1/n = 1.

    This is essentially a restatement of Bloom's theorem,
    showing the bounded-gap condition is much stronger than needed. -/
theorem erdos_299_density_variant (A : Set ℕ) (h0 : 0 ∉ A) (hdens : HasPositiveUpperDensity A) :
    ∃ S : Finset ℕ, ↑S ⊆ A ∧ HasUnitFractionSum S := by
  exact bloom_theorem A h0 hdens

/-!
## Part VII: Concrete Examples

We verify some basic facts about sequences and unit fractions.
-/

/-- The arithmetic sequence 2, 3, 4, 5, ... has uniform gaps of 1. -/
theorem arith_seq_bounded_gaps : HasUniformBoundedGaps (fun n => n + 2) 1 := by
  intro n
  -- (n + 1 + 2) - (n + 2) = 1 ≤ 1
  show (n + 1 + 2) - (n + 2) ≤ 1
  omega

/-- The set {2, 3, 6} gives a unit fraction sum: 1/2 + 1/3 + 1/6 = 1. -/
theorem egyptian_236 : HasUnitFractionSum {2, 3, 6} := by
  constructor
  · intro n hn
    simp only [mem_insert, mem_singleton] at hn
    rcases hn with rfl | rfl | rfl <;> omega
  · native_decide

/-- The set {2, 4, 6, 12} gives a unit fraction sum: 1/2 + 1/4 + 1/6 + 1/12 = 1. -/
theorem egyptian_2_4_6_12 : HasUnitFractionSum {2, 4, 6, 12} := by
  constructor
  · intro n hn
    simp only [mem_insert, mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl <;> omega
  · native_decide

/-!
## Part VIII: Why Bounded Gaps Matter

The bounded gap condition is crucial. Without it, sparse sequences CAN avoid unit fractions.
-/

/-- Example of a sparse sequence: powers of 2.
    The sequence 1, 2, 4, 8, 16, ... has unbounded gaps (gaps double each time).
    Interestingly, no finite subset of {2^n : n ≥ 1} sums to exactly 1 as reciprocals,
    since ∑_{i=1}^{k} 1/2^i = 1 - 1/2^k < 1 for any finite k. -/
theorem powers_of_two_gaps_unbounded : ¬∃ C, HasUniformBoundedGaps (fun n => 2^(n+1)) C := by
  intro ⟨C, hC⟩
  -- The gap 2^{n+2} - 2^{n+1} = 2^{n+1} grows without bound
  -- Consider gap at position C: 2^{C+2} - 2^{C+1} = 2^{C+1}
  have h := hC C
  -- The gap is 2^{C+1}, which must be ≤ C by hC
  -- But 2^{C+1} > C for all C, contradiction
  have hgap : 2^(C+1+1) - 2^(C+1) = 2^(C+1) := by
    have : 2^(C+1+1) = 2 * 2^(C+1) := by ring
    omega
  have hbound : 2^(C+1+1) - 2^(C+1) ≤ C := h
  rw [hgap] at hbound
  -- Now we have 2^{C+1} ≤ C, but 2^{C+1} > C for all C
  have hlt : C + 1 < 2^(C+1) := @Nat.lt_two_pow_self (C + 1)
  omega

/-- Summary: Erdős Problem #299 is SOLVED (Answer: NO)

    Key insights:
    1. Bounded-gap sequences have positive density
    2. Positive density sets contain unit fraction sums (Bloom 2021)
    3. Therefore, no bounded-gap sequence avoids unit fraction sums

    The problem beautifully connects:
    - Arithmetic progressions and density
    - Egyptian fractions (unit fraction decompositions)
    - Additive combinatorics -/
theorem erdos_299_summary :
    (¬∃ (a : ℕ → ℕ), StrictMono a ∧ (∀ n, 0 < a n) ∧ HasBoundedGaps a ∧ AvoidsUnitFractionSum a) ∧
    (∀ A : Set ℕ, 0 ∉ A → HasPositiveUpperDensity A →
        ∃ S : Finset ℕ, ↑S ⊆ A ∧ HasUnitFractionSum S) ∧
    HasUnitFractionSum {2, 3, 6} := by
  refine ⟨erdos_299_no_such_sequence, ?_, egyptian_236⟩
  intro A h0 hdens
  exact erdos_299_density_variant A h0 hdens

end Erdos299