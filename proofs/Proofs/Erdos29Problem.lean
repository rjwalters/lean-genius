/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 388a6cbc-c62f-455a-a6cc-a71e76544f58

The following was proved by Aristotle:

- theorem economical_equiv (A : Set ℕ) : IsEconomical A ↔ IsEconomical' A

- theorem univ_not_economical : ¬IsEconomical Set.univ

- theorem squares_not_basis : ¬IsAdditiveBasis { n : ℕ | ∃ k : ℕ, n = k^2 }

- theorem sidon_not_basis (A : Set ℕ) (hS : IsSidon A) : ¬IsAdditiveBasis A

The following was negated by Aristotle:

- theorem basis_size_lower_bound (A : Set ℕ) (hA : IsAdditiveBasis A) :
    ∀ N ≥ 1, (Set.ncard (A ∩ Set.Icc 1 N) : ℝ) ≥ Real.sqrt N

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```
-/

/-
Erdős Problem #29: Explicit Economical Additive Basis

Source: https://erdosproblems.com/29
Status: SOLVED (Jain-Pham-Sawhney-Zakharov 2024)
Prize: $100

Statement:
Is there an explicit construction of a set A ⊆ ℕ such that A + A = ℕ but
1_A ∗ 1_A(n) = o(n^ε) for every ε > 0?

Meaning: Can we find an additive basis A (every natural number is a sum of two
elements from A) where the number of representations grows slower than any
polynomial?

History:
- Sidon asked Erdős this in 1932
- Erdős proved existence using probabilistic methods
- Jain, Pham, Sawhney, Zakharov (2024) gave an explicit construction

The explicit construction resolves a 90+ year old question with a concrete
algorithm rather than a probabilistic existence proof.

Reference: Jain, Pham, Sawhney, Zakharov (2024) "An explicit economical
           additive basis" arXiv:2405.08650
-/

import Mathlib


open Set Finset Nat Filter

namespace Erdos29

/-! ## Basic Definitions -/

/-- The sumset A + B = {a + b : a ∈ A, b ∈ B}. -/
def Sumset (A B : Set ℕ) : Set ℕ := { n | ∃ a ∈ A, ∃ b ∈ B, n = a + b }

notation:65 A " +ₛ " B => Sumset A B

/-- A + A for a single set. -/
def Doubling (A : Set ℕ) : Set ℕ := A +ₛ A

/-- The representation function r_A(n) = #{(a,b) ∈ A² : a + b = n}. -/
noncomputable def representationCount (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard { p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n }

/-- Alternative: count pairs (a, b) with a ≤ b and a + b = n. -/
noncomputable def orderedRepCount (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard { p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2 ∧ p.1 + p.2 = n }

/-! ## Additive Bases -/

/-- A set A is an additive basis of order 2 if A + A = ℕ. -/
def IsAdditiveBasis (A : Set ℕ) : Prop := Doubling A = Set.univ

/-- Equivalent: every n ∈ ℕ is representable as a sum of two elements from A. -/
def CoversAll (A : Set ℕ) : Prop := ∀ n : ℕ, n ∈ Doubling A

theorem additive_basis_iff (A : Set ℕ) : IsAdditiveBasis A ↔ CoversAll A := by
  unfold IsAdditiveBasis CoversAll
  constructor
  · intro h n
    rw [h]
    trivial
  · intro h
    ext n
    simp only [Set.mem_univ, iff_true]
    exact h n

/-! ## The Economical Condition -/

/-- The representation count is o(n^ε) for all ε > 0.
    This means: for all ε > 0, r_A(n) / n^ε → 0 as n → ∞. -/
def IsEconomical (A : Set ℕ) : Prop :=
  ∀ ε > 0, Tendsto (fun n => (representationCount A n : ℝ) / (n : ℝ)^ε) atTop (nhds 0)

/-- Equivalent formulation: for all ε > 0, r_A(n) = o(n^ε). -/
def IsEconomical' (A : Set ℕ) : Prop :=
  ∀ ε > 0, ∀ C > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀, (representationCount A n : ℝ) < C * (n : ℝ)^ε

theorem economical_equiv (A : Set ℕ) : IsEconomical A ↔ IsEconomical' A := by
  -- To prove the equivalence, we can use the fact that the limit definition of o(n^ε) is equivalent to the big-O definition with a constant C.
  apply Iff.intro;
  · intro h ε hε C hC;
    -- By the definition of the limit, for any ε > 0, there exists an N₀ such that for all n ≥ N₀, the ratio is less than C.
    have h_limit : ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀, (representationCount A n : ℝ) / (n : ℝ)^ε < C := by
      intro ε hε; have := h ε hε; have := this.eventually ( gt_mem_nhds hC ) ; aesop;
    exact Exists.elim ( h_limit ε hε ) fun N₀ hN₀ => ⟨ N₀ + 1, fun n hn => by have := hN₀ n ( by linarith ) ; rwa [ div_lt_iff₀ ( by norm_cast; exact pow_pos ( by linarith ) _ ) ] at this ⟩;
  · -- To prove the implication from IsEconomical' to IsEconomical, we use the fact that if for all C > 0, there exists an N₀ such that for all n ≥ N₀, r_A(n) < C * n^ε, then the limit of r_A(n) / n^ε as n approaches infinity is 0.
    intro h
    have h_lim : ∀ ε > 0, ∀ C > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀, (representationCount A n : ℝ) / (n : ℝ)^ε < C := by
      exact fun ε hε C hC => by rcases h ε hε C hC with ⟨ N₀, hN₀ ⟩ ; exact ⟨ N₀ + 1, fun n hn => by rw [ div_lt_iff₀ ( by norm_cast; exact pow_pos ( by linarith ) _ ) ] ; exact_mod_cast hN₀ n ( by linarith ) ⟩ ;
    intro ε hε; rw [ Metric.tendsto_nhds ] ; aesop;

-- Standard equivalence of limit definitions

/-! ## Erdős's Original Problem -/

/-- Erdős Problem #29: Does there exist an explicit economical additive basis? -/
def Erdos29Statement : Prop :=
  ∃ A : Set ℕ, IsAdditiveBasis A ∧ IsEconomical A

/-! ## The Probabilistic Existence (Erdős) -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry429466', 'Erdos29.erdos_probabilistic_existence']-/
/-- Erdős proved existence using probabilistic method (non-constructive). -/
axiom erdos_probabilistic_existence :
  ∃ A : Set ℕ, IsAdditiveBasis A ∧ IsEconomical A

/-! ## The Explicit Construction (JPSZ 2024) -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['Erdos29.JPSZ_set', 'harmonicSorry692634']-/
/-- The Jain-Pham-Sawhney-Zakharov construction.
    This is an explicit, computable set satisfying both conditions. -/
axiom JPSZ_set : Set ℕ

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry207162', 'Erdos29.JPSZ_is_basis']-/
/-- The JPSZ set is an additive basis. -/
axiom JPSZ_is_basis : IsAdditiveBasis JPSZ_set

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['Erdos29.JPSZ_is_economical', 'harmonicSorry299836']-/
/-- The JPSZ set is economical. -/
axiom JPSZ_is_economical : IsEconomical JPSZ_set

/-- The main theorem: Erdős Problem #29 is SOLVED. -/
theorem erdos_29_solved : Erdos29Statement :=
  ⟨JPSZ_set, JPSZ_is_basis, JPSZ_is_economical⟩

/-! ## Properties of the JPSZ Construction -/

/-- The JPSZ set has density 0. -/
def HasDensityZero (A : Set ℕ) : Prop :=
  Tendsto (fun N => (Set.ncard (A ∩ Set.Icc 1 N) : ℝ) / N) atTop (nhds 0)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry294151', 'Erdos29.JPSZ_density_zero']-/
/-- The JPSZ set has density 0 (necessary for economical bases). -/
axiom JPSZ_density_zero : HasDensityZero JPSZ_set

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry121130', 'Erdos29.JPSZ_representation_bound']-/
/-- Representation count bound: r_A(n) ≤ exp(C √(log n)) for JPSZ. -/
axiom JPSZ_representation_bound :
  ∃ C > 0, ∀ n ≥ 2, (representationCount JPSZ_set n : ℝ) ≤
    Real.exp (C * Real.sqrt (Real.log n))

/-! ## Comparison with Other Bases -/

/-- The natural numbers ℕ itself is an additive basis (trivially). -/
theorem univ_is_basis : IsAdditiveBasis Set.univ := by
  unfold IsAdditiveBasis Doubling Sumset
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_univ, true_and, iff_true]
  use 0, n
  ring

/-- But ℕ is not economical: r_ℕ(n) = n + 1. -/
theorem univ_not_economical : ¬IsEconomical Set.univ := by
  -- r_ℕ(n) = n + 1, which is not o(n^ε) for ε < 1
  -- This leads to contradiction since n+1 doesn't go to 0 when divided by n^(1/2)
  unfold Erdos29.IsEconomical;
  push_neg;
  use 1;
  -- Let's simplify the expression for the representation count.
  have h_rep_count : ∀ n : ℕ, n > 0 → Erdos29.representationCount Set.univ n = n + 1 := by
    intros n hn_pos
    have h_rep_count : {p : ℕ × ℕ | p.1 ∈ Set.univ ∧ p.2 ∈ Set.univ ∧ p.1 + p.2 = n} = Finset.image (fun k => (k, n - k)) (Finset.range (n + 1)) := by
      ext ⟨x, y⟩; simp [Finset.mem_image];
      exact ⟨ fun h => ⟨ by linarith, by omega ⟩, fun h => by omega ⟩;
    rw [ Erdos29.representationCount, h_rep_count, Set.ncard_coe_finset, Finset.card_image_of_injective ] <;> aesop_cat;
  rw [ Filter.tendsto_congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ h_rep_count n hn ] ) ] ; norm_num [ add_div, div_self, ne_of_gt ];
  exact fun h => absurd ( tendsto_nhds_unique h ( Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with n hn; aesop ) ) ( tendsto_inverse_atTop_nhds_zero_nat ) ) ) ( by norm_num )

/-- The squares are not an additive basis (not every n is sum of two squares). -/
theorem squares_not_basis : ¬IsAdditiveBasis { n : ℕ | ∃ k : ℕ, n = k^2 } := by
  intro h
  -- 3 is not a sum of two squares
  have : (3 : ℕ) ∈ Doubling { n : ℕ | ∃ k : ℕ, n = k^2 } := by
    rw [additive_basis_iff] at h
    exact h 3
  unfold Doubling Sumset at this
  simp only [Set.mem_setOf_eq] at this
  obtain ⟨a, ⟨ka, hka⟩, b, ⟨kb, hkb⟩, hab⟩ := this
  -- 3 cannot be written as sum of two squares
  -- The squares ≤ 3 are 0 and 1, and no combination sums to 3
  subst_vars; have := Nat.le_of_lt_succ ( show ka < 3 by nlinarith only [ hab ] ) ; have := Nat.le_of_lt_succ ( show kb < 3 by nlinarith only [ hab ] ) ; interval_cases ka <;> interval_cases kb <;> trivial;

/-! ## Thin Bases and Sidon Sets -/

/-- A Sidon set has at most one representation for each sum (r_A(n) ≤ 2). -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ n : ℕ, orderedRepCount A n ≤ 1

/-- No Sidon set can be an additive basis.
    (Sidon sets are too thin to cover all of ℕ.) -/
theorem sidon_not_basis (A : Set ℕ) (hS : IsSidon A) : ¬IsAdditiveBasis A := by
  -- A Sidon set has |A ∩ [1,N]| ≤ √N + O(1)
  -- So A + A has at most N + O(√N) elements in [1, 2N]
  -- Therefore A + A ≠ ℕ
  -- Assume A is a Sidon set and an additive basis.
  by_contra h_contra
  have h_zero : 0 ∈ A := by
    unfold Erdos29.IsAdditiveBasis at h_contra;
    simp_all +decide [ Set.ext_iff, Erdos29.Doubling ];
    obtain ⟨ a, ha, b, hb, hab ⟩ := h_contra 0;
    grind +ring
  have h_one : 1 ∈ A := by
    -- Since $A$ is an additive basis, $1$ must be representable as a sum of two elements from $A$.
    have h_one_representable : ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ a + b = 1 := by
      exact h_contra.symm.subset ( Set.mem_univ 1 ) |> Exists.imp fun x hx => by aesop;
    rcases h_one_representable with ⟨ a, b, ha, hb, hab ⟩ ; rcases a with ( _ | _ | a ) <;> rcases b with ( _ | _ | b ) <;> simp_all +arith +decide only;
  have h_two : 2 ∉ A := by
    -- By definition of Sidon set, since $2 = 1 + 1$ and $2 = 0 + 2$, the ordered representations $(1, 1)$ and $(0, 2)$ must be distinct.
    have h_distinct : orderedRepCount A 2 ≤ 1 := by
      exact hS 2;
    contrapose! h_distinct;
    -- By definition of orderedRepCount, we need to show that there are at least two pairs (a, b) in A × A such that a + b = 2 and a ≤ b.
    have h_ordered : {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2 ∧ p.1 + p.2 = 2} ⊇ {(0, 2), (1, 1)} := by
      rintro p ( rfl | rfl ) <;> simp +decide [ * ];
    have h_card : Set.ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2 ∧ p.1 + p.2 = 2} ≥ Set.ncard ({(0, 2), (1, 1)} : Set (ℕ × ℕ)) := by
      apply_rules [ Set.ncard_le_ncard ];
      exact Set.finite_iff_bddAbove.mpr ⟨ ⟨ 2, 2 ⟩, by rintro ⟨ a, b ⟩ ⟨ ha, hb, hab, h ⟩ ; exact ⟨ by linarith, by linarith ⟩ ⟩;
    exact lt_of_lt_of_le ( by norm_num ) h_card
  have h_three : 3 ∈ A := by
    -- Since A is an additive basis, 3 must be in A + A.
    have h_three_in_sumset : 3 ∈ Erdos29.Doubling A := by
      exact h_contra.symm.subset ( Set.mem_univ _ );
    obtain ⟨ a, ha, b, hb, hab ⟩ := h_three_in_sumset;
    rcases a with ( _ | _ | a ) <;> rcases b with ( _ | _ | b ) <;> simp_all +arith +decide only;
    · aesop;
    · aesop;
    · aesop;
    · subst hab; aesop;
  have h_four : 4 ∉ A := by
    have := hS 4; simp_all +decide [ Erdos29.IsSidon, Erdos29.orderedRepCount ] ;
    exact fun h_four => absurd ( hS 4 ) ( by erw [ show { p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2 ∧ p.1 + p.2 = 4 } = { ( 1, 3 ), ( 0, 4 ) } by ext ⟨ x, y ⟩ ; rcases x with ( _ | _ | _ | _ | x ) <;> rcases y with ( _ | _ | _ | _ | y ) <;> simp_all +arith +decide ] ; simp +decide )
  have h_five : 5 ∈ A := by
    -- Consider $n=5$. Since $A$ is an additive basis, there exist $a, b \in A$ such that $a + b = 5$.
    obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ a + b = 5 := by
      exact h_contra.symm.subset ( Set.mem_univ 5 ) |> fun ⟨ a, ha, b, hb, hab ⟩ => ⟨ a, b, ha, hb, hab ▸ rfl ⟩;
    rcases a with ( _ | _ | _ | _ | _ | a ) <;> rcases b with ( _ | _ | _ | _ | _ | b ) <;> simp_all +arith +decide only
  have h_six : 6 ∉ A := by
    -- By definition of a Sidon set, there should be at most one pair (a, b) in A × A such that a + b = 6.
    have h_unique_pair : ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A → a + b = 6 → c + d = 6 → (a ≤ b ∧ c ≤ d) → (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
      intro a b c d ha hb hc hd hab hcd h
      have h_card : Set.ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2 ∧ p.1 + p.2 = 6} ≤ 1 := by
        exact hS 6;
      cases h_card.eq_or_lt <;> simp_all +decide [ Set.ncard_eq_toFinset_card' ];
      · simp_all +decide [ Set.eq_singleton_iff_unique_mem ];
        grind;
      · rw [ @Set.ncard_eq_zero ] at *;
        · simp_all +decide [ Set.ext_iff ];
        · exact Set.finite_iff_bddAbove.mpr ⟨ ⟨ 6, 6 ⟩, by rintro ⟨ x, y ⟩ ⟨ hx, hy, hxy, h ⟩ ; exact ⟨ by linarith, by linarith ⟩ ⟩;
    specialize h_unique_pair 1 5 3 3 ; simp_all +decide;
  -- Consider the number 6. We have 6 = 1 + 5 and 6 = 3 + 3. Both representations are valid since 1, 5, 3 ∈ A. This contradicts the Sidon property (count ≤ 1).
  have h_six_representations : orderedRepCount A 6 ≥ 2 := by
    -- Let's count the number of pairs (a, b) in A such that a + b = 6 and a ≤ b.
    have h_pairs : {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2 ∧ p.1 + p.2 = 6} ⊇ {(1, 5), (3, 3)} := by
      norm_num [ Set.insert_subset_iff, h_one, h_three, h_five ];
    have h_card : Set.ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2 ∧ p.1 + p.2 = 6} ≥ Set.ncard ({(1, 5), (3, 3)} : Set (ℕ × ℕ)) := by
      apply_rules [ Set.ncard_le_ncard ];
      exact Set.finite_iff_bddAbove.mpr ⟨ ⟨ 6, 6 ⟩, by rintro ⟨ a, b ⟩ ⟨ ha, hb, hab, h ⟩ ; exact ⟨ by linarith, by linarith ⟩ ⟩;
    exact h_card.trans' ( by norm_num );
  exact h_six_representations.not_lt ( lt_of_le_of_lt ( hS 6 ) ( by norm_num ) )

/- The JPSZ construction is a "middle ground":
   - Not as thin as Sidon sets (which can't be bases)
   - Not as thick as ℕ (which isn't economical)
   - Just right: basis with subpolynomial representations -/

/-! ## Explicit vs Probabilistic -/

/-- A set is "explicit" if it's computable/constructive. -/
class ExplicitSet (A : Set ℕ) where
  membership_decidable : DecidablePred (· ∈ A)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry13003', 'Erdos29.JPSZ_explicit']-/
/-- The JPSZ set is explicit (has a constructive definition). -/
axiom JPSZ_explicit : ExplicitSet JPSZ_set

/- This distinguishes JPSZ from Erdős's probabilistic proof:
   - Erdős: ∃ A with properties (non-constructive)
   - JPSZ: Here is A explicitly (constructive) -/

/-! ## Historical Context

The problem originated in 1932 when Sidon asked Erdős.

Erdős's probabilistic argument:
Take each n ∈ A with probability p_n = n^{-1/2 + o(1)}.
Then with positive probability, A is both a basis and economical.

Why explicit matters:
1. Algorithmic applications (can compute A ∩ [1,N])
2. Mathematical insight into structure
3. Resolves 90+ year old open problem completely -/

/-! ## Lower Bounds -/

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

/-
There exists a set A that is an additive basis but violates the square root lower bound for N=2.
-/
def CounterexampleA : Set ℕ := {0, 1} ∪ {n | 3 ≤ n}

theorem counterexample_to_lower_bound :
    ∃ A, IsAdditiveBasis A ∧ ∃ N ≥ 1, (Set.ncard (A ∩ Set.Icc 1 N) : ℝ) < Real.sqrt N := by
  use CounterexampleA
  constructor
  · -- A is an additive basis
    rw [IsAdditiveBasis, Doubling, Sumset]
    ext n
    simp only [Set.mem_univ, iff_true, Set.mem_setOf_eq]
    -- Show n = a + b
    -- Consider two cases: $n \leq 1$ or $n \geq 2$.
    by_cases hn : n ≤ 1;
    · interval_cases n <;> [ exact ⟨ 0, by norm_num [ Erdos29.CounterexampleA ], 0, by norm_num [ Erdos29.CounterexampleA ], rfl ⟩ ; exact ⟨ 1, by norm_num [ Erdos29.CounterexampleA ], 0, by norm_num [ Erdos29.CounterexampleA ], rfl ⟩ ];
    · -- Since $n > 1$, we have $n \geq 3$ or $n = 2$.
      by_cases hn3 : n ≥ 3;
      · use n, by
          exact Or.inr hn3, 0, by
          exact Or.inl <| by norm_num;
        norm_num;
      · interval_cases n ; exists 1, by simp +decide [ Erdos29.CounterexampleA ], 1, by simp +decide [ Erdos29.CounterexampleA ] ;
  · -- Inequality fails for N=2
    use 2
    constructor
    · norm_num
    · -- |A ∩ [1, 2]| < √2
      rw [CounterexampleA]
      rw [ show ( { 0, 1 } ∪ { n | 3 ≤ n } : Set ℕ ) ∩ Set.Icc 1 2 = { 1 } by ext ( _ | _ | _ | k ) <;> simp +arith +decide ] ; norm_num [ Real.lt_sqrt ]

end AristotleLemmas

/-
Any additive basis A must have |A ∩ [1,N]| ≥ √N.
-/
theorem basis_size_lower_bound (A : Set ℕ) (hA : IsAdditiveBasis A) :
    ∀ N ≥ 1, (Set.ncard (A ∩ Set.Icc 1 N) : ℝ) ≥ Real.sqrt N := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Apply the theorem counterexample_to_lower_bound to obtain the existence of A and N.
  apply counterexample_to_lower_bound

-/
/-- Any additive basis A must have |A ∩ [1,N]| ≥ √N. -/
theorem basis_size_lower_bound (A : Set ℕ) (hA : IsAdditiveBasis A) :
    ∀ N ≥ 1, (Set.ncard (A ∩ Set.Icc 1 N) : ℝ) ≥ Real.sqrt N := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry153138', 'Erdos29.JPSZ_size_optimal']-/
/-- The JPSZ construction is essentially optimal in size. -/
axiom JPSZ_size_optimal :
  ∃ C > 0, ∀ N ≥ 1, (Set.ncard (JPSZ_set ∩ Set.Icc 1 N) : ℝ) ≤
    C * Real.sqrt N * Real.sqrt (Real.log N)

/-! ## Summary

**Problem Status: SOLVED**

Erdős Problem #29 asked for an explicit construction of an additive basis A
(A + A = ℕ) where the representation function r_A(n) = o(n^ε) for all ε > 0.

**Answer: YES** (Jain-Pham-Sawhney-Zakharov 2024)

**Historical Journey:**
- 1932: Sidon asks Erdős the question
- ~1950s: Erdős proves existence using probabilistic methods
- 2024: JPSZ provide an explicit construction

**Significance:**
- Transforms existence proof into constructive algorithm
- 90+ years from question to complete answer
- Demonstrates power of modern combinatorics

**Key Properties of JPSZ Set:**
- Explicit and computable
- A + A = ℕ (additive basis)
- r_A(n) ≤ exp(C√(log n)) (economical)
- |A ∩ [1,N]| ≈ √N · √(log N) (optimal size)

References:
- Jain, Pham, Sawhney, Zakharov (2024): arXiv:2405.08650
- Erdős: Original probabilistic proof
- Sidon (1932): Original question
-/

end Erdos29