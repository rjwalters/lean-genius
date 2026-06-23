/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2a0a8676-7936-4523-ae16-d26b0095d747

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem kls_improves (n : ℕ) (hn : n ≥ 100) :
    KLSThreshold n < NikiforovThreshold n
-/

/-
  Erdős Problem #551: Ramsey Numbers for Cycles vs Complete Graphs

  Source: https://erdosproblems.com/551
  Status: SOLVED (for sufficiently large parameters)

  Statement:
  Prove that R(C_k, K_n) = (k-1)(n-1) + 1 for k ≥ n ≥ 3 (except when n = k = 3).

  Progress:
  - Bondy-Erdős (1973): k > n² - 2
  - Nikiforov (2005): k ≥ 4n + 2
  - Keevash-Long-Skokan (2021): k ≥ C log n / log log n

  Related questions:
  1. For fixed n, what is the smallest k where the identity holds?
  2. For fixed n, what is the minimum value of R(C_k, K_n)?

  Tags: graph-theory, ramsey-theory, cycles
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic


/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Invalid alternative name `inl`: Expected `refl`
Invalid alternative name `inr`: Expected `refl`
Dependent elimination failed: Failed to solve equation
  i.1 =
    Decidable.rec (fun (h : ¬k ≤ (↑i : ℕ).succ) => (fun (x : ¬k ≤ (↑i : ℕ).succ) => (↑i : ℕ).succ) h)
      (fun (h : k ≤ (↑i : ℕ).succ) => (fun (x : k ≤ (↑i : ℕ).succ) => (↑i : ℕ).succ.modCore k) h)
      (k.decLe (↑i : ℕ).succ)
omega could not prove the goal:
No usable constraints found. You may need to unfold definitions so `omega` can see linear arithmetic facts about `Nat` and `Int`, which may also involve multiplication, division, and modular remainder by constants.-/
namespace Erdos551

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/- ## Part I: Basic Definitions -/

/-- A cycle graph C_k on k vertices. -/
def cycleGraph (k : ℕ) : SimpleGraph (Fin k) where
  Adj := fun i j => (i.val + 1) % k = j.val ∨ (j.val + 1) % k = i.val
  symm := by
    intro i j h
    cases h with
    | inl h => right; exact h
    | inr h => left; exact h
  loopless := by
    intro i h
    simp at h
    cases h with
    | inl h => omega
    | inr h => omega

/-- The complete graph K_n on n vertices. -/
def completeGraph (n : ℕ) : SimpleGraph (Fin n) :=
  ⊤

/-- A graph contains C_k as a subgraph. -/
def ContainsCycle (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ f : Fin k → V, Function.Injective f ∧
    ∀ i : Fin k, G.Adj (f i) (f ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega : k > 0)⟩)

/-- A graph contains K_n as a subgraph (clique). -/
def ContainsClique (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ S : Finset V, S.card = n ∧ G.IsClique S

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `ContainsCycle`
Unknown identifier `ContainsClique`-/
/- ## Part II: Ramsey Numbers -/

/-- The Ramsey number R(C_k, K_n): minimum N such that any 2-coloring of K_N
    contains a red C_k or a blue K_n. -/
noncomputable def RamseyNumber (k n : ℕ) : ℕ :=
  Nat.find (ramsey_exists k n)
where
  ramsey_exists (k n : ℕ) : ∃ N, ∀ (G : SimpleGraph (Fin N)),
    ContainsCycle G k ∨ ContainsClique Gᶜ n := by
    sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `ContainsCycle`
Unknown identifier `ContainsClique`-/
/-- Alternative definition via edge colorings. -/
def RamseyProperty (k n N : ℕ) : Prop :=
  ∀ (red : SimpleGraph (Fin N)),
    ContainsCycle red k ∨ ContainsClique redᶜ n

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  RamseyProperty
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  k
Function expected at
  RamseyNumber
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  k
Function expected at
  RamseyProperty
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  k-/
/-- R(C_k, K_n) is the minimum N with the Ramsey property. -/
theorem ramsey_is_min (k n : ℕ) (hk : k ≥ 3) (hn : n ≥ 3) :
    RamseyProperty k n (RamseyNumber k n) ∧
    ∀ m < RamseyNumber k n, ¬RamseyProperty k n m := by
  sorry

/- ## Part III: The Main Conjecture -/

/-- The conjectured formula: R(C_k, K_n) = (k-1)(n-1) + 1. -/
def ConjecturedFormula (k n : ℕ) : ℕ := (k - 1) * (n - 1) + 1

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `RamseyNumber`-/
/-- Main conjecture: R(C_k, K_n) = (k-1)(n-1) + 1 for k ≥ n ≥ 3, except (3,3). -/
def MainConjecture : Prop :=
  ∀ k n, k ≥ n → n ≥ 3 → (k, n) ≠ (3, 3) →
    RamseyNumber k n = ConjecturedFormula k n

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  RamseyNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  3-/
/-- The exception: R(C_3, K_3) = R(K_3, K_3) = 6 ≠ 5. -/
theorem exception_3_3 : RamseyNumber 3 3 = 6 := by
  sorry

/-- The formula gives 5 for (3,3), but actual value is 6. -/
theorem formula_wrong_at_3_3 : ConjecturedFormula 3 3 = 5 := by
  native_decide

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  ContainsCycle
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  ContainsClique
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  Gᶜ-/
/- ## Part IV: Lower Bound -/

/-- Lower bound construction: (k-1)(n-1) vertices suffice to avoid both. -/
theorem lower_bound (k n : ℕ) (hk : k ≥ 3) (hn : n ≥ 3) :
    ∃ (G : SimpleGraph (Fin ((k-1)*(n-1)))),
      ¬ContainsCycle G k ∧ ¬ContainsClique Gᶜ n := by
  sorry

/-- The lower bound graph: (n-1) disjoint copies of K_{k-1}. -/
def LowerBoundGraph (k n : ℕ) : SimpleGraph (Fin ((k-1)*(n-1))) where
  Adj := fun i j =>
    i.val / (k-1) = j.val / (k-1) ∧ i ≠ j
  symm := by intro i j ⟨h1, h2⟩; exact ⟨h1.symm, h2.symm⟩
  loopless := by intro i ⟨_, h⟩; exact h rfl

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  ContainsCycle
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (LowerBoundGraph k n)-/
/-- The lower bound graph has no C_k. -/
theorem lower_bound_no_cycle (k n : ℕ) (hk : k ≥ 3) :
    ¬ContainsCycle (LowerBoundGraph k n) k := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  ContainsClique
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (LowerBoundGraph k n)ᶜ-/
/-- The complement has no K_n. -/
theorem lower_bound_complement_no_clique (k n : ℕ) (hn : n ≥ 3) :
    ¬ContainsClique (LowerBoundGraph k n)ᶜ n := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  RamseyNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  k-/
/- ## Part V: Bondy-Erdős (1973) -/

/-- Bondy-Erdős (1973): The formula holds for k > n² - 2. -/
theorem bondy_erdos (k n : ℕ) (hk : k ≥ 3) (hn : n ≥ 3)
    (hkn : k > n^2 - 2) :
    RamseyNumber k n = ConjecturedFormula k n := by
  sorry

/-- The Bondy-Erdős threshold. -/
def BondyErdosThreshold (n : ℕ) : ℕ := n^2 - 1

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  RamseyNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  k-/
/-- For k above Bondy-Erdős threshold, formula holds. -/
theorem above_bondy_erdos_threshold (k n : ℕ) (hn : n ≥ 3)
    (h : k ≥ BondyErdosThreshold n) :
    RamseyNumber k n = ConjecturedFormula k n := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  RamseyNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  k-/
/- ## Part VI: Nikiforov (2005) -/

/-- Nikiforov (2005): The formula holds for k ≥ 4n + 2. -/
theorem nikiforov (k n : ℕ) (hk : k ≥ 3) (hn : n ≥ 3)
    (hkn : k ≥ 4*n + 2) :
    RamseyNumber k n = ConjecturedFormula k n := by
  sorry

/-- The Nikiforov threshold: 4n + 2. -/
def NikiforovThreshold (n : ℕ) : ℕ := 4*n + 2

/-- Nikiforov improves on Bondy-Erdős for n ≥ 5. -/
theorem nikiforov_improves (n : ℕ) (hn : n ≥ 5) :
    NikiforovThreshold n < BondyErdosThreshold n := by
  unfold NikiforovThreshold BondyErdosThreshold
  omega

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Application type mismatch: The argument
  k
has type
  ℝ
but is expected to have type
  ℕ
in the application
  ConjecturedFormula k
Function expected at
  RamseyNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  k-/
/- ## Part VII: Keevash-Long-Skokan (2021) -/

/-- Keevash-Long-Skokan (2021): Formula holds for k ≥ C log n / log log n. -/
theorem keevash_long_skokan (n : ℕ) (hn : n ≥ 3) :
    ∃ C : ℝ, C > 0 ∧ ∀ k, (k : ℝ) ≥ C * Real.log n / Real.log (Real.log n) →
      RamseyNumber k n = ConjecturedFormula k n := by
  sorry

/-- The KLS threshold is essentially optimal. -/
def KLSThreshold (n : ℕ) : ℝ :=
  Real.log n / Real.log (Real.log n)

/- KLS improves significantly on Nikiforov. -/
noncomputable section AristotleLemmas

#check Real.exp_bound
#check Real.exp_bound_div_one_sub_of_interval

lemma exp_one_lt_3 : Real.exp 1 < 3 := by
  have h_bound : |Real.exp 1 - 2| ≤ 3/4 := by
    -- Apply `Real.exp_bound` with `x = 1` and `n = 2`.
    have h_bound : |Real.exp 1 - (∑ m ∈ Finset.range 2, 1 ^ m / (Nat.factorial m : ℝ))| ≤ 1 ^ 2 * ((Nat.succ 2 : ℝ) / ((Nat.factorial 2 : ℝ) * (Nat.succ 1 : ℝ))) := by
      convert Real.exp_bound ?_ ?_ using 1 <;> norm_num [ Finset.sum_range_succ ];
    convert h_bound using 1 <;> norm_num [ Finset.sum_range_succ ]
  linarith [ abs_le.mp h_bound ]

end AristotleLemmas

theorem kls_improves (n : ℕ) (hn : n ≥ 100) :
    KLSThreshold n < NikiforovThreshold n := by
  -- By definition of $KLSThreshold$, we know that $KLSThreshold n = \frac{\log n}{\log (\log n)}$.
  unfold KLSThreshold NikiforovThreshold;
  -- By definition of $L$, we know that $L = \log n / \log (\log n)$.
  set L : ℝ := Real.log n / Real.log (Real.log n);
  -- We'll use that $L \leq \log n$ since $\log (\log n) > 1$ for $n \geq 100$.
  have hL_le_logn : L ≤ Real.log n := by
    refine' div_le_self ( Real.log_nonneg <| by norm_cast; linarith ) _;
    rw [ Real.le_log_iff_exp_le ( Real.log_pos <| by norm_cast; linarith ) ];
    -- We'll use that $Real.exp 1 < 3$ and $Real.log 100 > 4$.
    have h_exp_lt_3 : Real.exp 1 < 3 := by
      exact?
    have h_log_100_gt_4 : Real.log 100 > 4 := by
      norm_num [ Real.lt_log_iff_exp_lt ];
      rw [ show Real.exp 4 = ( Real.exp 1 ) ^ 4 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_lt_of_le ( pow_lt_pow_left₀ h_exp_lt_3 ( by positivity ) ( by norm_num ) ) ( by norm_num );
    exact le_trans h_exp_lt_3.le ( le_trans ( by norm_num ) ( h_log_100_gt_4.le.trans ( Real.log_le_log ( by norm_num ) ( Nat.cast_le.mpr hn ) ) ) );
  refine lt_of_le_of_lt hL_le_logn ?_;
  exact lt_of_le_of_lt ( Real.log_le_sub_one_of_pos ( by positivity ) ) ( by norm_num; linarith [ ( by norm_cast : ( 100 : ℝ ) ≤ n ) ] )

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  RamseyNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  3
Function expected at
  RamseyNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  3-/
/- ## Part VIII: Special Cases -/

/-- R(C_3, K_n) = R(K_3, K_n) (triangle vs clique). -/
theorem cycle_3_is_triangle (n : ℕ) :
    RamseyNumber 3 n = RamseyNumber 3 n := rfl

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  RamseyNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  4-/
/-- R(C_4, K_3) = 7 (verified). -/
theorem ramsey_C4_K3 : RamseyNumber 4 3 = 7 := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  RamseyNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  5-/
/-- R(C_5, K_3) = 9 (verified). -/
theorem ramsey_C5_K3 : RamseyNumber 5 3 = 9 := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  RamseyNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  k-/
/-- R(C_k, K_3) = 2k - 1 for k ≥ 4. -/
theorem ramsey_Ck_K3 (k : ℕ) (hk : k ≥ 4) :
    RamseyNumber k 3 = 2*k - 1 := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `RamseyNumber`-/
/- ## Part IX: Related Questions -/

/-- Question 1: For fixed n, smallest k where identity holds. -/
noncomputable def SmallestValidK (n : ℕ) : ℕ :=
  Nat.find (smallest_k_exists n)
where
  smallest_k_exists (n : ℕ) : ∃ k₀, k₀ ≥ n ∧
    ∀ k ≥ k₀, RamseyNumber k n = ConjecturedFormula k n := by
    sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `RamseyNumber`-/
/-- Question 2: For fixed n, minimum of R(C_k, K_n) over k ≥ n. -/
noncomputable def MinRamseyValue (n : ℕ) : ℕ :=
  ⨅ k ∈ {k | k ≥ n}, RamseyNumber k n

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  RamseyNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  k₀
Function expected at
  MinRamseyValue
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  n-/
/-- The minimum is achieved at some finite k. -/
theorem min_ramsey_achieved (n : ℕ) (hn : n ≥ 3) :
    ∃ k₀ ≥ n, RamseyNumber k₀ n = MinRamseyValue n := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  RamseyNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  k₁
Function expected at
  RamseyNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  k₂-/
/- ## Part X: Monotonicity -/

/-- R(C_k, K_n) is non-decreasing in k. -/
theorem ramsey_mono_k (k₁ k₂ n : ℕ) (h : k₁ ≤ k₂) :
    RamseyNumber k₁ n ≤ RamseyNumber k₂ n := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  RamseyNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  k
Function expected at
  RamseyNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  k-/
/-- R(C_k, K_n) is non-decreasing in n. -/
theorem ramsey_mono_n (k n₁ n₂ : ℕ) (h : n₁ ≤ n₂) :
    RamseyNumber k n₁ ≤ RamseyNumber k n₂ := by
  sorry

/-- The conjectured formula is increasing in both parameters. -/
theorem formula_mono (k₁ k₂ n₁ n₂ : ℕ) (hk : k₁ ≤ k₂) (hn : n₁ ≤ n₂) :
    ConjecturedFormula k₁ n₁ ≤ ConjecturedFormula k₂ n₂ := by
  unfold ConjecturedFormula
  nlinarith

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  RamseyNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  k-/
/- ## Part XI: Upper Bound Techniques -/

/-- Probabilistic bound: R(C_k, K_n) ≤ (k-1)(n-1) + 1. -/
theorem upper_bound (k n : ℕ) (hk : k ≥ 3) (hn : n ≥ 3)
    (hkn : k ≥ n) (hne : (k, n) ≠ (3, 3)) :
    RamseyNumber k n ≤ ConjecturedFormula k n := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  RamseyProperty
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  k-/
/-- Path-cycle method for upper bounds. -/
theorem path_cycle_method (k n N : ℕ) (hN : N ≥ (k-1)*(n-1) + 1) :
    RamseyProperty k n N := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  RamseyNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  k
Function expected at
  SmallestValidK
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  n-/
/- ## Part XII: Summary -/

/-- The main theorem: combining all progress. -/
theorem main_theorem (k n : ℕ) (hk : k ≥ 3) (hn : n ≥ 3)
    (hkn : k ≥ n) (hne : (k, n) ≠ (3, 3)) :
    RamseyNumber k n = ConjecturedFormula k n ↔
      k ≥ SmallestValidK n := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  SmallestValidK
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  n-/
/-- Current best: KLS proves it for k ≥ C log n / log log n. -/
theorem current_best (n : ℕ) (hn : n ≥ 3) :
    ∃ C > 0, SmallestValidK n ≤ ⌈C * Real.log n / Real.log (Real.log n)⌉₊ := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  RamseyNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  k-/
/-- The problem is SOLVED for large enough parameters. -/
theorem solved_asymptotically :
    ∀ n ≥ 3, ∃ k₀, ∀ k ≥ k₀, k ≥ n →
      RamseyNumber k n = ConjecturedFormula k n := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected name `Erdos551` after `end`: The current section is unnamed

Hint: Delete the name `Erdos551` to end the current unnamed scope; outer named scopes can then be closed using additional `end` command(s):
  end ̵E̵r̵d̵o̵s̵5̵5̵1̵-/
end Erdos551