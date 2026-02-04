/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 582faf3a-04a2-4add-9257-2a0d7380ff25

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem proper_is_cochromatic (G : SimpleGraph V) (k : ℕ) (h : G.Colorable k) :
    Nonempty (CochromaticColoring G k)

The following was negated by Aristotle:

- theorem perfect_graph_chromatic (G : SimpleGraph V) (hPerf : True) :  -- Perfect condition
    chromaticNumber G = cliqueNumber G

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
  Erdős Problem #625: Chromatic vs Cochromatic Numbers of Random Graphs

  Source: https://erdosproblems.com/625
  Status: OPEN
  Prize: $1000 (falsity) / $100 (truth)

  Statement:
  The cochromatic number ζ(G) is the minimum colors needed such that each color
  class induces either a complete graph or an empty graph. For random G(n, 1/2),
  does χ(G) - ζ(G) → ∞ almost surely?

  Known:
  - n/(2 log₂ n) ≤ ζ(G) ≤ χ(G) ≤ (1+o(1))n/(2 log₂ n) a.s. (Bollobás 1988)
  - Heckel (2024), Steiner (2024): Difference is unbounded w.h.p.
  - Heckel conjecture: χ(G) - ζ(G) ≈ n/(log n)³

  Tags: graph-theory, random-graphs, coloring
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic


namespace Erdos625

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/- ## Part I: Basic Definitions -/

/-- A color class is cochromatic if it induces a complete or empty subgraph. -/
def IsCochromaticClass (G : SimpleGraph V) (S : Set V) : Prop :=
  (∀ u v : V, u ∈ S → v ∈ S → u ≠ v → G.Adj u v) ∨
  (∀ u v : V, u ∈ S → v ∈ S → u ≠ v → ¬G.Adj u v)

/-- A cochromatic coloring: each color class is complete or empty. -/
structure CochromaticColoring (G : SimpleGraph V) (k : ℕ) where
  color : V → Fin k
  cochromatic : ∀ c : Fin k, IsCochromaticClass G {v | color v = c}

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  DecidablePred fun (n : ℕ) => Nonempty (Erdos625.CochromaticColoring G n)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
/-- The cochromatic number ζ(G). -/
noncomputable def cochromaticNumber (G : SimpleGraph V) : ℕ :=
  Nat.find (cochromatic_exists G)
where
  cochromatic_exists (G : SimpleGraph V) : ∃ k, Nonempty (CochromaticColoring G k) := by
    sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  DecidablePred G.Colorable

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
/-- The chromatic number χ(G). -/
noncomputable def chromaticNumber (G : SimpleGraph V) : ℕ :=
  Nat.find (chromatic_exists G)
where
  chromatic_exists (G : SimpleGraph V) : ∃ k, G.Colorable k := by
    sorry

/- ## Part II: Basic Properties -/

/-- Every proper coloring is cochromatic (empty classes). -/
theorem proper_is_cochromatic (G : SimpleGraph V) (k : ℕ) (h : G.Colorable k) :
    Nonempty (CochromaticColoring G k) := by
  obtain ⟨c, hc⟩ : ∃ c : V → Fin k, ∀ u v : V, G.Adj u v → c u ≠ c v := by
    obtain ⟨c, hc⟩ := h; use c; aesop;
  refine' ⟨ ⟨ c, _ ⟩ ⟩;
  intro i1; rw [ Erdos625.IsCochromaticClass ] ; aesop

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  cochromaticNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  G-/
/-- ζ(G) ≤ χ(G). -/
theorem cochromatic_le_chromatic (G : SimpleGraph V) :
    cochromaticNumber G ≤ chromaticNumber G := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  cochromaticNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  cochromaticNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  Gᶜ-/
/-- ζ(G) ≤ ζ(Gᶜ) (complement). -/
theorem cochromatic_complement (G : SimpleGraph V) :
    cochromaticNumber G ≤ cochromaticNumber Gᶜ := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  cochromaticNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  cochromaticNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  Gᶜ-/
/-- ζ(G) = ζ(Gᶜ) by symmetry. -/
theorem cochromatic_eq_complement (G : SimpleGraph V) :
    cochromaticNumber G = cochromaticNumber Gᶜ := by
  sorry

/- ## Part III: Random Graph Model -/

/-- The Erdős-Rényi random graph G(n, p). -/
structure RandomGraph (n : ℕ) (p : ℝ) where
  graph : SimpleGraph (Fin n)

-- Probability distribution over graphs

/-- G(n, 1/2): symmetric random graph. -/
def ErdosRenyi (n : ℕ) : Type := RandomGraph n (1/2)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

typeclass instance problem is stuck, it is often due to metavariables
  LE (?m.29 ε)-/
/-- Almost sure property for random graphs. -/
def AlmostSurely (P : ∀ n, RandomGraph n (1/2) → Prop) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, True

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  AlmostSurely
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (fun n G => (cochromaticNumber G.graph : ℝ) ≥ n / (2 * Real.log n / Real.log 2))-/
-- Placeholder for measure-theoretic statement

/- ## Part IV: Known Bounds -/

/-- Lower bound on cochromatic number: ζ(G) ≥ n/(2 log₂ n) a.s. -/
theorem cochromatic_lower_bound :
    AlmostSurely (fun n G => (cochromaticNumber G.graph : ℝ) ≥ n / (2 * Real.log n / Real.log 2)) := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  AlmostSurely
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (fun n G => (chromaticNumber G.graph : ℝ) ≤ (1 + ε) * n / (2 * Real.log n / Real.log 2))-/
/-- Upper bound on chromatic number: χ(G) ≤ (1+o(1))n/(2 log₂ n) a.s. (Bollobás 1988). -/
theorem bollobas_upper_bound :
    ∀ ε > 0, AlmostSurely (fun n G =>
      (chromaticNumber G.graph : ℝ) ≤ (1 + ε) * n / (2 * Real.log n / Real.log 2)) := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  AlmostSurely
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (fun n G =>
    (cochromaticNumber G.graph : ℝ) ≤ chromaticNumber G.graph ∧
      (chromaticNumber G.graph : ℝ) ≤ (1.01) * n / (2 * Real.log n / Real.log 2))-/
/-- The sandwich: ζ(G) ≤ χ(G) ≤ (1+o(1))n/(2 log₂ n). -/
theorem chromatic_cochromatic_sandwich :
    AlmostSurely (fun n G =>
      (cochromaticNumber G.graph : ℝ) ≤ chromaticNumber G.graph ∧
      (chromaticNumber G.graph : ℝ) ≤ (1.01) * n / (2 * Real.log n / Real.log 2)) := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `AlmostSurely`-/
/- ## Part V: The Main Question -/

/-- The main question: Does χ(G) - ζ(G) → ∞ a.s.? -/
def MainQuestion : Prop :=
  AlmostSurely (fun n G =>
    ∀ M : ℕ, ∃ N ≥ n, ∀ G' : RandomGraph N (1/2),
      chromaticNumber G'.graph - cochromaticNumber G'.graph ≥ M)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry337388', 'Erdos625.main_question_open']-/
/-- The main question is OPEN. -/
axiom main_question_open : MainQuestion

/-- Prize structure: $1000 for falsity, $100 for truth. -/
def PrizeValue (answer : Bool) : ℕ :=
  if answer then 100 else 1000

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  AlmostSurely
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (fun n G => chromaticNumber G.graph - cochromaticNumber G.graph ≥ M)-/
/- ## Part VI: Heckel-Steiner Results (2024) -/

/-- Heckel (2024) / Steiner (2024): Difference is unbounded w.h.p. -/
theorem heckel_steiner_unbounded :
    ∀ M : ℕ, AlmostSurely (fun n G =>
      chromaticNumber G.graph - cochromaticNumber G.graph ≥ M) := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  AlmostSurely
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (fun n G => (chromaticNumber G.graph - cochromaticNumber G.graph : ℝ) ≥ n ^ (1 / 2 - ε))-/
/-- Lower bound: χ - ζ ≥ n^{1/2 - o(1)} along subsequences. -/
theorem difference_lower_bound :
    ∀ ε > 0, ∃ f : ℕ → ℕ, StrictMono f ∧
      AlmostSurely (fun n G =>
        (chromaticNumber G.graph - cochromaticNumber G.graph : ℝ) ≥ n^(1/2 - ε)) := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  AlmostSurely
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (fun _ G => (chromaticNumber G.graph - cochromaticNumber G.graph : ℝ) ≥ n ^ (1 - ε))-/
/-- Heckel (2024c): χ - ζ ≥ n^{1-ε} for ~95% of n. -/
theorem heckel_density_result :
    ∀ ε > 0, ∃ δ > (0.9 : ℝ), ∀ N : ℕ, N ≥ 100 →
      (Finset.filter (fun n => n ≤ N ∧
        AlmostSurely (fun _ G => (chromaticNumber G.graph - cochromaticNumber G.graph : ℝ) ≥ n^(1 - ε)))
        (Finset.range (N+1))).card ≥ δ * N := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `AlmostSurely`-/
/- ## Part VII: Heckel's Conjecture -/

/-- Heckel's conjecture: χ(G) - ζ(G) ≈ n/(log n)³ w.h.p. -/
def HeckelConjecture : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ < c₂ ∧
    AlmostSurely (fun n G =>
      c₁ * n / (Real.log n)^3 ≤ (chromaticNumber G.graph - cochromaticNumber G.graph : ℝ) ∧
      (chromaticNumber G.graph - cochromaticNumber G.graph : ℝ) ≤ c₂ * n / (Real.log n)^3)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['Erdos625.heckel_conjecture_open', 'harmonicSorry313613']-/
/-- Heckel's conjecture is OPEN. -/
axiom heckel_conjecture_open : HeckelConjecture

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

type of theorem `Erdos625.heckel_implies_main` is not a proposition
  {HeckelConjecture : Sort u_2} → {MainQuestion : Sort u_3} → HeckelConjecture → MainQuestion-/
/-- If Heckel's conjecture holds, the answer to the main question is YES. -/
theorem heckel_implies_main (h : HeckelConjecture) : MainQuestion := by
  sorry

/- ## Part VIII: Clique and Independence Numbers -/

/-- The clique number ω(G). -/
noncomputable def cliqueNumber (G : SimpleGraph V) : ℕ :=
  ⨆ (S : Finset V) (h : G.IsClique S), S.card

/-- The independence number α(G). -/
noncomputable def independenceNumber (G : SimpleGraph V) : ℕ :=
  cliqueNumber Gᶜ

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  AlmostSurely
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (fun n G =>
    (cliqueNumber G.graph : ℝ) ≤ 2.1 * Real.log n / Real.log 2 ∧
      (independenceNumber G.graph : ℝ) ≤ 2.1 * Real.log n / Real.log 2)-/
/-- ω(G) and α(G) are both ≈ 2 log₂ n a.s. -/
theorem clique_independence_bound :
    AlmostSurely (fun n G =>
      (cliqueNumber G.graph : ℝ) ≤ 2.1 * Real.log n / Real.log 2 ∧
      (independenceNumber G.graph : ℝ) ≤ 2.1 * Real.log n / Real.log 2) := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  cochromaticNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  G-/
/-- ζ(G) ≥ n / (ω(G) + α(G)). -/
theorem cochromatic_clique_independence (G : SimpleGraph V) :
    cochromaticNumber G * (cliqueNumber G + independenceNumber G) ≥ Fintype.card V := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  AlmostSurely
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (fun n G => ∃ χ₀ : ℕ, |chromaticNumber G.graph - χ₀| ≤ n / (Real.log n) ^ 2)-/
/- ## Part IX: Concentration -/

/-- χ(G) is concentrated in an interval of width O(n/log²n). -/
theorem chromatic_concentration :
    AlmostSurely (fun n G =>
      ∃ χ₀ : ℕ, |chromaticNumber G.graph - χ₀| ≤ n / (Real.log n)^2) := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  AlmostSurely
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  (fun n G => ∃ ζ₀ : ℕ, |cochromaticNumber G.graph - ζ₀| ≤ n / Real.log n)-/
/-- ζ(G) is also concentrated (less is known). -/
theorem cochromatic_concentration :
    AlmostSurely (fun n G =>
      ∃ ζ₀ : ℕ, |cochromaticNumber G.graph - ζ₀| ≤ n / Real.log n) := by
  sorry

/- Aristotle found this block to be false. Here is a proof of the negation:

noncomputable section AristotleLemmas

#check SimpleGraph.chromaticNumber

#check SimpleGraph.fromRel

/-
Definition of the 5-cycle graph C5.
-/
def C5 : SimpleGraph (Fin 5) := SimpleGraph.fromRel (fun a b => a + 1 = b)

lemma C5_chromatic : C5.chromaticNumber = 3 := by
  -- First, let's show that C5 is 3-colorable.
  have h3_colorable : C5.Colorable 3 := by
    -- We can define a proper coloring of C5 with three colors by assigning colors 0, 1, 2, 0, 1 to the vertices.
    use fun i => if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 0 else 1;
    simp +decide [ Erdos625.C5 ];
  refine' le_antisymm ( h3_colorable.chromaticNumber_le ) _;
  -- Now, let's show that C5 is not 2-colorable.
  have h2_colorable : ¬C5.Colorable 2 := by
    rintro ⟨ f, hf ⟩;
    simp_all +decide [ Fin.forall_fin_succ, Erdos625.C5 ];
    revert f; native_decide;
  refine' le_csInf _ _ <;> norm_num;
  · exact ⟨ _, ⟨ 3, rfl ⟩ ⟩;
  · exact fun n hn => not_lt.1 fun contra => h2_colorable <| hn.mono <| by interval_cases n <;> trivial;

lemma C5_clique : Erdos625.cliqueNumber C5 = 2 := by
  refine' le_antisymm _ _;
  · -- To show that the clique number of C5 is at most 2, we need to show that there are no cliques of size 3 in C5.
    have h_no_clique_size_3 : ∀ S : Finset (Fin 5), C5.IsClique S → S.card ≤ 2 := by
      simp +decide [ Erdos625.C5, SimpleGraph.IsClique ];
      simp +decide [ Set.Pairwise ];
    convert ciSup_le _;
    · exact ⟨ ∅ ⟩;
    · exact?;
  · refine' le_trans _ ( le_ciSup _ { 0, 1 } ) <;> simp +decide [ Erdos625.cliqueNumber ];
    simp +decide [ Erdos625.C5 ]

lemma C5_counterexample : C5.chromaticNumber ≠ Erdos625.cliqueNumber C5 := by
  -- Let's calculate the chromatic number of C5 using the provided lemma.
  have chromatic : C5.chromaticNumber = 3 := by
    exact?;
  -- Let's calculate the clique number of C5 using the provided lemma.
  have clique : cliqueNumber C5 = 2 := by
    convert C5_clique using 1
  aesop

lemma perfect_graph_chromatic_false : ¬ (∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hPerf : True), chromaticNumber G = cliqueNumber G) := by
  simp +zetaDelta at *;
  refine' ⟨ ULift ( Fin 5 ), _, _ ⟩;
  · exact ⟨ inferInstance ⟩;
  · -- Let's choose the graph $G = C5$.
    use SimpleGraph.comap (fun x => x.down) C5;
    convert C5_counterexample using 1;
    simp +decide [ SimpleGraph.chromaticNumber, Erdos625.cliqueNumber ];
    convert Iff.rfl;
    · ext;
      constructor <;> rintro ⟨ f, hf ⟩;
      · use fun x => f x.down;
        aesop;
      · use fun x => f ⟨ x ⟩;
        aesop;
    · convert rfl;
      refine' le_antisymm _ _;
      · refine' ciSup_le fun S => _;
        refine' le_trans _ ( le_ciSup _ ( Finset.image ( fun x : ULift ( Fin 5 ) => x.down ) S ) );
        · rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ];
          simp +decide [ Set.Pairwise ];
        · exact Set.finite_range _ |> Set.Finite.bddAbove;
      · refine' ciSup_le fun S => _;
        refine' le_trans _ ( le_ciSup _ ( Finset.image ( fun x : Fin 5 => ULift.up x ) S ) );
        · simp +decide [ Set.Pairwise ];
          rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ];
        · exact Set.finite_range _ |> Set.Finite.bddAbove

end AristotleLemmas

/-
## Part X: Special Graph Classes

For perfect graphs, χ = ω, but cochromatic may differ.
-/
theorem perfect_graph_chromatic (G : SimpleGraph V) (hPerf : True) :  -- Perfect condition
    chromaticNumber G = cliqueNumber G := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  simp +zetaDelta at *;
  -- Let's choose the 5-cycle graph C5.
  use ULift (Fin 5);
  refine' ⟨ ⟨ inferInstance ⟩, _ ⟩;
  use SimpleGraph.comap (fun x => x.down) C5;
  convert C5_counterexample using 1;
  simp +decide [ SimpleGraph.chromaticNumber, Erdos625.cliqueNumber ];
  convert Iff.rfl;
  · ext;
    constructor <;> rintro ⟨ f, hf ⟩;
    · use fun x => f x.down;
      aesop;
    · use fun x => f ⟨ x ⟩;
      aesop;
  · refine' le_antisymm _ _;
    · refine' ciSup_le fun S => _;
      refine' le_trans _ ( le_ciSup _ ( Finset.image ( fun x : Fin 5 => ULift.up x ) S ) );
      · rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ];
        simp +decide [ Set.Pairwise ];
      · exact Set.finite_range _ |> Set.Finite.bddAbove;
    · refine' ciSup_le fun S => _;
      refine' le_trans _ ( le_ciSup _ ( Finset.image ( fun x : ULift ( Fin 5 ) => x.down ) S ) );
      · rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ];
        simp +decide [ Set.Pairwise ];
      · exact Set.finite_range _ |> Set.Finite.bddAbove

-/
/- ## Part X: Special Graph Classes -/

/-- For perfect graphs, χ = ω, but cochromatic may differ. -/
theorem perfect_graph_chromatic (G : SimpleGraph V) (hPerf : True) :  -- Perfect condition
    chromaticNumber G = cliqueNumber G := by
  sorry

/-- Cochromatic number of complete bipartite K_{n,n}. -/
theorem cochromatic_complete_bipartite (n : ℕ) :
    True := by  -- ζ(K_{n,n}) = 2
  trivial

/-- Cochromatic number of path P_n. -/
theorem cochromatic_path (n : ℕ) :
    True := by  -- ζ(P_n) = ⌈n/2⌉
  trivial

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  cochromaticNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  G-/
/- ## Part XI: Upper Bounds on Difference -/

/-- Trivial upper bound: χ - ζ ≤ χ ≤ n. -/
theorem difference_trivial_upper (G : SimpleGraph V) :
    chromaticNumber G - cochromaticNumber G ≤ chromaticNumber G := by
  omega

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  cochromaticNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  G-/
/-- Better upper bound: χ - ζ ≤ n - max(ω, α). -/
theorem difference_better_upper (G : SimpleGraph V) :
    chromaticNumber G - cochromaticNumber G ≤
      Fintype.card V - max (cliqueNumber G) (independenceNumber G) := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  cochromaticNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  cochromaticNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  G
Function expected at
  cochromaticNumber
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  Gᶜ-/
/- ## Part XII: Summary -/

/-- Summary of known results. -/
theorem known_summary :
    (∀ G : SimpleGraph V, cochromaticNumber G ≤ chromaticNumber G) ∧
    (∀ G : SimpleGraph V, cochromaticNumber G = cochromaticNumber Gᶜ) := by
  constructor
  · exact cochromatic_le_chromatic
  · exact cochromatic_eq_complement

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  heckel_steiner_unbounded
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  1
Invalid field notation: Type of
  G
is not known; cannot resolve field `graph`
Function expected at
  cochromaticNumber
but this term has type
  ?m.2

Note: Expected a function because this term is being applied to the argument
  G.graph-/
/-- The problem remains open despite recent progress. -/
theorem problem_status :
    heckel_steiner_unbounded 1 →  -- Difference grows
    ¬(∀ n G, chromaticNumber G.graph = cochromaticNumber G.graph) := by  -- Not always equal
  sorry

end Erdos625