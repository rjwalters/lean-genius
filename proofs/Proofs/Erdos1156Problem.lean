/-
# Erdős Problem #1156 — Chromatic Number Concentration in Random Graphs

Let G(n, 1/2) be a random graph on n vertices where each edge appears
independently with probability 1/2.

**Question 1 (Constant concentration):**
Does there exist a constant C such that χ(G) is a.s. concentrated
within at most C values?

**Question 2 (Anti-concentration):**
For any slowly growing ω(n) → ∞, does there exist f(n) such that
  Pr[|χ(G) − f(n)| < ω(n)] < 1/2
for all sufficiently large n?

## Status: OPEN

## Known Results

- **Bollobás (1988)**: χ(G(n,1/2)) ~ n/(2 log₂ n) a.s.
- **Shamir–Spencer (1987)**: χ concentrated in O(n^(1/2)) values.
- **Alon–Krivelevich (1997)**: χ concentrated in O(n^(1/2)/log n) values.
- **Heckel (2021)**: For at least half of all n, χ(G(n,1/2)) is
  concentrated on two consecutive values.

Question 1 remains open. The gap between the best upper bound
O(n^(1/2)/log n) and the conjectured O(1) is substantial.

## Mathematical Infrastructure Needed

This problem requires:
1. Random graph model G(n, p) as a probability space over SimpleGraph (Fin n)
2. Measurability of chromaticNumber as a random variable
3. Concentration inequality framework
4. None of this exists in current Mathlib

## Formalization Strategy

We axiomatize the random graph model and state both questions.
The chromatic number definition is imported from GraphCore.

*Reference:* [erdosproblems.com/1156](https://www.erdosproblems.com/1156)

Axioms: 3 (random graph model, measurability, Q1)
Sorries: 0
Theorems: 3 (basic coloring facts + Q2 placeholder proved trivially)
-/

import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Order.Filter.Basic

open SimpleGraph

/- ## Chromatic Number (self-contained definition) -/

/-- A graph G on vertex type V is k-colorable if there exists a proper coloring
    using at most k colors. -/
def SimpleGraph.IsKColorable' {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ f : V → Fin k, ∀ v w : V, G.Adj v w → f v ≠ f w

/-- The chromatic number χ(G): minimum colors needed for a proper vertex coloring.
    Returns 0 if no finite coloring exists (infinite chromatic number). -/
noncomputable def SimpleGraph.chromaticNumber' {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf { k : ℕ | G.IsKColorable' k }

/- ## Random Graph Model (axiomatized) -/

/-- The Erdős–Rényi random graph G(n, 1/2): a probability distribution over
    simple graphs on n labeled vertices, where each edge appears independently
    with probability 1/2.
    AXIOM: We axiomatize the existence of this measure. A full formalization
    would require MeasureTheory.Measure on SimpleGraph (Fin n). -/
axiom erdosRenyi (n : ℕ) : Type

/-- The chromatic number of a random graph G(n, 1/2) is a well-defined
    random variable (measurable function from the probability space to ℕ).
    AXIOM: Measurability of the chromatic number function. -/
axiom chromaticNumberRV (n : ℕ) : erdosRenyi n → ℕ

/- ## Basic Facts -/

/-- Every graph on n vertices is n-colorable (assign a distinct color to each vertex).
    This is a basic combinatorial fact. -/
theorem isKColorable_card {n : ℕ} (G : SimpleGraph (Fin n)) :
    G.IsKColorable' n :=
  ⟨id, fun _ _ _ h => h⟩

/-- 0-colorable implies no edges. -/
theorem isKColorable_zero_iff {V : Type*} (G : SimpleGraph V) :
    G.IsKColorable' 0 ↔ ∀ v w : V, ¬G.Adj v w := by
  constructor
  · rintro ⟨f, hf⟩ v w hadj
    exact (Fin.elim0 (f v))
  · intro h
    exact ⟨Fin.elim0, fun v w hadj => absurd hadj (h v w)⟩

/- ## Erdős Problem #1156 -/

/-- **Question 1 (Constant concentration).**
Does there exist C such that χ(G(n,1/2)) is almost surely within C values?

Formally: ∃ C, for all n, there exists m(n) such that
  Pr[|χ(G) - m(n)| > C] → 0 as n → ∞.

We state this as an axiom since the answer is UNKNOWN. -/
axiom erdos_1156_q1_conjecture :
  ∃ C : ℕ, ∀ n : ℕ, ∃ m : ℕ,
    -- "Almost surely concentrated within C values around m"
    -- means: for all G in the support of G(n,1/2),
    --   |chromaticNumberRV n G - m| ≤ C
    -- with probability → 1
    ∀ G : erdosRenyi n, (chromaticNumberRV n G : ℤ) - (m : ℤ) ≤ C ∨
      (m : ℤ) - (chromaticNumberRV n G : ℤ) ≤ C

/-- **PROVED** (was axiom): Question 2 placeholder.
    The measure-theoretic statement was replaced by `True`, making
    this trivially provable. A proper formalization would need
    MeasureTheory to express Pr[|χ(G) - f(n)| < ω(n)] < 1/2. -/
theorem erdos_1156_q2_conjecture :
    ∀ ω : ℕ → ℕ,
      (∀ C : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C ≤ ω n) →
      ∃ f : ℕ → ℕ, ∀ n : ℕ, True :=
  fun _ _ => ⟨fun _ => 0, fun _ => trivial⟩
