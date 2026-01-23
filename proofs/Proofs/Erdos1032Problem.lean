/-
Erdős Problem #1032: 4-Chromatic Critical Graphs with High Minimum Degree

**Statement**: A graph is 4-chromatic critical if it has chromatic number 4
and removing any edge decreases χ to 3.

Is there, for arbitrarily large n, a 4-chromatic critical graph on n vertices
with minimum degree ≫ n?

**Status**: OPEN

**Known Results**:
- Simonovits & Toft (1972): δ ≫ n^{1/3} achievable
- Dirac: 6-chromatic critical can have δ > n/2
- Open for 5-chromatic critical too

Reference: https://erdosproblems.com/1032
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card

open Nat

namespace Erdos1032

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
## Part I: Chromatic Number
-/

/-- The chromatic number of G (axiomatized for simplicity). -/
axiom chromaticNumber (G : SimpleGraph V) : ℕ

/-- χ(G) ≥ 1 for any graph. -/
axiom chi_ge_one (G : SimpleGraph V) : chromaticNumber G ≥ 1

/-- χ(G) ≤ |V|. -/
axiom chi_le_card (G : SimpleGraph V) : chromaticNumber G ≤ Fintype.card V

/-
## Part II: Critical Graphs
-/

/-- G is k-chromatic critical if χ(G) = k and removing any edge reduces χ to k-1. -/
def IsChromaticCritical (G : SimpleGraph V) (k : ℕ) : Prop :=
  chromaticNumber G = k ∧
  ∀ e ∈ G.edgeSet, chromaticNumber (G.deleteEdges {e}) = k - 1

/-- G is 4-chromatic critical. -/
def Is4Critical (G : SimpleGraph V) : Prop := IsChromaticCritical G 4

/-
## Part III: The Main Question
-/

/-- Minimum degree of a graph. -/
noncomputable def minDegree (G : SimpleGraph V) : ℕ :=
  Finset.univ.inf' ⟨Classical.arbitrary V, Finset.mem_univ _⟩ G.degree

/-- The main question: For arbitrarily large n, does there exist a 4-critical
    graph on n vertices with min degree ≫ n?

    More precisely: Is there c > 0 such that for infinitely many n,
    there exists 4-critical G on n vertices with δ(G) ≥ c·n? -/
def mainConjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ Set.Infinite {n : ℕ |
    ∃ G : SimpleGraph (Fin n), Is4Critical G ∧ (minDegree G : ℝ) ≥ c * n}

/-- Alternative: For any c > 0, eventually no such graphs exist. -/
def mainConjectureNeg : Prop :=
  ∀ c : ℝ, c > 0 → ∃ N : ℕ, ∀ n ≥ N,
    ∀ G : SimpleGraph (Fin n), Is4Critical G → (minDegree G : ℝ) < c * n

/-
## Part IV: Known Bounds
-/

/-- Simonovits-Toft (1972): There exist 4-critical graphs with δ ≫ n^{1/3}. -/
axiom simonovits_toft_bound :
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    ∃ G : SimpleGraph (Fin n), Is4Critical G ∧
      (minDegree G : ℝ) ≥ (1 - ε) * (n : ℝ)^(1/3 : ℝ)

/-- Dirac: 6-chromatic critical graphs can have δ > n/2. -/
axiom dirac_6critical :
  Set.Infinite {n : ℕ |
    ∃ G : SimpleGraph (Fin n), IsChromaticCritical G 6 ∧ (minDegree G : ℝ) > n / 2}

/-- Toft's conjecture: A 4-critical graph on n vertices has at least (5/3 + o(1))n edges. -/
def toftConjecture : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    ∀ G : SimpleGraph (Fin n), Is4Critical G →
      (G.edgeFinset.card : ℝ) ≥ (5/3 - ε) * n

/-
## Part V: Basic Properties of Critical Graphs
-/

/-- In a k-critical graph, every vertex has degree ≥ k-1. -/
axiom critical_min_degree (G : SimpleGraph V) (k : ℕ) (hk : k ≥ 1)
    (hcrit : IsChromaticCritical G k) (v : V) :
    G.degree v ≥ k - 1

/-- In particular, 4-critical graphs have δ ≥ 3. -/
theorem four_critical_delta_ge_3 (G : SimpleGraph V) (h : Is4Critical G) :
    minDegree G ≥ 3 := by
  sorry

/-- A k-critical graph is connected. -/
axiom critical_connected (G : SimpleGraph V) (k : ℕ) (hk : k ≥ 2)
    (hcrit : IsChromaticCritical G k) :
    G.Connected

/-
## Part VI: Examples
-/

/-- K_4 is 4-critical. -/
axiom K4_is_4critical :
    Is4Critical (⊤ : SimpleGraph (Fin 4))

/-- Odd wheels W_{2k+1} are 4-critical for k ≥ 2.
    (Wheel W_n = cycle C_{n-1} + central vertex) -/
axiom odd_wheels_4critical (k : ℕ) (hk : k ≥ 2) :
    ∃ W : SimpleGraph (Fin (2*k + 2)), Is4Critical W ∧
      minDegree W = 3

/-
## Part VII: Summary
-/

/-- Erdős Problem #1032: Summary

    **Definition**: 4-critical = χ = 4 and removing any edge gives χ = 3.

    **Question**: Can δ(G) ≫ n for 4-critical G on n vertices?

    **Known**:
    - δ ≫ n^{1/3} achievable (Simonovits-Toft 1972)
    - δ ≥ 3 always (since χ = 4)
    - 6-critical can have δ > n/2 (Dirac)
    - 5-critical case also open

    **Toft's conjecture**: |E| ≥ (5/3 + o(1))n. -/
theorem erdos_1032_summary :
    -- Lower bound on min degree exists
    (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      ∃ G : SimpleGraph (Fin n), Is4Critical G ∧
        (minDegree G : ℝ) ≥ (1 - ε) * (n : ℝ)^(1/3 : ℝ)) ∧
    -- Higher chromatic numbers allow higher min degree
    Set.Infinite {n : ℕ |
      ∃ G : SimpleGraph (Fin n), IsChromaticCritical G 6 ∧ (minDegree G : ℝ) > n / 2} := by
  exact ⟨simonovits_toft_bound, dirac_6critical⟩

end Erdos1032
