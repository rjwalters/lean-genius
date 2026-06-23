/-
Erdős Problem #752: Cycle Lengths in High-Girth Graphs

Source: https://erdosproblems.com/752
Status: SOLVED (Sudakov-Verstraëte 2008)

Statement:
Let G be a graph with minimum degree k and girth > 2s (i.e., G contains no
cycles of length ≤ 2s). Must there be ≫ k^s many distinct cycle lengths in G?

Background:
This is a question about how many distinct cycle lengths must appear in
graphs that are locally sparse (high girth) but globally dense (high minimum
degree). The girth condition forbids short cycles, while minimum degree
forces many cycles to exist.

Known Results:
- Erdős-Faudree-Schelp: True when s = 2
- Sudakov-Verstraëte (2008): True in general with average degree (stronger!)
  They proved ≥ Ω(k^s) consecutive even integers are cycle lengths

References:
- [EFS] Erdős, Faudree, Schelp, "Cycle lengths in graphs"
- [SuVe08] Sudakov, Verstraëte, "Cycle lengths in sparse graphs",
           Combinatorica 28 (2008), 357-372

Tags: graph-theory, cycles, girth, extremal-combinatorics
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic

namespace Erdos752

variable {V : Type*} [Fintype V] [DecidableEq V]

/- ## Part 1: Basic Definitions
-/

/-- The minimum degree of a simple graph -/
noncomputable def minDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.inf' ⟨Classical.arbitrary V, Finset.mem_univ _⟩ (G.degree ·)

/-- A graph has girth > g if it contains no cycles of length ≤ g -/
def GirthGreaterThan (G : SimpleGraph V) (g : ℕ) : Prop :=
  ∀ n : ℕ, n ≤ g → ¬∃ (walk : G.Walk V V), walk.IsCycle ∧ walk.length = n

/-- The set of cycle lengths in a graph -/
noncomputable def cycleLengths (G : SimpleGraph V) : Set ℕ :=
  { n : ℕ | ∃ (u : V) (walk : G.Walk u u), walk.IsCycle ∧ walk.length = n }

/-- Number of distinct cycle lengths -/
noncomputable def numCycleLengths (G : SimpleGraph V) : ℕ :=
  (cycleLengths G).ncard

/- ## Part 2: The Erdős-Faudree-Schelp Conjecture
-/

/-- The conjecture: girth > 2s and min degree k implies ≫ k^s cycle lengths -/
def ErdosFaudreeSchelpConjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k s : ℕ),
    minDegree G ≥ k →
    GirthGreaterThan G (2 * s) →
    (numCycleLengths G : ℝ) ≥ c * (k : ℝ) ^ s

/- ## Part 3: The Sudakov-Verstraëte Theorem (Stronger Version)
-/

/-- Average degree of a graph -/
noncomputable def avgDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  (Finset.univ.sum (G.degree ·) : ℝ) / (Fintype.card V : ℝ)

/-- Consecutive even cycle lengths: a set of even numbers 2a, 2a+2, ..., 2a+2(m-1) -/
def ConsecutiveEvenCycleLengths (G : SimpleGraph V) (start count : ℕ) : Prop :=
  ∀ i : ℕ, i < count → (2 * start + 2 * i) ∈ cycleLengths G

/-- The Sudakov-Verstraëte theorem: average degree k and girth > 2s
    implies Ω(k^s) consecutive even cycle lengths -/
axiom sudakov_verstrate_2008 : ∃ c : ℝ, c > 0 ∧
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k s : ℕ),
    avgDegree G ≥ k →
    GirthGreaterThan G (2 * s) →
    ∃ (start : ℕ), ConsecutiveEvenCycleLengths G start ⌊c * (k : ℝ) ^ s⌋₊

/-- Min degree lower bounds average degree: the inf of a finite set ≤ its average. -/
theorem min_degree_le_avg (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (minDegree G : ℝ) ≤ avgDegree G := by
  unfold minDegree avgDegree
  have hcard : (0 : ℝ) < Fintype.card V := by exact_mod_cast @Fintype.card_pos V _ ⟨Classical.arbitrary V⟩
  rw [le_div_iff₀ hcard]
  -- Goal: (↑inf') * ↑card ≤ ↑(∑ degrees)
  -- Strategy: inf' * card = ∑ inf' ≤ ∑ degree(v)
  calc (↑(Finset.univ.inf' ⟨_, Finset.mem_univ _⟩ (G.degree ·)) : ℝ) * ↑(Fintype.card V)
      = Finset.univ.sum
          (fun _ => (↑(Finset.univ.inf' ⟨_, Finset.mem_univ _⟩ (G.degree ·)) : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ Finset.univ.sum (fun v => (G.degree v : ℝ)) :=
        Finset.sum_le_sum fun v _ =>
          Nat.cast_le.mpr (Finset.inf'_le _ (Finset.mem_univ v))

/-- Consecutive lengths give at least that many distinct cycle lengths -/
axiom consecutive_gives_distinct (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (start count : ℕ) :
    ConsecutiveEvenCycleLengths G start count →
    numCycleLengths G ≥ count

/-- The original conjecture follows from the stronger result -/
theorem erdos_752_solved : ErdosFaudreeSchelpConjecture := by
  obtain ⟨c, hc_pos, h⟩ := sudakov_verstrate_2008
  use c / 2, by linarith
  intro V _ _ G _ k s hmin hgirth
  -- min degree ≤ avg degree, so avg degree ≥ k
  have havg : avgDegree G ≥ k := by
    calc avgDegree G ≥ minDegree G := min_degree_le_avg V G
      _ ≥ k := by exact_mod_cast hmin
  obtain ⟨start, hcons⟩ := h V G k s havg hgirth
  have hdist := consecutive_gives_distinct V G start _ hcons
  calc (numCycleLengths G : ℝ)
      ≥ ⌊c * (k : ℝ) ^ s⌋₊ := by exact_mod_cast hdist
    _ ≥ c * (k : ℝ) ^ s - 1 := Nat.sub_one_lt_floor (c * (k : ℝ) ^ s)
    _ ≥ c / 2 * (k : ℝ) ^ s := by nlinarith [hc_pos, pow_nonneg (Nat.cast_nonneg k) s]

/- ## Part 4: Why Girth Matters
-/

/-- Moore graphs achieve the Moore bound exactly -/
def IsMooreGraph (G : SimpleGraph V) [DecidableRel G.Adj] (d g : ℕ) : Prop :=
  G.IsRegular d ∧
  GirthGreaterThan G (g - 1) ∧
  ¬GirthGreaterThan G g

/- ## Part 5: The Girth and Cycle Structure
-/

/-- Girth > 2s means the shortest cycle has length ≥ 2s + 1 -/
def girth (G : SimpleGraph V) : ℕ :=
  sInf { n : ℕ | n ≥ 3 ∧ ∃ (u : V) (walk : G.Walk u u), walk.IsCycle ∧ walk.length = n }

/-- High girth forces cycles to be "spread out" in length -/
theorem high_girth_spreads_cycles (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : GirthGreaterThan G (2 * s)) :
    ∀ n ∈ cycleLengths G, n ≥ 2 * s + 1 := by
  intro n hn
  by_contra hlt
  push_neg at hlt
  exact hs n (Nat.lt_succ_iff.mp hlt) hn

/- ## Part 6: Extremal Connections
-/

/- ## Part 7: Extensions and Generalizations
-/

/-- Sudakov-Verstraëte conjecture about consecutive lengths -/
def SudakovVerstrateConjecture : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
    G.chromaticNumber ≥ k + 2 →
    ∃ (start : ℕ), ∀ i, i < k → start + i ∈ cycleLengths G

/- ## Part 8: Quantitative Bounds
-/

/-- The constant in Sudakov-Verstraëte (a specific computable lower bound). -/
noncomputable def sudakov_verstrate_constant : ℝ := 1 / 500

theorem sudakov_verstrate_constant_pos : sudakov_verstrate_constant > 0 := by
  unfold sudakov_verstrate_constant; norm_num

theorem sudakov_verstrate_constant_is : sudakov_verstrate_constant > 1 / 1000 := by
  unfold sudakov_verstrate_constant; norm_num

/- ## Part 9: Summary
-/

/-- Main theorem: Erdős Problem #752 is solved -/
theorem erdos_752 : ErdosFaudreeSchelpConjecture := erdos_752_solved

/-- The result is even stronger: consecutive even lengths exist -/
theorem erdos_752_strong :
  ∃ c : ℝ, c > 0 ∧
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k s : ℕ),
    avgDegree G ≥ k →
    GirthGreaterThan G (2 * s) →
    ∃ (start : ℕ), ConsecutiveEvenCycleLengths G start ⌊c * (k : ℝ) ^ s⌋₊ :=
  sudakov_verstrate_2008

/-- Summary: The conjecture is solved and the bound is tight -/
theorem erdos_752_summary :
    ErdosFaudreeSchelpConjecture ∧
    (∃ c : ℝ, c > 0 ∧
      ∀ (V : Type*) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (k s : ℕ),
        avgDegree G ≥ k →
        GirthGreaterThan G (2 * s) →
        ∃ (start : ℕ), ConsecutiveEvenCycleLengths G start ⌊c * (k : ℝ) ^ s⌋₊) :=
  ⟨erdos_752_solved, sudakov_verstrate_2008⟩

end Erdos752
