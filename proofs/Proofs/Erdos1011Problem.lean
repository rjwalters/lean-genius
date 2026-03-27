/-
  Erdős Problem #1011: Triangles in Graphs with High Chromatic Number

  Source: https://erdosproblems.com/1011
  Status: OPEN

  Statement:
  Let f_r(n) be minimal such that every graph on n vertices with ≥ f_r(n)
  edges and chromatic number ≥ r contains a triangle. Determine f_r(n).

  Background:
  This problem connects three fundamental graph parameters: edge count,
  chromatic number, and triangle existence. Turán's theorem handles the
  case r = 2. For higher chromatic numbers, the interaction becomes subtle.

  Known results:
  • f_2(n) = ⌊n²/4⌋ + 1 (Turán's theorem)
  • f_3(n) = ⌊(n-1)²/4⌋ + 2 (Erdős-Gallai 1962)
  • f_4(n) = ⌊(n-3)²/4⌋ + 6 for n ≥ 150 (Ren-Wang-Wang-Yang 2024)
  • Asymptotic: f_r(n) = n²/4 - g(r)·n/2 + O(1) (Simonovits)
  • Bounds: (1/2 - o(1))r² log r ≤ g(r) ≤ (2 + o(1))r² log r

  References:
  [Er62d] Erdős-Gallai, "On maximal paths and circuits of graphs" (1962)
  [Si74] Simonovits, PhD thesis, discussion on p. 358
  [DI22] Davies-Illingworth (2022) - Lower bound on g(r)
  [HHKP25] Hefty-Horn-King-Pfender (2025) - Upper bound on g(r)

  Tags: graph-theory, chromatic-number, triangles, turan-type, open-problem
-/

import Mathlib
import Proofs.GraphCore

open Finset GraphCore
open SimpleGraph hiding chromaticNumber

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
## Basic Graph Properties

Chromatic number and triangle containment.
-/

/-- A graph contains a triangle -/
def HasTriangle (G : SimpleGraph V) : Prop :=
  ∃ a b c : V, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj a c

/-
## The Threshold Function f_r(n)

f_r(n) is minimal such that chromatic number ≥ r and ≥ f_r(n) edges implies triangle.
-/

/-- Predicate: graph has chromatic number at least r -/
def hasChromatic (G : SimpleGraph V) (r : ℕ) : Prop :=
  chromaticNumber G ≥ r

/-- The threshold function f_r(n) -/
noncomputable def f (r n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ (V : Type*) [Fintype V] [DecidableEq V],
    Fintype.card V = n →
    ∀ G : SimpleGraph V, [DecidableRel G.Adj] →
    hasChromatic G r → edgeCount G ≥ m → HasTriangle G}

/-
## Turán's Theorem: The Case r = 2

Any graph with > n²/4 edges contains a triangle.
-/

/-- Turán number: maximum edges in triangle-free graph on n vertices -/
def turanNumber (n : ℕ) : ℕ := n^2 / 4

/-- Turán's theorem: f_2(n) = ⌊n²/4⌋ + 1 -/
axiom turan_theorem :
  ∀ n ≥ 1, f 2 n = turanNumber n + 1

/-
## Erdős-Gallai: The Case r = 3

f_3(n) = ⌊(n-1)²/4⌋ + 2
-/

/-- The threshold for r = 3 -/
def f3Threshold (n : ℕ) : ℕ := (n - 1)^2 / 4 + 2

/-- Erdős-Gallai theorem (1962): f_3(n) = ⌊(n-1)²/4⌋ + 2 -/
axiom erdos_gallai_theorem :
  ∀ n ≥ 3, f 3 n = f3Threshold n

/-
## The Case r = 4

f_4(n) = ⌊(n-3)²/4⌋ + 6 for large n (Ren-Wang-Wang-Yang 2024)
-/

/-- The threshold for r = 4 -/
def f4Threshold (n : ℕ) : ℕ := (n - 3)^2 / 4 + 6

/-
## The Simonovits Asymptotic

f_r(n) = n²/4 - g(r)·n/2 + O(1)
-/

/-- g(r): vertices to remove from χ ≥ r triangle-free graph to make bipartite -/
noncomputable def g (r : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ (V : Type*) [Fintype V] [DecidableEq V],
    ∃ G : SimpleGraph V, [DecidableRel G.Adj] →
    ¬HasTriangle G ∧ hasChromatic G r ∧
    ∀ S : Finset V, S.card < k → ¬∃ (W : Type*) [Fintype W],
      ∃ H : SimpleGraph W, chromaticNumber H ≤ 2}

/-- Simonovits asymptotic formula -/
axiom simonovits_asymptotic :
  ∀ r ≥ 2, ∃ C : ℕ, ∀ n ≥ r,
    |((f r n : ℤ) - n^2/4 + (g r : ℤ) * n / 2)| ≤ C

/-
## Bounds on g(r)

The key open question: determining g(r) precisely.
-/

/-- Lower bound: g(r) ≥ (1/2 - o(1))r² log r (Davies-Illingworth 2022) -/
axiom davies_illingworth_lower :
  ∀ ε > 0, ∃ R : ℕ, ∀ r ≥ R,
    (g r : ℝ) ≥ (1/2 - ε) * r^2 * Real.log r

/-- Upper bound: g(r) ≤ (2 + o(1))r² log r (Hefty-Horn-King-Pfender 2025) -/
axiom hhkp_upper :
  ∀ ε > 0, ∃ R : ℕ, ∀ r ≥ R,
    (g r : ℝ) ≤ (2 + ε) * r^2 * Real.log r

/-
## Monotonicity Properties
-/

/-
## Special Values of g(r)
-/

/-
## The Main Conjecture

Determine the exact value of g(r).
-/

/-- The main open question: what is g(r) exactly? -/
def erdos1011Conjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ r ≥ 2,
    |(g r : ℝ) - c * r^2 * Real.log r| ≤ r^2

/-- Pomerance-style conjecture: g(r) ~ r² log r -/
def gAsymptoticConjecture : Prop :=
  ∃ c : ℝ, 1/2 ≤ c ∧ c ≤ 2 ∧
    Filter.Tendsto (fun r => (g r : ℝ) / (r^2 * Real.log r))
      Filter.atTop (nhds c)

#check f
#check g
#check turan_theorem
#check erdos_gallai_theorem
#check simonovits_asymptotic
#check davies_illingworth_lower
#check hhkp_upper
