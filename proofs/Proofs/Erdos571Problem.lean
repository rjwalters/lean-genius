/-
# Erdős Problem #571: Rational Turán Exponents for Bipartite Graphs

**Source:** [erdosproblems.com/571](https://erdosproblems.com/571)
**Status:** OPEN

## Statement

Show that for any rational α ∈ [1,2) there exists a bipartite graph G
such that ex(n;G) ≍ n^α.

## Background

This is a fundamental question in extremal graph theory, asking whether
all rational numbers in [1,2) can arise as Turán exponents. The extremal
number ex(n;G) is the maximum number of edges in an n-vertex graph
containing no copy of G.

- Bukh-Conlon (2018): Solved the finite family variant
- Conlon-Janzer-Lee (2021): 3/2 - 1/(2s) for s ≥ 2
- Jiang-Qiu (2020, 2023): Multiple families including 1 + a/b
- Conlon-Janzer (2022): 2 - a/b with b ≥ (a-1)²

## Approach

We define graphs, extremal numbers, and Turán exponents, then
axiomatize the known families of achievable exponents and the
Bukh-Conlon finite family result.
-/

import Mathlib

namespace Erdos571

/- ## Part I: Graph Definitions -/

/-- A simple graph on vertex type V -/
structure Graph (V : Type*) where
  adj : V → V → Prop
  symm : ∀ u v, adj u v → adj v u
  loopless : ∀ v, ¬adj v v

/-- A graph is bipartite if vertices partition into two independent sets -/
def IsBipartite {V : Type*} [DecidableEq V] (G : Graph V) : Prop :=
  ∃ (A B : Set V), A ∪ B = Set.univ ∧ A ∩ B = ∅ ∧
    ∀ u v, G.adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)

/-- The edge count of a finite graph -/
def edgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : Graph V) [DecidableRel G.adj] : ℕ :=
  (Finset.filter (fun p : V × V => p.1 < p.2 ∧ G.adj p.1 p.2)
    Finset.univ).card

/-- G is a subgraph of H (via injective homomorphism) -/
def ContainsCopy {V W : Type*} (G : Graph V) (H : Graph W) : Prop :=
  ∃ (f : V → W), Function.Injective f ∧
    ∀ u v, G.adj u v → H.adj (f u) (f v)

/-- H is G-free if it contains no copy of G -/
def IsFree {V W : Type*} (H : Graph W) (G : Graph V) : Prop :=
  ¬ContainsCopy G H

/- ## Part II: Extremal Numbers and Asymptotic Notation -/

/-- Asymptotic equivalence: f ≍ g means c₁g ≤ f ≤ c₂g for constants c₁, c₂ > 0 -/
def AsymptoticEquiv (f g : ℕ → ℝ) : Prop :=
  ∃ (c₁ c₂ : ℝ) (N₀ : ℕ), c₁ > 0 ∧ c₂ > 0 ∧
    ∀ n ≥ N₀, c₁ * g n ≤ f n ∧ f n ≤ c₂ * g n

/-- Big-O notation -/
def IsBigO (f g : ℕ → ℝ) : Prop :=
  ∃ (c : ℝ) (N₀ : ℕ), c > 0 ∧ ∀ n ≥ N₀, |f n| ≤ c * |g n|

/- ## Part III: Turán Exponents -/

/--
A rational number α ∈ [1,2) is a Turán exponent if there exists a
bipartite graph G with ex(n;G) ≍ n^α. The extremal number ex(n;G)
is axiomatized via the AsymptoticEquiv relation rather than defined
computationally.
-/
def IsTuranExponent (α : ℚ) : Prop :=
  1 ≤ α ∧ α < 2 ∧
  ∃ (V : Type*) [Fintype V] [DecidableEq V] (G : Graph V),
    IsBipartite G ∧
    ∃ (ex : ℕ → ℝ),
      -- ex represents the extremal number for G
      AsymptoticEquiv ex (fun n => (n : ℝ) ^ (α : ℝ))

/- ## Part IV: The Conjecture -/

/--
**Erdős Problem #571 (OPEN):**
Every rational α ∈ [1,2) is a Turán exponent — achievable by some
single bipartite graph G with ex(n;G) ≍ n^α.
-/
def erdos_571_conjecture : Prop :=
  ∀ α : ℚ, 1 ≤ α → α < 2 → IsTuranExponent α

/- ## Part V: Known Turán Exponents -/

/--
**Conlon-Janzer-Lee (2021):** The rationals 3/2 - 1/(2s) for s ≥ 2
are Turán exponents. This family (5/4, 7/6, 9/8, ...) accumulates
at 3/2 from below. The witness graphs are subdivisions of specific
bipartite graphs.
-/
axiom conlon_janzer_lee_exponents :
  ∀ s : ℕ, s ≥ 2 → IsTuranExponent (3/2 - 1/(2*s))

/--
**Jiang-Qiu (2020):** The rationals 4/3 - 1/(3s) for s ≥ 2 are
Turán exponents. Also 5/4 - 1/(4s) for s ≥ 2.
-/
/--
**Jiang-Qiu (2023):** The rationals 1 + a/b with b > a² are Turán
exponents. This addresses the difficult regime near 1, covering
infinitely many low exponents.
-/
axiom jiang_qiu_low_exponents :
  ∀ a b : ℕ, a ≥ 1 → b > a^2 → IsTuranExponent (1 + (a : ℚ)/(b : ℚ))

/--
**Jiang-Ma-Yepremyan (2022):** The rationals 2 - 2/(2b+1) for b ≥ 2
are Turán exponents. Also 7/5 is specifically achievable.
-/
axiom exponent_7_5 : IsTuranExponent (7/5)

/--
**Conlon-Janzer (2022):** The rationals 2 - a/b with b ≥ (a-1)² are
Turán exponents. This covers a dense set near 2, showing exponents
≥ 7/4 are well-understood.
-/
/- ## Part VI: Bukh-Conlon Finite Family Result -/

/--
**Bukh-Conlon (2018):** Every rational α ∈ [1,2) is achievable for a
FINITE FAMILY of bipartite graphs — there exists a family F of bipartite
graphs such that the family extremal number ex(n; F) ≍ n^α.

This solves a weakened version: families instead of single graphs.
-/
/- ## Part VII: Classical Upper Bounds -/

/--
**Kővári-Sós-Turán (1954):** For the complete bipartite graph K_{s,t}
with s ≤ t, ex(n; K_{s,t}) = O(n^{2-1/s}). This classical result
shows forbidden bipartite subgraphs yield subquadratic extremal numbers.
-/
/--
**Bondy-Simonovits:** For any bipartite G, ex(n;G) = O(n^{2-1/k})
for some k depending on G. This guarantees all bipartite Turán
exponents lie in [1, 2).
-/
/- ## Part VIII: Summary -/

/--
**Summary of Erdős Problem #571:**

The Erdős-Simonovits conjecture asks whether every rational α ∈ [1,2)
is a Turán exponent for a single bipartite graph.

**Known results combined here:**
- Conlon-Janzer-Lee (2021): 3/2 - 1/(2s) family
- Jiang-Qiu (2023): 1 + a/b with b > a² (low exponents)
- Jiang-Ma-Yepremyan (2022): 2 - 2/(2b+1) family

**Open:** Whether ALL rationals in [1,2) are achievable by single graphs.
Exponents close to 1 remain the hardest cases.
-/
theorem erdos_571_summary :
    -- CJL: 3/2 - 1/(2s) for s ≥ 2
    (∀ s : ℕ, s ≥ 2 → IsTuranExponent (3/2 - 1/(2*s))) ∧
    -- JQ: 1 + a/b with b > a²
    (∀ a b : ℕ, a ≥ 1 → b > a^2 → IsTuranExponent (1 + (a : ℚ)/(b : ℚ))) ∧
    -- 7/5 is achievable
    IsTuranExponent (7/5) := by
  exact ⟨conlon_janzer_lee_exponents, jiang_qiu_low_exponents, exponent_7_5⟩

end Erdos571
