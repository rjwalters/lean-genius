/-
Erdős Problem #572: Lower Bound for Extremal Function of Even Cycles

Source: https://erdosproblems.com/572
Status: PARTIALLY SOLVED (Benson 1966 for k=3,5; LUW 1995 for general weaker bound)

Statement:
Show that for k ≥ 3,
  ex(n; C_{2k}) >> n^{1+1/k}

where ex(n; C_{2k}) is the maximum number of edges in an n-vertex graph
containing no cycle of length 2k.

Partial Results:
- Benson (1966): Proved for k = 3 and k = 5
- Lazebnik-Ustimenko-Woldar (1995): Proved ex(n; C_{2k}) >> n^{1+2/(3k-3+ν)}
  where ν = 0 for odd k, ν = 1 for even k

Upper Bound (known):
- Bondy-Simonovits (1974): ex(n; C_{2k}) << k·n^{1+1/k}

The gap between lower and upper bounds remains open for k ≥ 4, k ≠ 5.

References:
- Benson, C.T. (1966): "Minimal regular graphs of girths eight and twelve"
  Canadian J. Math., 1091-1094
- Bondy, J.A. and Simonovits, M. (1974): "Cycles of even length in graphs"
  J. Combinatorial Theory Ser. B, 97-105
- Lazebnik, F., Ustimenko, V.A., Woldar, A.J. (1995): Bull. Amer. Math. Soc.
- See also Problem #765 and the graphs collection
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

open SimpleGraph

namespace Erdos572

/-
## Part I: Graph-Theoretic Definitions

The extremal function ex(n; H) asks: what is the maximum number of edges
in an n-vertex graph that contains no copy of H as a subgraph?
-/

/--
**Cycle of length k:**
A cycle C_k on k vertices.

For simplicity, we work with this as a property of graphs rather than
constructing the cycle explicitly.
-/
def hasCycleOfLength (G : SimpleGraph V) (k : ℕ) [Fintype V] : Prop :=
  ∃ (vertices : Fin k → V), Function.Injective vertices ∧
    (∀ i : Fin k, G.Adj (vertices i) (vertices ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega : 0 < k)⟩))

/--
**C_{2k}-free graph:**
A graph G is C_{2k}-free if it contains no cycle of length 2k.
-/
def isCycleFree (G : SimpleGraph V) (length : ℕ) [Fintype V] : Prop :=
  ¬hasCycleOfLength G length

/--
**Edge count:**
The number of edges in a simple graph.
-/
noncomputable def edgeCount (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/-
## Part II: The Extremal Function

ex(n; C_{2k}) = max{|E(G)| : G has n vertices and no C_{2k}}
-/

/--
**Extremal function for even cycles:**
ex(n; C_{2k}) is the maximum number of edges in an n-vertex C_{2k}-free graph.
-/
noncomputable def exCycle (n k : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) [Fintype V] [DecidableEq V],
    ∃ (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n ∧ isCycleFree G (2 * k) ∧ edgeCount G = m}

/-
## Part III: Known Results

Upper and lower bounds on the extremal function.
-/

/--
**Bondy-Simonovits Upper Bound (1974):**
ex(n; C_{2k}) ≤ c·k·n^{1+1/k} for some constant c.

More precisely, for n sufficiently large:
  ex(n; C_{2k}) ≤ (1/2)·k^{1/k}·n^{1+1/k} + O(n)
-/
axiom bondy_simonovits_upper :
  ∀ k : ℕ, k ≥ 2 →
  ∃ c : ℝ, c > 0 ∧
    ∀ n : ℕ, n ≥ 1 →
      (exCycle n k : ℝ) ≤ c * k * (n : ℝ)^(1 + 1/(k : ℝ))

/--
**Benson's Theorem (1966):**
For k = 3: ex(n; C_6) ≥ c·n^{4/3} for some c > 0.
For k = 5: ex(n; C_{10}) ≥ c·n^{6/5} for some c > 0.

Benson constructed explicit graphs (generalized polygons) achieving
the conjectured lower bound for these cases.
-/
axiom benson_k3 :
  ∃ c : ℝ, c > 0 ∧
    ∀ n : ℕ, n ≥ 1 →
      (exCycle n 3 : ℝ) ≥ c * (n : ℝ)^(4/3 : ℝ)

axiom benson_k5 :
  ∃ c : ℝ, c > 0 ∧
    ∀ n : ℕ, n ≥ 1 →
      (exCycle n 5 : ℝ) ≥ c * (n : ℝ)^(6/5 : ℝ)

/--
**Lazebnik-Ustimenko-Woldar Theorem (1995):**
For all k ≥ 3:
  ex(n; C_{2k}) ≥ c·n^{1+2/(3k-3+ν)}
where ν = 0 if k is odd, ν = 1 if k is even.

This is weaker than the conjectured n^{1+1/k} but works for all k.
-/
def luwExponent (k : ℕ) : ℝ :=
  1 + 2 / (3 * k - 3 + if k % 2 = 0 then 1 else 0 : ℝ)

axiom lazebnik_ustimenko_woldar :
  ∀ k : ℕ, k ≥ 3 →
  ∃ c : ℝ, c > 0 ∧
    ∀ n : ℕ, n ≥ 1 →
      (exCycle n k : ℝ) ≥ c * (n : ℝ)^(luwExponent k)

/-
## Part IV: The Conjecture

Erdős's conjecture is that the lower bound should match the upper bound
up to a constant factor.
-/

/--
**Erdős Problem #572 (Conjecture):**
For k ≥ 3, ex(n; C_{2k}) >> n^{1+1/k}.

That is, there exists c > 0 such that ex(n; C_{2k}) ≥ c·n^{1+1/k}.
-/
def erdosConjectureLowerBound (k : ℕ) : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ n : ℕ, n ≥ 1 →
      (exCycle n k : ℝ) ≥ c * (n : ℝ)^(1 + 1/(k : ℝ))

/--
**Erdős Problem #572: Partial Solution**

The conjecture is proved for k = 3 and k = 5 (Benson 1966).
For other k, only the weaker LUW bound is known.
-/
theorem erdos_572_k3 : erdosConjectureLowerBound 3 := by
  unfold erdosConjectureLowerBound
  obtain ⟨c, hc_pos, hc⟩ := benson_k3
  use c
  constructor
  · exact hc_pos
  · intro n hn
    have h := hc n hn
    -- 4/3 = 1 + 1/3, so this follows from Benson's result
    convert h using 2
    norm_num

theorem erdos_572_k5 : erdosConjectureLowerBound 5 := by
  unfold erdosConjectureLowerBound
  obtain ⟨c, hc_pos, hc⟩ := benson_k5
  use c
  constructor
  · exact hc_pos
  · intro n hn
    have h := hc n hn
    -- 6/5 = 1 + 1/5, so this follows from Benson's result
    convert h using 2
    norm_num

/-
## Part V: Comparison of Exponents

The LUW exponent vs the conjectured exponent.
-/

/--
The conjectured exponent is 1 + 1/k.
-/
def conjecturedExponent (k : ℕ) : ℝ := 1 + 1 / (k : ℝ)

/--
The LUW exponent is always less than or equal to the conjectured exponent.
-/
theorem luw_weaker_than_conjectured (k : ℕ) (hk : k ≥ 3) :
    luwExponent k ≤ conjecturedExponent k := by
  unfold luwExponent conjecturedExponent
  -- For k ≥ 3, we have 3k - 3 + ν ≥ 2k, so 2/(3k-3+ν) ≤ 1/k
  sorry

/--
For k = 3 (odd), LUW gives exponent 1 + 2/6 = 4/3, matching the conjecture.
-/
theorem luw_matches_k3 : luwExponent 3 = conjecturedExponent 3 := by
  unfold luwExponent conjecturedExponent
  norm_num

/--
For k = 4 (even), LUW gives 1 + 2/10 = 6/5 = 1.2, but conjecture is 1 + 1/4 = 1.25.
-/
theorem luw_gap_k4 : luwExponent 4 < conjecturedExponent 4 := by
  unfold luwExponent conjecturedExponent
  norm_num

/--
For k = 5 (odd), LUW gives 1 + 2/12 = 7/6 ≈ 1.167, but Benson achieves 1 + 1/5 = 1.2.
-/
theorem luw_vs_benson_k5 : luwExponent 5 < conjecturedExponent 5 := by
  unfold luwExponent conjecturedExponent
  norm_num

/-
## Part VI: Special Cases

The case k = 2 (4-cycles) is well-understood.
-/

/--
**Erdős-Klein Theorem (1938):**
ex(n; C_4) ~ (1/2)·n^{3/2}

The extremal graphs are related to finite projective planes.
-/
axiom erdos_klein_c4 :
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
    ∀ n : ℕ, n ≥ 1 →
      c₁ * (n : ℝ)^(3/2 : ℝ) ≤ (exCycle n 2 : ℝ) ∧
      (exCycle n 2 : ℝ) ≤ c₂ * (n : ℝ)^(3/2 : ℝ)

/--
C_4-free graphs and the Kővári-Sós-Turán theorem.
For bipartite graphs, ex(n; C_4) is related to the Zarankiewicz problem.
-/

/-
## Part VII: Odd Cycles

For odd cycles, the situation is completely different.
-/

/--
**Odd Cycle Extremal Function:**
ex(n; C_{2k+1}) = ⌊n²/4⌋ for k ≥ 1 and n > 2k+1.

The extremal graphs are complete bipartite graphs K_{⌊n/2⌋, ⌈n/2⌉}.
This is because bipartite graphs contain no odd cycles.
-/
axiom odd_cycle_extremal :
  ∀ k n : ℕ, k ≥ 1 → n > 2 * k + 1 →
    exCycle n (2 * k + 1) = n^2 / 4

/-
## Part VIII: Main Results Summary
-/

/--
**Erdős Problem #572: Summary**

1. **Conjecture:** ex(n; C_{2k}) >> n^{1+1/k} for k ≥ 3
2. **Proved:** For k = 3 and k = 5 (Benson 1966)
3. **Best general bound:** ex(n; C_{2k}) >> n^{1+2/(3k-3+ν)} (LUW 1995)
4. **Upper bound:** ex(n; C_{2k}) << k·n^{1+1/k} (Bondy-Simonovits 1974)
5. **Status:** Conjecture open for k = 4 and k ≥ 6
-/
theorem erdos_572_summary :
    erdosConjectureLowerBound 3 ∧
    erdosConjectureLowerBound 5 ∧
    luwExponent 3 = conjecturedExponent 3 := by
  exact ⟨erdos_572_k3, erdos_572_k5, luw_matches_k3⟩

/--
The best known lower bounds.
-/
theorem best_known_lower_bounds :
    -- k = 3 achieves the conjectured bound
    (∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 → (exCycle n 3 : ℝ) ≥ c * (n : ℝ)^(4/3 : ℝ)) ∧
    -- k = 5 achieves the conjectured bound
    (∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 → (exCycle n 5 : ℝ) ≥ c * (n : ℝ)^(6/5 : ℝ)) ∧
    -- General k uses LUW bound
    (∀ k : ℕ, k ≥ 3 → ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      (exCycle n k : ℝ) ≥ c * (n : ℝ)^(luwExponent k)) :=
  ⟨benson_k3, benson_k5, lazebnik_ustimenko_woldar⟩

end Erdos572
