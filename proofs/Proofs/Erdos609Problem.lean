/-
  Erdős Problem #609: Monochromatic Odd Cycles in Edge Colorings

  Source: https://erdosproblems.com/609
  Status: OPEN

  Statement:
  Let f(n) be the minimal m such that if the edges of K_{2^n+1} are colored
  with n colors, then there must be a monochromatic odd cycle of length ≤ m.

  Estimate f(n).

  Key Observations:
  - K_{2^n} CAN be n-colored avoiding all monochromatic odd cycles (doubling construction)
  - K_{2^n+1} forces at least one monochromatic odd cycle
  - How short must this forced cycle be?

  Best Known Bounds:
    - Lower: f(n) ≥ 2^{c√(log n)} [Day-Johnson 2017] — f(n) → ∞
    - Upper: f(n) ≤ C · 2^n / n [Girão-Hunter 2024]
    - Upper: f(n) ≤ C · n^{3/2} · 2^{n/2} [Janzer-Yip 2025] — improvement!

  The exponential gap between lower and upper bounds means the problem is far from solved.

  Timeline:
    - 1997: Chung asked whether f(n) → ∞
    - 2017: Day-Johnson proved f(n) → ∞ via lower bound 2^{c√(log n)}
    - 2024: Girão-Hunter gave first "almost matching" upper bound 2^n / n^{1-o(1)}
    - 2025: Janzer-Yip improved upper bound to n^{3/2} · 2^{n/2}

  References:
    [DJ17] Day, Johnson, "Coloring by cycle length" (2017)
    [GH24] Girão, Hunter, "Monochromatic odd cycles" (2024)
    [JY25] Janzer, Yip, "Improved bounds for monochromatic odd cycles" (2025)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real SimpleGraph

namespace Erdos609

/- ## Part I: Graph Colorings and Odd Cycles -/

/-- An n-edge-coloring of a vertex type V assigns a color in Fin n to each edge. -/
def EdgeColoring (V : Type*) (n : ℕ) := Sym2 V → Fin n

/-- A coloring is **bipartite in color c** if the monochromatic-c subgraph is bipartite.
    Equivalently, there are no odd monochromatic-c cycles. -/
def ColorIsBipartite {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (G : SimpleGraph V) (coloring : EdgeColoring V n) (c : Fin n) : Prop :=
  (G.spanningCoe (fun e => coloring e = c)).IsBipartite

/-- The **complete graph** K_N on Fin N. -/
abbrev K (N : ℕ) : SimpleGraph (Fin N) := SimpleGraph.completeGraph (Fin N)

/-- A coloring of K_{2^n+1} with n colors has a **monochromatic odd cycle of length ≤ m**
    if some color class contains an odd closed walk of length ≤ m. -/
axiom HasMonoOddCycle {n : ℕ} (coloring : EdgeColoring (Fin (2^n + 1)) n) (m : ℕ) : Prop

/- ## Part II: The Threshold Phenomenon -/

/-- **K_{2^n} can be n-colored with no monochromatic odd cycles.**

    The **doubling construction**: Build the coloring inductively.
    - Base (n=1): K_2 has only one edge; color it red. No odd cycles (only 2 vertices).
    - Step (n → n+1): Given a valid n-coloring of K_{2^n}, take two disjoint copies
      A = {0,...,2^n-1} and B = {2^n,...,2^{n+1}-1}. Color edges within A and within B
      using the old n colors (bipartite by hypothesis). Color all A-B cross edges with
      the new (n+1)-th color. The cross edges form a complete bipartite graph K_{2^n, 2^n},
      which is bipartite — so no odd monochromatic cycles in the new color. -/
axiom K_2n_avoids_odd_cycles (n : ℕ) :
    ∃ coloring : EdgeColoring (Fin (2^n)) n,
      ∀ m : ℕ, ¬HasMonoOddCycle coloring m

/-- **K_{2^n+1} forces a monochromatic odd cycle** (for n ≥ 1).

    The extra vertex tips the balance: with 2^n+1 vertices but only 2^n configurations,
    by the pigeonhole argument on bipartite colorings, at least one color must contain
    an odd cycle. This is the key threshold result. -/
axiom K_2n_plus_1_forces_odd_cycle (n : ℕ) (hn : n ≥ 1) :
    ∀ coloring : EdgeColoring (Fin (2^n + 1)) n,
      ∃ m : ℕ, HasMonoOddCycle coloring m

/- ## Part III: The Function f(n) -/

/-- **f(n)**: the minimal m such that every n-coloring of K_{2^n+1} has a monochromatic
    odd cycle of length ≤ m.

    Axiomatized: defining this via Nat.find requires the existence proof
    (from K_2n_plus_1_forces_odd_cycle) and care about the finiteness of the minimum. -/
axiom f : ℕ → ℕ

/-- The defining property of f(n): for any n-coloring of K_{2^n+1}, there is a
    monochromatic odd cycle of length ≤ f(n). -/
axiom f_forces (n : ℕ) (hn : n ≥ 1) :
    ∀ coloring : EdgeColoring (Fin (2^n + 1)) n, HasMonoOddCycle coloring (f n)

/-- The minimality of f(n): for any m < f(n), some n-coloring of K_{2^n+1} avoids
    monochromatic odd cycles of length ≤ m. -/
axiom f_minimal (n : ℕ) (hn : n ≥ 1) (m : ℕ) (hm : m < f n) :
    ∃ coloring : EdgeColoring (Fin (2^n + 1)) n, ¬HasMonoOddCycle coloring m

/-- **Short odd cycles can be avoided**: For any fixed odd cycle length k, and
    sufficiently large n, some n-coloring of K_{2^n+1} avoids all odd cycles of
    length ≤ k. (This shows f(n) → ∞.) -/
axiom short_cycles_avoidable (k : ℕ) (hk : Odd k) (hk3 : k ≥ 3) :
    ∃ N : ℕ, ∀ n ≥ N,
      ∃ coloring : EdgeColoring (Fin (2^n + 1)) n, ¬HasMonoOddCycle coloring k

/- ## Part IV: Known Bounds on f(n) -/

/-- **Chung's Question (1997)**: Does f(n) → ∞?

    Formally: for every M, there exists N such that f(n) ≥ M for all n ≥ N. -/
def chungQuestion : Prop :=
  ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N, f n ≥ M

/-- **Day-Johnson (2017)**: f(n) ≥ 2^{c·√(log n)} for some c > 0.

    This answered Chung's question affirmatively: the forced odd cycles
    must be exponentially long in √(log n). -/
axiom day_johnson_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ n ≥ 2, (f n : ℝ) ≥ 2 ^ (c * Real.sqrt (Real.log n))

/-- **Chung's question answered** (Day-Johnson 2017): f(n) → ∞.

    Follows from the Day-Johnson lower bound since 2^{c·√(log n)} → ∞. -/
axiom f_tends_to_infinity : chungQuestion

/-- **Girão-Hunter (2024)**: f(n) ≤ C · 2^n / n for some C > 0.

    The first bound showing f(n) is subexponential in n (up to a factor of n). -/
axiom girao_hunter_upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ n ≥ 2, (f n : ℝ) ≤ C * 2^n / n

/-- **Janzer-Yip (2025)**: f(n) ≤ C · n^{3/2} · 2^{n/2} for some C > 0.

    A significant improvement: the upper bound drops from Θ(2^n/n) to O(n^{3/2} · 2^{n/2}),
    cutting the exponent in the 2-power from n to n/2. -/
axiom janzer_yip_upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ n ≥ 2, (f n : ℝ) ≤ C * n ^ ((3 : ℝ) / 2) * 2 ^ ((n : ℝ) / 2)

/- ## Part V: The Gap -/

/-
**Current knowledge summary:**

  2^{c√(log n)} ≤ f(n) ≤ C · n^{3/2} · 2^{n/2}

The ratio of upper to lower bound is:
  C · n^{3/2} · 2^{n/2} / 2^{c√(log n)} = C · n^{3/2} · 2^{n/2 - c√(log n)}

As n → ∞, n/2 - c√(log n) → ∞, so the gap is SUPER-EXPONENTIAL.

This means our understanding of f(n) is fundamentally incomplete.

**Conjectured true behavior**: Neither bound is expected to be sharp.
The gap suggests f(n) lies somewhere in a range with no clear "canonical" behavior.
Closing the gap is one of the main open problems in graph Ramsey theory.
-/

/-- The size of the gap between the Janzer-Yip upper bound and Day-Johnson lower bound. -/
noncomputable def boundsGap (n : ℕ) : ℝ :=
  n ^ ((3 : ℝ) / 2) * 2 ^ ((n : ℝ) / 2) / 2 ^ Real.sqrt (Real.log n)

/- ## Part VI: Main Results -/

/-- **Erdős Problem #609 — Best Known Bounds**:

    2^{c·√(log n)} ≤ f(n) ≤ C · n^{3/2} · 2^{n/2}

    This is the current state of knowledge. The exact asymptotics of f(n) are unknown.
    This is an **OPEN** problem. -/
theorem erdos_609_bounds :
    (∃ c : ℝ, c > 0 ∧ ∀ n ≥ 2, (f n : ℝ) ≥ 2 ^ (c * Real.sqrt (Real.log n))) ∧
    (∃ C : ℝ, C > 0 ∧ ∀ n ≥ 2, (f n : ℝ) ≤ C * n ^ ((3 : ℝ) / 2) * 2 ^ ((n : ℝ) / 2)) :=
  ⟨day_johnson_lower_bound, janzer_yip_upper_bound⟩

/-- **Corollary**: f(n) → ∞ (Chung's question answered). -/
theorem erdos_609_unbounded : chungQuestion := f_tends_to_infinity

/-- **The threshold**: K_{2^n} avoids monochromatic odd cycles, but K_{2^n+1} cannot. -/
theorem erdos_609_threshold (n : ℕ) (hn : n ≥ 1) :
    (∃ coloring : EdgeColoring (Fin (2^n)) n, ∀ m, ¬HasMonoOddCycle coloring m) ∧
    (∀ coloring : EdgeColoring (Fin (2^n + 1)) n, ∃ m, HasMonoOddCycle coloring m) :=
  ⟨K_2n_avoids_odd_cycles n, K_2n_plus_1_forces_odd_cycle n hn⟩

/- ## Part VII: Related Problems and Context -/

/-
**Related Erdős Problems:**

- **Erdős #608**: Given the edges of K_n are 2-colored, what is the minimum largest
  monochromatic odd cycle that must appear? A related but simpler (2-color) version
  of the problem.

- **Erdős #610/611**: Other Ramsey-type problems about forced subgraphs in colorings
  of complete graphs.

**Connection to bipartite graphs:**
Each color class avoiding odd cycles must be a bipartite graph. The doubling
construction exploits this: K_{2^n, 2^n} is bipartite, so its edges can be one color
class without creating odd cycles. With n "doublings," we can accommodate n color classes.

The extra vertex in K_{2^n+1} breaks this structure: one vertex connects to both sides
of every bipartition, forcing an odd cycle in some color.

**Graph-theoretic interpretation:**
The condition that a graph is bipartite is equivalent to 2-colorability of vertices (no odd
cycles). So "n-coloring of K_{2^n+1} with no monochromatic odd cycles" = "choosing n bipartite
spanning subgraphs covering all edges of K_{2^n+1}." The threshold is exactly at 2^n+1
vertices.
-/

end Erdos609
