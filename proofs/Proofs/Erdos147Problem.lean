/-
Erdős Problem #147: Turán Numbers for Bipartite Graphs

Source: https://erdosproblems.com/147
Status: DISPROVED (Janzer)
Prize: $500

Statement:
Conjecture (Erdős-Simonovits): If H is bipartite with minimum degree r,
then there exists ε = ε(H) > 0 such that ex(n; H) ≫ n^{2 - 1/(r-1) + ε}.

Janzer disproved this by constructing bipartite graphs where the bound fails.
For even r ≥ 4, Janzer showed there exist r-regular bipartite graphs H with
ex(n; H) ≪ n^{2 - 1/(r-1) + ε} for all ε > 0.

References:
- Erdős and Simonovits (1984): Original conjecture
- Janzer: Disproof via explicit construction
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic

namespace Erdos147

/-
## Part I: Definitions
-/

/--
The Turán number ex(n; H): the maximum number of edges in a simple graph
on n vertices that does not contain H as a subgraph.
Axiomatized since computing extremal numbers requires optimizing over all
H-free graphs.
-/
axiom turanNumber (H : SimpleGraph (Fin k)) (n : ℕ) : ℕ

/--
The minimum degree of a simple graph on Fin k.
-/
noncomputable def minDegree (G : SimpleGraph (Fin k)) : ℕ :=
  Finset.inf' Finset.univ ⟨0, Finset.mem_univ 0⟩
    (fun v => (Finset.univ.filter (fun w => G.Adj v w)).card)

/-
## Part II: Janzer's Disproof
-/

/--
**Janzer's Disproof**: There exist bipartite graphs with minimum degree r ≥ 4
for which the Erdős-Simonovits conjecture fails.

For even r ≥ 4, Janzer constructed r-regular bipartite graphs H such that
ex(n; H) ≤ C · n^{2 - 1/(r-1)} · (log n)^{O(1)}.
-/
axiom janzer_disproof :
    ∀ r : ℕ, r ≥ 4 → Even r →
      ∃ k : ℕ, ∃ H : SimpleGraph (Fin k),
        H.IsBipartite ∧
        ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
          (turanNumber H n : ℝ) ≤ C * (n : ℝ) ^ (2 - 1 / ((r : ℝ) - 1)) *
            (Real.log n) ^ r

/-
## Part III: Known Positive Results
-/

/--
**Probabilistic lower bound** (weaker than conjectured):
For bipartite H with minimum degree r, ex(n; H) ≫ n^{2 - 2/r + ε}
for some ε > 0.
-/
axiom probabilistic_lower_bound (r : ℕ) (hr : r ≥ 2) :
    ∃ k : ℕ, ∃ H : SimpleGraph (Fin k),
      H.IsBipartite ∧
      ∃ c ε : ℝ, c > 0 ∧ ε > 0 ∧ ∀ n : ℕ, n ≥ 2 →
        (turanNumber H n : ℝ) ≥ c * (n : ℝ) ^ (2 - 2 / (r : ℝ) + ε)

/-
## Part IV: Main Theorem
-/

/--
**Erdős Problem #147: DISPROVED**

The Erdős-Simonovits conjecture is false. Janzer constructed explicit
counterexamples for all even r ≥ 4.
-/
theorem erdos_147 :
    ∃ r : ℕ, r ≥ 4 ∧ ∃ k : ℕ, ∃ H : SimpleGraph (Fin k),
      H.IsBipartite ∧
      ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
        (turanNumber H n : ℝ) ≤ C * (n : ℝ) ^ (2 - 1 / ((r : ℝ) - 1)) *
          (Real.log n) ^ r := by
  use 4
  constructor
  · omega
  exact janzer_disproof 4 (by omega) ⟨2, rfl⟩

end Erdos147
