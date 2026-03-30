/-
Erdős Problem #615: Ramsey-Turán Number rt(n; 4, n/log n)

Source: https://erdosproblems.com/615
Status: SOLVED (Fox-Loh-Zhao, 2015)

Statement:
Does there exist some constant c > 0 such that if G is a graph with n vertices
and >= (1/8 - c)n² edges then G must contain either a K₄ or an independent set
on at least n/log n vertices?

Answer: NO

Background:
The Ramsey-Turán number rt(n; k, ℓ) is the maximum number of edges in an
n-vertex graph containing no Kₖ and no independent set of size ℓ.

The question asks: is rt(n; 4, n/log n) < (1/8 - c)n² for some c > 0?

History:
- Erdős-Hajnal-Simonovits-Sós-Szemerédi [EHSSS93] posed the problem
- Erdős-Hajnal-Sós-Szemerédi [EHSS83] proved rt(n; 4, εn) < (1/8 + o(1))n²
- Sudakov [Su03] proved rt(n; 4, ne^(-f(n))) = o(n²) when f(n)/√log n → ∞
- Fox-Loh-Zhao [FLZ15] resolved it: rt(n; 4, ne^(-f(n))) >= (1/8 - o(1))n²
  when f(n) = o(√(log n / log log n))

Reference:
- Fox, Loh, Zhao (2015): "The critical window for the classical Ramsey-Turán
  problem", Combinatorica
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Finite.Basic

open SimpleGraph

namespace Erdos615

/-
## Part I: Core Definitions

Ramsey-Turán theory combines extremal graph theory and Ramsey theory.
-/

-- ehss_upper_bound: unused axiom removed (never referenced by any theorem)
**Sudakov (2003):**
rt(n; 4, ne^(-f(n))) = o(n²) whenever f(n)/√log n → ∞

This shows that for "very slow" growth of the independence number bound,
the Ramsey-Turán number becomes subquadratic.
-/
-- sudakov_upper_bound: unused axiom removed (never referenced by any theorem)
## Part IV: Fox-Loh-Zhao Resolution

The answer to the conjecture is NO.
-/

-- fox_loh_zhao_lower_bound: unused axiom removed (never referenced by any theorem)
**Corollary: The Conjecture is FALSE**
There is no c > 0 such that rt(n; 4, n/log n) < (1/8 - c)n²

Proof: For f(n) = log n, we have n/log n = ne^(-log n).
Since log n = o(√(log n / log log n)), the Fox-Loh-Zhao theorem gives
rt(n; 4, n/log n) >= (1/8 - o(1))n².
-/
axiom erdos_615_false : ¬erdos_615_conjecture

-- turan_k4: unused axiom removed (never referenced by any theorem)
**Linear Independence Number:**
rt(n; 4, εn) = (1/8 + o(1))n² for any fixed ε > 0

The 1/8 threshold appears when we require α(G) < εn.
-/
axiom rt_linear : ∀ ε : ℝ, ε > 0 →
  ∀ δ : ℝ, δ > 0 →
  ∀ᶠ n : ℕ in Filter.atTop,
    |((rt n 4 (Nat.floor (ε * n)) : ℝ) / n^2) - threshold_one_eighth| < δ

-- rt_turan_bound: unused axiom removed (never referenced by any theorem)
## Part VIII: The Construction

Fox-Loh-Zhao's proof constructs a specific graph achieving (1/8 - o(1))n² edges.
-/

-- simonovits_sos_construction: unused axiom removed (never referenced by any theorem)
## Part IX: Main Results Summary
-/

/--
**Erdős Problem #615 Summary:**

Question: Is rt(n; 4, n/log n) < (1/8 - c)n² for some c > 0?
Answer: NO (Fox-Loh-Zhao, 2015)

Key results:
1. For linear α(G) < εn: rt = (1/8 + o(1))n² (Erdős et al.)
2. For very slow growth f(n)/√log n → ∞: rt = o(n²) (Sudakov)
3. Critical window at f(n) ≈ √(log n / log log n) (Fox-Loh-Zhao)
4. For n/log n: rt = (1/8 - o(1))n², disproving the conjecture
-/
theorem erdos_615_summary :
    ¬erdos_615_conjecture ∧
    (∀ ε : ℝ, ε > 0 →
      ∀ δ : ℝ, δ > 0 →
      ∀ᶠ n : ℕ in Filter.atTop,
        |((rt n 4 (Nat.floor (ε * n)) : ℝ) / n^2) - threshold_one_eighth| < δ) := by
  exact ⟨erdos_615, rt_linear⟩

/--
**The answer to Erdős #615 is NO.**
The threshold 1/8 cannot be improved for independence number n/log n.
-/
theorem erdos_615_answer : ¬erdos_615_conjecture := erdos_615

end Erdos615
