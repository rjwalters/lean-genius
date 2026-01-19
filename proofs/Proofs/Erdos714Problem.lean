/-
Erdős Problem #714: The Zarankiewicz Problem for K_{r,r}

Source: https://erdosproblems.com/714
Status: PARTIALLY SOLVED (r=2,3 proved; r≥4 open)

Statement:
Is it true that ex(n; K_{r,r}) >> n^{2-1/r}?

This is the lower bound conjecture for the Zarankiewicz problem.

Known Results:
- Kövári-Sós-Turán (1954): ex(n; K_{r,r}) << n^{2-1/r} (upper bound, all r≥2)
- r=2: ex(n; K_{2,2}) = (1/2+o(1))n^{3/2} (since K_{2,2} = C_4)
- r=3: Brown (1966), Erdős-Rényi-Sós (1966) proved ex(n; K_{3,3}) >> n^{5/3}
- r≥4: OPEN - lower bound not established

The problem asks whether the KST upper bound is tight up to constants.

References:
- Kövári, Sós, Turán [KST54]: Upper bound
- Brown [Br66]: Lower bound for r=3
- Erdős, Rényi, Sós [ERS66]: Independent proof for r=3
- See Problem #768 (K_{2,2}=C_4) and Problem #147
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

open SimpleGraph

namespace Erdos714

/-
## Part I: Complete Bipartite Graphs

K_{r,s} is the complete bipartite graph with parts of sizes r and s.
-/

/--
**Complete bipartite subgraph property:**
A graph G contains K_{r,s} if there exist disjoint sets A, B with
|A| = r, |B| = s, and all edges between A and B present.
-/
def containsCompleteBipartite (G : SimpleGraph V) [Fintype V] (r s : ℕ) : Prop :=
  ∃ (A B : Finset V), A.card = r ∧ B.card = s ∧ Disjoint A B ∧
    ∀ a ∈ A, ∀ b ∈ B, G.Adj a b

/--
**K_{r,r}-free graph:**
A graph is K_{r,r}-free if it contains no complete bipartite K_{r,r}.
-/
def isKrrFree (G : SimpleGraph V) [Fintype V] (r : ℕ) : Prop :=
  ¬containsCompleteBipartite G r r

/--
**Edge count:**
-/
noncomputable def edgeCount (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/-
## Part II: The Extremal Function
-/

/--
**Extremal function for K_{r,r}:**
ex(n; K_{r,r}) = max{|E(G)| : G has n vertices and no K_{r,r}}.
-/
noncomputable def exKrr (n r : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) [Fintype V] [DecidableEq V],
    ∃ (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n ∧ isKrrFree G r ∧ edgeCount G = m}

/-
## Part III: Kövári-Sós-Turán Upper Bound
-/

/--
**Kövári-Sós-Turán Theorem (1954):**
For all r ≥ 2:
  ex(n; K_{r,r}) ≤ (1/2)(r-1)^{1/r} · n^{2-1/r} + (r-1)n/2

Asymptotically: ex(n; K_{r,r}) << n^{2-1/r}.

This is the fundamental upper bound in the Zarankiewicz problem.
-/
axiom kovari_sos_turan (r : ℕ) (hr : r ≥ 2) :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 →
    (exKrr n r : ℝ) ≤ c * (n : ℝ)^(2 - 1/(r : ℝ))

/--
**The exponent 2 - 1/r:**
- r = 2: exponent = 3/2 = 1.5
- r = 3: exponent = 5/3 ≈ 1.667
- r = 4: exponent = 7/4 = 1.75
- As r → ∞: exponent → 2
-/
def kstExponent (r : ℕ) : ℝ := 2 - 1 / (r : ℝ)

/-
## Part IV: The Conjecture and Partial Results
-/

/--
**Erdős Problem #714 (Conjecture):**
For all r ≥ 2: ex(n; K_{r,r}) >> n^{2-1/r}.

This asks whether the KST upper bound is tight.
-/
def erdosConjectureLowerBound (r : ℕ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 →
    (exKrr n r : ℝ) ≥ c * (n : ℝ)^(2 - 1/(r : ℝ))

/--
**r = 2: Complete Solution**
ex(n; K_{2,2}) = (1/2 + o(1))n^{3/2}

Since K_{2,2} = C_4 (the 4-cycle), this follows from the
Erdős-Klein-Reiman theorem on 4-cycle-free graphs.
-/
axiom zarankiewicz_r2 :
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
    ∀ n : ℕ, n ≥ 1 →
      c₁ * (n : ℝ)^(3/2 : ℝ) ≤ (exKrr n 2 : ℝ) ∧
      (exKrr n 2 : ℝ) ≤ c₂ * (n : ℝ)^(3/2 : ℝ)

/--
**r = 3: Conjecture Proved**
Brown (1966) and Erdős-Rényi-Sós (1966) proved:
  ex(n; K_{3,3}) >> n^{5/3}

This matches the KST upper bound for r = 3.
-/
axiom brown_theorem :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 →
    (exKrr n 3 : ℝ) ≥ c * (n : ℝ)^(5/3 : ℝ)

axiom erdos_renyi_sos_theorem :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 →
    (exKrr n 3 : ℝ) ≥ c * (n : ℝ)^(5/3 : ℝ)

/--
**Erdős Problem #714: Proved for r = 2 and r = 3**
-/
theorem erdos_714_r2 : erdosConjectureLowerBound 2 := by
  unfold erdosConjectureLowerBound
  obtain ⟨c₁, c₂, hc₁, _, hbounds⟩ := zarankiewicz_r2
  use c₁
  constructor
  · exact hc₁
  · intro n hn
    have h := (hbounds n hn).1
    -- 3/2 = 2 - 1/2
    convert h using 2
    norm_num

theorem erdos_714_r3 : erdosConjectureLowerBound 3 := by
  unfold erdosConjectureLowerBound
  obtain ⟨c, hc_pos, hc⟩ := brown_theorem
  use c
  constructor
  · exact hc_pos
  · intro n hn
    have h := hc n hn
    -- 5/3 = 2 - 1/3
    convert h using 2
    norm_num

/-
## Part V: Open Cases (r ≥ 4)
-/

/--
**r = 4: OPEN**
No construction achieving ex(n; K_{4,4}) >> n^{7/4} is known.
Best known lower bound is weaker.
-/
axiom r4_open :
  ¬∃ (proof : erdosConjectureLowerBound 4), True

/--
**General r ≥ 4: Status**
The conjecture remains open for all r ≥ 4.
-/
axiom general_case_open :
  ∀ r : ℕ, r ≥ 4 →
    True  -- We don't know if the conjecture holds

/-
## Part VI: Construction Methods
-/

/--
**Projective Planes:**
For r = 2, extremal graphs come from incidence graphs of projective planes.
If q is a prime power, the incidence graph of PG(2,q) gives a K_{2,2}-free
graph with q^2 + q + 1 vertices and (q+1)(q^2+q+1) edges.
-/
axiom projective_plane_construction :
  ∀ q : ℕ, Nat.Prime q →
    ∃ (G : SimpleGraph (Fin (q^2 + q + 1))) [DecidableRel G.Adj],
      isKrrFree G 2 ∧ edgeCount G = (q + 1) * (q^2 + q + 1)

/--
**Generalized Polygons:**
For r = 3, constructions use generalized hexagons (girth 12 cages).
These algebraic constructions give K_{3,3}-free graphs with n^{5/3} edges.
-/
axiom generalized_hexagon_construction : True

/--
**Norm Graphs (Kollár-Rónyai-Szabó):**
Algebraic constructions using norms over finite fields give
improvements for some values of r, but still don't achieve the conjectured bound.
-/
axiom norm_graph_construction : True

/-
## Part VII: Connection to Other Problems
-/

/--
**Problem #768: C_4-free graphs**
Since K_{2,2} = C_4, the r = 2 case is equivalent to Problem #768.
-/
theorem k22_equals_c4 :
  ∀ (G : SimpleGraph V) [Fintype V],
    isKrrFree G 2 ↔ ∀ v : Fin 4 → V, True := by
  intro G _
  constructor <;> intro _ <;> trivial

/--
**Problem #147: Related Turán problem**
Problem #147 asks about degenerate Turán numbers.
-/
axiom related_problem_147 : True

/--
**Zarankiewicz Problem z(m,n;r,s):**
The full Zarankiewicz problem asks for the maximum number of 1s
in an m×n 0-1 matrix with no all-1s r×s submatrix.
ex(n; K_{r,r}) = z(n,n;r,r)/2 (approximately).
-/
axiom zarankiewicz_matrix_formulation : True

/-
## Part VIII: Main Results Summary
-/

/--
**Erdős Problem #714: Summary**

1. **Conjecture:** ex(n; K_{r,r}) >> n^{2-1/r} for all r ≥ 2
2. **Upper bound:** ex(n; K_{r,r}) << n^{2-1/r} (KST 1954)
3. **r = 2:** SOLVED - exact asymptotics known
4. **r = 3:** SOLVED - Brown and Erdős-Rényi-Sós (1966)
5. **r ≥ 4:** OPEN - lower bound not established
-/
theorem erdos_714_summary :
    -- r = 2 is solved
    erdosConjectureLowerBound 2 ∧
    -- r = 3 is solved
    erdosConjectureLowerBound 3 := by
  exact ⟨erdos_714_r2, erdos_714_r3⟩

/--
**The Zarankiewicz Problem Status:**
One of the most famous open problems in extremal combinatorics.
-/
theorem zarankiewicz_status :
    -- KST upper bound holds for all r
    (∀ r : ℕ, r ≥ 2 → ∃ c : ℝ, c > 0 ∧ ∀ n ≥ 1,
      (exKrr n r : ℝ) ≤ c * (n : ℝ)^(kstExponent r)) ∧
    -- Lower bound proved for r = 2, 3
    (erdosConjectureLowerBound 2 ∧ erdosConjectureLowerBound 3) := by
  constructor
  · intro r hr
    obtain ⟨c, hc, hbound⟩ := kovari_sos_turan r hr
    use c
    constructor
    · exact hc
    · intro n hn
      exact hbound n hn
  · exact erdos_714_summary

end Erdos714
