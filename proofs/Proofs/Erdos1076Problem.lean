/-
  Erdős Problem #1076: Extremal Numbers for 3-Uniform Hypergraphs

  Source: https://erdosproblems.com/1076
  Status: SOLVED (Bohman-Warnke 2019, Glock-Kühn-Lo-Osthus 2020)

  Statement:
  Let k ≥ 5 and let F_k be the family of all 3-uniform hypergraphs with k
  vertices and k-2 edges. Is it true that ex₃(n, F_k) ~ n²/6?

  Answer: YES (PROVED)

  Key Results:
  - Brown-Erdős-Sós (1973): Proved for k=4, showed ex₃(n, F_k) ≍_k n²
  - Erdős (1974): Supporting theorem about 5-vertex and 6-vertex subgraphs
  - Bohman-Warnke (2019): Proved the asymptotic
  - Glock-Kühn-Lo-Osthus (2020): Independent proof

  Related Problems:
  - #207: Stronger version with exact extremal numbers

  References:
  - [BES73] Brown-Erdős-Sós, "Some extremal problems on r-graphs" (1973)
  - [BoWa19] Bohman-Warnke, "Large girth approximate Steiner triple systems" (2019)
  - [GKLO20] Glock-Kühn-Lo-Osthus, "On a conjecture of Erdős..." (2020)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic

open Real Filter

namespace Erdos1076

/-
## Part I: 3-Uniform Hypergraphs
-/

/-- A 3-uniform hypergraph on n vertices is a collection of 3-element subsets. -/
structure Hypergraph3 (n : ℕ) where
  edges : Finset (Fin n × Fin n × Fin n)
  uniform : ∀ e ∈ edges, e.1 < e.2.1 ∧ e.2.1 < e.2.2

/-- The number of edges in a 3-uniform hypergraph. -/
def numEdges (H : Hypergraph3 n) : ℕ := H.edges.card

/-- The number of vertices involved in at least one edge. -/
def numVertices (H : Hypergraph3 n) : ℕ :=
  (H.edges.image (fun e => ({e.1, e.2.1, e.2.2} : Finset (Fin n)))).sup id |>.card

/-- A hypergraph in F_k: k vertices and k-2 edges. -/
def IsInFamilyF (k : ℕ) (H : Hypergraph3 n) : Prop :=
  numVertices H = k ∧ numEdges H = k - 2

/-
## Part II: The Family F_k
-/

/-- The family F_k of all 3-uniform hypergraphs with k vertices and k-2 edges. -/
def FamilyF (k n : ℕ) : Set (Hypergraph3 n) :=
  { H | IsInFamilyF k H }

/-- For k = 4: F_4 consists of hypergraphs with 4 vertices and 2 edges. -/
theorem family_F4_description :
    ∀ (H : Hypergraph3 n), H ∈ FamilyF 4 n ↔ numVertices H = 4 ∧ numEdges H = 2 := by
  intro H
  simp [FamilyF, IsInFamilyF]

/-- For k = 5: F_5 consists of hypergraphs with 5 vertices and 3 edges. -/
theorem family_F5_description :
    ∀ (H : Hypergraph3 n), H ∈ FamilyF 5 n ↔ numVertices H = 5 ∧ numEdges H = 3 := by
  intro H
  simp [FamilyF, IsInFamilyF]

/-- For k = 6: F_6 consists of hypergraphs with 6 vertices and 4 edges. -/
theorem family_F6_description :
    ∀ (H : Hypergraph3 n), H ∈ FamilyF 6 n ↔ numVertices H = 6 ∧ numEdges H = 4 := by
  intro H
  simp [FamilyF, IsInFamilyF]

/-
## Part III: Subgraph Containment
-/

/-- A hypergraph H contains a copy of G as a subgraph. -/
def ContainsSubgraph (H : Hypergraph3 n) (G : Hypergraph3 m) : Prop :=
  ∃ (f : Fin m → Fin n), Function.Injective f ∧
    ∀ e ∈ G.edges, (f e.1, f e.2.1, f e.2.2) ∈ H.edges ∨
      (f e.1, f e.2.2, f e.2.1) ∈ H.edges ∨
      (f e.2.1, f e.1, f e.2.2) ∈ H.edges ∨
      (f e.2.1, f e.2.2, f e.1) ∈ H.edges ∨
      (f e.2.2, f e.1, f e.2.1) ∈ H.edges ∨
      (f e.2.2, f e.2.1, f e.1) ∈ H.edges

/-- A hypergraph is F_k-free if it contains no member of F_k. -/
def IsFkFree (k : ℕ) (H : Hypergraph3 n) : Prop :=
  ∀ G : Hypergraph3 n, G ∈ FamilyF k n → ¬ContainsSubgraph H G

/-
## Part IV: Extremal Numbers
-/

/-- The extremal number ex₃(n, F_k): max edges in an F_k-free 3-uniform hypergraph on n vertices. -/
noncomputable def ex3 (n k : ℕ) : ℕ :=
  Nat.find (⟨0, by
    use ⟨∅, by simp⟩
    constructor
    · intro G _ h; exact h.elim
    · simp [numEdges]
  ⟩ : ∃ m, ∃ H : Hypergraph3 n, IsFkFree k H ∧ numEdges H ≥ m)

/-- The extremal number is achieved by some hypergraph. -/
axiom ex3_achieved (n k : ℕ) (hk : k ≥ 4) :
  ∃ H : Hypergraph3 n, IsFkFree k H ∧ numEdges H = ex3 n k

/-
## Part V: Brown-Erdős-Sós Results (1973)
-/

/-- Brown-Erdős-Sós (1973): For k = 4, ex₃(n, F_4) ~ n²/6. -/
axiom brown_erdos_sos_k4 :
  Tendsto (fun n => (ex3 n 4 : ℝ) / n^2) atTop (nhds (1/6))

/-- Brown-Erdős-Sós (1973): For all k ≥ 4, ex₃(n, F_k) = Θ_k(n²). -/
axiom brown_erdos_sos_general (k : ℕ) (hk : k ≥ 4) :
  ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
    ∀ n : ℕ, n ≥ k → c₁ * n^2 ≤ (ex3 n k : ℝ) ∧ (ex3 n k : ℝ) ≤ c₂ * n^2

/-
## Part VI: Erdős's Supporting Theorem (1974)
-/

/-- Erdős (1974): Hypergraphs with > (1/3)C(n,2) edges contain F_5 or F_6 members. -/
axiom erdos_1974_supporting (n : ℕ) (H : Hypergraph3 n)
    (hH : (numEdges H : ℝ) > (1/3) * (n * (n-1) / 2)) :
  (∃ G, G ∈ FamilyF 5 n ∧ ContainsSubgraph H G) ∨
  (∃ G, G ∈ FamilyF 6 n ∧ ContainsSubgraph H G)

/-- The threshold (1/3)C(n,2) is relevant for the conjecture. -/
def thresholdEdges (n : ℕ) : ℝ := (1/3) * (n * (n-1) / 2)

/-- Note: n²/6 ≈ (1/3)C(n,2) asymptotically. -/
theorem threshold_asymptotic (n : ℕ) (hn : n > 0) :
    thresholdEdges n = n^2/6 - n/6 := by
  simp [thresholdEdges]
  ring

/-
## Part VII: The Main Conjecture
-/

/-- The Brown-Erdős-Sós Conjecture: ex₃(n, F_k) ~ n²/6 for all k ≥ 5. -/
def BrownErdosSosConjecture : Prop :=
  ∀ k : ℕ, k ≥ 5 → Tendsto (fun n => (ex3 n k : ℝ) / n^2) atTop (nhds (1/6))

/-- Equivalent formulation with explicit limits. -/
def BrownErdosSosConjecture' : Prop :=
  ∀ k : ℕ, k ≥ 5 → ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    |(ex3 n k : ℝ) / n^2 - 1/6| < ε

/-
## Part VIII: The Solution
-/

/-- **Bohman-Warnke Theorem (2019):**
    The conjecture is TRUE for all k ≥ 5. -/
axiom bohman_warnke_theorem : BrownErdosSosConjecture

/-- **Glock-Kühn-Lo-Osthus Theorem (2020):**
    Independent proof of the same result. -/
axiom glock_kuhn_lo_osthus_theorem : BrownErdosSosConjecture

/-- The asymptotic is n²/6 for all k ≥ 5. -/
theorem ex3_asymptotic (k : ℕ) (hk : k ≥ 5) :
    Tendsto (fun n => (ex3 n k : ℝ) / n^2) atTop (nhds (1/6)) :=
  bohman_warnke_theorem k hk

/-
## Part IX: Upper and Lower Bounds
-/

/-- Upper bound: ex₃(n, F_k) ≤ (1/6 + o(1))n². -/
theorem ex3_upper_bound (k : ℕ) (hk : k ≥ 5) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, (ex3 n k : ℝ) ≤ (1/6 + ε) * n^2 := by
  intro ε hε
  have h := ex3_asymptotic k hk
  sorry

/-- Lower bound: ex₃(n, F_k) ≥ (1/6 - o(1))n². -/
theorem ex3_lower_bound (k : ℕ) (hk : k ≥ 5) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, (ex3 n k : ℝ) ≥ (1/6 - ε) * n^2 := by
  intro ε hε
  have h := ex3_asymptotic k hk
  sorry

/-
## Part X: Connection to Steiner Triple Systems
-/

/-- A Steiner triple system of order n: partition of pairs into triples. -/
def IsSteinerTripleSystem (H : Hypergraph3 n) : Prop :=
  ∀ i j : Fin n, i ≠ j → ∃! e ∈ H.edges, (i = e.1 ∨ i = e.2.1 ∨ i = e.2.2) ∧
    (j = e.1 ∨ j = e.2.1 ∨ j = e.2.2)

/-- The number of edges in an STS(n) is n(n-1)/6. -/
theorem sts_num_edges (n : ℕ) (H : Hypergraph3 n) (hH : IsSteinerTripleSystem H) :
    (numEdges H : ℝ) = n * (n-1) / 6 := by
  sorry

/-- Connection: extremal hypergraphs are related to approximate STS. -/
def extremalSTSConnection : Prop :=
  -- The extremal number n²/6 corresponds to near-STS density
  -- Large girth approximate STS constructions achieve the bound
  True

/-
## Part XI: Exact Results for Special k
-/

/-- For k satisfying divisibility conditions, exact values are known. -/
axiom exact_values_divisibility (k : ℕ) (hk : k ≥ 4)
    (hdiv : ∃ m : ℕ, k = 3*m + 1 ∨ k = 3*m) :
  ∃ f : ℕ → ℕ, ∀ n : ℕ, n ≥ k → ex3 n k = f n

/-- Related Problem #207 gives exact extremal numbers. -/
def problem207Connection : Prop :=
  -- Problem #207 is a stronger version asking for exact values
  -- This problem #1076 asks only for asymptotics
  True

/-
## Part XII: Summary
-/

/-- **Erdős Problem #1076: SOLVED**

Question: For k ≥ 5, is ex₃(n, F_k) ~ n²/6?

Answer: YES (Bohman-Warnke 2019, Glock-Kühn-Lo-Osthus 2020)

The family F_k consists of 3-uniform hypergraphs with k vertices and k-2 edges.
The extremal number ex₃(n, F_k) = (1/6 + o(1))n² for all k ≥ 5.
This matches the density of Steiner triple systems.
-/
theorem erdos_1076 : BrownErdosSosConjecture := bohman_warnke_theorem

/-- Main result: the conjecture is TRUE. -/
theorem erdos_1076_main : BrownErdosSosConjecture := erdos_1076

/-- The problem is solved for all k ≥ 5. -/
theorem erdos_1076_solved (k : ℕ) (hk : k ≥ 5) :
    Tendsto (fun n => (ex3 n k : ℝ) / n^2) atTop (nhds (1/6)) :=
  erdos_1076 k hk

end Erdos1076
