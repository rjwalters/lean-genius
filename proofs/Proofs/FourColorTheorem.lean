/-
  The Four Color Theorem

  Every planar graph can be colored with at most four colors such that
  no two adjacent vertices share the same color.

  This formalization presents the key conceptual components of the proof:
  1. Planar graphs and colorability
  2. Euler's formula for planar graphs
  3. The Five Color Theorem (a tractable warm-up)
  4. Kempe chains and color swapping
  5. Reducibility and unavoidability
  6. The main theorem

  This is an illustrative proof sketch. The complete proof (Appel-Haken 1976,
  Gonthier 2005) requires computer verification of 1,936 configurations.

  Historical note: First posed in 1852, proved in 1976, and formally
  verified in Coq in 2005 by Georges Gonthier.
-/

namespace FourColor

-- ============================================================
-- PART 1: Graph Theory Foundations
-- ============================================================

-- A graph is a set of vertices with edges between them
structure Graph where
  Vertex : Type
  Edge : Vertex → Vertex → Prop
  edge_symm : ∀ u v, Edge u v → Edge v u

-- A coloring assigns colors to vertices
def Coloring (G : Graph) (k : Nat) := G.Vertex → Fin k

-- A coloring is proper if adjacent vertices have different colors
def ProperColoring (G : Graph) (k : Nat) (c : Coloring G k) : Prop :=
  ∀ u v, G.Edge u v → c u ≠ c v

-- A graph is k-colorable if it admits a proper k-coloring
def Colorable (G : Graph) (k : Nat) : Prop :=
  ∃ c : Coloring G k, ProperColoring G k c

-- Every graph is colorable with enough colors (trivial upper bound)
-- Assign each vertex a unique color from 0 to n-1
axiom trivial_colorable : ∀ G : Graph, ∃ k, Colorable G k

-- The chromatic number is the minimum k for which G is k-colorable
noncomputable def chromaticNumber (G : Graph) : Nat :=
  Nat.find (trivial_colorable G)

-- ============================================================
-- PART 2: Planar Graphs
-- ============================================================

-- A graph is planar if it can be embedded in the plane without edge crossings
-- We axiomatize this property
axiom Planar : Graph → Prop

-- Planarity is preserved under subgraphs
axiom planar_subgraph : ∀ G H, Planar G → (∀ v, H.Vertex = G.Vertex) →
  (∀ u v, H.Edge u v → G.Edge u v) → Planar H

-- ============================================================
-- PART 3: Euler's Formula
-- ============================================================

-- For a connected planar graph: V - E + F = 2
-- where V = vertices, E = edges, F = faces (including outer face)

-- Count of vertices, edges, and faces for a finite planar graph
axiom vertexCount : Graph → Nat
axiom edgeCount : Graph → Nat
axiom faceCount : Graph → Nat

-- Euler's formula for connected planar graphs
axiom euler_formula : ∀ G, Planar G →
  vertexCount G - edgeCount G + faceCount G = 2

-- Key consequence: every planar graph has a vertex of degree ≤ 5
-- This follows from Euler's formula via an averaging argument

-- Degree of a vertex (number of neighbors)
-- We axiomatize this as it requires finiteness assumptions on the graph
axiom degree : (G : Graph) → G.Vertex → Nat

-- Every planar graph with at least one vertex has a vertex of degree ≤ 5
axiom exists_low_degree_vertex : ∀ G, Planar G →
  (∃ _ : G.Vertex, True) → ∃ v : G.Vertex, degree G v ≤ 5

-- ============================================================
-- PART 4: The Five Color Theorem (Warm-up)
-- ============================================================

/-
  The Five Color Theorem is much easier to prove than Four Color.
  We prove it by induction on vertices:

  Base case: The empty graph is trivially 5-colorable.

  Inductive step: Given a planar graph G with n vertices:
  1. Find a vertex v of degree ≤ 5 (guaranteed by Euler)
  2. Remove v to get G' with n-1 vertices
  3. By induction, G' is 5-colorable
  4. Restore v: it has ≤ 5 neighbors, using ≤ 5 colors
  5. Since we have 5 colors and ≤ 5 neighbors, one color is always free
-/

-- Graph with a vertex removed
axiom removeVertex : (G : Graph) → G.Vertex → Graph

-- Removing a vertex preserves planarity
axiom remove_preserves_planar : ∀ G v, Planar G → Planar (removeVertex G v)

-- Induction principle for graphs based on vertex count
-- If a property holds for graphs with fewer vertices, it holds for all
axiom graph_induction :
  ∀ (P : Graph → Prop),
  (∀ G, (∀ G', vertexCount G' < vertexCount G → P G') → P G) →
  ∀ G, P G

-- Key lemma: removing a low-degree vertex and extending the coloring
axiom extend_coloring_5 : ∀ G v,
  Planar G → degree G v ≤ 5 →
  Colorable (removeVertex G v) 5 →
  Colorable G 5

-- Five Color Theorem
theorem five_color_theorem : ∀ G, Planar G → Colorable G 5 := by
  intro G hPlanar
  -- Use graph induction on vertex count
  apply graph_induction (fun G => Planar G → Colorable G 5)
  intro G' ih hPlanar'
  -- Find a vertex of degree ≤ 5
  by_cases h : ∃ _ : G'.Vertex, True
  case pos =>
    -- Graph has at least one vertex
    obtain ⟨v, hv⟩ := exists_low_degree_vertex G' hPlanar' h
    -- Remove v, color the rest by induction
    have hSmaller : vertexCount (removeVertex G' v) < vertexCount G' := by
      exact Nat.pred_lt (by omega)  -- removing a vertex decreases count
    have hPlanar'' := remove_preserves_planar G' v hPlanar'
    have hColorable := ih (removeVertex G' v) hSmaller hPlanar''
    -- Extend the coloring to include v
    exact extend_coloring_5 G' v hPlanar' hv hColorable
  case neg =>
    -- Empty graph is trivially colorable
    exact ⟨fun v => (h ⟨v, trivial⟩).elim, fun u v _ => (h ⟨u, trivial⟩).elim⟩
  exact hPlanar

-- ============================================================
-- PART 5: Kempe Chains
-- ============================================================

/-
  Kempe's brilliant idea: given a proper coloring, we can "swap" colors
  along connected components of vertices using two colors.

  A Kempe chain for colors a and b starting at vertex v is the maximal
  connected component of vertices colored a or b that contains v.

  Swapping a ↔ b on a Kempe chain produces another proper coloring.

  This technique is key to both the Five and Four Color theorems,
  but Kempe's original application to Four Colors was flawed.
-/

-- A Kempe chain is a path of alternating colors
structure KempeChain (G : Graph) (k : Nat) (c : Coloring G k) where
  color1 : Fin k
  color2 : Fin k
  vertices : List G.Vertex
  colors_differ : color1 ≠ color2
  alternating : ∀ v ∈ vertices, c v = color1 ∨ c v = color2
  connected : ∀ i (hi : i + 1 < vertices.length),
    G.Edge (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩)

-- Swapping colors on a Kempe chain preserves properness
axiom kempe_swap_proper : ∀ G k (c : Coloring G k) (chain : KempeChain G k c),
  ProperColoring G k c →
  ∃ c', ProperColoring G k c' ∧
    (∀ v ∈ chain.vertices,
      (c v = chain.color1 → c' v = chain.color2) ∧
      (c v = chain.color2 → c' v = chain.color1)) ∧
    (∀ v, v ∉ chain.vertices → c' v = c v)

-- ============================================================
-- PART 6: Reducibility
-- ============================================================

/-
  A configuration C is REDUCIBLE if:
  Whenever C appears in a planar graph G, we can conclude G is 4-colorable
  without directly coloring G.

  Specifically: if G contains C, we can find a smaller graph G' such that
  any 4-coloring of G' extends to a 4-coloring of G (possibly with
  Kempe chain adjustments).

  Checking reducibility requires case analysis of how colorings extend.
  For the Four Color Theorem, this analysis is too complex for humans
  and required computer verification.
-/

-- A configuration is a small graph pattern
structure Configuration where
  pattern : Graph
  boundary : List pattern.Vertex  -- vertices connected to rest of graph

-- A configuration is reducible if it can always be eliminated
-- in the search for a minimal counterexample
def Reducible (C : Configuration) : Prop :=
  ∀ G, Planar G →
    -- If G contains C...
    (∃ embed : C.pattern.Vertex → G.Vertex,
      ∀ u v, C.pattern.Edge u v → G.Edge (embed u) (embed v)) →
    -- Then G is 4-colorable
    Colorable G 4

-- Key fact: there exists a set of 1,936 reducible configurations
-- (verified by computer in Appel-Haken and formalized by Gonthier)
axiom reducible_configurations : List Configuration
axiom all_reducible : ∀ C ∈ reducible_configurations, Reducible C

-- ============================================================
-- PART 7: Unavoidability
-- ============================================================

/-
  A set S of configurations is UNAVOIDABLE if every planar graph
  contains at least one configuration from S.

  The proof uses "discharging": assign initial charges to vertices
  based on degree, then redistribute charges according to rules.
  The total charge is fixed by Euler's formula. If we can show the
  final charge implies some configuration must exist, we're done.

  Appel and Haken showed their 1,936 configurations are unavoidable.
-/

def Unavoidable (configs : List Configuration) : Prop :=
  ∀ G, Planar G → ∃ C ∈ configs,
    ∃ embed : C.pattern.Vertex → G.Vertex,
      ∀ u v, C.pattern.Edge u v → G.Edge (embed u) (embed v)

-- The discharging method proves unavoidability
-- Initial charge: 6 - degree(v) for each vertex
-- Discharging rules redistribute charge while preserving total
-- Final analysis shows some reducible configuration must appear

axiom unavoidable_set : Unavoidable reducible_configurations

-- ============================================================
-- PART 8: Computer Verification
-- ============================================================

/-
  The Appel-Haken proof (1976) required:
  - 1,200 hours of computer time
  - Verification of 1,936 configurations
  - 400+ pages of hand verification for discharging rules

  Many mathematicians were skeptical: How do we know the program is correct?

  Georges Gonthier's Coq formalization (2005) addressed this:
  - Every step machine-checked by Coq's small trusted kernel
  - The proof itself is a certificate anyone can verify
  - Reduced trust from "large program" to "small proof checker"

  This established a new paradigm: formal proof as the gold standard
  for complex mathematical theorems.
-/

-- We axiomatize that the computer verification was successful
axiom computer_verified_reducibility :
  ∀ C ∈ reducible_configurations, Reducible C

axiom computer_verified_unavoidability :
  Unavoidable reducible_configurations

-- ============================================================
-- PART 9: The Four Color Theorem
-- ============================================================

/-
  Main argument by contradiction:

  1. Suppose there exists a non-4-colorable planar graph
  2. Take a minimal counterexample G (fewest vertices)
  3. By unavoidability, G contains some reducible configuration C
  4. By reducibility of C, G can be simplified to G'
  5. G' is smaller, so by minimality, G' is 4-colorable
  6. But reducibility means G' being 4-colorable implies G is 4-colorable
  7. Contradiction!

  Therefore, all planar graphs are 4-colorable.
-/

-- A minimal counterexample (if it existed)
def MinimalCounterexample (G : Graph) : Prop :=
  Planar G ∧ ¬Colorable G 4 ∧
  ∀ G', Planar G' → vertexCount G' < vertexCount G → Colorable G' 4

-- No minimal counterexample exists
theorem no_minimal_counterexample : ¬∃ G, MinimalCounterexample G := by
  intro ⟨G, hMin⟩
  -- G contains some unavoidable configuration C
  have ⟨C, hC_in, embed, hEmbed⟩ := unavoidable_set G hMin.1
  -- C is reducible
  have hRed := all_reducible C hC_in
  -- Therefore G is 4-colorable
  have hCol := hRed G hMin.1 ⟨embed, hEmbed⟩
  -- Contradiction with ¬Colorable G 4
  exact hMin.2.1 hCol

-- Well-founded induction gives us: if no minimal counterexample, then all are colorable
axiom no_counterexample_implies_colorable :
  (¬∃ G, MinimalCounterexample G) →
  ∀ G, Planar G → Colorable G 4

-- The Four Color Theorem
theorem four_color_theorem : ∀ G, Planar G → Colorable G 4 := by
  -- Use the fact that no minimal counterexample exists
  exact no_counterexample_implies_colorable no_minimal_counterexample

-- If G is k-colorable, then chromaticNumber G ≤ k
axiom colorable_implies_chromatic_le : ∀ G k, Colorable G k → chromaticNumber G ≤ k

-- Stated in terms of chromatic number
theorem chromatic_number_at_most_four : ∀ G, Planar G → chromaticNumber G ≤ 4 := by
  intro G hPlanar
  have h := four_color_theorem G hPlanar
  exact colorable_implies_chromatic_le G 4 h

-- ============================================================
-- PART 10: Philosophical Implications
-- ============================================================

/-
  The Four Color Theorem raised profound questions:

  1. WHAT IS A PROOF?
     Traditional proofs can be surveyed by humans. The Four Color proof
     cannot—it essentially relies on computer verification. Is this still
     mathematics?

  2. TRUST AND VERIFICATION
     We trust the proof because we trust the computer program. But programs
     have bugs. Gonthier's Coq formalization shifts trust to a smaller
     kernel: the proof checker itself.

  3. FORMALIZATION AS FOUNDATION
     Rather than trusting informal arguments or large programs, we can
     trust machine-checked formal proofs. The proof *is* the certificate.

  4. THE FUTURE OF MATHEMATICS
     As theorems grow more complex, computer assistance becomes essential.
     The question is not whether to use computers, but how to ensure
     correctness. Formal verification provides one answer.

  5. BEAUTY VS TRUTH
     Many mathematicians hoped for an "elegant" proof of Four Color.
     The computer-assisted proof is undeniably ugly but undeniably correct.
     Does mathematical aesthetics matter if we have certainty?
-/

-- ============================================================
-- PART 11: Summary
-- ============================================================

/-
  The Proof in a Nutshell:

  1. EULER'S CONSTRAINT: Planar graphs have structural limitations
     (every planar graph has a vertex of degree ≤ 5)

  2. FIVE COLORS: Easy by induction—always one spare color

  3. FOUR COLORS: Kempe chains help, but don't quite work
     (Kempe's 1879 "proof" was flawed)

  4. REDUCIBILITY: Certain configurations can be eliminated from
     any minimal counterexample

  5. UNAVOIDABILITY: Every planar graph contains at least one
     reducible configuration (proved by discharging)

  6. COMPUTER VERIFICATION: Both reducibility and unavoidability
     require checking 1,936 configurations by computer

  7. CONCLUSION: No minimal counterexample exists, so every
     planar graph is 4-colorable

  The genius was combining classical graph theory with computational
  muscle—and later, with formal verification to ensure correctness.
-/

end FourColor

-- Final type check of the main theorems
#check @FourColor.four_color_theorem
#check @FourColor.five_color_theorem
#check @FourColor.no_minimal_counterexample
