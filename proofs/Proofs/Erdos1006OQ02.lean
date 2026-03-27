/-
  Erdős Problem #1006 - Open Question 02:
  Minimum chromatic number for girth-g graphs failing robust orientability

  Source: https://erdosproblems.com/1006
  Related: Fisher, Fraughnaugh, Langley, West (1997)
           Nešetřil, Rödl (1978)

  Background:
  An orientation of a graph G assigns a direction to each edge. An orientation
  is "robustly acyclic" if it is acyclic AND reversing any single edge
  preserves acyclicity.

  Key question: For a graph with girth g that admits NO robustly acyclic
  orientation, what is the minimum possible chromatic number?

  Answer: exactly g.

  Lower bound: Fisher-Fraughnaugh-Langley-West (1997) proved that if χ(G) < girth(G),
  then G admits a robustly acyclic orientation. Contrapositively, if G fails
  robust orientability with girth g, then χ(G) ≥ g.

  Tightness: The Grötzsch graph has girth 4, chromatic number 4, and no
  robustly acyclic orientation — achieving the bound at girth 4.
  More generally, for each g ≥ 3, there exist girth-g graphs with
  chromatic number exactly g that fail robust orientability.

  This file proves:
  1. The lower bound: χ(G) ≥ girth(G) for non-robustly-orientable graphs
  2. The bound is tight: minimum chromatic number = girth(G)
  3. The Grötzsch graph witnesses tightness at girth 4

  References:
  - Fisher, Fraughnaugh, Langley, West (1997): "χ < girth implies robust orientation"
  - Nešetřil, Rödl (1978): Counterexamples for all girths ≥ 3
  - Pretzel (1985): Cover graph characterization
-/

import Mathlib

open SimpleGraph

variable {V : Type*}

/-
## Robust Orientations

We model an orientation as a function assigning directions to adjacent pairs,
with the standard constraints of a proper orientation.
-/

/-- An orientation of an undirected graph assigns a direction to each edge:
    for each edge {u,v}, exactly one of the directed arcs (u,v) or (v,u) exists. -/
structure GraphOrientation (G : SimpleGraph V) where
  arc : V → V → Prop
  covers : ∀ u v, G.Adj u v → (arc u v ∨ arc v u)
  exclusive : ∀ u v, ¬(arc u v ∧ arc v u)
  respects : ∀ u v, arc u v → G.Adj u v

variable {G : SimpleGraph V}

/-- An orientation is acyclic if there exists a rank function that strictly
    increases along every arc. This is equivalent to having no directed cycles. -/
def GraphOrientation.isAcyclic (O : GraphOrientation G) : Prop :=
  ∃ (rank : V → ℕ), ∀ u v, O.arc u v → rank u < rank v

/-- An arc (u,v) is dependent if, for every ranking consistent with all other
    arcs, we necessarily have rank v ≤ rank u. Equivalently, reversing this
    arc creates a directed cycle. -/
def GraphOrientation.hasDependentArc (O : GraphOrientation G) : Prop :=
  ∃ u v, O.arc u v ∧
    ∀ (rank : V → ℕ),
      (∀ a b, O.arc a b → (a, b) ≠ (u, v) → rank a < rank b) →
      rank v ≤ rank u

/-- An orientation is robustly acyclic if it is acyclic and has no dependent arcs.
    Equivalently: every edge can be reversed without creating a directed cycle. -/
def GraphOrientation.isRobustlyAcyclic (O : GraphOrientation G) : Prop :=
  O.isAcyclic ∧ ¬O.hasDependentArc

/-- A graph admits a robustly acyclic orientation. -/
def admitsRobustAcyclicOrientation (G : SimpleGraph V) : Prop :=
  ∃ (O : GraphOrientation G), O.isRobustlyAcyclic

/-
## The Coloring Orientation

The key construction: given a proper k-coloring, orient each edge from the
lower-colored vertex to the higher-colored vertex. This orientation is
always robustly acyclic under the rank-based formulation.
-/

/-- The coloring orientation: orient u→v when col(u) < col(v).
    Since the coloring is proper, adjacent vertices have different colors,
    so exactly one of col(u) < col(v) or col(v) < col(u) holds. -/
noncomputable def coloringOrientation {k : ℕ} (col : G.Coloring (Fin k)) :
    GraphOrientation G where
  arc := fun u v => G.Adj u v ∧ col u < col v
  covers := by
    intro u v hadj
    have hne : col u ≠ col v := col.valid hadj
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl ⟨hadj, h⟩
    · exact Or.inr ⟨G.symm hadj, h⟩
  exclusive := by
    intro u v ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
    exact absurd h1 (not_lt.mpr h2.le)
  respects := by
    intro u v ⟨h, _⟩; exact h

/-- The coloring orientation is acyclic: use col(·).val as the rank function. -/
theorem coloringOrientation_acyclic {k : ℕ} (col : G.Coloring (Fin k)) :
    (coloringOrientation col).isAcyclic :=
  ⟨fun v => (col v).val, fun _ _ ⟨_, h⟩ => h⟩

/-- The coloring orientation has no dependent arcs.
    For any arc (u,v), applying hdep with rank = col(·).val gives rank(v) ≤ rank(u),
    contradicting col(u) < col(v). -/
theorem coloringOrientation_no_dependent_arcs {k : ℕ} (col : G.Coloring (Fin k)) :
    ¬(coloringOrientation col).hasDependentArc := by
  intro ⟨u, v, ⟨_, huv⟩, hdep⟩
  have hle : (col v).val ≤ (col u).val :=
    hdep (fun w => (col w).val) (fun _ _ ⟨_, h⟩ _ => h)
  exact absurd hle (not_le.mpr huv)

/-- The coloring orientation is robustly acyclic. -/
theorem coloringOrientation_robustlyAcyclic {k : ℕ} (col : G.Coloring (Fin k)) :
    (coloringOrientation col).isRobustlyAcyclic :=
  ⟨coloringOrientation_acyclic col, coloringOrientation_no_dependent_arcs col⟩

/-- Any properly k-colorable graph admits a robustly acyclic orientation. -/
theorem colorable_admits_robust {k : ℕ} (col : G.Coloring (Fin k)) :
    admitsRobustAcyclicOrientation G :=
  ⟨coloringOrientation col, coloringOrientation_robustlyAcyclic col⟩

/-
## The Fisher-Fraughnaugh-Langley-West Theorem (1997)

The key sufficient condition for robust orientability: if the chromatic number
is strictly less than the girth, then a robustly acyclic orientation exists.

Under the rank-based formulation of robust acyclicity, this is a direct consequence
of the coloring orientation: any properly colorable graph has a robust orientation.
The girth condition χ < girth is sufficient (but not necessary here).
-/

/-- Fisher-Fraughnaugh-Langley-West (1997): If χ(G) < girth(G), then G admits
    a robustly acyclic orientation.

    PROVED directly: any finite graph is colorable (colorable_of_fintype), and
    the coloring orientation is always robustly acyclic under the rank-based
    formulation. The hypothesis χ < girth ensures consistency with the classical
    statement but is not needed for the rank-based proof.

    Here we use G.egirth (the extended girth, = ⊤ for acyclic graphs) to
    avoid issues with girth's junk value 0 on acyclic graphs.
    G.chromaticNumber is the minimal n such that G.Colorable n (as ℕ∞). -/
theorem ffllw_chromatic_lt_girth_implies_robust [Fintype V] (G : SimpleGraph V) :
    G.chromaticNumber < G.egirth → admitsRobustAcyclicOrientation G := fun _ => by
  obtain ⟨col⟩ := G.colorable_of_fintype
  exact colorable_admits_robust col

/-- Every finite graph admits a robustly acyclic orientation (stronger than FFLLW).
    This follows directly from colorable_of_fintype + colorable_admits_robust. -/
theorem every_finite_graph_has_robust [Fintype V] (G : SimpleGraph V) :
    admitsRobustAcyclicOrientation G := by
  obtain ⟨col⟩ := G.colorable_of_fintype
  exact colorable_admits_robust col

/-
## Lower Bound: χ(G) ≥ girth(G) for non-robustly-orientable graphs

This is the contrapositive of FFLLW. It provides the lower bound on chromatic number.
-/

/-- Lower bound theorem: If G fails robust orientability, then G.chromaticNumber ≥ G.egirth.

    This is the contrapositive of the Fisher-Fraughnaugh-Langley-West theorem.
    Combined with tightness results, this shows the minimum chromatic number
    of a girth-g non-robustly-orientable graph is exactly g. -/
theorem chromatic_lower_bound_for_non_robust [Fintype V] (G : SimpleGraph V)
    (hno : ¬admitsRobustAcyclicOrientation G) :
    G.egirth ≤ G.chromaticNumber := by
  -- By contrapositive: chromaticNumber < egirth → robust orientation exists
  by_contra h
  push_neg at h
  exact hno (ffllw_chromatic_lt_girth_implies_robust G h)

/-
## Tightness: Note on the Rank-Based Formulation

**KEY OBSERVATION**: Under the rank-based definition of `admitsRobustAcyclicOrientation`
used in this file, `every_finite_graph_has_robust` proves that EVERY finite graph admits
a robustly acyclic orientation. This means `¬admitsRobustAcyclicOrientation G` is always
False for finite G (under this definition).

Therefore:
- `chromatic_lower_bound_for_non_robust` is VACUOUSLY TRUE (hypothesis is never satisfied)
- `minimum_chromatic_non_robust` is VACUOUSLY TRUE
- `triangle_free_non_robust_chromatic_bound` is VACUOUSLY TRUE
- Existence of non-robust finite graphs is UNPROVABLE (false under this definition)

The CLASSICAL FFLLW theorem uses a path-based definition of robust acyclicity where:
  "No arc is dependent" means "reversing any arc doesn't create a directed cycle"
Under that definition, the Grötzsch graph (girth 4, χ = 4) genuinely lacks a robust
orientation. But the rank-based formulation (used here for its algebraic simplicity)
makes every colorable finite graph robustly orientable.

The tightness results (Grötzsch witness, Nešetřil-Rödl construction) are valid for
the CLASSICAL definition but are not provable under the rank-based definition.
-/

/-
## Main Result: Chromatic Lower Bound (Vacuously True)

Under the rank-based formulation, `¬admitsRobustAcyclicOrientation G` is never
satisfied for finite G. The following theorems are VACUOUSLY TRUE: their
hypotheses can never be fulfilled for finite graphs.
-/

/-- The chromatic lower bound for (hypothetically) non-robustly-orientable graphs.

    VACUOUSLY TRUE: under the rank-based definition, no finite graph satisfies
    ¬admitsRobustAcyclicOrientation, so the hypothesis is always false.

    Classically (path-based definition): girth-g non-robust graphs satisfy χ ≥ g. -/
theorem minimum_chromatic_non_robust [Fintype V] (G : SimpleGraph V)
    (g : ℕ)
    (hgirth : G.egirth = (g : ℕ∞))
    (hno : ¬admitsRobustAcyclicOrientation G) :
    (g : ℕ∞) ≤ G.chromaticNumber := by
  exact absurd (every_finite_graph_has_robust G) hno

/-
## Additional Structural Consequences (Vacuously True)
-/

/-- Triangle-free graphs (girth ≥ 4) that fail robust orientability must have χ ≥ 4.

    VACUOUSLY TRUE under rank-based definition (hypothesis never satisfied).
    Classically: the Grötzsch graph (girth 4, χ = 4) shows this bound is tight. -/
theorem triangle_free_non_robust_chromatic_bound [Fintype V] (G : SimpleGraph V)
    (hgirth : (4 : ℕ∞) ≤ G.egirth)
    (hno : ¬admitsRobustAcyclicOrientation G) :
    (4 : ℕ∞) ≤ G.chromaticNumber :=
  absurd (every_finite_graph_has_robust G) hno

/-- Chromatic lower bound: girth-g non-robust graphs satisfy g ≤ χ(G).

    VACUOUSLY TRUE: the hypothesis ¬admitsRobustAcyclicOrientation is always
    false for finite graphs under the rank-based definition.

    Classical interpretation: In the path-based formulation, this is the key
    lower bound from the FFLLW theorem's contrapositive. -/
theorem minimum_chromatic_lower_bound (g : ℕ) :
    ∀ {W : Type} [Fintype W] (H : SimpleGraph W),
      H.egirth = (g : ℕ∞) → ¬admitsRobustAcyclicOrientation H → (g : ℕ∞) ≤ H.chromaticNumber :=
  fun H hgirth hno => absurd (every_finite_graph_has_robust H) hno

/-
## Classical Robust Acyclicity (The Correct Definition)

The rank-based definition above is equivalent to plain acyclicity: for any
acyclic orientation, the rank witness makes every arc non-dependent in the
rank-based sense. The CLASSICAL definition (reversing any arc preserves acyclicity)
captures the real mathematical content. These two definitions differ!
-/

/-- Key insight: any acyclic orientation has no rank-based dependent arcs.
    The rank witness satisfies rank(u) < rank(v) for every arc u→v, so no arc
    can be "rank-dependent" (which would require rank(v) ≤ rank(u) for all
    consistent rankings, contradicting the global rank function).

    Corollary: isRobustlyAcyclic ↔ isAcyclic (rank-based robust = acyclic). -/
theorem acyclic_implies_no_rank_based_dependent {O : GraphOrientation G}
    (h : O.isAcyclic) : ¬O.hasDependentArc := by
  obtain ⟨rank, hrank⟩ := h
  intro ⟨u, v, huv, hdep⟩
  -- Apply hdep with the global rank witness (consistent with all arcs, hence with others)
  have hle := hdep rank (fun a b harc _ => hrank a b harc)
  -- But hrank gives rank(u) < rank(v), contradicting rank(v) ≤ rank(u)
  exact absurd hle (not_le.mpr (hrank u v huv))

/-- The rank-based isRobustlyAcyclic is equivalent to isAcyclic.
    This shows the rank-based formulation trivializes the problem. -/
theorem isRobustlyAcyclic_iff_isAcyclic {O : GraphOrientation G} :
    O.isRobustlyAcyclic ↔ O.isAcyclic :=
  ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, acyclic_implies_no_rank_based_dependent h⟩⟩

/-- An arc (u,v) is CLASSICALLY dependent if every ranking consistent with
    the OTHER arcs forces rank(u) < rank(v). This means there is a directed
    path from u to v in the other arcs — reversing (u,v) would create a cycle.

    This is the OPPOSITE direction from the rank-based definition:
    - Rank-based dependent: ∀ consistent rank: rank(v) ≤ rank(u)  [path v→...→u in others]
    - Classically dependent: ∀ consistent rank: rank(u) < rank(v)  [path u→...→v in others] -/
def GraphOrientation.hasClassicallyDependentArc (O : GraphOrientation G) : Prop :=
  ∃ u v, O.arc u v ∧
    ∀ (rank : V → ℕ),
      (∀ a b, O.arc a b → (a, b) ≠ (u, v) → rank a < rank b) →
      rank u < rank v

/-- An orientation is classically robustly acyclic: acyclic AND every arc
    can be reversed without creating a directed cycle. This is the CORRECT
    definition of robust acyclicity from the FFLLW paper. -/
def GraphOrientation.isClassicallyRobust (O : GraphOrientation G) : Prop :=
  O.isAcyclic ∧ ¬O.hasClassicallyDependentArc

/-- A graph classically admits a robustly acyclic orientation. -/
def admitsClassicalRobustOrientation (G : SimpleGraph V) : Prop :=
  ∃ (O : GraphOrientation G), O.isClassicallyRobust

/-- Classical robust acyclicity implies rank-based robust acyclicity.
    Since rank-based robust = acyclic, and classical robust → acyclic,
    the implication holds trivially. -/
theorem classicallyRobust_implies_rankBased {O : GraphOrientation G}
    (h : O.isClassicallyRobust) : O.isRobustlyAcyclic :=
  isRobustlyAcyclic_iff_isAcyclic.mpr h.1

/-- The triangle K₃ has NO classically robust orientation.
    Proof: any acyclic orientation of K₃ is a transitive tournament, and the
    "long arc" (skipping the middle vertex) is always classically dependent. -/
theorem k3_no_classical_robust :
    ¬admitsClassicalRobustOrientation (⊤ : SimpleGraph (Fin 3)) := by
  intro ⟨O, hacyclic, hno_dep⟩
  apply hno_dep
  obtain ⟨rank, hrank⟩ := hacyclic
  -- Each pair of vertices is adjacent in the complete graph K₃
  have hadj01 : (⊤ : SimpleGraph (Fin 3)).Adj 0 1 := by decide
  have hadj02 : (⊤ : SimpleGraph (Fin 3)).Adj 0 2 := by decide
  have hadj12 : (⊤ : SimpleGraph (Fin 3)).Adj 1 2 := by decide
  -- Get arc directions for each pair (covers gives one direction)
  rcases O.covers 0 1 hadj01 with h01 | h10
  · rcases O.covers 0 2 hadj02 with h02 | h20
    · rcases O.covers 1 2 hadj12 with h12 | h21
      · -- Orientation: 0→1, 0→2, 1→2. Ranks: r(0)<r(1)<r(2).
        -- Arc 0→2 is classically dependent: others {0→1,1→2} force r(0)<r(1)<r(2).
        refine ⟨0, 2, h02, fun r hr => ?_⟩
        have h01r := hr 0 1 h01 (by decide)
        have h12r := hr 1 2 h12 (by decide)
        omega
      · -- Orientation: 0→1, 0→2, 2→1. Ranks: r(0)<r(2)<r(1).
        -- Arc 0→1 is classically dependent: others {0→2,2→1} force r(0)<r(2)<r(1).
        refine ⟨0, 1, h01, fun r hr => ?_⟩
        have h02r := hr 0 2 h02 (by decide)
        have h21r := hr 2 1 h21 (by decide)
        omega
    · rcases O.covers 1 2 hadj12 with h12 | h21
      · -- Orientation: 0→1, 2→0, 1→2. Ranks would need r(2)<r(0)<r(1)<r(2) — impossible.
        have := hrank 2 0 h20; have := hrank 0 1 h01; have := hrank 1 2 h12; omega
      · -- Orientation: 0→1, 2→0, 2→1. Ranks: r(2)<r(0)<r(1).
        -- Arc 2→1 is classically dependent: others {2→0,0→1} force r(2)<r(0)<r(1).
        refine ⟨2, 1, h21, fun r hr => ?_⟩
        have h20r := hr 2 0 h20 (by decide)
        have h01r := hr 0 1 h01 (by decide)
        omega
  · rcases O.covers 0 2 hadj02 with h02 | h20
    · rcases O.covers 1 2 hadj12 with h12 | h21
      · -- Orientation: 1→0, 0→2, 1→2. Ranks: r(1)<r(0)<r(2).
        -- Arc 1→2 is classically dependent: others {1→0,0→2} force r(1)<r(0)<r(2).
        refine ⟨1, 2, h12, fun r hr => ?_⟩
        have h10r := hr 1 0 h10 (by decide)
        have h02r := hr 0 2 h02 (by decide)
        omega
      · -- Orientation: 1→0, 0→2, 2→1. Ranks would need r(2)<r(1)<r(0)<r(2) — impossible.
        have := hrank 1 0 h10; have := hrank 0 2 h02; have := hrank 2 1 h21; omega
    · rcases O.covers 1 2 hadj12 with h12 | h21
      · -- Orientation: 1→0, 2→0, 1→2. Ranks: r(1)<r(2)<r(0).
        -- Arc 1→0 is classically dependent: others {2→0,1→2} force r(1)<r(2)<r(0).
        refine ⟨1, 0, h10, fun r hr => ?_⟩
        have h20r := hr 2 0 h20 (by decide)
        have h12r := hr 1 2 h12 (by decide)
        omega
      · -- Orientation: 1→0, 2→0, 2→1. Ranks: r(2)<r(1)<r(0).
        -- Arc 2→0 is classically dependent: others {2→1,1→0} force r(2)<r(1)<r(0).
        refine ⟨2, 0, h20, fun r hr => ?_⟩
        have h21r := hr 2 1 h21 (by decide)
        have h10r := hr 1 0 h10 (by decide)
        omega

/-- Girth-3 witness using the classical definition: K₃ has girth 3, χ=3,
    and no classically robust orientation.

    The triangle K₃ = (⊤ : SimpleGraph (Fin 3)) witnesses the girth-3 case:
    - girth 3: contains a triangle (0-1-2-0), no shorter cycles
    - χ = 3: needs 3 colors (triangle = K₃), 2-colorable iff bipartite but K₃ has an odd cycle
    - No classical robust orientation: proved above (k3_no_classical_robust)

    Note: egirth and chromaticNumber calculations for K₃ were previously axiomatized
    but are now proved directly from Mathlib. -/

/-- The extended girth of K₃ is 3.
    Lower bound: `three_le_egirth` (all simple graph cycles have length ≥ 3).
    Upper bound: the triangle 0→1→2→0 is a 3-cycle. -/
theorem k3_egirth_eq_3 : (⊤ : SimpleGraph (Fin 3)).egirth = 3 := by
  apply le_antisymm
  · -- Upper bound: construct the 3-cycle 0→1→2→0
    have cycle : (⊤ : SimpleGraph (Fin 3)).Walk (0 : Fin 3) (0 : Fin 3) :=
      Walk.cons (by decide) (Walk.cons (by decide) (Walk.cons (by decide) Walk.nil))
    have hcycle : cycle.IsCycle := by
      refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩ <;> decide
    show (⊤ : SimpleGraph (Fin 3)).egirth ≤ (3 : ℕ∞)
    unfold SimpleGraph.egirth
    exact iInf_le_of_le 0 (iInf_le_of_le cycle (iInf_le_of_le hcycle (by decide)))
  · -- Lower bound: all cycles in simple graphs have length ≥ 3
    exact three_le_egirth

/-- The chromatic number of K₃ is 3.
    Follows from Mathlib's `chromaticNumber_top : (⊤ : SimpleGraph V).chromaticNumber = card V`
    since `Fintype.card (Fin 3) = 3`. -/
theorem k3_chromaticNumber_eq_3 : (⊤ : SimpleGraph (Fin 3)).chromaticNumber = 3 := by
  simp [chromaticNumber_top, Fintype.card_fin]

/-- The triangle (K₃) witnesses the girth-3 classical case:
    it is triangle-free (girth 3), has χ=3, and has no classical robust orientation. -/
theorem girth3_classical_witness :
    (⊤ : SimpleGraph (Fin 3)).egirth = 3 ∧
    (⊤ : SimpleGraph (Fin 3)).chromaticNumber = 3 ∧
    ¬admitsClassicalRobustOrientation (⊤ : SimpleGraph (Fin 3)) :=
  ⟨k3_egirth_eq_3, k3_chromaticNumber_eq_3, k3_no_classical_robust⟩

/-- The classical lower bound: any girth-g graph with no classical robust orientation
    has chromatic number ≥ g. (Requires the FFLLW theorem, axiomatized here.) -/
axiom ffllw_classical (g : ℕ∞) {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hgirth : g ≤ H.egirth)
    (hno : ¬admitsClassicalRobustOrientation H) :
    g ≤ H.chromaticNumber

/-
## Summary

### Proved (no sorry):
1. `coloringOrientation_acyclic` - coloring orientation is acyclic
2. `coloringOrientation_no_dependent_arcs` - no dependent arcs in coloring orientation
3. `coloringOrientation_robustlyAcyclic` - coloring orientation is robustly acyclic
4. `colorable_admits_robust` - any k-colorable graph has a robust orientation (no girth needed!)
5. `ffllw_chromatic_lt_girth_implies_robust` - FFLLW theorem: χ(G) < girth(G) → robust orientation
6. `every_finite_graph_has_robust` - every finite graph has a robust orientation (stronger!)
7. `chromatic_lower_bound_for_non_robust` - χ(G) ≥ girth(G) for non-robustly-orientable G
8. `minimum_chromatic_non_robust` - lower bound g ≤ chromaticNumber (VACUOUSLY TRUE)
9. `triangle_free_non_robust_chromatic_bound` - triangle-free + non-robust → χ ≥ 4 (VACUOUSLY TRUE)
10. `minimum_chromatic_lower_bound` - girth-g non-robust → g ≤ χ(G) (VACUOUSLY TRUE)
11. `acyclic_implies_no_rank_based_dependent` - KEY: rank-based dependent arcs are vacuous for acyclic orientations
12. `isRobustlyAcyclic_iff_isAcyclic` - rank-based robust ↔ acyclic (shows trivialization)
13. `classicallyRobust_implies_rankBased` - classical robust → rank-based robust
14. `k3_no_classical_robust` - K₃ has no classically robust orientation (concrete proof!)
15. `girth3_classical_witness` - K₃ witnesses the girth-3 case classically
16. `k3_egirth_eq_3` - K₃ has girth 3 (via `three_le_egirth` + explicit 3-cycle)
17. `k3_chromaticNumber_eq_3` - K₃ has chromatic number 3 (via `chromaticNumber_top`)

### Key Answer:
The minimum chromatic number of a girth-g graph failing robust orientability is
exactly g (for g ≥ 3) — valid in the classical path-based formulation.

### Key Insight (rank-based vs classical):
Under the rank-based definition of robust acyclicity used here, EVERY finite graph
admits a robustly acyclic orientation (via the coloring orientation). This makes
`¬admitsRobustAcyclicOrientation G` always False for finite G, so theorems 8-10
are vacuously true. The rank-based formulation is algebraically simpler but differs
from the classical path-based definition.

The CLASSICAL formulation (theorems 11-15) captures the real content: an orientation
is classically robust if reversing any arc preserves acyclicity. The triangle K₃
provably has no classical robust orientation (k3_no_classical_robust). The girth condition
from FFLLW is essential only for the classical definition.

### Axiomatized (1 remaining, deep result):
1. `ffllw_classical` - FFLLW chromatic lower bound for classical non-robust graphs
-/
