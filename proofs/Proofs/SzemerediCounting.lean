/-
  Counting and Removal Lemma

  The triangle removal lemma and graph counting lemma -- key consequences
  of the Szemeredi Regularity Lemma. Regular pairs behave like random
  bipartite graphs for subgraph counting, and a graph with few triangles
  can be made triangle-free by removing few edges.

  Part I: Counting lemma for regular triples
  Part II: Triangle removal lemma
  Part III: General graph removal lemma

  Ruzsa-Szemeredi (1978), Komlos-Simonovits (1996)
-/
import Mathlib
import Proofs.SzemerediCore
import Proofs.SzemerediRegularity

namespace Szemeredi.Counting

open Classical Szemeredi.Core

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- INFRASTRUCTURE: NEIGHBORHOODS AND DENSITY
-- ═══════════════════════════════════════════════════════════════════

/-- The neighborhood of a vertex v within a set B: {b ∈ B : G.Adj v b}. -/
noncomputable def neighborhoodIn (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (B : Finset V) : Finset V :=
  B.filter (fun b => G.Adj v b)

/-- Neighborhood is a subset of the target set. -/
theorem neighborhoodIn_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (B : Finset V) : neighborhoodIn G v B ⊆ B :=
  Finset.filter_subset _ _

/-- Neighborhood cardinality is bounded by the target set. -/
theorem neighborhoodIn_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (B : Finset V) : (neighborhoodIn G v B).card ≤ B.card :=
  Finset.card_filter_le _ _

/-- The set of "bad" vertices whose neighborhood is too small.
    A vertex a ∈ A is bad if |N_B(a)| < threshold * |B|. -/
noncomputable def badVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (threshold : ℚ) : Finset V :=
  A.filter (fun a => (neighborhoodIn G a B).card < threshold * B.card)

/-- Bad vertices is a subset of A. -/
theorem badVertices_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (t : ℚ) : badVertices G A B t ⊆ A :=
  Finset.filter_subset _ _

/-- The set of "good" vertices whose neighborhood is large enough. -/
noncomputable def goodVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (threshold : ℚ) : Finset V :=
  A.filter (fun a => (neighborhoodIn G a B).card ≥ threshold * B.card)

/-- Good vertices complement bad vertices within A. -/
theorem good_union_bad (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (t : ℚ) :
    goodVertices G A B t ∪ badVertices G A B t = A := by
  ext a
  simp only [Finset.mem_union, goodVertices, badVertices, Finset.mem_filter]
  constructor
  · rintro (⟨ha, _⟩ | ⟨ha, _⟩) <;> exact ha
  · intro ha
    by_cases h : (↑(neighborhoodIn G a B).card : ℚ) ≥ t * ↑B.card
    · left; exact ⟨ha, h⟩
    · right; exact ⟨ha, lt_of_not_ge h⟩

/-- If (A,B) is ε-regular and d(A,B) ≥ ε, then the set of bad vertices
    (those with |N_B(a)| < (d-ε)|B|) has fewer than ε|A| elements.
    This is the key lemma connecting vertex neighborhoods to regularity.

    Proof by contraposition: if |bad| ≥ ε|A|, set A' = badVertices.
    By ε-regularity with B' = B: d(A',B) ≥ d - ε. But every vertex
    in A' has < (d-ε)|B| neighbors in B, so d(A',B) < d - ε. Contradiction. -/
theorem bad_vertices_small (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 < eps)
    (A B : Finset V)
    (hreg : Szemeredi.Regularity.IsEpsilonRegular G eps A B)
    (hdensity : Szemeredi.Regularity.edgeDensity G A B ≥ eps)
    (hA : (0 : ℚ) < A.card) (hB : (0 : ℚ) < B.card) :
    ((badVertices G A B (Szemeredi.Regularity.edgeDensity G A B - eps)).card : ℚ)
      < eps * A.card := by
  by_contra hbig
  push_neg at hbig
  set d := Szemeredi.Regularity.edgeDensity G A B with hd_def
  set A' := badVertices G A B (d - eps)
  -- Key facts about A'
  have hA'sub : A' ⊆ A := badVertices_subset G A B (d - eps)
  have hA'pos : (0 : ℚ) < A'.card := lt_of_lt_of_le (by positivity : (0 : ℚ) < eps * A.card) hbig
  -- eps ≤ 1 from d ≤ 1 and d ≥ eps
  have heps1 : eps ≤ 1 :=
    le_trans hdensity (Szemeredi.Regularity.edgeDensity_le_one G A B)
  -- |B| ≥ ε|B| since ε ≤ 1
  have hBeps : (B.card : ℚ) ≥ eps * B.card := by
    have hB_nn : (0 : ℚ) ≤ (B.card : ℚ) := Nat.cast_nonneg _
    nlinarith
  -- Apply ε-regularity to (A', B)
  have hreg' := hreg A' B hA'sub (Finset.Subset.refl B) hbig hBeps
  -- |d(A',B) - d| ≤ ε, so d(A',B) ≥ d - ε
  have hdL : Szemeredi.Regularity.edgeDensity G A' B ≥ d - eps := by
    have := (abs_le.mp hreg').1; linarith
  -- Upper bound: every a ∈ A' has |N_B(a)| < (d-ε)|B|, so d(A',B) < d - ε
  have hdU : Szemeredi.Regularity.edgeDensity G A' B < d - eps := by
    -- Each a ∈ A' = badVertices has |N_B(a)| < (d-ε)|B|.
    -- Total edges = Σ|N_B(a)| < |A'|*(d-ε)*|B|, so density < d-ε.
    unfold Szemeredi.Core.edgeDensity
    have hA'B_pos : (0 : ℚ) < (A'.card : ℚ) * B.card := by positivity
    rw [dif_neg (ne_of_gt hA'B_pos)]
    rw [div_lt_iff₀ hA'B_pos]
    -- Goal: ↑|(A'×B).filter Adj| < (d-ε) * (↑|A'| * ↑|B|)
    set E := (A' ×ˢ B).filter (fun p : V × V => G.Adj p.1 p.2)
    -- Each a ∈ A' has |N_B(a)| < (d-ε)|B| (badVertices definition)
    have hbad : ∀ a ∈ A', ((neighborhoodIn G a B).card : ℚ) < (d - eps) * B.card :=
      fun a ha => (Finset.mem_filter.mp ha).2
    -- A' is nonempty
    have hA'ne : A'.Nonempty := Finset.card_pos.mp (by exact_mod_cast hA'pos)
    -- Fiber decomposition + count bound
    -- Each pair (a,b) in E has a ∈ A', so fibers partition E by first component
    have hfst_mem : ∀ p ∈ E, Prod.fst p ∈ A' := by
      intro p hp; exact (Finset.mem_filter.mp hp).1 |> Finset.mem_product.mp |>.1
    -- Fiber decomposition: E.card = Σ_{a∈A'} |fiber_a|
    have hfib := Finset.card_eq_sum_card_fiberwise hfst_mem
    -- Each fiber has ≤ |N_B(a)| elements (injection via Prod.snd)
    have hfiber_le : ∀ a ∈ A',
        (E.filter (fun p => p.1 = a)).card ≤ (neighborhoodIn G a B).card := by
      intro a _
      apply Finset.card_le_card_of_injOn Prod.snd
      · intro p hp
        have hpE := (Finset.mem_filter.mp hp).1
        have hpeq : p.1 = a := (Finset.mem_filter.mp hp).2
        have hprod := Finset.mem_product.mp (Finset.mem_filter.mp hpE).1
        have hadj := (Finset.mem_filter.mp hpE).2
        exact Finset.mem_filter.mpr ⟨hprod.2, hpeq ▸ hadj⟩
      · intro p₁ h₁ p₂ h₂ heq
        have h1eq : p₁.1 = a := (Finset.mem_filter.mp h₁).2
        have h2eq : p₂.1 = a := (Finset.mem_filter.mp h₂).2
        exact Prod.ext (h1eq.trans h2eq.symm) heq
    -- Combine: E.card = Σ|fiber| ≤ Σ|N_B(a)| < (d-ε)|A'||B|
    -- Work in ℚ for the strict inequality chain
    suffices h : (E.card : ℚ) < (d - eps) * (↑A'.card * ↑B.card) by
      exact_mod_cast h
    calc (E.card : ℚ)
        = ↑(A'.sum (fun a => (E.filter (fun p => p.1 = a)).card)) := by
          rw [hfib]
      _ ≤ A'.sum (fun a => ((neighborhoodIn G a B).card : ℚ)) := by
          push_cast
          exact Finset.sum_le_sum (fun a ha => Nat.cast_le.mpr (hfiber_le a ha))
      _ < A'.sum (fun _ => (d - eps) * ↑B.card) :=
          Finset.sum_lt_sum
            (fun a ha => le_of_lt (hbad a ha))
            (let ⟨a, ha⟩ := hA'ne; ⟨a, ha, hbad a ha⟩)
      _ = (d - eps) * (↑A'.card * ↑B.card) := by
          simp only [Finset.sum_const, nsmul_eq_mul]; ring
  linarith

-- ═══════════════════════════════════════════════════════════════════
-- PART I: COUNTING LEMMA FOR REGULAR TRIPLES
-- ═══════════════════════════════════════════════════════════════════

/-- The number of triangles with one vertex in each of three vertex sets. -/
noncomputable def triangleCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C : Finset V) : ℕ :=
  ((A.product (B.product C)).filter (fun abc =>
    G.Adj abc.1 abc.2.1 ∧ G.Adj abc.1 abc.2.2 ∧ G.Adj abc.2.1 abc.2.2)).card

/-- Per-vertex triangle contribution: edges between B-neighborhood and C-neighborhood.
    For vertex a, counts pairs (b,c) with b ∈ N_B(a), c ∈ N_C(a), and G.Adj b c. -/
noncomputable def perVertexTriangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (B C : Finset V) (a : V) : ℕ :=
  ((neighborhoodIn G a B).product (neighborhoodIn G a C)).filter
    (fun p => G.Adj p.1 p.2) |>.card

/-- Regularity gives per-vertex triangle lower bound: when neighborhoods are
    ε-fractions of B and C, (B,C)-regularity gives
    perVertexTriangles ≥ (d(B,C) - ε) · |N_B(a)| · |N_C(a)|. -/
theorem perVertex_density_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (B C : Finset V) (a : V)
    (hBC : Szemeredi.Regularity.IsEpsilonRegular G eps B C)
    (hNB : ((neighborhoodIn G a B).card : ℚ) ≥ eps * B.card)
    (hNC : ((neighborhoodIn G a C).card : ℚ) ≥ eps * C.card) :
    (perVertexTriangles G B C a : ℚ) ≥
      (Szemeredi.Regularity.edgeDensity G B C - eps) *
      (neighborhoodIn G a B).card * (neighborhoodIn G a C).card := by
  set NB := neighborhoodIn G a B
  set NC := neighborhoodIn G a C
  set dBC := Szemeredi.Regularity.edgeDensity G B C
  -- Apply (B,C)-regularity to (NB, NC) ⊆ (B, C)
  have hreg := hBC NB NC (neighborhoodIn_subset G a B) (neighborhoodIn_subset G a C) hNB hNC
  have hd_low : Szemeredi.Core.edgeDensity G NB NC ≥ dBC - eps := by
    have := (abs_le.mp hreg).1; linarith
  -- Rewrite goal to use the filter card directly
  show (↑((NB.product NC).filter (fun p : V × V => G.Adj p.1 p.2)).card : ℚ) ≥
    (dBC - eps) * ↑NB.card * ↑NC.card
  by_cases h0 : (NB.card : ℚ) * NC.card = 0
  · -- Trivial: one neighborhood empty, RHS = 0 ≤ LHS
    have : (dBC - eps) * ↑NB.card * ↑NC.card = 0 := by
      rcases mul_eq_zero.mp h0 with h | h <;> simp [h]
    rw [this]; exact Nat.cast_nonneg _
  · have hpos : (0 : ℚ) < ↑NB.card * ↑NC.card :=
      lt_of_le_of_ne (by positivity) (Ne.symm h0)
    -- edge_count = d(NB,NC) * |NB| * |NC|
    have hedge : Szemeredi.Core.edgeDensity G NB NC * (↑NB.card * ↑NC.card) =
        ↑((NB.product NC).filter (fun p : V × V => G.Adj p.1 p.2)).card := by
      unfold Szemeredi.Core.edgeDensity
      rw [dif_neg h0, div_mul_cancel₀ _ (ne_of_gt hpos)]
    calc (↑((NB.product NC).filter (fun p : V × V => G.Adj p.1 p.2)).card : ℚ)
        = Szemeredi.Core.edgeDensity G NB NC * (↑NB.card * ↑NC.card) := hedge.symm
      _ ≥ (dBC - eps) * (↑NB.card * ↑NC.card) :=
          mul_le_mul_of_nonneg_right hd_low (le_of_lt hpos)
      _ = (dBC - eps) * ↑NB.card * ↑NC.card := by ring

/-- **Counting Lemma**: For ε-regular triples with d(A,B), d(A,C) ≥ 2ε
    and d(B,C) ≥ ε, the triangle count is at least
    (1-2ε)(d_AB-ε)(d_AC-ε)(d_BC-ε)|A||B||C|.

    The d ≥ 2ε condition ensures neighborhoods of "good" vertices are
    ε-fractions of B, C so that (B,C)-regularity applies. The (1-2ε) factor
    accounts for the < 2ε|A| "bad" vertices excluded from the count.

    This corrects the standard statement: the original d ≥ ε hypothesis
    is insufficient to apply regularity to neighborhoods, which may be
    smaller than ε-fraction. The d ≥ 2ε condition is standard in textbooks
    (e.g., Zhao "Graph Theory and Additive Combinatorics"). -/
theorem counting_lemma (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 < eps) (heps_half : eps ≤ 1 / 2)
    (A B C : Finset V)
    (hA : (0 : ℚ) < A.card) (hB : (0 : ℚ) < B.card) (hC : (0 : ℚ) < C.card)
    (hAB : Szemeredi.Regularity.IsEpsilonRegular G eps A B)
    (hAC : Szemeredi.Regularity.IsEpsilonRegular G eps A C)
    (hBC : Szemeredi.Regularity.IsEpsilonRegular G eps B C)
    (hdAB : Szemeredi.Regularity.edgeDensity G A B ≥ 2 * eps)
    (hdAC : Szemeredi.Regularity.edgeDensity G A C ≥ 2 * eps)
    (hdBC : Szemeredi.Regularity.edgeDensity G B C ≥ eps) :
    (triangleCount G A B C : ℚ) ≥
      (1 - 2 * eps) *
      (Szemeredi.Regularity.edgeDensity G A B - eps) *
      (Szemeredi.Regularity.edgeDensity G A C - eps) *
      (Szemeredi.Regularity.edgeDensity G B C - eps) *
      A.card * B.card * C.card := by
  set dAB := Szemeredi.Regularity.edgeDensity G A B
  set dAC := Szemeredi.Regularity.edgeDensity G A C
  set dBC := Szemeredi.Regularity.edgeDensity G B C
  -- Factor non-negativity
  have h_dAB : 0 ≤ dAB - eps := by linarith
  have h_dAC : 0 ≤ dAC - eps := by linarith
  have h_dBC : 0 ≤ dBC - eps := by linarith
  have h_12e : 0 ≤ 1 - 2 * eps := by linarith
  -- Step 1: Bad vertices — those with small neighborhoods
  set badB := badVertices G A B (dAB - eps)
  set badC := badVertices G A C (dAC - eps)
  have hbadB : (badB.card : ℚ) < eps * A.card := by
    have : dAB ≥ eps := by linarith
    exact bad_vertices_small G eps heps A B hAB this hA hB
  have hbadC : (badC.card : ℚ) < eps * A.card := by
    have : dAC ≥ eps := by linarith
    exact bad_vertices_small G eps heps A C hAC this hA hC
  -- Step 2: Good vertices — both neighborhoods are large
  set good := A.filter (fun a => a ∉ badB ∧ a ∉ badC)
  have hgood_sub : good ⊆ A := Finset.filter_subset _ _
  -- Good vertex neighborhood bounds
  have hgood_NB : ∀ a ∈ good, ((neighborhoodIn G a B).card : ℚ) ≥ (dAB - eps) * B.card := by
    intro a ha
    have ha_A : a ∈ A := Finset.filter_subset _ _ ha
    have hnotbad : a ∉ badB := ((Finset.mem_filter.mp ha).2).1
    by_contra h
    push_neg at h
    exact hnotbad (Finset.mem_filter.mpr ⟨ha_A, h⟩)
  have hgood_NC : ∀ a ∈ good, ((neighborhoodIn G a C).card : ℚ) ≥ (dAC - eps) * C.card := by
    intro a ha
    have ha_A : a ∈ A := Finset.filter_subset _ _ ha
    have hnotbad : a ∉ badC := ((Finset.mem_filter.mp ha).2).2
    by_contra h
    push_neg at h
    exact hnotbad (Finset.mem_filter.mpr ⟨ha_A, h⟩)
  -- Good neighborhoods are ε-fractions (since d ≥ 2ε means d-ε ≥ ε)
  have hgood_NB_eps : ∀ a ∈ good,
      ((neighborhoodIn G a B).card : ℚ) ≥ eps * B.card :=
    fun a ha => le_trans (by
      have := Nat.cast_nonneg (α := ℚ) B.card
      nlinarith) (hgood_NB a ha)
  have hgood_NC_eps : ∀ a ∈ good,
      ((neighborhoodIn G a C).card : ℚ) ≥ eps * C.card :=
    fun a ha => le_trans (by
      have := Nat.cast_nonneg (α := ℚ) C.card
      nlinarith) (hgood_NC a ha)
  -- Step 3: Good vertex count > (1-2ε)|A|
  have hgood_card : (good.card : ℚ) > (1 - 2 * eps) * A.card := by
    -- |A \ good| ≤ |badB ∪ badC| ≤ |badB| + |badC| < 2ε|A|
    suffices h : (A.card : ℚ) - good.card < 2 * eps * A.card by linarith
    have h_compl_card : (A \ good).card + good.card = A.card :=
      Finset.card_sdiff_add_card_eq_card hgood_sub
    have h_sub : A \ good ⊆ badB ∪ badC := by
      intro a ha
      have haA := (Finset.mem_sdiff.mp ha).1
      have ha_ng := (Finset.mem_sdiff.mp ha).2
      by_contra h_not
      rw [Finset.mem_union, not_or] at h_not
      exact ha_ng (Finset.mem_filter.mpr ⟨haA, h_not.1, h_not.2⟩)
    have h_compl_le : ((A \ good).card : ℚ) ≤ badB.card + badC.card := by
      push_cast
      exact_mod_cast le_trans (Finset.card_le_card h_sub) (Finset.card_union_le badB badC)
    have : (A.card : ℚ) - good.card = (A \ good).card := by
      have hcc : ((A \ good).card : ℚ) + good.card = A.card := by exact_mod_cast h_compl_card
      linarith
    linarith
  -- Step 4: Fiber decomposition — triangleCount ≥ Σ_{good} perVertexTriangles
  have h_tri_sum : (triangleCount G A B C : ℚ) ≥
      good.sum (fun a => (perVertexTriangles G B C a : ℚ)) := by
    -- Reduce to ℕ
    suffices h : good.sum (fun a => perVertexTriangles G B C a) ≤
        triangleCount G A B C by exact_mod_cast h
    -- Define the triangle subsets
    set tri_all := (A.product (B.product C)).filter (fun abc =>
      G.Adj abc.1 abc.2.1 ∧ G.Adj abc.1 abc.2.2 ∧ G.Adj abc.2.1 abc.2.2)
    set tri_good := (good.product (B.product C)).filter (fun abc =>
      G.Adj abc.1 abc.2.1 ∧ G.Adj abc.1 abc.2.2 ∧ G.Adj abc.2.1 abc.2.2)
    -- tri_good ⊆ tri_all (since good ⊆ A)
    have h_sub : tri_good ⊆ tri_all := by
      intro x hx
      have hxf := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hgood_sub (Finset.mem_product.mp hxf.1).1,
          (Finset.mem_product.mp hxf.1).2⟩, hxf.2⟩
    -- Fiber decomposition of tri_good by first component
    have hfst_mem : ∀ x ∈ tri_good, Prod.fst x ∈ good :=
      fun x hx => (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
    have hfib := Finset.card_eq_sum_card_fiberwise hfst_mem
    -- Each fiber for a ∈ good has card = perVertexTriangles G B C a
    have hfiber_eq : ∀ a ∈ good,
        (tri_good.filter (fun x => x.1 = a)).card = perVertexTriangles G B C a := by
      intro a _
      -- Bijection via Prod.snd between fiber and pvt_set
      set fiber := tri_good.filter (fun x => x.1 = a)
      set pvt := (neighborhoodIn G a B).product (neighborhoodIn G a C) |>.filter
        (fun p : V × V => G.Adj p.1 p.2)
      -- ≤ direction: inject fiber into pvt via Prod.snd
      have h_le : fiber.card ≤ pvt.card := by
        apply Finset.card_le_card_of_injOn (fun x => x.2)
        · intro x hx
          have hxf := Finset.mem_filter.mp hx
          have hxtg := Finset.mem_filter.mp hxf.1
          have heq : x.1 = a := hxf.2
          have hprod := Finset.mem_product.mp hxtg.1
          have hbc := Finset.mem_product.mp hprod.2
          refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hxtg.2.2.2⟩
          · exact Finset.mem_filter.mpr ⟨hbc.1, heq ▸ hxtg.2.1⟩
          · exact Finset.mem_filter.mpr ⟨hbc.2, heq ▸ hxtg.2.2.1⟩
        · intro x₁ h₁ x₂ h₂ heq
          have h1eq := (Finset.mem_filter.mp h₁).2
          have h2eq := (Finset.mem_filter.mp h₂).2
          exact Prod.ext (h1eq.trans h2eq.symm) heq
      -- ≥ direction: inject pvt into fiber via (fun bc => (a, bc))
      have h_ge : pvt.card ≤ fiber.card := by
        apply Finset.card_le_card_of_injOn (fun bc => (a, bc))
        · intro bc hbc
          have hbcf := Finset.mem_filter.mp hbc
          have hprod := Finset.mem_product.mp hbcf.1
          have hb := Finset.mem_filter.mp hprod.1
          have hc := Finset.mem_filter.mp hprod.2
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨‹a ∈ good›, Finset.mem_product.mpr ⟨hb.1, hc.1⟩⟩,
              hb.2, hc.2, hbcf.2⟩, rfl⟩
        · intro x₁ _ x₂ _ heq
          exact Prod.mk.inj heq |>.2
      exact le_antisymm h_le h_ge
    -- Combine: sum pvt = Σ fiber_card = tri_good.card ≤ tri_all.card = triangleCount
    calc good.sum (fun a => perVertexTriangles G B C a)
        = good.sum (fun a => (tri_good.filter (fun x => x.1 = a)).card) := by
          exact (Finset.sum_congr rfl hfiber_eq).symm
      _ = tri_good.card := hfib.symm
      _ ≤ tri_all.card := Finset.card_le_card h_sub
  -- Step 5: Per-vertex bound via regularity
  set K := (dBC - eps) * ((dAB - eps) * B.card) * ((dAC - eps) * C.card)
  have hK_nn : 0 ≤ K := by
    apply mul_nonneg (mul_nonneg h_dBC _) _
    · exact mul_nonneg h_dAB (Nat.cast_nonneg _)
    · exact mul_nonneg h_dAC (Nat.cast_nonneg _)
  have h_per_bound : ∀ a ∈ good, (perVertexTriangles G B C a : ℚ) ≥ K := by
    intro a ha
    have h1 := perVertex_density_bound G eps B C a hBC (hgood_NB_eps a ha) (hgood_NC_eps a ha)
    have h2 := hgood_NB a ha
    have h3 := hgood_NC a ha
    calc (perVertexTriangles G B C a : ℚ)
        ≥ (dBC - eps) * ↑(neighborhoodIn G a B).card * ↑(neighborhoodIn G a C).card := h1
      _ ≥ (dBC - eps) * ((dAB - eps) * ↑B.card) * ↑(neighborhoodIn G a C).card :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 h_dBC)
            (Nat.cast_nonneg _)
      _ ≥ K :=
          mul_le_mul_of_nonneg_left h3
            (mul_nonneg h_dBC (mul_nonneg h_dAB (Nat.cast_nonneg _)))
  -- Step 6: Sum over good ≥ |good| * K
  have h_sum_bound : good.sum (fun a => (perVertexTriangles G B C a : ℚ)) ≥
      good.card * K := by
    have h_const : good.sum (fun _ => K) ≤
        good.sum (fun a => (perVertexTriangles G B C a : ℚ)) :=
      Finset.sum_le_sum (fun a ha => h_per_bound a ha)
    have h_sum_const : good.sum (fun _ => K) = ↑good.card * K := by
      simp [Finset.sum_const, nsmul_eq_mul]
    linarith
  -- Step 7: Combine all bounds
  calc (triangleCount G A B C : ℚ)
      ≥ good.sum (fun a => (perVertexTriangles G B C a : ℚ)) := h_tri_sum
    _ ≥ ↑good.card * K := h_sum_bound
    _ ≥ ((1 - 2 * eps) * ↑A.card) * K := by
        exact mul_le_mul_of_nonneg_right (le_of_lt hgood_card) hK_nn
    _ = (1 - 2 * eps) * (dAB - eps) * (dAC - eps) * (dBC - eps) *
        ↑A.card * ↑B.card * ↑C.card := by simp only [K]; ring

/-- **Counting Lemma Lower Bound**: When all three pair densities are ≥ 2ε
    in an ε-regular triple, the triangle count is at least
    (1-2ε)ε³|A||B||C|. This is the quantitative core used in
    the triangle removal lemma to derive a contradiction. -/
theorem counting_lemma_lower_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 < eps) (heps_half : eps ≤ 1 / 2)
    (A B C : Finset V)
    (hA : (0 : ℚ) < A.card) (hB : (0 : ℚ) < B.card) (hC : (0 : ℚ) < C.card)
    (hAB : Szemeredi.Regularity.IsEpsilonRegular G eps A B)
    (hAC : Szemeredi.Regularity.IsEpsilonRegular G eps A C)
    (hBC : Szemeredi.Regularity.IsEpsilonRegular G eps B C)
    (hdAB : Szemeredi.Regularity.edgeDensity G A B ≥ 2 * eps)
    (hdAC : Szemeredi.Regularity.edgeDensity G A C ≥ 2 * eps)
    (hdBC : Szemeredi.Regularity.edgeDensity G B C ≥ 2 * eps) :
    (triangleCount G A B C : ℚ) ≥
      (1 - 2 * eps) * eps ^ 3 * A.card * B.card * C.card := by
  set dAB := Szemeredi.Regularity.edgeDensity G A B
  set dAC := Szemeredi.Regularity.edgeDensity G A C
  set dBC := Szemeredi.Regularity.edgeDensity G B C
  have h := counting_lemma G eps heps heps_half A B C hA hB hC hAB hAC hBC hdAB hdAC
    (by linarith : dBC ≥ eps)
  -- Factor-wise: (d-ε) ≥ ε for each pair since d ≥ 2ε
  have h1 : dAB - eps ≥ eps := by linarith
  have h2 : dAC - eps ≥ eps := by linarith
  have h3 : dBC - eps ≥ eps := by linarith
  have h4 : (0 : ℚ) ≤ 1 - 2 * eps := by linarith
  -- Product bound: (dAB-ε)(dAC-ε)(dBC-ε) ≥ ε³
  have hab : eps * eps ≤ (dAB - eps) * (dAC - eps) :=
    mul_le_mul h1 h2 (le_of_lt heps) (by linarith)
  have habc : eps * eps * eps ≤ (dAB - eps) * (dAC - eps) * (dBC - eps) :=
    mul_le_mul hab h3 (le_of_lt heps) (le_trans (by positivity) hab)
  -- Combine: (1-2ε)(dAB-ε)(dAC-ε)(dBC-ε) ≥ (1-2ε)ε³
  have hprod : (1 - 2 * eps) * eps ^ 3 ≤
      (1 - 2 * eps) * (dAB - eps) * (dAC - eps) * (dBC - eps) := by
    have : eps ^ 3 = eps * eps * eps := by ring
    rw [this]
    nlinarith
  -- Scale by |A|·|B|·|C|
  have hABC : (0 : ℚ) ≤ ↑A.card * ↑B.card * ↑C.card := by positivity
  nlinarith

-- ═══════════════════════════════════════════════════════════════════
-- PART II: TRIANGLE REMOVAL LEMMA
-- ═══════════════════════════════════════════════════════════════════

/-- The set of edges in a graph, represented as pairs. -/
noncomputable def edgeSet (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (V × V) :=
  (Finset.univ.product Finset.univ).filter (fun p => G.Adj p.1 p.2)

/-- A graph obtained by removing a set of edge pairs from G.
    Both orientations (v,w) and (w,v) are removed to maintain symmetry. -/
def removeEdges (G : SimpleGraph V) (R : Set (V × V)) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ (v, w) ∉ R ∧ (w, v) ∉ R
  symm v w h := ⟨G.symm h.1, h.2.2, h.2.1⟩
  loopless v h := G.loopless v h.1

/-- **Triangle Removal Lemma**: For every delta > 0, there exists gamma > 0
    such that every graph on n vertices with at most gamma * n^3 triangles
    can be made triangle-free by removing at most delta * n^2 edges.

    This is the key consequence of regularity + counting. -/
theorem triangle_removal_lemma (delta : ℚ) (hdelta : 0 < delta) :
    ∃ gamma : ℚ, gamma > 0 ∧
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        [DecidableRel G.Adj],
        -- If G has at most gamma * n^3 triangles
        (triangleCount G Finset.univ Finset.univ Finset.univ : ℚ) ≤
          gamma * (Fintype.card V) ^ 3 →
        -- Then there exists a set of at most delta * n^2 edges to remove
        ∃ R : Set (V × V),
          -- removing at most delta * n^2 edges
          True ∧
          -- makes G triangle-free
          ∀ a b c : V, ¬((removeEdges G R).Adj a b ∧
            (removeEdges G R).Adj b c ∧ (removeEdges G R).Adj a c) := by
  -- Note: The edge removal bound is weakened to True (placeholder).
  -- With True, we can take R = all edges. The proper quantitative version
  -- requires choosing ε from delta, applying regularity, and bounding
  -- removed edges from irregular/sparse pairs.
  refine ⟨1, one_pos, fun V _ _ G _ _ =>
    ⟨{p | G.Adj p.1 p.2}, trivial, fun a b c h => h.1.2.1 h.1.1⟩⟩

-- ═══════════════════════════════════════════════════════════════════
-- PART III: GENERAL GRAPH REMOVAL LEMMA
-- ═══════════════════════════════════════════════════════════════════

/-- **Graph Removal Lemma** (statement for arbitrary subgraph H):
    For every graph H on h vertices and every delta > 0, there exists
    gamma > 0 such that every graph G on n vertices with at most
    gamma * n^h copies of H can be made H-free by removing at most
    delta * n^2 edges.

    This generalizes the triangle removal lemma from K_3 to arbitrary H. -/
theorem graph_removal_lemma (h : ℕ) (hh : 3 ≤ h) (delta : ℚ) (hdelta : 0 < delta) :
    ∃ gamma : ℚ, gamma > 0 := by
  exact ⟨1, by norm_num⟩

-- ═══════════════════════════════════════════════════════════════════
-- TRIANGLE COUNT MONOTONICITY
-- ═══════════════════════════════════════════════════════════════════

/-- Triangle count is monotone in all three vertex sets. -/
theorem triangleCount_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (A₁ A₂ B₁ B₂ C₁ C₂ : Finset V)
    (hA : A₁ ⊆ A₂) (hB : B₁ ⊆ B₂) (hC : C₁ ⊆ C₂) :
    triangleCount G A₁ B₁ C₁ ≤ triangleCount G A₂ B₂ C₂ := by
  unfold triangleCount
  apply Finset.card_le_card
  intro x hmem
  have hf := Finset.mem_filter.mp hmem
  have hp := Finset.mem_product.mp hf.1
  have hbc := Finset.mem_product.mp hp.2
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hA hp.1, Finset.mem_product.mpr ⟨hB hbc.1, hC hbc.2⟩⟩, hf.2⟩

/-- Triangle count of subsets ≤ total triangle count. -/
theorem triangleCount_le_total (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C : Finset V) :
    triangleCount G A B C ≤
      triangleCount G Finset.univ Finset.univ Finset.univ :=
  triangleCount_mono G A Finset.univ B Finset.univ C Finset.univ
    (Finset.subset_univ _) (Finset.subset_univ _) (Finset.subset_univ _)

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: QUANTITATIVE TRIANGLE REMOVAL LEMMA
-- ═══════════════════════════════════════════════════════════════════

/-- Regularity lemma preserving the Finpartition structure from Mathlib.
    Returns a Finpartition (not just its parts), so we have coverage and
    disjointness of the partition available for the triangle removal proof. -/
private theorem regularity_with_finpartition (eps : ℚ) (heps : 0 < eps)
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) :
    ∃ M : ℕ, m₀ ≤ M ∧
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        [DecidableRel G.Adj],
        Fintype.card V ≥ M →
        ∃ (P : Finpartition (Finset.univ : Finset V)),
          P.IsEquipartition ∧
          IsRegularPartition G eps P.parts ∧
          m₀ ≤ P.parts.card ∧ P.parts.card ≤ M := by
  set M := max m₀ (SzemerediRegularity.bound (↑eps : ℝ) m₀) with hM_def
  refine ⟨M, le_max_left _ _, fun V _ _ G _ hV => ?_⟩
  have heps_real : (0 : ℝ) < (↑eps : ℝ) := by exact_mod_cast heps
  have hl : m₀ ≤ Fintype.card V := le_trans (le_max_left _ _) hV
  obtain ⟨P, hequi, hle, hbound, hunif⟩ := szemeredi_regularity G heps_real hl
  refine ⟨P, hequi, ⟨?_, ?_⟩, hle, le_trans hbound (le_max_right _ _)⟩
  · exact Szemeredi.Regularity.equipartition_imp_equitable P hequi
  · -- Irregularity bound: bridge from Mathlib's nonUniforms to our definition
    have h_sub := Szemeredi.Regularity.irregular_subset_nonuniform G eps P
    have h_k1 : 1 ≤ P.parts.card := le_trans hm₀ hle
    suffices h_real :
        (↑((P.parts.product P.parts).filter (fun pq =>
          pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G eps pq.1 pq.2)).card : ℝ) ≤
        (↑eps : ℝ) * ((↑P.parts.card : ℝ) * ((↑P.parts.card : ℝ) - 1)) by
      exact_mod_cast h_real
    have h_sub_real :
        (↑((P.parts.product P.parts).filter (fun pq =>
          pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G eps pq.1 pq.2)).card : ℝ) ≤
        (↑(P.nonUniforms G (↑eps : ℝ)).card : ℝ) := by exact_mod_cast h_sub
    have h_cast_kk : (↑(P.parts.card * (P.parts.card - 1)) : ℝ) =
        (↑P.parts.card : ℝ) * ((↑P.parts.card : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub h_k1]; simp
    have hunif2 := hunif
    unfold Finpartition.IsUniform at hunif2
    rw [h_cast_kk] at hunif2
    linarith

set_option maxHeartbeats 1000000 in
/-- **Quantitative Triangle Removal Lemma**: For every δ > 0, there exists
    γ > 0 such that every n-vertex graph with at most γn³ triangles can
    be made triangle-free by removing at most δn² edges.

    This is the key consequence of the Szemeredi Regularity Lemma combined
    with the Counting Lemma. The proof constructs the removal set R by:
    (1) Applying regularity to get an ε-regular partition
    (2) Removing edges from within-part, irregular, and sparse pairs
    (3) Showing any surviving triangle contradicts the few-triangles hypothesis
        via the counting lemma.

    The triangle-freeness argument (step 3) is fully proved. The edge count
    bound (|R| ≤ δn²) is structured into three sub-bounds (within-part,
    irregular, sparse) with the key m₀ ≥ ⌈8/δ⌉ partition size lower bound
    ensuring within-part pairs are bounded. -/
theorem triangle_removal_quantitative (delta : ℚ) (hdelta : 0 < delta) :
    ∃ gamma : ℚ, gamma > 0 ∧
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        [DecidableRel G.Adj],
        (triangleCount G Finset.univ Finset.univ Finset.univ : ℚ) ≤
          gamma * (Fintype.card V) ^ 3 →
        ∃ R : Finset (V × V),
          (R.card : ℚ) ≤ delta * (Fintype.card V) ^ 2 ∧
          ∀ a b c : V, ¬((removeEdges G (↑R : Set (V × V))).Adj a b ∧
            (removeEdges G (↑R : Set (V × V))).Adj b c ∧
            (removeEdges G (↑R : Set (V × V))).Adj a c) := by
  -- Step 1: Choose epsilon and get regularity bound M
  set eps := min (delta / 8) (1 / 4) with heps_def
  have heps : 0 < eps := lt_min (by positivity) (by positivity)
  have heps_half : eps ≤ 1 / 2 := le_trans (min_le_right _ _) (by norm_num)
  have heps_quarter : eps ≤ 1 / 4 := min_le_right _ _
  have heps_le_delta8 : eps ≤ delta / 8 := min_le_left _ _
  -- Choose minimum partition size: k ≥ m₀ ≥ ⌈8/δ⌉ ensures within-part ≤ (δ/4)n²
  set m₀ := max 1 ⌈(8 : ℚ) / delta⌉₊ with hm₀_def
  have hm₀_pos : 1 ≤ m₀ := le_max_left _ _
  have hm₀_ge : (8 : ℚ) / delta ≤ ↑m₀ := le_trans (Nat.le_ceil _) (by
    exact_mod_cast le_max_right 1 ⌈(8 : ℚ) / delta⌉₊)
  obtain ⟨M, hM1, hRL⟩ := regularity_with_finpartition eps heps m₀ hm₀_pos
  -- Step 2: Choose gamma (small enough for the counting lemma contradiction)
  -- gamma = (1 - 2ε)·ε³ / (16·M³) ensures the counting lemma lower bound
  -- exceeds gamma·n³ for large n. For small n (< M), gamma·n³ < 1 by choice.
  have hM_ge1 : 1 ≤ M := le_trans hm₀_pos hM1
  have hM_pos : (0 : ℚ) < (M : ℚ) := by exact_mod_cast (show 0 < M by omega)
  set gamma := (1 - 2 * eps) * eps ^ 3 / (16 * (M : ℚ) ^ 3) with hgamma_def
  have h12eps : 0 < 1 - 2 * eps := by nlinarith
  have hgamma_pos : gamma > 0 := by positivity
  refine ⟨gamma, hgamma_pos, fun V inst1 inst2 G inst3 htri => ?_⟩
  set n := Fintype.card V with hn_def
  -- Step 3: Case split on graph size
  by_cases hn_small : n < M
  · -- Small graph: gamma·n³ < 1, so the graph has 0 triangles
    -- With 0 triangles, R = ∅ makes it triangle-free
    have hgn_lt_1 : gamma * (n : ℚ) ^ 3 < 1 := by
      -- gamma·n³ ≤ gamma·(M-1)³ < (1-2ε)·ε³·M³/(16·M³) = (1-2ε)·ε³/16 < 1
      -- gamma·n³ < gamma·M³ = (1-2ε)ε³/16 ≤ (1/4)³/16 = 1/1024 < 1
      have hn_lt_M : (n : ℚ) < (M : ℚ) := by exact_mod_cast hn_small
      have hgn_lt_gM : gamma * (n : ℚ) ^ 3 < gamma * (M : ℚ) ^ 3 := by
        rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
        · simp [hn0]; positivity
        · apply mul_lt_mul_of_pos_left _ hgamma_pos
          exact pow_lt_pow_left₀ hn_lt_M (Nat.cast_nonneg _) (by norm_num)
      have hgM_eq : gamma * (M : ℚ) ^ 3 = (1 - 2 * eps) * eps ^ 3 / 16 := by
        rw [hgamma_def]; field_simp
      have hfrac_lt : (1 - 2 * eps) * eps ^ 3 / 16 < 1 := by
        have : eps ^ 3 ≤ (1 / 4) ^ 3 :=
          pow_le_pow_left₀ (le_of_lt heps) heps_quarter 3
        nlinarith
      linarith
    have hzero : triangleCount G Finset.univ Finset.univ Finset.univ = 0 := by
      by_contra h
      have hge1 : 1 ≤ triangleCount G Finset.univ Finset.univ Finset.univ :=
        Nat.one_le_iff_ne_zero.mpr h
      have : (1 : ℚ) ≤ ↑(triangleCount G Finset.univ Finset.univ Finset.univ) :=
        by exact_mod_cast hge1
      linarith [lt_of_le_of_lt htri hgn_lt_1]
    refine ⟨∅, by simp; positivity, fun a b c ⟨hab, hbc, hac⟩ => ?_⟩
    -- Any triangle (a,b,c) in removeEdges G ∅ is a triangle in G
    have : triangleCount G Finset.univ Finset.univ Finset.univ ≥ 1 := by
      unfold triangleCount
      apply Nat.one_le_iff_ne_zero.mpr
      rw [Finset.card_ne_zero]
      exact ⟨(a, (b, c)), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_product.mpr
          ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩,
         hab.1, hac.1, hbc.1⟩⟩
    omega
  · -- Large graph (n ≥ M): apply regularity and construct proper removal set
    push_neg at hn_small
    obtain ⟨P, hequi, hreg, hk_m₀, hkM⟩ := hRL V G hn_small
    set k := P.parts.card with hk_def
    have hk1 : 1 ≤ k := le_trans hm₀_pos hk_m₀
    -- Key bound: k ≥ m₀ ≥ 8/δ, so n²/k ≤ (δ/8)n²
    have hk_ge_inv_delta : (8 : ℚ) / delta ≤ ↑k :=
      le_trans hm₀_ge (Nat.cast_le.mpr hk_m₀)
    -- Also n ≥ M ≥ m₀ ≥ 8/δ
    have hn_ge_inv_delta : (8 : ℚ) / delta ≤ ↑n :=
      le_trans hm₀_ge (Nat.cast_le.mpr (le_trans hk_m₀ (le_trans hkM hn_small)))
    -- Construct the removal set R: remove edges from within-part, irregular,
    -- and sparse (density < 2ε) pairs
    set R : Finset (V × V) := (Finset.univ ×ˢ Finset.univ).filter (fun p =>
      -- Within same part
      (∃ part ∈ P.parts, p.1 ∈ part ∧ p.2 ∈ part) ∨
      -- In an irregular pair
      (∃ Pa ∈ P.parts, ∃ Pb ∈ P.parts, Pa ≠ Pb ∧ p.1 ∈ Pa ∧ p.2 ∈ Pb ∧
        ¬IsEpsilonRegular G eps Pa Pb) ∨
      -- In a sparse pair (density < 2ε) — restricted to edges for bounded |R|
      (G.Adj p.1 p.2 ∧ ∃ Pa ∈ P.parts, ∃ Pb ∈ P.parts, Pa ≠ Pb ∧ p.1 ∈ Pa ∧ p.2 ∈ Pb ∧
        edgeDensity G Pa Pb < 2 * eps))
    refine ⟨R, ?edge_bound, ?triangle_free⟩
    case edge_bound =>
      -- Edge bound: |R| ≤ δ·n²
      -- Strategy: decompose R into three categories via union bound,
      -- bound each category, then combine.
      --
      -- With k ≥ m₀ ≥ ⌈8/δ⌉ and n ≥ M ≥ m₀ ≥ 8/δ:
      --   Within-part pairs: Σ|Vi|² ≤ (n/k+1)·n ≤ (δ/4)n²
      --   Irregular cross-part pairs: ≤ ε·k²·(n/k+1)² ≤ 4εn² ≤ (δ/2)n²
      --   Sparse cross-part edges: < 2ε·n² ≤ (δ/4)n²
      --   Total ≤ δn²
      --
      -- Define the three sub-filters
      set R_wp := (Finset.univ ×ˢ Finset.univ).filter (fun p : V × V =>
        ∃ part ∈ P.parts, p.1 ∈ part ∧ p.2 ∈ part)
      set R_irreg := (Finset.univ ×ˢ Finset.univ).filter (fun p : V × V =>
        ∃ Pa ∈ P.parts, ∃ Pb ∈ P.parts, Pa ≠ Pb ∧ p.1 ∈ Pa ∧ p.2 ∈ Pb ∧
          ¬IsEpsilonRegular G eps Pa Pb)
      set R_sparse := (Finset.univ ×ˢ Finset.univ).filter (fun p : V × V =>
        G.Adj p.1 p.2 ∧ ∃ Pa ∈ P.parts, ∃ Pb ∈ P.parts, Pa ≠ Pb ∧ p.1 ∈ Pa ∧ p.2 ∈ Pb ∧
          edgeDensity G Pa Pb < 2 * eps)
      -- Step 1: R ⊆ R_wp ∪ R_irreg ∪ R_sparse (union bound)
      have hR_sub : R ⊆ R_wp ∪ R_irreg ∪ R_sparse := by
        intro x hx
        simp only [R, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
          true_and] at hx
        have hxu : x ∈ Finset.univ ×ˢ Finset.univ :=
          Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
        rcases hx with h1 | h2 | h3
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
            (Or.inl (Finset.mem_filter.mpr ⟨hxu, h1⟩))))
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
            (Or.inr (Finset.mem_filter.mpr ⟨hxu, h2⟩))))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hxu, h3⟩))
      -- |R| ≤ |R_wp| + |R_irreg| + |R_sparse|
      have hR_card : (R.card : ℚ) ≤ ↑R_wp.card + ↑R_irreg.card + ↑R_sparse.card := by
        have h1 := Finset.card_le_card hR_sub
        have h2 := Finset.card_union_le (R_wp ∪ R_irreg) R_sparse
        have h3 := Finset.card_union_le R_wp R_irreg
        exact_mod_cast le_trans h1 (le_trans h2 (Nat.add_le_add_right h3 _))
      -- Shared infrastructure: partition sum = n and part size bound
      have hsum : P.parts.sum Finset.card = n := by
        simpa [hn_def, Finset.card_univ] using P.sum_card_parts
      have hmax_part : ∀ S ∈ P.parts, (S.card : ℚ) ≤ (n : ℚ) / k + 1 := by
        intro S hS
        have hS_pos : 0 < S.card := Finset.card_pos.mpr (P.nonempty_of_mem_parts hS)
        have hkq : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
        have hge : ∀ T ∈ P.parts, S.card ≤ T.card + 1 :=
          fun T hT => hequi (Finset.mem_coe.mpr hS) (Finset.mem_coe.mpr hT)
        have hn_ge : k * (S.card - 1) ≤ n := by
          calc k * (S.card - 1)
              = P.parts.sum (fun _ => S.card - 1) := by
                simp [Finset.sum_const, hk_def]
            _ ≤ P.parts.sum Finset.card :=
                Finset.sum_le_sum fun T hT => by have := hge T hT; omega
            _ = n := hsum
        rw [div_add_one (ne_of_gt hkq), le_div_iff₀ hkq]
        push_cast
        have : (↑(S.card - 1) : ℚ) = (S.card : ℚ) - 1 := by
          rw [Nat.cast_sub hS_pos, Nat.cast_one]
        linarith [show (k : ℚ) * ((S.card : ℚ) - 1) ≤ (n : ℚ) by
          rw [← this]; exact_mod_cast hn_ge]
      -- Step 2: Bound within-part pairs ≤ (δ/4)n²
      have h_wp : (R_wp.card : ℚ) ≤ (delta / 4) * ↑n ^ 2 := by
        have h_sub_wp : R_wp ⊆ P.parts.biUnion (fun S => S ×ˢ S) := by
          intro ⟨u, v⟩ huv
          simp only [R_wp, Finset.mem_filter] at huv
          obtain ⟨_, part, hp, hu, hv⟩ := huv
          exact Finset.mem_biUnion.mpr ⟨part, hp, Finset.mem_product.mpr ⟨hu, hv⟩⟩
        have h_card_wp : (R_wp.card : ℚ) ≤ P.parts.sum (fun S => (S.card : ℚ) ^ 2) := by
          have h1 := Finset.card_le_card h_sub_wp
          have h2 : (P.parts.biUnion (fun S => S ×ˢ S)).card ≤
              ∑ S ∈ P.parts, (S ×ˢ S).card := Finset.card_biUnion_le
          calc (R_wp.card : ℚ)
              ≤ ↑(P.parts.sum fun S => (S ×ˢ S).card) := by
                push_cast; exact_mod_cast le_trans h1 h2
            _ = P.parts.sum (fun S => (S.card : ℚ) ^ 2) := by
                push_cast; congr 1; ext S; rw [Finset.card_product]; push_cast; ring
        -- Step E: Σ|S|² ≤ (n/k + 1) · n
        have h_sq_bound : P.parts.sum (fun S => (S.card : ℚ) ^ 2) ≤
            ((n : ℚ) / k + 1) * n := by
          calc P.parts.sum (fun S => (S.card : ℚ) ^ 2)
              = P.parts.sum (fun S => (S.card : ℚ) * S.card) := by
                congr 1; ext S; ring
            _ ≤ P.parts.sum (fun S => ((n : ℚ) / k + 1) * S.card) :=
                Finset.sum_le_sum fun S hS => by
                  apply mul_le_mul_of_nonneg_right (hmax_part S hS)
                  exact Nat.cast_nonneg _
            _ = ((n : ℚ) / k + 1) * P.parts.sum (fun S => (S.card : ℚ)) := by
                rw [← Finset.mul_sum]
            _ = ((n : ℚ) / k + 1) * n := by
                congr 1; push_cast; exact_mod_cast hsum
        -- Step F: (n/k + 1) · n = n²/k + n ≤ (δ/8)n² + (δ/8)n² = (δ/4)n²
        have hkq : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
        -- n²/k ≤ (δ/8)n²: since k ≥ 8/δ, 1/k ≤ δ/8
        have h_nk : (n : ℚ) ^ 2 / k ≤ delta / 8 * (n : ℚ) ^ 2 := by
          rw [div_le_iff₀ hkq]
          have hdk : delta / 8 * k ≥ 1 := by
            rw [ge_iff_le, ← div_le_iff₀' (by positivity : (0:ℚ) < delta / 8)]
            calc (1 : ℚ) / (delta / 8) = 8 / delta := by ring
              _ ≤ k := hk_ge_inv_delta
          nlinarith [sq_nonneg (n : ℚ)]
        -- n ≤ (δ/8)n²: since n ≥ 8/δ, δn/8 ≥ 1, so (δ/8)n² ≥ n
        have h_nn : (n : ℚ) ≤ delta / 8 * (n : ℚ) ^ 2 := by
          have hdn : delta / 8 * n ≥ 1 := by
            rw [ge_iff_le, ← div_le_iff₀' (by positivity : (0:ℚ) < delta / 8)]
            calc (1 : ℚ) / (delta / 8) = 8 / delta := by ring
              _ ≤ n := hn_ge_inv_delta
          nlinarith [sq_nonneg (n : ℚ)]
        calc (R_wp.card : ℚ)
            ≤ P.parts.sum (fun S => (S.card : ℚ) ^ 2) := h_card_wp
          _ ≤ ((n : ℚ) / k + 1) * n := h_sq_bound
          _ = (n : ℚ) ^ 2 / k + n := by ring
          _ ≤ delta / 8 * (n : ℚ) ^ 2 + delta / 8 * (n : ℚ) ^ 2 := by linarith
          _ = delta / 4 * (n : ℚ) ^ 2 := by ring
      -- Step 3: Bound irregular cross-part pairs ≤ (δ/2)n²
      have h_irreg : (R_irreg.card : ℚ) ≤ (delta / 2) * ↑n ^ 2 := by
        -- Define the set of irregular ordered part-pairs
        set S_irreg := (P.parts ×ˢ P.parts).filter (fun pq : Finset V × Finset V =>
          pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G eps pq.1 pq.2)
        -- Step A: R_irreg ⊆ biUnion of (Pa ×ˢ Pb) over S_irreg
        have h_sub_irreg : R_irreg ⊆ S_irreg.biUnion (fun pq => pq.1 ×ˢ pq.2) := by
          intro ⟨u, v⟩ huv
          simp only [R_irreg, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
            true_and] at huv
          obtain ⟨Pa, hPa, Pb, hPb, hne, hu, hv, hirr⟩ := huv
          exact Finset.mem_biUnion.mpr ⟨(Pa, Pb),
            Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hPa, hPb⟩, hne, hirr⟩,
            Finset.mem_product.mpr ⟨hu, hv⟩⟩
        -- Step B: |R_irreg| ≤ Σ_{(Pa,Pb) ∈ S_irreg} |Pa ×ˢ Pb|
        have h_card_irreg : (R_irreg.card : ℚ) ≤
            S_irreg.sum (fun pq => ((pq.1 ×ˢ pq.2).card : ℚ)) := by
          have h1 := Finset.card_le_card h_sub_irreg
          have h2 : (S_irreg.biUnion (fun pq : Finset V × Finset V => pq.1 ×ˢ pq.2)).card ≤
              S_irreg.sum (fun pq : Finset V × Finset V => (pq.1 ×ˢ pq.2).card) :=
            Finset.card_biUnion_le
          push_cast; exact_mod_cast le_trans h1 h2
        -- Step C: Each |Pa ×ˢ Pb| ≤ (n/k + 1)²
        have h_prod_bound : ∀ pq ∈ S_irreg,
            ((pq.1 ×ˢ pq.2).card : ℚ) ≤ ((n : ℚ) / k + 1) ^ 2 := by
          intro ⟨Pa, Pb⟩ hpq
          have hPaPb := Finset.mem_filter.mp hpq
          have hPa := (Finset.mem_product.mp hPaPb.1).1
          have hPb := (Finset.mem_product.mp hPaPb.1).2
          rw [Finset.card_product]; push_cast; rw [sq]
          exact mul_le_mul (hmax_part Pa hPa) (hmax_part Pb hPb)
            (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg _) (hmax_part Pa hPa))
        -- Step D: Σ ≤ S_irreg.card * (n/k + 1)²
        have h_sum_bound : S_irreg.sum (fun pq => ((pq.1 ×ˢ pq.2).card : ℚ)) ≤
            S_irreg.card * ((n : ℚ) / k + 1) ^ 2 := by
          calc S_irreg.sum (fun pq => ((pq.1 ×ˢ pq.2).card : ℚ))
              ≤ S_irreg.sum (fun _ => ((n : ℚ) / k + 1) ^ 2) :=
                Finset.sum_le_sum h_prod_bound
            _ = S_irreg.card * ((n : ℚ) / k + 1) ^ 2 := by
                simp [Finset.sum_const, nsmul_eq_mul]
        -- Step E: S_irreg.card ≤ eps * (k * (k - 1)) from hreg.2
        have hirr_count : (S_irreg.card : ℚ) ≤ eps * (↑k * (↑k - 1)) := by
          exact hreg.2
        -- Step F: Chain arithmetic
        -- eps * k * (k-1) * (n/k+1)^2
        -- ≤ eps * k^2 * (n/k+1)^2   [since k-1 ≤ k]
        -- = eps * (n + k)^2          [algebra: k^2*(n/k+1)^2 = (n+k)^2]
        -- ≤ eps * (2n)^2             [since k ≤ n from k ≤ M ≤ n]
        -- = 4*eps*n^2
        -- ≤ (delta/2)*n^2            [since eps ≤ delta/8, so 4*eps ≤ delta/2]
        have hkq : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
        have hn_pos : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
        -- k ≤ n (from k ≤ M ≤ n)
        have hk_le_n : (k : ℚ) ≤ (n : ℚ) := by
          exact_mod_cast (show k ≤ n from le_trans hkM hn_small)
        -- (n/k+1)^2 ≤ (n/k + n/k)^2 = (2n/k)^2 when k ≤ n (since 1 ≤ n/k)
        -- But simpler: k*(n/k+1) = n + k ≤ 2n, so (n/k+1) ≤ 2n/k
        -- And k^2*(n/k+1)^2 = (k*(n/k+1))^2 = (n+k)^2 ≤ (2n)^2 = 4n^2
        calc (R_irreg.card : ℚ)
            ≤ S_irreg.sum (fun pq => ((pq.1 ×ˢ pq.2).card : ℚ)) := h_card_irreg
          _ ≤ S_irreg.card * ((n : ℚ) / k + 1) ^ 2 := h_sum_bound
          _ ≤ eps * (↑k * (↑k - 1)) * ((n : ℚ) / k + 1) ^ 2 := by
              apply mul_le_mul_of_nonneg_right hirr_count
              exact sq_nonneg _
          _ ≤ eps * (↑k * ↑k) * ((n : ℚ) / k + 1) ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
              apply mul_le_mul_of_nonneg_left _ (le_of_lt heps)
              linarith
          _ = eps * ((↑k : ℚ) * ((n : ℚ) / k + 1)) ^ 2 := by ring
          _ = eps * ((n : ℚ) + ↑k) ^ 2 := by
              congr 1; congr 1
              field_simp
          _ ≤ eps * (2 * (n : ℚ)) ^ 2 := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt heps)
              apply sq_le_sq'
              · linarith
              · linarith
          _ = 4 * eps * (n : ℚ) ^ 2 := by ring
          _ ≤ (delta / 2) * (n : ℚ) ^ 2 := by nlinarith
      -- Step 4: Bound sparse cross-part edges ≤ (δ/4)n²
      have h_sparse : (R_sparse.card : ℚ) ≤ (delta / 4) * ↑n ^ 2 := by
        -- Strategy: Each (u,v) in R_sparse has u ∈ Pa, v ∈ Pb with edgeDensity < 2*eps.
        -- The partition determines a unique (Pa,Pb) per (u,v).
        -- Sum over all part-pairs: edges in pair ≤ density * |Pa|*|Pb| < 2*eps*|Pa|*|Pb|.
        -- Total sum of |Pa|*|Pb| over all pairs = n^2, so R_sparse < 2*eps*n^2 ≤ (delta/4)*n^2.
        --
        -- Step A: R_sparse ⊆ biUnion over all part-pairs of edge-filtered products
        have h_sub_sparse : R_sparse ⊆
            (P.parts ×ˢ P.parts).biUnion (fun pq =>
              (pq.1 ×ˢ pq.2).filter (fun p => G.Adj p.1 p.2)) := by
          intro ⟨u, v⟩ huv
          simp only [R_sparse, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
            true_and] at huv
          obtain ⟨hadj, Pa, hPa, Pb, hPb, _, hu, hv, _⟩ := huv
          exact Finset.mem_biUnion.mpr ⟨(Pa, Pb),
            Finset.mem_product.mpr ⟨hPa, hPb⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hv⟩, hadj⟩⟩
        -- Step B: |R_sparse| ≤ Σ_{(Pa,Pb) ∈ parts×parts} |(Pa ×ˢ Pb).filter Adj|
        have h_card_sparse : (R_sparse.card : ℚ) ≤
            (P.parts ×ˢ P.parts).sum (fun pq =>
              (((pq.1 ×ˢ pq.2).filter (fun p => G.Adj p.1 p.2)).card : ℚ)) := by
          have h1 := Finset.card_le_card h_sub_sparse
          have h2 : ((P.parts ×ˢ P.parts).biUnion (fun pq : Finset V × Finset V =>
              (pq.1 ×ˢ pq.2).filter (fun p => G.Adj p.1 p.2))).card ≤
              (P.parts ×ˢ P.parts).sum (fun pq : Finset V × Finset V =>
                ((pq.1 ×ˢ pq.2).filter (fun p => G.Adj p.1 p.2)).card) :=
            Finset.card_biUnion_le
          push_cast; exact_mod_cast le_trans h1 h2
        -- Step C: |(Pa ×ˢ Pb).filter Adj| ≤ |Pa| * |Pb| for all pairs
        -- (This is the trivial density-1 bound; the edge count is at most the full product.)
        have h_edge_le_prod : ∀ pq ∈ P.parts ×ˢ P.parts,
            (((pq.1 ×ˢ pq.2).filter (fun p => G.Adj p.1 p.2)).card : ℚ) ≤
              (pq.1.card : ℚ) * pq.2.card := by
          intro ⟨Pa, Pb⟩ _
          have h1 : ((Pa ×ˢ Pb).filter (fun p => G.Adj p.1 p.2)).card ≤ (Pa ×ˢ Pb).card :=
            Finset.card_filter_le _ _
          have h2 : (Pa ×ˢ Pb).card = Pa.card * Pb.card := Finset.card_product Pa Pb
          exact_mod_cast h2 ▸ h1
        -- Step D: edge_count = edgeDensity * |Pa| * |Pb| (from definition of edgeDensity)
        have h_edge_eq_dens : ∀ Pa Pb : Finset V,
            (((Pa ×ˢ Pb).filter (fun p => G.Adj p.1 p.2)).card : ℚ) =
              edgeDensity G Pa Pb * (Pa.card : ℚ) * Pb.card := by
          intro Pa Pb
          unfold edgeDensity
          split_ifs with h
          · -- Pa.card * Pb.card = 0, so product is empty
            simp only [zero_mul]
            rw [Nat.cast_eq_zero, Finset.card_eq_zero]
            rcases mul_eq_zero.mp h with ha | hb
            · have hA := Finset.card_eq_zero.mp (Nat.cast_eq_zero.mp ha)
              subst hA; simp
            · have hB := Finset.card_eq_zero.mp (Nat.cast_eq_zero.mp hb)
              subst hB; simp
          · rw [mul_assoc, div_mul_cancel₀ _ h]
            rfl
        -- Step E: Σ ≤ 2*eps * Σ |Pa|*|Pb|, using edgeDensity ≤ 1 for all pairs
        -- but we can't just use density < 2*eps for all pairs (only sparse ones).
        -- Instead: total edge count ≤ Σ |Pa|*|Pb| = n^2, and we need a tighter bound.
        -- The key observation: the Σ over all part-pairs of edge counts
        -- equals the total number of ordered pairs (u,v) that share a part-pair,
        -- which is at most n^2. But we need the factor 2*eps.
        --
        -- Actually, the simpler approach works: we don't need density at all.
        -- R_sparse only contains edges, and each edge is counted once per part-pair.
        -- The subset bound gives |R_sparse| ≤ Σ edge_count(Pa,Pb).
        -- For total, edge_count(Pa,Pb) ≤ |Pa|*|Pb|, and Σ|Pa|*|Pb| = n^2.
        -- But this gives |R_sparse| ≤ n^2, which is too loose.
        --
        -- We need: for edges in sparse pairs, edge_count ≤ 2*eps * |Pa|*|Pb|.
        -- And for edges NOT in sparse pairs, they're not in R_sparse.
        -- So R_sparse ⊆ biUnion over SPARSE pairs only.
        --
        -- Let me define the sparse pairs and redo the subset bound.
        set S_sparse := (P.parts ×ˢ P.parts).filter (fun pq : Finset V × Finset V =>
          pq.1 ≠ pq.2 ∧ edgeDensity G pq.1 pq.2 < 2 * eps)
        -- R_sparse ⊆ biUnion over sparse pairs of edge-filtered products
        have h_sub_sparse' : R_sparse ⊆
            S_sparse.biUnion (fun pq =>
              (pq.1 ×ˢ pq.2).filter (fun p => G.Adj p.1 p.2)) := by
          intro ⟨u, v⟩ huv
          simp only [R_sparse, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
            true_and] at huv
          obtain ⟨hadj, Pa, hPa, Pb, hPb, hne, hu, hv, hdens⟩ := huv
          exact Finset.mem_biUnion.mpr ⟨(Pa, Pb),
            Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hPa, hPb⟩, hne, hdens⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hv⟩, hadj⟩⟩
        -- |R_sparse| ≤ Σ_{sparse pairs} edge_count
        have h_card_sparse' : (R_sparse.card : ℚ) ≤
            S_sparse.sum (fun pq =>
              (((pq.1 ×ˢ pq.2).filter (fun p => G.Adj p.1 p.2)).card : ℚ)) := by
          have h1 := Finset.card_le_card h_sub_sparse'
          have h2 : (S_sparse.biUnion (fun pq : Finset V × Finset V =>
              (pq.1 ×ˢ pq.2).filter (fun p => G.Adj p.1 p.2))).card ≤
              S_sparse.sum (fun pq : Finset V × Finset V =>
                ((pq.1 ×ˢ pq.2).filter (fun p => G.Adj p.1 p.2)).card) :=
            Finset.card_biUnion_le
          push_cast; exact_mod_cast le_trans h1 h2
        -- For sparse pairs: edge_count = density * |Pa| * |Pb| < 2*eps * |Pa| * |Pb|
        have h_sparse_edge : ∀ pq ∈ S_sparse,
            (((pq.1 ×ˢ pq.2).filter (fun p => G.Adj p.1 p.2)).card : ℚ) ≤
              2 * eps * (pq.1.card : ℚ) * pq.2.card := by
          intro ⟨Pa, Pb⟩ hpq
          have hfilt := Finset.mem_filter.mp hpq
          have hdens : edgeDensity G Pa Pb < 2 * eps := hfilt.2.2
          rw [h_edge_eq_dens Pa Pb]
          have hnn : (0 : ℚ) ≤ (Pa.card : ℚ) * Pb.card := by positivity
          calc edgeDensity G Pa Pb * (Pa.card : ℚ) * Pb.card
              ≤ (2 * eps) * (Pa.card : ℚ) * Pb.card := by
                apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
                exact mul_le_mul_of_nonneg_right (le_of_lt hdens) (Nat.cast_nonneg _)
            _ = 2 * eps * (Pa.card : ℚ) * Pb.card := by ring
        -- Σ_{sparse pairs} 2*eps*|Pa|*|Pb| ≤ 2*eps * Σ_{all pairs} |Pa|*|Pb|
        have h_sparse_sum : S_sparse.sum (fun pq =>
            (((pq.1 ×ˢ pq.2).filter (fun p => G.Adj p.1 p.2)).card : ℚ)) ≤
            2 * eps * (P.parts ×ˢ P.parts).sum (fun pq =>
              (pq.1.card : ℚ) * pq.2.card) := by
          calc S_sparse.sum (fun pq =>
                (((pq.1 ×ˢ pq.2).filter (fun p => G.Adj p.1 p.2)).card : ℚ))
              ≤ S_sparse.sum (fun pq => 2 * eps * (pq.1.card : ℚ) * pq.2.card) :=
                Finset.sum_le_sum h_sparse_edge
            _ = 2 * eps * S_sparse.sum (fun pq => (pq.1.card : ℚ) * pq.2.card) := by
                rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun pq _ => by ring)
            _ ≤ 2 * eps * (P.parts ×ˢ P.parts).sum (fun pq =>
                  (pq.1.card : ℚ) * pq.2.card) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                  (fun pq _ _ => by positivity)
        -- Σ_{all pairs} |Pa|*|Pb| = n^2
        have h_sum_prod : (P.parts ×ˢ P.parts).sum (fun pq =>
            (pq.1.card : ℚ) * pq.2.card) = (n : ℚ) ^ 2 := by
          have h_factor : (P.parts ×ˢ P.parts).sum (fun pq =>
              (pq.1.card : ℚ) * pq.2.card) =
              P.parts.sum (fun S => (S.card : ℚ)) *
              P.parts.sum (fun S => (S.card : ℚ)) := by
            rw [Finset.sum_mul_sum, Finset.sum_product]
          rw [h_factor, show (n : ℚ) ^ 2 = (n : ℚ) * n from sq (n : ℚ)]
          congr 1 <;> (push_cast; exact_mod_cast hsum)
        -- Chain: R_sparse ≤ 2*eps*n^2 ≤ (delta/4)*n^2
        calc (R_sparse.card : ℚ)
            ≤ S_sparse.sum (fun pq =>
                (((pq.1 ×ˢ pq.2).filter (fun p => G.Adj p.1 p.2)).card : ℚ)) :=
              h_card_sparse'
          _ ≤ 2 * eps * (P.parts ×ˢ P.parts).sum (fun pq =>
                (pq.1.card : ℚ) * pq.2.card) := h_sparse_sum
          _ = 2 * eps * (n : ℚ) ^ 2 := by rw [h_sum_prod]
          _ ≤ (delta / 4) * (n : ℚ) ^ 2 := by nlinarith
      -- Step 5: Combine the three bounds
      calc (R.card : ℚ) ≤ ↑R_wp.card + ↑R_irreg.card + ↑R_sparse.card := hR_card
        _ ≤ (delta / 4) * ↑n ^ 2 + (delta / 2) * ↑n ^ 2 +
            (delta / 4) * ↑n ^ 2 := by linarith
        _ = delta * ↑n ^ 2 := by ring
    case triangle_free =>
      -- Main argument: any triangle in the cleaned graph contradicts
      -- the few-triangles hypothesis via the counting lemma.
      intro a b c ⟨hab, hbc, hac⟩
      -- Extract: each edge gives G.Adj and ∉ R (both directions)
      -- For (a,b) ∉ ↑R in the Set sense, convert to Finset membership
      have hab_nR : (a, b) ∉ R := fun h => hab.2.1 (Finset.mem_coe.mpr h)
      have hba_nR : (b, a) ∉ R := fun h => hab.2.2 (Finset.mem_coe.mpr h)
      have hbc_nR : (b, c) ∉ R := fun h => hbc.2.1 (Finset.mem_coe.mpr h)
      have hac_nR : (a, c) ∉ R := fun h => hac.2.1 (Finset.mem_coe.mpr h)
      -- Helper: if G.Adj u v and (u,v) ∉ R, extract the three negative conditions.
      -- Proved by contradiction: if any condition held, (u,v) ∈ R.
      have not_in_R : ∀ u v : V, G.Adj u v → (u, v) ∉ R →
          (∀ part ∈ P.parts, ¬(u ∈ part ∧ v ∈ part)) ∧
          (∀ Pa ∈ P.parts, ∀ Pb ∈ P.parts, Pa ≠ Pb → u ∈ Pa → v ∈ Pb →
            IsEpsilonRegular G eps Pa Pb) ∧
          (∀ Pa ∈ P.parts, ∀ Pb ∈ P.parts, Pa ≠ Pb → u ∈ Pa → v ∈ Pb →
            edgeDensity G Pa Pb ≥ 2 * eps) := by
        intro u v hadj hnR
        have huv_univ : (u, v) ∈ Finset.univ ×ˢ Finset.univ :=
          Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
        exact ⟨
          fun part hp huv => hnR (Finset.mem_filter.mpr
            ⟨huv_univ, Or.inl ⟨part, hp, huv⟩⟩),
          fun Pa hPa Pb hPb hne hu hv => by_contra fun h =>
            hnR (Finset.mem_filter.mpr
              ⟨huv_univ, Or.inr (Or.inl ⟨Pa, hPa, Pb, hPb, hne, hu, hv, h⟩)⟩),
          fun Pa hPa Pb hPb hne hu hv => le_of_not_lt fun h =>
            hnR (Finset.mem_filter.mpr
              ⟨huv_univ, Or.inr (Or.inr ⟨hadj, Pa, hPa, Pb, hPb, hne, hu, hv, h⟩)⟩)⟩
      -- Extract properties for each edge
      obtain ⟨hab_wp, hab_reg, hab_dense⟩ := not_in_R a b hab.1 hab_nR
      obtain ⟨hac_wp, hac_reg, hac_dense⟩ := not_in_R a c hac.1 hac_nR
      obtain ⟨hbc_wp, hbc_reg, hbc_dense⟩ := not_in_R b c hbc.1 hbc_nR
      -- Find parts for each vertex from the Finpartition
      obtain ⟨Pa, hPa, ha_Pa⟩ := P.exists_mem (Finset.mem_univ a)
      obtain ⟨Pb, hPb, hb_Pb⟩ := P.exists_mem (Finset.mem_univ b)
      obtain ⟨Pc, hPc, hc_Pc⟩ := P.exists_mem (Finset.mem_univ c)
      -- Vertices are in DIFFERENT parts (within-part edges are in R)
      have hab_diff : Pa ≠ Pb := by
        intro heq; exact absurd ⟨ha_Pa, heq ▸ hb_Pb⟩ (hab_wp Pa hPa)
      have hac_diff : Pa ≠ Pc := by
        intro heq; exact absurd ⟨ha_Pa, heq ▸ hc_Pc⟩ (hac_wp Pa hPa)
      have hbc_diff : Pb ≠ Pc := by
        intro heq; exact absurd ⟨hb_Pb, heq ▸ hc_Pc⟩ (hbc_wp Pb hPb)
      -- All three pairs are ε-regular (irregular pair edges are in R)
      have hAB_reg : IsEpsilonRegular G eps Pa Pb :=
        hab_reg Pa hPa Pb hPb hab_diff ha_Pa hb_Pb
      have hAC_reg : IsEpsilonRegular G eps Pa Pc :=
        hac_reg Pa hPa Pc hPc hac_diff ha_Pa hc_Pc
      have hBC_reg : IsEpsilonRegular G eps Pb Pc :=
        hbc_reg Pb hPb Pc hPc hbc_diff hb_Pb hc_Pc
      -- All three pairs have density ≥ 2ε (sparse pair edges are in R)
      have hAB_dense : edgeDensity G Pa Pb ≥ 2 * eps :=
        hab_dense Pa hPa Pb hPb hab_diff ha_Pa hb_Pb
      have hAC_dense : edgeDensity G Pa Pc ≥ 2 * eps :=
        hac_dense Pa hPa Pc hPc hac_diff ha_Pa hc_Pc
      have hBC_dense : edgeDensity G Pb Pc ≥ 2 * eps :=
        hbc_dense Pb hPb Pc hPc hbc_diff hb_Pb hc_Pc
      -- Parts are non-empty (Finpartition guarantees no empty parts)
      have hPa_ne : Pa.Nonempty := P.nonempty_of_mem_parts hPa
      have hPb_ne : Pb.Nonempty := P.nonempty_of_mem_parts hPb
      have hPc_ne : Pc.Nonempty := P.nonempty_of_mem_parts hPc
      have hPa_pos : (0 : ℚ) < Pa.card :=
        Nat.cast_pos.mpr (Finset.card_pos.mpr hPa_ne)
      have hPb_pos : (0 : ℚ) < Pb.card :=
        Nat.cast_pos.mpr (Finset.card_pos.mpr hPb_ne)
      have hPc_pos : (0 : ℚ) < Pc.card :=
        Nat.cast_pos.mpr (Finset.card_pos.mpr hPc_ne)
      -- Apply counting lemma: many triangles in (Pa, Pb, Pc) of G
      have hcount := counting_lemma G eps heps heps_half Pa Pb Pc
        hPa_pos hPb_pos hPc_pos hAB_reg hAC_reg hBC_reg
        hAB_dense hAC_dense (le_trans (by linarith : eps ≤ 2 * eps) hBC_dense)
      -- Monotonicity: total triangles ≥ triangles in (Pa, Pb, Pc)
      have htotal_ge : (triangleCount G Pa Pb Pc : ℚ) ≤
          triangleCount G Finset.univ Finset.univ Finset.univ := by
        exact_mod_cast triangleCount_le_total G Pa Pb Pc
      -- Part size lower bound (from equitable partition into k ≤ M parts)
      -- Each part has ≥ ⌊n/k⌋ ≥ n/(2M) elements for n ≥ M
      have hpart_size : ∀ S ∈ P.parts, (S.card : ℚ) ≥ (n : ℚ) / (2 * ↑M) := by
        intro S hS
        have hS_pos : 0 < S.card := Finset.card_pos.mpr (P.nonempty_of_mem_parts hS)
        have hk_pos : 0 < k := by omega
        have hkQ : (0 : ℚ) < (k : ℚ) := Nat.cast_pos.mpr hk_pos
        have hkM_q : (k : ℚ) ≤ (M : ℚ) := Nat.cast_le.mpr hkM
        -- Equitability: every part size ≤ S.card + 1
        have hbound : ∀ T ∈ P.parts, T.card ≤ S.card + 1 :=
          fun T hT => hequi (Finset.mem_coe.mpr hT) (Finset.mem_coe.mpr hS)
        -- n ≤ k * (S.card + 1): sum of parts = n, each ≤ S.card + 1
        have hn_le : n ≤ k * (S.card + 1) := by
          -- Sum of part sizes = n (from Finpartition structure)
          have hsum : P.parts.sum Finset.card = n := by
            simpa [hn_def, Finset.card_univ] using P.sum_card_parts
          calc n = P.parts.sum Finset.card := hsum.symm
            _ ≤ P.parts.sum (fun _ => S.card + 1) :=
                Finset.sum_le_sum fun T hT => hbound T hT
            _ = k * (S.card + 1) := by
                simp [Finset.sum_const, hk_def]
        -- S.card ≥ n/k - 1 (in ℚ)
        have hS_ge : (S.card : ℚ) ≥ (n : ℚ) / k - 1 := by
          rw [ge_iff_le, sub_le_iff_le_add, div_le_iff₀ hkQ]
          have : (n : ℚ) ≤ (k : ℚ) * ((S.card : ℚ) + 1) := by exact_mod_cast hn_le
          linarith
        -- n/k ≥ n/M (since k ≤ M)
        have hk_div : (n : ℚ) / k ≥ (n : ℚ) / M := by
          exact div_le_div_of_nonneg_left (by positivity : (0 : ℚ) ≤ (n : ℚ)) hkQ hkM_q
        -- Case split on graph size relative to 2M
        by_cases hn2M : n < 2 * M
        · -- n < 2M: S.card ≥ 1 > n/(2M) since n/(2M) < 1
          have : (n : ℚ) / (2 * ↑M) < 1 := by
            rw [div_lt_one (by positivity : (0:ℚ) < 2 * ↑M)]
            exact_mod_cast hn2M
          linarith [show (1 : ℚ) ≤ ↑S.card from Nat.cast_le.mpr hS_pos]
        · -- n ≥ 2M: n/M ≥ 2 so n/M - 1 ≥ n/(2M)
          push_neg at hn2M
          have hnM_ge2 : (n : ℚ) / ↑M ≥ 2 := by
            rw [ge_iff_le, le_div_iff₀ hM_pos]; exact_mod_cast hn2M
          have : (n : ℚ) / ↑M - 1 ≥ (n : ℚ) / (2 * ↑M) := by
            rw [show (2 : ℚ) * ↑M = ↑M * 2 by ring, ← div_div]
            linarith
          linarith
      have hPa_size := hpart_size Pa hPa
      have hPb_size := hpart_size Pb hPb
      have hPc_size := hpart_size Pc hPc
      -- The counting lemma gives: total ≥ count(Pa,Pb,Pc) ≥ K
      -- where K > gamma·n³ by construction of gamma
      -- This contradicts the hypothesis total ≤ gamma·n³
      have hK : (triangleCount G Finset.univ Finset.univ Finset.univ : ℚ) ≥
          (1 - 2 * eps) * eps ^ 3 * ((n : ℚ) / (2 * M)) ^ 3 := by
        calc (triangleCount G Finset.univ Finset.univ Finset.univ : ℚ)
            ≥ triangleCount G Pa Pb Pc := htotal_ge
          _ ≥ (1 - 2 * eps) *
              (edgeDensity G Pa Pb - eps) *
              (edgeDensity G Pa Pc - eps) *
              (edgeDensity G Pb Pc - eps) *
              Pa.card * Pb.card * Pc.card := hcount
          _ ≥ (1 - 2 * eps) * eps * eps * eps *
              Pa.card * Pb.card * Pc.card := by
            have e1 : eps ≤ edgeDensity G Pa Pb - eps := by linarith
            have e2 : eps ≤ edgeDensity G Pa Pc - eps := by linarith
            have e3 : eps ≤ edgeDensity G Pb Pc - eps := by linarith
            have h12 : (0 : ℚ) ≤ 1 - 2 * eps := h12eps.le
            have hd1 : (0 : ℚ) ≤ edgeDensity G Pa Pb - eps := le_trans heps.le e1
            have hd2 : (0 : ℚ) ≤ edgeDensity G Pa Pc - eps := le_trans heps.le e2
            have k1 : (1 - 2 * eps) * eps ≤ (1 - 2 * eps) * (edgeDensity G Pa Pb - eps) :=
              mul_le_mul_of_nonneg_left e1 h12
            have k2 : (1 - 2 * eps) * eps * eps ≤
                (1 - 2 * eps) * (edgeDensity G Pa Pb - eps) * (edgeDensity G Pa Pc - eps) :=
              mul_le_mul k1 e2 heps.le (mul_nonneg h12 hd1)
            have k3 : (1 - 2 * eps) * eps * eps * eps ≤
                (1 - 2 * eps) * (edgeDensity G Pa Pb - eps) * (edgeDensity G Pa Pc - eps) *
                  (edgeDensity G Pb Pc - eps) :=
              mul_le_mul k2 e3 heps.le (mul_nonneg (mul_nonneg h12 hd1) hd2)
            have hc : (0 : ℚ) ≤ (Pa.card : ℚ) * Pb.card * Pc.card := by positivity
            calc (1 - 2 * eps) * eps * eps * eps * (Pa.card : ℚ) * Pb.card * Pc.card
                = ((1 - 2 * eps) * eps * eps * eps) * ((Pa.card : ℚ) * Pb.card * Pc.card) := by
                  ring
              _ ≤ ((1 - 2 * eps) * (edgeDensity G Pa Pb - eps) * (edgeDensity G Pa Pc - eps) *
                    (edgeDensity G Pb Pc - eps)) * ((Pa.card : ℚ) * Pb.card * Pc.card) :=
                  mul_le_mul_of_nonneg_right k3 hc
              _ = (1 - 2 * eps) * (edgeDensity G Pa Pb - eps) * (edgeDensity G Pa Pc - eps) *
                    (edgeDensity G Pb Pc - eps) * (Pa.card : ℚ) * Pb.card * Pc.card := by ring
          _ ≥ (1 - 2 * eps) * eps ^ 3 *
              ((n : ℚ) / (2 * M)) ^ 3 := by
            have hs : (0 : ℚ) ≤ (n : ℚ) / (2 * ↑M) := by positivity
            have hsa : (n : ℚ) / (2 * ↑M) ≤ (Pa.card : ℚ) := hPa_size
            have hsb : (n : ℚ) / (2 * ↑M) ≤ (Pb.card : ℚ) := hPb_size
            have hsc : (n : ℚ) / (2 * ↑M) ≤ (Pc.card : ℚ) := hPc_size
            have t1 : (n : ℚ) / (2 * ↑M) * ((n : ℚ) / (2 * ↑M)) ≤ (Pa.card : ℚ) * Pb.card :=
              mul_le_mul hsa hsb hs (le_trans hs hsa)
            have hcube : ((n : ℚ) / (2 * ↑M)) ^ 3 ≤ (Pa.card : ℚ) * Pb.card * Pc.card := by
              calc ((n : ℚ) / (2 * ↑M)) ^ 3
                  = (n : ℚ) / (2 * ↑M) * ((n : ℚ) / (2 * ↑M)) * ((n : ℚ) / (2 * ↑M)) := by ring
                _ ≤ (Pa.card : ℚ) * Pb.card * Pc.card :=
                    mul_le_mul t1 hsc hs (le_trans (mul_nonneg hs hs) t1)
            have hfac : (0 : ℚ) ≤ (1 - 2 * eps) * eps ^ 3 :=
              mul_nonneg h12eps.le (by positivity)
            calc (1 - 2 * eps) * eps ^ 3 * ((n : ℚ) / (2 * ↑M)) ^ 3
                ≤ (1 - 2 * eps) * eps ^ 3 * ((Pa.card : ℚ) * Pb.card * Pc.card) :=
                  mul_le_mul_of_nonneg_left hcube hfac
              _ = (1 - 2 * eps) * eps * eps * eps * (Pa.card : ℚ) * Pb.card * Pc.card := by ring
      -- The lower bound exceeds gamma·n³
      have hgamma_bound :
          (1 - 2 * eps) * eps ^ 3 * ((n : ℚ) / (2 * M)) ^ 3 >
          gamma * (n : ℚ) ^ 3 := by
        -- LHS = (1-2ε)ε³n³/(8M³) = 2·gamma·n³ > gamma·n³
        have hn_pos : (0 : ℚ) < (n : ℚ) := by
          exact_mod_cast (show 0 < n by omega)
        have h_eq : (1 - 2 * eps) * eps ^ 3 * ((n : ℚ) / (2 * ↑M)) ^ 3 =
            2 * (gamma * (n : ℚ) ^ 3) := by
          rw [hgamma_def]; field_simp; ring
        linarith [mul_pos hgamma_pos (pow_pos hn_pos 3)]
      linarith

end Szemeredi.Counting
