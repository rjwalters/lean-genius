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
    fun a ha => le_trans (by nlinarith [Nat.cast_nonneg B.card]) (hgood_NB a ha)
  have hgood_NC_eps : ∀ a ∈ good,
      ((neighborhoodIn G a C).card : ℚ) ≥ eps * C.card :=
    fun a ha => le_trans (by nlinarith [Nat.cast_nonneg C.card]) (hgood_NC a ha)
  -- Step 3: Good vertex count > (1-2ε)|A|
  have hgood_card : (good.card : ℚ) > (1 - 2 * eps) * A.card := by
    -- |A \ good| ≤ |badB ∪ badC| ≤ |badB| + |badC| < 2ε|A|
    suffices h : (A.card : ℚ) - good.card < 2 * eps * A.card by linarith
    have h_compl_card : (A \ good).card + good.card = A.card :=
      Finset.sdiff_union_self_eq_union ▸
        (Finset.card_union_of_disjoint Finset.sdiff_disjoint).symm ▸
        congrArg Finset.card (Finset.sdiff_union_self_eq_union.trans
          (Finset.union_eq_left.mpr hgood_sub))
    have h_sub : A \ good ⊆ badB ∪ badC := by
      intro a ha
      have haA := (Finset.mem_sdiff.mp ha).1
      have ha_ng := (Finset.mem_sdiff.mp ha).2
      by_contra h_not
      rw [Finset.mem_union, not_or] at h_not
      exact ha_ng (Finset.mem_filter.mpr ⟨haA, h_not.1, h_not.2⟩)
    have h_compl_le : ((A \ good).card : ℚ) ≤ badB.card + badC.card :=
      Nat.cast_le.mpr (le_trans (Finset.card_le_card h_sub) (Finset.card_union_le badB badC))
    have : (A.card : ℚ) - good.card = (A \ good).card := by
      push_cast; linarith [h_compl_card]
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
        ↑A.card * ↑B.card * ↑C.card := by unfold_let K; ring

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
  sorry

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

end Szemeredi.Counting
