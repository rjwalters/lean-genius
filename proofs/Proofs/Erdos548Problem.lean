/-
  Erdős Problem #548: The Erdős-Sós Conjecture

  Source: https://erdosproblems.com/548
  Status: OPEN (falsifiable)

  Statement:
  Let n ≥ k+1. Every graph on n vertices with at least (k-1)/2 · n + 1 edges
  contains every tree on k+1 vertices.

  Equivalently: If a graph G has average degree > k-1, then G contains
  every tree with k edges as a subgraph.

  Key Results:
  - Trivial bound: n(k-1)+1 edges suffice (inductive proof)
  - Brandt-Dobson (1996): True for graphs with girth ≥ 5
  - Saclé-Wozniak (1997): True for graphs with no C₄
  - Wang-Li-Liu (2000): True if complement has girth ≥ 5
  - The full conjecture remains open

  Related:
  - Erdős-Gallai (1959): Maximum edges without k independent edges
  - Komlós-Sós-Szemerédi: Announced proof for large k (unpublished details)

  References:
  [ErSo63] Erdős-Sós, original conjecture
  [BrDo96] Brandt-Dobson, girth 5 case
  [SaWo97] Saclé-Wozniak, C₄-free case

  Tags: graph-theory, trees, extremal-graph-theory, erdos-sos, subgraphs
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
open scoped Classical

namespace Erdos548

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/- ## Part I: Trees -/

/-- A tree is a connected acyclic graph.  Delegates to Mathlib's
    `SimpleGraph.IsTree` (`Connected ∧ IsAcyclic`).

    (The former local definition `Connected ∧ ∀ v w, Adj v w → Reachable v w`
    was degenerate: the second conjunct holds for *every* graph, so it defined
    "connected", not "tree" — which made `tree_edge_count` a false statement.) -/
def IsTree (G : SimpleGraph V) : Prop := G.IsTree

/-- A tree on k+1 vertices has exactly k edges.  (Formerly an axiom; provable
    from Mathlib's `SimpleGraph.IsTree.card_edgeFinset` once `IsTree` denotes a
    genuine tree.) -/
theorem tree_edge_count {T : SimpleGraph V} (hT : IsTree T) (hn : Fintype.card V = k + 1) :
    T.edgeFinset.card = k := by
  classical
  have hT' : T.IsTree := hT
  have h := hT'.card_edgeFinset
  omega

/-- The path graph P_n on n vertices. -/
def pathGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := (i.val + 1 = j.val) ∨ (j.val + 1 = i.val)
  symm := by
    constructor
    intro i j h
    cases h with
    | inl h => right; exact h
    | inr h => left; exact h
  loopless := by
    constructor
    intro i h
    cases h with
    | inl h => omega
    | inr h => omega

/-- The star graph K_{1,k} with k leaves. -/
def starGraph (k : ℕ) : SimpleGraph (Fin (k + 1)) where
  Adj i j := (i.val = 0 ∧ j.val ≠ 0) ∨ (j.val = 0 ∧ i.val ≠ 0)
  symm.symm := by
    intro i j h
    cases h with
    | inl h => right; exact ⟨h.1, h.2⟩
    | inr h => left; exact ⟨h.1, h.2⟩
  loopless.irrefl := by
    intro i h
    cases h with
    | inl h => exact h.2 h.1
    | inr h => exact h.2 h.1

/-- The star's edge set: one edge from the centre `0` to each other vertex. -/
theorem starGraph_edgeFinset (k : ℕ) :
    (starGraph k).edgeFinset =
      (Finset.univ.erase (0 : Fin (k + 1))).image
        (fun j => s((0 : Fin (k + 1)), j)) := by
  ext e
  refine Sym2.inductionOn e fun i j => ?_
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_image,
    Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro (⟨hi, hj⟩ | ⟨hj, hi⟩)
    · have hi0 : i = (0 : Fin (k + 1)) := Fin.ext (by simpa using hi)
      refine ⟨j, fun h0 => hj (by simp [h0]), by rw [hi0]⟩
    · have hj0 : j = (0 : Fin (k + 1)) := Fin.ext (by simpa using hj)
      refine ⟨i, fun h0 => hi (by simp [h0]), ?_⟩
      rw [hj0, Sym2.eq_swap]
  · rintro ⟨a, ha0, hae⟩
    rw [Sym2.eq_iff] at hae
    rcases hae with ⟨h0i, haj⟩ | ⟨h0j, hai⟩
    · exact Or.inl ⟨by simp [← h0i], fun h => ha0 (Fin.ext (by simp [haj, h]))⟩
    · exact Or.inr ⟨by simp [← h0j], fun h => ha0 (Fin.ext (by simp [hai, h]))⟩

/-- The star on `k+1` vertices has exactly `k` edges. -/
theorem starGraph_edgeFinset_card (k : ℕ) : (starGraph k).edgeFinset.card = k := by
  rw [starGraph_edgeFinset]
  have hinj : Set.InjOn (fun j => s((0 : Fin (k + 1)), j))
      (Finset.univ.erase (0 : Fin (k + 1))) := by
    intro a _ b _ hab
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨-, h⟩ | ⟨h0b, ha0⟩
    · exact h
    · rw [ha0, h0b]
  rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]
  omega

/-- The star graph is connected: every vertex is adjacent to the centre `0`. -/
theorem starGraph_connected (k : ℕ) : (starGraph k).Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨fun i j => ?_, ⟨0⟩⟩
  have h0 : ∀ a : Fin (k + 1), a.val ≠ 0 → (starGraph k).Adj 0 a :=
    fun a ha => Or.inl ⟨by simp, ha⟩
  by_cases hij : i = j
  · exact hij ▸ SimpleGraph.Reachable.refl i
  · by_cases hi : i.val = 0
    · by_cases hj : j.val = 0
      · exact absurd (Fin.ext (hi.trans hj.symm)) hij
      · have hi0 : i = (0 : Fin (k + 1)) := Fin.ext (by simpa using hi)
        exact hi0 ▸ (h0 j hj).reachable
    · by_cases hj : j.val = 0
      · have hj0 : j = (0 : Fin (k + 1)) := Fin.ext (by simpa using hj)
        exact hj0 ▸ ((h0 i hi).symm).reachable
      · exact ((h0 i hi).symm.reachable).trans (h0 j hj).reachable

/-- Stars are trees.  (Formerly a sorry; proved via
    `SimpleGraph.isTree_iff_connected_and_card`: the star is connected with
    exactly `k` edges on `k+1` vertices.  True for every `k`; the original
    `k ≥ 1` hypothesis is kept for signature stability.) -/
theorem star_is_tree (k : ℕ) (hk : k ≥ 1) : IsTree (starGraph k) := by
  show (starGraph k).IsTree
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨starGraph_connected k, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
    starGraph_edgeFinset_card, Nat.card_eq_fintype_card, Fintype.card_fin]

/- ## Part II: Subgraph Containment -/

/-- G contains H as a subgraph if there's an injective homomorphism from H to G. -/
def ContainsSubgraph (G : SimpleGraph V) {W : Type*} [Fintype W] (H : SimpleGraph W) : Prop :=
  ∃ f : W → V, Function.Injective f ∧ ∀ v w, H.Adj v w → G.Adj (f v) (f w)

/-- A graph is T-free if it doesn't contain T as a subgraph. -/
def TreeFree (G : SimpleGraph V) {W : Type*} [Fintype W] (T : SimpleGraph W) : Prop :=
  ¬ContainsSubgraph G T

/- ## Part III: Edge Counting and Average Degree -/

/-- Number of edges in a graph. -/
noncomputable def edgeCount (G : SimpleGraph V) : ℕ := G.edgeFinset.card

/-- Sum of degrees equals twice the number of edges. -/
theorem sum_degrees_eq_twice_edges (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Finset.univ.sum fun v => G.degree v) = 2 * edgeCount G := by
  have h := G.sum_degrees_eq_twice_card_edges
  unfold edgeCount
  convert h using 2
  congr!

/-- Average degree of a graph. -/
noncomputable def avgDegree (G : SimpleGraph V) : ℚ :=
  if h : Fintype.card V = 0 then 0
  else (2 * edgeCount G : ℚ) / Fintype.card V

/-- A graph has average degree > k-1 iff it has > (k-1)n/2 edges.

    (Statement repair: the original sorried statement omitted `k ≥ 1` and was
    false at `k = 0` — there the ℚ-side threshold `↑k - 1 = -1` is trivially
    beaten while the ℕ-side threshold `(k-1) * n / 2` truncates to `0`.) -/
theorem avg_degree_iff_edges (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 1 ≤ k) :
    avgDegree G > k - 1 ↔ edgeCount G > (k - 1) * Fintype.card V / 2 := by
  have hcast : ((k : ℚ) - 1) = ((k - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub hk, Nat.cast_one]
  by_cases hn : Fintype.card V = 0
  · -- no vertices: both sides are false
    have hV : IsEmpty V := Fintype.card_eq_zero_iff.mp hn
    have hE : edgeCount G = 0 := by
      rw [edgeCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro e
      induction e using Sym2.inductionOn with
      | hf a b => exact fun _ => hV.elim a
    rw [avgDegree, dif_pos hn]
    constructor
    · intro h
      exfalso
      have h1 : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
      rw [gt_iff_lt, hcast] at h
      have : (0 : ℚ) ≤ ((k - 1 : ℕ) : ℚ) := Nat.cast_nonneg _
      linarith
    · intro h
      rw [hn, Nat.mul_zero, Nat.zero_div, hE] at h
      exact absurd h (lt_irrefl 0)
  · have hn' : (0 : ℚ) < (Fintype.card V : ℚ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have key : avgDegree G > (k : ℚ) - 1 ↔
        (k - 1) * Fintype.card V < 2 * edgeCount G := by
      rw [avgDegree, dif_neg hn, gt_iff_lt, hcast, lt_div_iff₀ hn']
      exact_mod_cast Iff.rfl
    rw [key]
    omega

/- ## Part IV: The Erdős-Sós Conjecture -/

/-- **Erdős-Sós Conjecture**

    Every graph on n vertices with more than (k-1)n/2 edges contains
    every tree on k+1 vertices as a subgraph.
-/
def ErdosSosConjecture : Prop :=
  ∀ (k : ℕ),
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
  ∀ (W : Type) [Fintype W] [DecidableEq W] (T : SimpleGraph W),
  IsTree T →
  Fintype.card W = k + 1 →
  Fintype.card V ≥ k + 1 →
  edgeCount G > (k - 1) * Fintype.card V / 2 →
  ContainsSubgraph G T

/-- The main problem statement as asked by Erdős. -/
def Erdos548Statement : Prop :=
  ∀ n k : ℕ, n ≥ k + 1 →
  ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  edgeCount G ≥ (k - 1) * n / 2 + 1 →
  ∀ (T : SimpleGraph (Fin (k + 1))),
  IsTree T →
  ContainsSubgraph G T

/- ## Part V: Known Results -/

/-- **Trivial Bound**

    n(k-1) + 1 edges suffice to contain any tree on k+1 vertices.
    (Much weaker than the conjecture.)
-/
axiom trivial_tree_bound (n k : ℕ) (hn : n ≥ k + 1)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : edgeCount G ≥ n * (k - 1) + 1)
    (T : SimpleGraph (Fin (k + 1))) (hT : IsTree T) :
    ContainsSubgraph G T

/-- **Girth of a graph**: length of shortest cycle, or ∞ if acyclic.
    (v4.31 migration: `G.Walk` is indexed by vertices, not the carrier type;
    quantify over a base vertex `v` and closed walks at `v`.) -/
noncomputable def girth (G : SimpleGraph V) : ℕ∞ :=
  ⨅ (v : V) (c : G.Walk v v) (_ : c.IsCycle), c.length

/-- G has girth ≥ g means no cycles shorter than g. -/
def hasGirthAtLeast (G : SimpleGraph V) (g : ℕ) : Prop :=
  ∀ (v : V) (c : G.Walk v v), c.IsCycle → c.length ≥ g

/-- **Brandt-Dobson (1996)**

    The Erdős-Sós conjecture holds for graphs with girth ≥ 5.
-/
axiom brandt_dobson (n k : ℕ) (hn : n ≥ k + 1)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hGirth : hasGirthAtLeast G 5)
    (hG : edgeCount G > (k - 1) * n / 2)
    (T : SimpleGraph (Fin (k + 1))) (hT : IsTree T) :
    ContainsSubgraph G T

/-- G is C₄-free (no 4-cycles). -/
def C4Free (G : SimpleGraph V) : Prop := hasGirthAtLeast G 5 ∨
  ∀ (a b c d : V), G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d

/-- **Saclé-Wozniak (1997)**

    The Erdős-Sós conjecture holds for C₄-free graphs.
-/
axiom sacle_wozniak (n k : ℕ) (hn : n ≥ k + 1)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hC4 : C4Free G)
    (hG : edgeCount G > (k - 1) * n / 2)
    (T : SimpleGraph (Fin (k + 1))) (hT : IsTree T) :
    ContainsSubgraph G T

/-- The complement of a graph. -/
def complement (G : SimpleGraph V) : SimpleGraph V where
  Adj v w := v ≠ w ∧ ¬G.Adj v w
  symm.symm := by
    intro v w ⟨hne, hnadj⟩
    exact ⟨hne.symm, fun h => hnadj (G.adj_symm h)⟩
  loopless.irrefl := by
    intro v ⟨hne, _⟩
    exact hne rfl

/-- **Wang-Li-Liu (2000)**

    The Erdős-Sós conjecture holds when the complement has girth ≥ 5.
-/
axiom wang_li_liu (n k : ℕ) (hn : n ≥ k + 1)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hComp : hasGirthAtLeast (complement G) 5)
    (hG : edgeCount G > (k - 1) * n / 2)
    (T : SimpleGraph (Fin (k + 1))) (hT : IsTree T) :
    ContainsSubgraph G T

/- ## Part VI: Extremal Function -/

/-- The extremal number ex(n, T) is the maximum edges in a T-free graph on n vertices. -/
noncomputable def extremalNumber (n : ℕ) {W : Type*} [Fintype W] (T : SimpleGraph W) : ℕ :=
  sSup {m : ℕ | ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
    TreeFree G T ∧ edgeCount G = m}

/-- The Erdős-Sós conjecture implies ex(n, T) ≤ (k-1)n/2 for trees T on k+1 vertices.

    (Statement repair: `W` must live in `Type` — `ErdosSosConjecture`
    quantifies its tree type over `Type`, so the universe-polymorphic
    `Type*` version is not derivable from it.) -/
theorem erdos_sos_implies_extremal {W : Type} [Fintype W] [DecidableEq W]
    (T : SimpleGraph W) (hT : IsTree T) (hk : Fintype.card W = k + 1) (n : ℕ) (hn : n ≥ k + 1) :
    ErdosSosConjecture → extremalNumber n T ≤ (k - 1) * n / 2 := by
  intro hesc
  refine csSup_le' ?_
  rintro m ⟨G, instG, hfree, hcount⟩
  by_contra hm
  push_neg at hm
  refine hfree ?_
  refine hesc k (Fin n) G W T hT hk ?_ ?_
  · simpa using hn
  · rw [Fintype.card_fin]
    omega

/- ## Part VII: Special Trees -/

/-- The path P_k achieves the extremal bound. -/
axiom path_extremal (n k : ℕ) (hn : n ≥ k + 1) (hk : k ≥ 2) :
    extremalNumber n (pathGraph (k + 1)) = (k - 1) * n / 2

/-- Stars are easier - they're contained in graphs with average degree ≥ k. -/
theorem star_easier (n k : ℕ) (hn : n ≥ k + 1)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : edgeCount G ≥ k * n / 2) :
    ContainsSubgraph G (starGraph k) := by
  -- Step 1: some vertex has degree ≥ k (pigeonhole on the degree sum).
  have hne : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin n, k ≤ G.degree v := by
    by_contra hall
    push_neg at hall
    -- every degree ≤ k - 1, and k ≥ 1 (a degree is < k), so sum ≤ (k-1) n
    obtain ⟨w⟩ := hne
    have hk1 : 1 ≤ k := by have := hall w; omega
    have hsum : (Finset.univ.sum fun u => G.degree u) ≤ (k - 1) * n := by
      calc (Finset.univ.sum fun u => G.degree u)
          ≤ Finset.univ.card • (k - 1) :=
            Finset.sum_le_card_nsmul _ _ _ (fun u _ => by have := hall u; omega)
        _ = (k - 1) * n := by
            rw [Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]
    rw [sum_degrees_eq_twice_edges, Nat.sub_mul, one_mul] at hsum
    -- omega needs the (nonlinear) fact n ≤ k*n spelled out
    have hkn : n ≤ k * n := Nat.le_mul_of_pos_left n hk1
    -- 2 * edgeCount ≥ 2 * (k*n/2) ≥ k*n - 1 and ≤ k*n - n with n ≥ 2
    omega
  -- Step 2: pick k distinct neighbours of v and map the star onto them.
  obtain ⟨S, hS, hScard⟩ :=
    Finset.exists_subset_card_eq (n := k) (s := G.neighborFinset v) (by rwa [G.card_neighborFinset_eq_degree])
  let e := S.orderIsoOfFin hScard
  refine ⟨Fin.cases v (fun i => (e i : Fin n)), ?_, ?_⟩
  · -- injectivity: v is not its own neighbour, and e is injective
    have hveS : ∀ i : Fin k, (e i : Fin n) ≠ v := by
      intro i hvi
      have : (e i : Fin n) ∈ G.neighborFinset v := hS (e i).2
      rw [hvi, SimpleGraph.mem_neighborFinset] at this
      exact G.irrefl this
    intro a b hab
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => rfl
      | succ j =>
        simp only [Fin.cases_zero, Fin.cases_succ] at hab
        exact absurd hab.symm (hveS j)
    | succ i =>
      induction b using Fin.cases with
      | zero =>
        simp only [Fin.cases_zero, Fin.cases_succ] at hab
        exact absurd hab (hveS i)
      | succ j =>
        simp only [Fin.cases_succ] at hab
        have : e i = e j := Subtype.ext hab
        rw [e.injective this]
  · -- adjacency: a star edge joins the centre to a leaf
    intro a b hab
    rcases hab with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · -- a is the centre, b = succ j is a leaf
      have ha0 : a = 0 := Fin.ext (by simpa using ha)
      induction b using Fin.cases with
      | zero => exact absurd (by simp) hb
      | succ j =>
        subst ha0
        simp only [Fin.cases_zero, Fin.cases_succ]
        have : (e j : Fin n) ∈ G.neighborFinset v := hS (e j).2
        rwa [SimpleGraph.mem_neighborFinset] at this
    · -- b is the centre, a = succ i is a leaf
      have hb0 : b = 0 := Fin.ext (by simpa using hb)
      induction a using Fin.cases with
      | zero => exact absurd (by simp) ha
      | succ i =>
        subst hb0
        simp only [Fin.cases_zero, Fin.cases_succ]
        have : (e i : Fin n) ∈ G.neighborFinset v := hS (e i).2
        rw [SimpleGraph.mem_neighborFinset] at this
        exact this.symm

/- ## Part VIII: The Komlós-Sós Bound -/

/-- **Komlós-Sós Theorem (announced)**

    For sufficiently large k, the Erdős-Sós conjecture holds.
    (Full proof not yet published in detail.)
-/
axiom komlos_sos_large_k :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ n ≥ k + 1,
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    edgeCount G > (k - 1) * n / 2 →
    ∀ (T : SimpleGraph (Fin (k + 1))), IsTree T →
    ContainsSubgraph G T

/- ## Part IX: Related Theorems -/

/-- **Erdős-Gallai Theorem (1959)**

    The maximum number of edges in a graph on n vertices with no
    k+1 independent edges is max(binom(2k+1, 2), binom(k, 2) + k(n-k)).
-/
axiom erdos_gallai_matching (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : edgeCount G > Nat.choose (2 * k + 1) 2 ∨
          edgeCount G > Nat.choose k 2 + k * (n - k)) :
    ∃ (edges : Finset (Fin n × Fin n)),
      edges.card = k + 1 ∧
      (∀ e ∈ edges, G.Adj e.1 e.2) ∧
      (∀ e₁ e₂, e₁ ∈ edges → e₂ ∈ edges → e₁ ≠ e₂ →
        e₁.1 ≠ e₂.1 ∧ e₁.1 ≠ e₂.2 ∧ e₁.2 ≠ e₂.1 ∧ e₁.2 ≠ e₂.2)

/-- The Turán number for paths. -/
noncomputable def turanPath (n k : ℕ) : ℕ := extremalNumber n (pathGraph k)

/-- Turán number for P_k is (k-2)n/2 for n ≥ k-1 (Erdős–Gallai). -/
axiom turan_path_formula (n k : ℕ) (hn : n ≥ k - 1) (hk : k ≥ 2) :
    turanPath n k = (k - 2) * n / 2

/- ## Part X: Open Status -/

/-- The Erdős-Sós conjecture remains open.

    The conjecture is marked "falsifiable" - potentially disprovable
    by a finite counterexample, but none has been found.
-/
def erdos_548_open : Prop := ErdosSosConjecture ∨ ¬ErdosSosConjecture

theorem erdos_548_status : erdos_548_open :=
  Classical.em ErdosSosConjecture

/- ## Part XI: Toward eliminating `trivial_tree_bound` — min-degree extraction

The classical proof of the trivial bound has two halves:
1. **Extraction** (PROVED below): a graph with at least `(k−1)·n + 1` edges
   contains a nonempty vertex set `s` in which every vertex has at least `k`
   neighbours *inside `s`* — iteratively delete any vertex with fewer than
   `k` internal neighbours; each deletion destroys at most `k − 1` edges, so
   the edge surplus survives to a nonempty core.
2. **Greedy tree embedding** (remaining): a set of internal minimum degree
   `≥ k` contains every tree on `k + 1` vertices — embed the tree one leaf at
   a time; at most `k` vertices are used, so a fresh neighbour always exists.
   This needs a leaf-removal induction for trees (Mathlib:
   `IsTree.exists_vert_degree_one_of_nontrivial`,
   `Connected.induce_compl_singleton_of_degree_eq_one`) and is left for a
   future session.

The extraction half is stated over `edgesInside` (edges with both endpoints
in a `Finset`), mirroring the sound internal-degree formulation used for the
chromatic-degeneracy lemma of Erdős #751 — a global min-degree statement
would be false (isolated vertices survive in any same-vertex-type subgraph). -/

/-- The edges of `G` with both endpoints inside `t`. -/
noncomputable def edgesInside (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ t)

/-- On the full vertex set, `edgesInside` is the whole edge set. -/
theorem edgesInside_univ (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgesInside G Finset.univ = G.edgeFinset := by
  unfold edgesInside
  exact Finset.filter_true_of_mem (fun e _ x _ => Finset.mem_univ x)

/-- Removing a vertex `v` from `t` destroys at most `deg_t(v)` inside-edges:
every inside-edge either avoids `v` (and survives in `t.erase v`) or joins
`v` to one of its neighbours inside `t`. -/
theorem edgesInside_erase_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) (v : V) :
    (edgesInside G t).card ≤
      (edgesInside G (t.erase v)).card +
        (t.filter (fun u => G.Adj v u)).card := by
  have hsub : edgesInside G t ⊆
      edgesInside G (t.erase v) ∪
        (t.filter (fun u => G.Adj v u)).image (fun u => s(v, u)) := by
    intro e he
    unfold edgesInside at he
    rw [Finset.mem_filter] at he
    obtain ⟨heE, hin⟩ := he
    by_cases hv : v ∈ e
    · -- `e = s(v, u)` for the other endpoint `u`
      rw [Finset.mem_union]
      right
      have hother := Sym2.other_spec hv
      refine Finset.mem_image.mpr ⟨Sym2.Mem.other hv, ?_, hother⟩
      rw [Finset.mem_filter]
      constructor
      · exact hin _ (by rw [← hother]; exact Sym2.mem_mk_right _ _)
      · have hadj : s(v, Sym2.Mem.other hv) ∈ G.edgeSet := by
          rw [hother]
          exact SimpleGraph.mem_edgeFinset.mp heE
        exact hadj
    · rw [Finset.mem_union]
      left
      unfold edgesInside
      rw [Finset.mem_filter]
      refine ⟨heE, fun x hx => Finset.mem_erase.mpr ⟨?_, hin x hx⟩⟩
      rintro rfl
      exact hv hx
  calc (edgesInside G t).card
      ≤ (edgesInside G (t.erase v) ∪
          (t.filter (fun u => G.Adj v u)).image (fun u => s(v, u))).card :=
        Finset.card_le_card hsub
    _ ≤ (edgesInside G (t.erase v)).card
        + ((t.filter (fun u => G.Adj v u)).image (fun u => s(v, u))).card :=
        Finset.card_union_le _ _
    _ ≤ _ := by
        have himg := Finset.card_image_le
          (s := t.filter (fun u => G.Adj v u)) (f := fun u => s(v, u))
        omega

/-- **Min-degree extraction (strong-induction core).** Any vertex set `t`
carrying at least `(k−1)·|t| + 1` inside-edges contains a nonempty subset
`s ⊆ t` in which every vertex has at least `k` neighbours inside `s`. -/
theorem exists_min_degree_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) :
    ∀ t : Finset V, (k - 1) * t.card + 1 ≤ (edgesInside G t).card →
      ∃ s : Finset V, s.Nonempty ∧ s ⊆ t ∧
        ∀ v ∈ s, k ≤ (s.filter (fun u => G.Adj v u)).card := by
  intro t
  induction t using Finset.strongInduction with
  | _ t ih =>
    intro hE
    by_cases hall : ∀ v ∈ t, k ≤ (t.filter (fun u => G.Adj v u)).card
    · refine ⟨t, ?_, Finset.Subset.refl t, hall⟩
      rcases Finset.eq_empty_or_nonempty t with rfl | hne
      · exfalso
        have hempty : edgesInside G (∅ : Finset V) = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro e he
          unfold edgesInside at he
          rw [Finset.mem_filter] at he
          exact absurd (he.2 e.out.1 (Sym2.out_fst_mem e))
            (Finset.notMem_empty _)
        rw [hempty] at hE
        simp at hE
      · exact hne
    · simp only [not_forall, not_le] at hall
      obtain ⟨v, hvt, hdeg⟩ := hall
      have hcard : (t.erase v).card = t.card - 1 := Finset.card_erase_of_mem hvt
      have hpos : 1 ≤ t.card := Finset.card_pos.mpr ⟨v, hvt⟩
      have hbound := edgesInside_erase_bound G t v
      have hmul : (k - 1) * t.card = (k - 1) * (t.card - 1) + (k - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hpos]
        ring
      obtain ⟨s, hne, hsub, hdegs⟩ := ih (t.erase v) (Finset.erase_ssubset hvt)
        (by rw [hcard]; omega)
      exact ⟨s, hne, hsub.trans (Finset.erase_subset v t), hdegs⟩

/-- **Min-degree extraction from the edge count.** A graph on `V` with at
least `(k−1)·|V| + 1` edges contains a nonempty vertex set `s` in which every
vertex has at least `k` neighbours inside `s` — the extraction half of the
classical proof of `trivial_tree_bound` (the hypothesis matches its
`edgeCount G ≥ n·(k−1) + 1` up to commutativity). The remaining half is the
greedy embedding of an arbitrary `(k+1)`-vertex tree into such an `s`. -/
theorem exists_min_degree_subset_of_edgeCount (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ)
    (h : (k - 1) * Fintype.card V + 1 ≤ edgeCount G) :
    ∃ s : Finset V, s.Nonempty ∧
      ∀ v ∈ s, k ≤ (s.filter (fun u => G.Adj v u)).card := by
  obtain ⟨s, hne, _, hdeg⟩ := exists_min_degree_subset G k Finset.univ (by
    rw [edgesInside_univ]
    simpa [edgeCount, Finset.card_univ] using h)
  exact ⟨s, hne, hdeg⟩

end Erdos548

/-
## Summary

This file formalizes Erdős Problem #548, the Erdős-Sós Conjecture.

**The Conjecture**: Every graph with average degree > k-1 contains
every tree on k+1 vertices.

**Status**: OPEN (potentially falsifiable by counterexample)

**What We Formalize**:
1. Trees: definition, path graphs, star graphs
2. Subgraph containment via injective homomorphisms
3. Edge counting and average degree
4. The main conjecture statement
5. Partial results:
   - Trivial bound: n(k-1)+1 edges suffice
   - Brandt-Dobson: girth ≥ 5 case
   - Saclé-Wozniak: C₄-free case
   - Wang-Li-Liu: complement girth ≥ 5
   - Komlós-Sós: large k case (announced)
6. Extremal function and bounds
7. Related: Erdős-Gallai theorem

**Key Insight**: The conjecture says the Turán number for any tree T
on k+1 vertices is at most (k-1)n/2. This is tight for paths.

**Open Questions**:
- Is the conjecture true?
- What is the smallest counterexample if false?
- Can the Komlós-Sós approach be completed?
-/
