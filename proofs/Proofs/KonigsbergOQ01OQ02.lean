/-
  Königsberg OQ-01 OQ-02: Eulerian Paths in Directed Graphs

  Open Question from KonigsbergOQ01 (Eulerian paths in undirected graphs):
  "Extend the Eulerian circuit characterization to directed graphs."

  ## The Directed Eulerian Theorem

  For a connected directed graph G = (V, E):

  **Eulerian Circuit** (visits every edge exactly once, returns to start):
    G has an Eulerian circuit ↔ ∀ v : inDegree(v) = outDegree(v)

  **Eulerian Path** (visits every edge exactly once, start ≠ end):
    G has an Eulerian path from s to t (s ≠ t) ↔
      outDegree(s) = inDegree(s) + 1  (start: one extra outgoing edge)
      inDegree(t)  = outDegree(t) + 1 (end: one extra incoming edge)
      ∀ v ≠ s, t: inDegree(v) = outDegree(v)

  ## Status: Partially proved

  This file proves:
  1. Handshaking lemmas for directed graphs (∑ outDegree = |E| = ∑ inDegree)
  2. **NECESSITY**: Balance is necessary for any Eulerian circuit (proved from first principles)
  3. Concrete directed graphs satisfying the Eulerian criteria

  Axiomatized: Hierholzer sufficiency and Eulerian path characterization.

  References:
  - Euler (1741): Original Königsberg bridges proof
  - Hierholzer (1873): Constructive proof for undirected case
  - West (2001): Introduction to Graph Theory, §1.3
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Tactic

namespace KonigsbergOQ01OQ02

open BigOperators Finset

/-
══════════════════════════════════════════════════════════════
PART I: DIRECTED GRAPH BASICS
══════════════════════════════════════════════════════════════ -/

/-- A directed graph on vertex type V with edge set E ⊆ V × V. -/
structure DiGraph (V : Type*) where
  edges : Finset (V × V)
  noSelfLoops : ∀ e ∈ edges, e.1 ≠ e.2

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Out-degree: number of edges leaving vertex v. -/
def outDegree (G : DiGraph V) (v : V) : ℕ :=
  (G.edges.filter (fun e => e.1 = v)).card

/-- In-degree: number of edges entering vertex v. -/
def inDegree (G : DiGraph V) (v : V) : ℕ :=
  (G.edges.filter (fun e => e.2 = v)).card

/-- A vertex is Eulerian-balanced if inDegree = outDegree. -/
def IsBalanced (G : DiGraph V) (v : V) : Prop :=
  inDegree G v = outDegree G v

/-- A directed graph is Eulerian-balanced if all vertices are balanced. -/
def IsEulerianBalanced (G : DiGraph V) : Prop :=
  ∀ v : V, IsBalanced G v

/-
══════════════════════════════════════════════════════════════
PART II: HANDSHAKING LEMMA FOR DIRECTED GRAPHS
══════════════════════════════════════════════════════════════ -/

/-- **Directed Handshaking Lemma**: Sum of all out-degrees = |E|.
    Proof: ∑_v |{e : e.1=v}| = ∑_e ∑_v [e.1=v] (swap) = ∑_e 1 = |E|. -/
theorem sum_outDegree_eq_edgeCount (G : DiGraph V) :
    ∑ v : V, outDegree G v = G.edges.card := by
  unfold outDegree
  have step : ∀ v : V, (G.edges.filter fun e => e.1 = v).card =
      ∑ e ∈ G.edges, if e.1 = v then 1 else 0 := fun v => by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [step]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Finset.card_eq_sum_ones.symm

/-- Sum of all in-degrees = |E|. Same proof by symmetry on second endpoint. -/
theorem sum_inDegree_eq_edgeCount (G : DiGraph V) :
    ∑ v : V, inDegree G v = G.edges.card := by
  unfold inDegree
  have step : ∀ v : V, (G.edges.filter fun e => e.2 = v).card =
      ∑ e ∈ G.edges, if e.2 = v then 1 else 0 := fun v => by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [step]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Finset.card_eq_sum_ones.symm

/-- Sum of out-degrees = sum of in-degrees. -/
theorem sum_outDegree_eq_sum_inDegree (G : DiGraph V) :
    ∑ v : V, outDegree G v = ∑ v : V, inDegree G v := by
  rw [sum_outDegree_eq_edgeCount, sum_inDegree_eq_edgeCount]

/-
══════════════════════════════════════════════════════════════
PART III: NECESSITY — BALANCE IS REQUIRED
══════════════════════════════════════════════════════════════ -/

/-- An Eulerian circuit: a closed walk using every edge exactly once.
    The strong formulation requires unique coverage (∃!) and that every
    walk step uses a graph edge (hsteps). -/
def HasEulerianCircuit (G : DiGraph V) : Prop :=
  ∃ (walk : List V), walk.length = G.edges.card + 1 ∧
    (∀ e ∈ G.edges, ∃! i : ℕ, i < walk.length - 1 ∧
      walk.get ⟨i, by omega⟩ = e.1 ∧ walk.get ⟨i + 1, by omega⟩ = e.2) ∧
    walk.head? = walk.getLast? ∧
    (∀ i (hi : i < walk.length - 1),
      (walk.get ⟨i, by omega⟩, walk.get ⟨i + 1, by omega⟩) ∈ G.edges)

/-
  Helper: for a closed walk of length n+1, the source-count at v equals
  the target-count at v. The bijection i ↦ (i=0 ? n-1 : i-1) maps
  {i < n : walk[i] = v} onto {i < n : walk[i+1] = v}.
-/
private lemma closed_walk_balance (walk : List V) (n : ℕ)
    (hlen : walk.length = n + 1)
    (hclosed : walk.get ⟨0, by omega⟩ = walk.get ⟨n, by omega⟩)
    (v : V) :
    ((Finset.range n).filter fun i => walk.get ⟨i, by omega⟩ = v).card =
    ((Finset.range n).filter fun i => walk.get ⟨i + 1, by omega⟩ = v).card := by
  -- Bijection: source position i ↦ target position (i = 0 ? n-1 : i-1)
  apply Finset.card_bij (fun i _ => if i = 0 then n - 1 else i - 1)
  · -- Maps into target filter
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    obtain ⟨hi_lt, hi_v⟩ := hi
    refine ⟨by split_ifs <;> omega, ?_⟩
    split_ifs with h
    · -- i = 0: target position n-1, need walk[n] = v
      have heq : walk.get ⟨n - 1 + 1, by omega⟩ = walk.get ⟨n, by omega⟩ := by
        congr 1; omega
      rw [heq, ← hclosed, h] at hi_v ⊢; exact hi_v
    · -- i > 0: target position i-1, need walk[i] = v
      have heq : walk.get ⟨i - 1 + 1, by omega⟩ = walk.get ⟨i, by omega⟩ := by
        congr 1; omega
      rw [heq]; exact hi_v
  · -- Injective
    intro i hi j hj heq
    simp only [Finset.mem_filter, Finset.mem_range] at hi hj
    split_ifs at heq with h1 h2 <;> omega
  · -- Surjective: for target position j, preimage is (j = n-1 ? 0 : j+1)
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    obtain ⟨hj_lt, hj_v⟩ := hj
    refine ⟨if j = n - 1 then 0 else j + 1, ⟨by split_ifs <;> omega, ?_⟩, ?_⟩
    · split_ifs with h
      · -- j = n-1: preimage = 0, need walk[0] = v
        -- walk[j+1] = walk[n] = walk[0] (closed), and walk[j+1] = v
        rw [← hclosed]
        have heq : walk.get ⟨j + 1, by omega⟩ = walk.get ⟨n, by omega⟩ := by
          congr 1; omega
        rw [← heq]; exact hj_v
      · -- j < n-1: preimage = j+1, need walk[j+1] = v
        exact hj_v
    · -- bijection value at preimage = j
      split_ifs with h
      · simp [h]; omega
      · simp; omega

/-- Helper: the walk step map i ↦ (walk[i], walk[i+1]) is a bijection between
    {i < n : walk[i] = v} and {e ∈ G.edges : e.1 = v}. -/
private lemma walk_source_eq_outDegree (G : DiGraph V) (walk : List V) (n : ℕ) (v : V)
    (hlen : walk.length = n + 1)
    (hcov : ∀ e ∈ G.edges, ∃! i : ℕ, i < n ∧
      walk.get ⟨i, by omega⟩ = e.1 ∧ walk.get ⟨i + 1, by omega⟩ = e.2)
    (hsteps : ∀ i (hi : i < n), (walk.get ⟨i, by omega⟩, walk.get ⟨i + 1, by omega⟩) ∈ G.edges) :
    ((Finset.range n).filter fun i => walk.get ⟨i, by omega⟩ = v).card =
    outDegree G v := by
  unfold outDegree
  -- Bijection: position i ↦ edge (walk[i], walk[i+1])
  symm
  apply Finset.card_bij (fun e he =>
    -- For each edge e ∈ filter, extract its unique position
    Classical.choose ((hcov e (Finset.mem_filter.mp he).1).exists))
  · -- Maps into range-filter (walk[pos(e)] = v)
    intro e he
    have hmem := (Finset.mem_filter.mp he).1
    have hv := (Finset.mem_filter.mp he).2
    obtain ⟨pos, ⟨hlt, hsrc, _⟩, _⟩ := hcov e hmem
    have hchoo := Classical.choose_spec ((hcov e hmem).exists)
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact hchoo.1.1
    · rw [hchoo.1.2.1, hv]
  · -- Injective: pos(e1) = pos(e2) → e1 = e2
    intro e1 he1 e2 he2 heq
    have hmem1 := (Finset.mem_filter.mp he1).1
    have hmem2 := (Finset.mem_filter.mp he2).1
    have hspec1 := Classical.choose_spec ((hcov e1 hmem1).exists)
    have hspec2 := Classical.choose_spec ((hcov e2 hmem2).exists)
    -- heq : pos(e1) = pos(e2), so walk[pos(e1)] = e1.1 = e2.1 and walk[pos+1] = e1.2 = e2.2
    rw [← heq] at hspec2
    exact Prod.ext (hspec1.1.2.1.symm.trans hspec2.1.2.1)
                   (hspec1.1.2.2.symm.trans hspec2.1.2.2)
  · -- Surjective: for each position i with walk[i] = v, find edge e with pos(e) = i
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨hi_lt, hi_v⟩ := hi
    -- The edge at position i
    set e := (walk.get ⟨i, by omega⟩, walk.get ⟨i + 1, by omega⟩) with he_def
    have he_mem : e ∈ G.edges := hsteps i (by omega)
    have he_src : e.1 = v := hi_v
    refine ⟨e, Finset.mem_filter.mpr ⟨he_mem, he_src⟩, ?_⟩
    -- Need: Classical.choose (hcov e he_mem).exists = i
    -- Both i and (the chosen position) satisfy the ∃! condition for e
    have hspec := Classical.choose_spec ((hcov e he_mem).exists)
    -- The uniqueness: any witness = the chosen one
    -- i satisfies: i < n, walk[i] = e.1, walk[i+1] = e.2
    have hi_spec : i < n ∧ walk.get ⟨i, by omega⟩ = e.1 ∧ walk.get ⟨i + 1, by omega⟩ = e.2 :=
      ⟨by omega, rfl, rfl⟩
    -- Uniqueness: Classical.choose ... = i (by uniqueness of ∃!)
    exact (hcov e he_mem).unique hspec.1 hi_spec

/-- Same bijection for in-degree. -/
private lemma walk_target_eq_inDegree (G : DiGraph V) (walk : List V) (n : ℕ) (v : V)
    (hlen : walk.length = n + 1)
    (hcov : ∀ e ∈ G.edges, ∃! i : ℕ, i < n ∧
      walk.get ⟨i, by omega⟩ = e.1 ∧ walk.get ⟨i + 1, by omega⟩ = e.2)
    (hsteps : ∀ i (hi : i < n), (walk.get ⟨i, by omega⟩, walk.get ⟨i + 1, by omega⟩) ∈ G.edges) :
    ((Finset.range n).filter fun i => walk.get ⟨i + 1, by omega⟩ = v).card =
    inDegree G v := by
  unfold inDegree
  symm
  apply Finset.card_bij (fun e he =>
    Classical.choose ((hcov e (Finset.mem_filter.mp he).1).exists))
  · -- Maps into range-filter (walk[pos(e)+1] = v)
    intro e he
    have hmem := (Finset.mem_filter.mp he).1
    have hv := (Finset.mem_filter.mp he).2
    have hspec := Classical.choose_spec ((hcov e hmem).exists)
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hspec.1.1, by rw [hspec.1.2.2, hv]⟩
  · -- Injective (same argument as walk_source_eq_outDegree)
    intro e1 he1 e2 he2 heq
    have hmem1 := (Finset.mem_filter.mp he1).1
    have hmem2 := (Finset.mem_filter.mp he2).1
    have hspec1 := Classical.choose_spec ((hcov e1 hmem1).exists)
    have hspec2 := Classical.choose_spec ((hcov e2 hmem2).exists)
    rw [← heq] at hspec2
    exact Prod.ext (hspec1.1.2.1.symm.trans hspec2.1.2.1)
                   (hspec1.1.2.2.symm.trans hspec2.1.2.2)
  · -- Surjective: for position i with walk[i+1] = v, find edge e with pos(e) = i
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨hi_lt, hi_v⟩ := hi
    set e := (walk.get ⟨i, by omega⟩, walk.get ⟨i + 1, by omega⟩) with he_def
    have he_mem : e ∈ G.edges := hsteps i (by omega)
    have he_tgt : e.2 = v := hi_v
    refine ⟨e, Finset.mem_filter.mpr ⟨he_mem, he_tgt⟩, ?_⟩
    have hspec := Classical.choose_spec ((hcov e he_mem).exists)
    have hi_spec : i < n ∧ walk.get ⟨i, by omega⟩ = e.1 ∧ walk.get ⟨i + 1, by omega⟩ = e.2 :=
      ⟨by omega, rfl, rfl⟩
    exact (hcov e he_mem).unique hspec.1 hi_spec

/-- **Necessity**: Any graph with an Eulerian circuit has balanced degrees.
    Proof: For each vertex v, outDegree = |{i : walk[i] = v}| = |{i : walk[i+1] = v}| = inDegree.
    The first and last equalities use the bijection between edges and walk positions.
    The middle equality uses the closed walk: walk[0] = walk[n] implies the
    source-count and target-count at any vertex are equal. -/
theorem eulerian_circuit_implies_balanced (G : DiGraph V) :
    HasEulerianCircuit G → IsEulerianBalanced G := by
  intro ⟨walk, hlen, hcov, hclosed, hsteps⟩
  intro v
  unfold IsBalanced
  set n := G.edges.card with hn
  -- walk.length - 1 = n
  have hn_eq : walk.length - 1 = n := by omega
  -- Normalize hcov to use n instead of walk.length - 1
  have hcov' : ∀ e ∈ G.edges, ∃! i : ℕ, i < n ∧
      walk.get ⟨i, by omega⟩ = e.1 ∧ walk.get ⟨i + 1, by omega⟩ = e.2 := by
    intro e he
    have h := hcov e he
    rwa [hn_eq] at h
  -- Normalize hsteps to use n
  have hsteps' : ∀ i (hi : i < n), (walk.get ⟨i, by omega⟩, walk.get ⟨i + 1, by omega⟩) ∈ G.edges :=
    fun i hi => hsteps i (hn_eq ▸ hi)
  -- Closed walk: walk[0] = walk[n]
  have hclosed_eq : walk.get ⟨0, by omega⟩ = walk.get ⟨n, by omega⟩ := by
    have hne : walk ≠ [] := by intro h; simp [h] at hlen
    -- head? of cons is definitionally some (first element)
    have h1 : walk.head? = some (walk.get ⟨0, by omega⟩) := by
      cases walk with
      | nil => exact absurd rfl hne
      | cons a t => rfl
    -- getLast? via List.getLast?_eq_getLast and List.getLast_eq_get
    have h2 : walk.getLast? = some (walk.get ⟨n, by omega⟩) := by
      rw [List.getLast?_eq_getLast hne]
      congr 1
      simp only [List.getLast_eq_get, List.get_eq_getElem]
      congr 1
      omega
    rw [h1, h2] at hclosed
    exact Option.some.inj hclosed
  -- Chain of equalities: inDegree = target-count = source-count = outDegree
  have h1 := walk_source_eq_outDegree G walk n v hlen hcov' hsteps'
  have h2 := walk_target_eq_inDegree G walk n v hlen hcov' hsteps'
  have h3 := closed_walk_balance walk n hlen hclosed_eq v
  omega

/-
══════════════════════════════════════════════════════════════
PART IV: THE DIRECTED EULERIAN THEOREM (axiomatized)
══════════════════════════════════════════════════════════════ -/

/-- A directed graph is weakly connected if its underlying undirected graph is connected. -/
def IsWeaklyConnected (G : DiGraph V) : Prop :=
  ∀ u v : V, u ≠ v → ∃ (path : List V),
    path.head? = some u ∧ path.getLast? = some v ∧
    ∀ i < path.length - 1, (path.get ⟨i, by omega⟩, path.get ⟨i+1, by omega⟩) ∈ G.edges ∨
                            (path.get ⟨i+1, by omega⟩, path.get ⟨i, by omega⟩) ∈ G.edges

/-- **Directed Eulerian Theorem** (Hierholzer's algorithm, axiomatized):
    Sufficiency requires constructing an Eulerian walk, which is classical graph theory. -/
axiom directed_eulerian_iff (G : DiGraph V) (hconn : IsWeaklyConnected G) :
    HasEulerianCircuit G ↔ IsEulerianBalanced G

/-- A directed graph has an Eulerian PATH from s to t (s ≠ t). -/
def HasEulerianPath (G : DiGraph V) (s t : V) : Prop :=
  ∃ (walk : List V), walk.head? = some s ∧ walk.getLast? = some t ∧
    walk.length = G.edges.card + 1 ∧
    (∀ e ∈ G.edges, ∃ i < walk.length - 1,
      walk.get ⟨i, by omega⟩ = e.1 ∧ walk.get ⟨i + 1, by omega⟩ = e.2)

axiom directed_euler_path_iff (G : DiGraph V) (hconn : IsWeaklyConnected G) (s t : V) (hst : s ≠ t) :
    HasEulerianPath G s t ↔
    outDegree G s = inDegree G s + 1 ∧
    inDegree G t = outDegree G t + 1 ∧
    ∀ v : V, v ≠ s → v ≠ t → IsBalanced G v

/-
══════════════════════════════════════════════════════════════
PART V: CONCRETE EXAMPLES
══════════════════════════════════════════════════════════════ -/

/-- Example: The directed 3-cycle A→B→C→A has an Eulerian circuit
    (all vertices have in-degree = out-degree = 1). -/
def directedTriangle : DiGraph (Fin 3) where
  edges := {(0, 1), (1, 2), (2, 0)}
  noSelfLoops := by decide

theorem directedTriangle_balanced : IsEulerianBalanced directedTriangle := by
  intro v; fin_cases v <;> native_decide

/-- Example: The directed path A→B→C has an Eulerian path from A to C. -/
def directedPath : DiGraph (Fin 3) where
  edges := {(0, 1), (1, 2)}
  noSelfLoops := by decide

theorem directedPath_path_degrees :
    outDegree directedPath 0 = inDegree directedPath 0 + 1 ∧
    inDegree directedPath 2 = outDegree directedPath 2 + 1 ∧
    ∀ v : Fin 3, v ≠ 0 → v ≠ 2 → IsBalanced directedPath v := by
  refine ⟨by native_decide, by native_decide, ?_⟩
  intro v hv0 hv2
  fin_cases v
  · exact absurd rfl hv0
  · native_decide
  · exact absurd rfl hv2

/-
══════════════════════════════════════════════════════════════
PART VI: CONSEQUENCES
══════════════════════════════════════════════════════════════ -/

/-- If G has an Eulerian circuit, the sum of (outDegree - inDegree) over all vertices is 0. -/
theorem eulerian_balanced_sum_zero (G : DiGraph V) (h : HasEulerianCircuit G) :
    ∑ v : V, (outDegree G v : ℤ) = ∑ v : V, (inDegree G v : ℤ) := by
  have := sum_outDegree_eq_sum_inDegree G
  exact_mod_cast this

/-- If G has an Eulerian circuit, every vertex has equal in- and out-degree. -/
theorem eulerian_balanced_implies_degree_balance (G : DiGraph V) (hc : HasEulerianCircuit G) (v : V) :
    inDegree G v = outDegree G v :=
  eulerian_circuit_implies_balanced G hc v

end KonigsbergOQ01OQ02
