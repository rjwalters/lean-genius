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
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
    -- getLast? via List.getLast?_eq_getLast and List.getLast_eq_getElem
    have h2 : walk.getLast? = some (walk.get ⟨n, by omega⟩) := by
      rw [List.getLast?_eq_getLast hne]
      congr 1
      simp only [List.getLast_eq_getElem, List.get_eq_getElem]
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

/-
══════════════════════════════════════════════════════════════
PART VII: HIERHOLZER SUFFICIENCY — MATHEMATICAL INFRASTRUCTURE
══════════════════════════════════════════════════════════════

  This section develops the key mathematical lemmas for Hierholzer's theorem:
  1. Open-walk counting: for a walk u → w (u ≠ w), the target count of w
     equals the source count of w plus 1.
  2. Greedy trail: maxTrail E v follows outgoing edges until exhausted.
  3. maxTrail_closed: in a balanced graph, maxTrail G.edges v is a closed circuit.
  4. circuit_exists: every non-empty balanced digraph has a directed circuit.
  5. remove_circuit_balanced: removing a circuit's edges preserves balance.
  6. euler_path_implies_degree_balance: necessity direction for Eulerian paths.

  The full sufficiency proof (directed_eulerian_iff ← balanced) requires one
  additional ingredient: splicing component circuits together (Hierholzer step).
  That remains axiomatized pending a Lean formalization of the splicing argument.
══════════════════════════════════════════════════════════════ -/

section HierholzerInfrastructure

/-
  STEP 1: OPEN-WALK COUNTING LEMMAS

  For a walk v₀, v₁, …, vₙ from v₀ to vₙ (v₀ ≠ vₙ):
  • The last vertex vₙ has target-count = source-count + 1.
  • The first vertex v₀ has source-count = target-count + 1.
  These are the counting facts that make the balance-contradiction argument work.
-/

/-- For an OPEN walk (head ≠ last), the target-count of the last vertex
    exceeds its source-count by exactly 1.
    Proof: the bijection i ↦ i+1 maps (target positions of w) \ {n-1} onto
    (source positions of w), and position n-1 is an extra target position. -/
private lemma open_walk_last_target_excess (walk : List V) (n : ℕ) (hn : 1 ≤ n)
    (hlen : walk.length = n + 1)
    (w : V)
    (hw0 : walk.get ⟨0, by omega⟩ ≠ w)
    (hwn : walk.get ⟨n, by omega⟩ = w) :
    ((Finset.range n).filter fun i => walk.get ⟨i + 1, by omega⟩ = w).card =
    ((Finset.range n).filter fun i => walk.get ⟨i, by omega⟩ = w).card + 1 := by
  set T := (Finset.range n).filter (fun i => walk.get ⟨i + 1, by omega⟩ = w)
  set S := (Finset.range n).filter (fun i => walk.get ⟨i, by omega⟩ = w)
  -- n-1 is in T: walk[(n-1)+1] = walk[n] = w
  have hn1_in_T : n - 1 ∈ T := by
    simp only [T, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have : n - 1 + 1 = n := by omega
    conv_lhs => rw [this]
    exact hwn
  rw [show T.card = (T.erase (n - 1)).card + 1 from by
    rw [← Finset.card_insert_of_not_mem (Finset.not_mem_erase _ _)]
    simp [Finset.insert_erase hn1_in_T]]
  congr 1
  -- Bijection: (T \ {n-1}) → S via i ↦ i+1
  apply Finset.card_bij (fun i _ => i + 1)
  · intro i hi
    simp only [T, S, Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at hi ⊢
    obtain ⟨hi_ne, hi_lt, hi_w⟩ := hi
    refine ⟨by omega, ?_⟩
    convert hi_w using 2; omega
  · intro i1 _ i2 _ h; omega
  · intro j hj
    simp only [S, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hj_lt, hj_w⟩ := hj
    -- j ≥ 1 since walk[0] ≠ w but walk[j] = w
    have hj1 : 1 ≤ j := by
      by_contra h; push_neg at h
      have : j = 0 := by omega
      exact hw0 (this ▸ hj_w)
    refine ⟨j - 1, ?_, by omega⟩
    simp only [T, Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, by omega, ?_⟩
    convert hj_w using 2; omega

/-- The symmetric lemma: for an open walk, the source-count of the first vertex
    exceeds its target-count by 1. -/
private lemma open_walk_first_source_excess (walk : List V) (n : ℕ) (hn : 1 ≤ n)
    (hlen : walk.length = n + 1)
    (w : V)
    (hw0 : walk.get ⟨0, by omega⟩ = w)
    (hwn : walk.get ⟨n, by omega⟩ ≠ w) :
    ((Finset.range n).filter fun i => walk.get ⟨i, by omega⟩ = w).card =
    ((Finset.range n).filter fun i => walk.get ⟨i + 1, by omega⟩ = w).card + 1 := by
  set S := (Finset.range n).filter (fun i => walk.get ⟨i, by omega⟩ = w)
  set T := (Finset.range n).filter (fun i => walk.get ⟨i + 1, by omega⟩ = w)
  -- 0 is in S: walk[0] = w
  have h0_in_S : 0 ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hw0⟩
  rw [show S.card = (S.erase 0).card + 1 from by
    rw [← Finset.card_insert_of_not_mem (Finset.not_mem_erase _ _)]
    simp [Finset.insert_erase h0_in_S]]
  congr 1
  -- Bijection: (S \ {0}) → T via i ↦ i-1
  apply Finset.card_bij (fun i _ => i - 1)
  · intro i hi
    simp only [S, T, Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at hi ⊢
    obtain ⟨hi_ne, hi_lt, hi_w⟩ := hi
    have hi1 : 1 ≤ i := by omega
    refine ⟨by omega, ?_⟩
    convert hi_w using 2; omega
  · intro i1 hi1 i2 hi2 h
    simp only [S, Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at hi1 hi2
    omega
  · intro j hj
    simp only [T, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hj_lt, hj_w⟩ := hj
    -- j+1 < n since walk[n] ≠ w
    have hjn : j + 1 < n := by
      by_contra h; push_neg at h
      have : j + 1 = n := by omega
      exact hwn (this ▸ hj_w)
    refine ⟨j + 1, ?_, by omega⟩
    simp only [S, Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by omega, hj_w⟩

/-
  STEP 2: GREEDY MAXIMAL TRAIL

  maxTrail E v: follow outgoing edges in E until none remain.
  Terminates because E strictly shrinks at each step.
-/

/-- Build a maximal trail greedily from v using edges in E.
    At each step, follow any available outgoing edge (removing it from E).
    Terminates since |E| decreases by 1 at each step. -/
private noncomputable def maxTrail (E : Finset (V × V)) (v : V) : List V :=
  if h : (E.filter (fun e => e.1 = v)).Nonempty then
    let e := h.choose
    v :: maxTrail (E.erase e) e.2
  else [v]
termination_by E.card
decreasing_by exact Finset.card_erase_lt_of_mem (Finset.mem_filter.mp h.choose_spec).1

/-- Track which edges remain unused after running maxTrail E v. -/
private noncomputable def maxTrailRem (E : Finset (V × V)) (v : V) : Finset (V × V) :=
  if h : (E.filter (fun e => e.1 = v)).Nonempty then
    maxTrailRem (E.erase h.choose) h.choose.2
  else E
termination_by E.card
decreasing_by exact Finset.card_erase_lt_of_mem (Finset.mem_filter.mp h.choose_spec).1

private lemma maxTrail_nonempty' (E : Finset (V × V)) (v : V) : maxTrail E v ≠ [] := by
  unfold maxTrail; split_ifs <;> simp

private lemma maxTrail_head' (E : Finset (V × V)) (v : V) :
    (maxTrail E v).head? = some v := by
  unfold maxTrail; split_ifs <;> simp

/-- The remaining edge set is a subset of the original. -/
private lemma maxTrailRem_subset (E : Finset (V × V)) (v : V) :
    maxTrailRem E v ⊆ E := by
  induction h_n : E.card using Nat.strong_rec_on generalizing E v with
  | _ n ih =>
    unfold maxTrailRem
    by_cases hout : (E.filter (fun e => e.1 = v)).Nonempty
    · simp only [hout, ↓reduceDite]
      have he : hout.choose ∈ E := (Finset.mem_filter.mp hout.choose_spec).1
      have hcard : (E.erase hout.choose).card < n := h_n ▸ Finset.card_erase_lt_of_mem he
      exact (ih _ hcard _ _ rfl).trans (Finset.erase_subset _ _)
    · simp [hout]

/-- The last vertex of maxTrail has no outgoing edges in the remaining set.
    This is the key maximality condition. -/
private lemma maxTrailRem_last_no_out (E : Finset (V × V)) (v : V) :
    (maxTrailRem E v).filter (fun e =>
      e.1 = (maxTrail E v).getLast (maxTrail_nonempty' E v)) = ∅ := by
  induction h_n : E.card using Nat.strong_rec_on generalizing E v with
  | _ n ih =>
    unfold maxTrail maxTrailRem
    by_cases hout : (E.filter (fun e => e.1 = v)).Nonempty
    · simp only [hout, ↓reduceDite]
      have he : hout.choose ∈ E := (Finset.mem_filter.mp hout.choose_spec).1
      have hcard : (E.erase hout.choose).card < n := h_n ▸ Finset.card_erase_lt_of_mem he
      -- getLast (v :: rest) = getLast rest (when rest ≠ [])
      have hne : maxTrail (E.erase hout.choose) hout.choose.2 ≠ [] :=
        maxTrail_nonempty' _ _
      rw [List.getLast_cons hne]
      exact ih _ hcard _ _ rfl
    · simp only [hout, ↓reduceDite]
      simp only [List.getLast_singleton]
      simpa using hout

/-- Every edge from the last vertex in E appears as a trail step.
    Equivalently: maxTrailRem has no outgoing edges from the last vertex in E. -/
private lemma maxTrail_last_exhausted (E : Finset (V × V)) (v : V) :
    let last_v := (maxTrail E v).getLast (maxTrail_nonempty' E v)
    ∀ e ∈ E, e.1 = last_v →
      ∃ i, i + 1 < (maxTrail E v).length ∧
        (maxTrail E v).get ⟨i, by omega⟩ = e.1 ∧
        (maxTrail E v).get ⟨i + 1, by omega⟩ = e.2 := by
  induction h_n : E.card using Nat.strong_rec_on generalizing E v with
  | _ n ih =>
    intro last_v e he hlast
    by_cases hout : (E.filter (fun e' => e'.1 = v)).Nonempty
    · have he₀ : hout.choose ∈ E := (Finset.mem_filter.mp hout.choose_spec).1
      have hv : hout.choose.1 = v := (Finset.mem_filter.mp hout.choose_spec).2
      have hcard : (E.erase hout.choose).card < n :=
        h_n ▸ Finset.card_erase_lt_of_mem he₀
      set e₀ := hout.choose
      set inner := maxTrail (E.erase e₀) e₀.2
      have hinner_ne : inner ≠ [] := maxTrail_nonempty' _ _
      have hinner_len : 0 < inner.length := List.length_pos.mpr hinner_ne
      have htrail : maxTrail E v = v :: inner := by
        unfold maxTrail; simp only [hout, ↓reduceDite]
      have htrail_len : (maxTrail E v).length = inner.length + 1 := by
        rw [htrail]; simp
      have hlast_eq : last_v = inner.getLast hinner_ne := by
        simp only [last_v, htrail, List.getLast_cons hinner_ne]
      have hinner_g0 : inner.get ⟨0, hinner_len⟩ = e₀.2 := by
        cases h_i : inner with
        | nil => exact absurd h_i hinner_ne
        | cons a _ =>
          have := maxTrail_head' (E.erase e₀) e₀.2
          rw [h_i] at this; simp only [List.head?_cons, Option.some.injEq] at this
          simp [this]
      by_cases heq : e = e₀
      · subst heq
        refine ⟨0, by omega, ?_, ?_⟩
        · rw [htrail, List.get_cons_zero]; exact hv.symm
        · rw [htrail]; simp only [List.get_cons_succ]; exact hinner_g0
      · have he_erase : e ∈ E.erase e₀ := Finset.mem_erase.mpr ⟨heq, he⟩
        have hlast_inner : e.1 = inner.getLast hinner_ne := hlast.trans hlast_eq
        obtain ⟨k, hk, hke1, hke2⟩ := ih _ hcard (E.erase e₀) e₀.2 rfl he_erase hlast_inner
        refine ⟨k + 1, by omega, ?_, ?_⟩
        · rw [htrail]; simp only [List.get_cons_succ]; exact hke1
        · rw [htrail]; simp only [List.get_cons_succ]; exact hke2
    · exfalso
      have htrail_empty : maxTrail E v = [v] := by unfold maxTrail; simp [hout]
      have hlast_v : last_v = v := by simp [last_v, htrail_empty]
      exact hout ⟨e, Finset.mem_filter.mpr ⟨he, hlast.trans hlast_v⟩⟩

/-- All steps of maxTrail E v use edges from E. -/
private lemma maxTrail_steps_in_E (E : Finset (V × V)) (v : V) :
    ∀ i, i + 1 < (maxTrail E v).length →
      ((maxTrail E v).get ⟨i, by omega⟩, (maxTrail E v).get ⟨i + 1, by omega⟩) ∈ E := by
  induction h_n : E.card using Nat.strong_rec_on generalizing E v with
  | _ n ih =>
    intro i hi
    unfold maxTrail at hi ⊢
    by_cases hout : (E.filter (fun e => e.1 = v)).Nonempty
    · simp only [hout, ↓reduceDite] at hi ⊢
      simp only [List.length_cons] at hi
      have he₀ : hout.choose ∈ E := (Finset.mem_filter.mp hout.choose_spec).1
      have hv : hout.choose.1 = v := (Finset.mem_filter.mp hout.choose_spec).2
      have hcard : (E.erase hout.choose).card < n :=
        h_n ▸ Finset.card_erase_lt_of_mem he₀
      cases i with
      | zero =>
        simp only [List.get_cons_zero, List.get_cons_succ]
        -- Goal: (v, (maxTrail (E.erase e₀) e₀.2).get ⟨0, _⟩) ∈ E
        -- (maxTrail (E.erase e₀) e₀.2).get ⟨0, _⟩ = e₀.2 by head lemma
        have hne : maxTrail (E.erase hout.choose) hout.choose.2 ≠ [] :=
          maxTrail_nonempty' _ _
        have hhead := maxTrail_head' (E.erase hout.choose) hout.choose.2
        match h_trail : maxTrail (E.erase hout.choose) hout.choose.2 with
        | [] => exact absurd h_trail hne
        | a :: rest =>
          rw [h_trail] at hhead
          simp only [List.head?_cons, Option.some.injEq] at hhead
          rw [h_trail, List.get_cons_zero, hhead]
          exact hv ▸ he₀
      | succ j =>
        simp only [List.get_cons_succ]
        have hinner := ih _ hcard (E.erase hout.choose) hout.choose.2 rfl j (by omega)
        exact Finset.mem_of_mem_erase hinner
    · simp only [hout, ↓reduceDite, List.length_singleton] at hi; omega

/-- Helper: first element of maxTrail is v (via get). -/
private lemma maxTrail_get_zero (E : Finset (V × V)) (v : V)
    (h : 0 < (maxTrail E v).length) :
    (maxTrail E v).get ⟨0, h⟩ = v := by
  have hhead := maxTrail_head' E v
  cases h_trail : maxTrail E v with
  | nil => exact absurd h_trail (maxTrail_nonempty' E v)
  | cons a rest =>
    rw [h_trail] at hhead
    simp only [List.head?_cons, Option.some.injEq] at hhead
    simp [List.get_cons_zero, hhead]

/-- No edge is used twice in maxTrail (distinct edges). -/
private lemma maxTrail_steps_distinct (E : Finset (V × V)) (v : V) :
    ∀ i j, i + 1 < (maxTrail E v).length → j + 1 < (maxTrail E v).length → i ≠ j →
      ((maxTrail E v).get ⟨i, by omega⟩, (maxTrail E v).get ⟨i + 1, by omega⟩) ≠
      ((maxTrail E v).get ⟨j, by omega⟩, (maxTrail E v).get ⟨j + 1, by omega⟩) := by
  induction h_n : E.card using Nat.strong_rec_on generalizing E v with
  | _ n ih =>
    intro i j hi hj hij
    unfold maxTrail at hi hj ⊢
    by_cases hout : (E.filter (fun e => e.1 = v)).Nonempty
    · simp only [hout, ↓reduceDite] at hi hj ⊢
      simp only [List.length_cons] at hi hj
      have he₀ : hout.choose ∈ E := (Finset.mem_filter.mp hout.choose_spec).1
      have hv : hout.choose.1 = v := (Finset.mem_filter.mp hout.choose_spec).2
      have hcard : (E.erase hout.choose).card < n :=
        h_n ▸ Finset.card_erase_lt_of_mem he₀
      -- Useful: get[0] of inner trail = hout.choose.2
      have hinner_g0 : ∀ (h0 : 0 < (maxTrail (E.erase hout.choose) hout.choose.2).length),
          (maxTrail (E.erase hout.choose) hout.choose.2).get ⟨0, h0⟩ = hout.choose.2 := fun h0 =>
        maxTrail_get_zero (E.erase hout.choose) hout.choose.2 h0
      cases i with
      | zero =>
        cases j with
        | zero => exact absurd rfl hij
        | succ k =>
          -- Step at pos 0 = e₀; step at pos k+1 is inner step ∈ E.erase e₀ ≠ e₀
          simp only [List.get_cons_zero, List.get_cons_succ]
          have hinner_k : ((maxTrail (E.erase hout.choose) hout.choose.2).get ⟨k, by omega⟩,
              (maxTrail (E.erase hout.choose) hout.choose.2).get ⟨k + 1, by omega⟩) ∈
              E.erase hout.choose :=
            maxTrail_steps_in_E (E.erase hout.choose) hout.choose.2 k (by omega)
          -- Step at pos 0: (v, inner[0]) = (hout.choose.1, hout.choose.2) = hout.choose
          intro h_eq
          have hg0 : (maxTrail (E.erase hout.choose) hout.choose.2).get ⟨0, by omega⟩ =
              hout.choose.2 := hinner_g0 (by omega)
          rw [hg0, show (v, hout.choose.2) = hout.choose from Prod.ext hv.symm rfl] at h_eq
          exact Finset.not_mem_erase hout.choose E (h_eq ▸ hinner_k)
      | succ k_i =>
        cases j with
        | zero =>
          -- Symmetric: step at pos 0 = e₀; step at pos k_i+1 is inner step ∈ E.erase e₀ ≠ e₀
          simp only [List.get_cons_zero, List.get_cons_succ]
          have hinner_ki : ((maxTrail (E.erase hout.choose) hout.choose.2).get ⟨k_i, by omega⟩,
              (maxTrail (E.erase hout.choose) hout.choose.2).get ⟨k_i + 1, by omega⟩) ∈
              E.erase hout.choose :=
            maxTrail_steps_in_E (E.erase hout.choose) hout.choose.2 k_i (by omega)
          intro h_eq
          have hg0 : (maxTrail (E.erase hout.choose) hout.choose.2).get ⟨0, by omega⟩ =
              hout.choose.2 := hinner_g0 (by omega)
          rw [hg0, show (v, hout.choose.2) = hout.choose from Prod.ext hv.symm rfl] at h_eq
          exact Finset.not_mem_erase hout.choose E (h_eq.symm ▸ hinner_ki)
        | succ k_j =>
          -- Both from inner trail (k_i and k_j with k_i ≠ k_j): use induction
          simp only [List.get_cons_succ]
          exact ih _ hcard (E.erase hout.choose) hout.choose.2 rfl k_i k_j (by omega) (by omega)
            (by intro h; exact hij (congrArg Nat.succ h))
    · simp only [hout, ↓reduceDite, List.length_singleton] at hi; omega

/-
  STEP 3: MAXIMAL TRAIL IS CLOSED IN A BALANCED GRAPH

  The core of Hierholzer's theorem: in a balanced digraph, the greedy maximal
  trail from any vertex v must return to v.

  Proof by balance contradiction:
  - Suppose the trail ends at last_v ≠ v.
  - All outgoing edges of last_v in G were used in the trail (maximality).
  - So source_count(last_v) = outDegree G last_v.
  - By the open-walk counting lemma: target_count(last_v) = source_count(last_v) + 1.
  - But target_count(last_v) ≤ inDegree G last_v = outDegree G last_v (balance).
  - Contradiction: outDegree G last_v + 1 ≤ outDegree G last_v.
-/

/-- In a balanced digraph G, the maximal greedy trail from any vertex v is closed. -/
theorem maxTrail_closed (G : DiGraph V) (hbal : IsEulerianBalanced G) (v : V) :
    (maxTrail G.edges v).head? = (maxTrail G.edges v).getLast? := by
  by_contra h_open
  set trail := maxTrail G.edges v
  have htrail_ne : trail ≠ [] := maxTrail_nonempty' _ _
  have htrail_head : trail.head? = some v := maxTrail_head' G.edges v
  set last_v := trail.getLast htrail_ne
  have hlast_some : trail.getLast? = some last_v := List.getLast?_eq_getLast htrail_ne
  rw [htrail_head, hlast_some] at h_open
  have hvw : v ≠ last_v := fun h => h_open (congrArg some h)
  -- Trail has length ≥ 2
  have hlen_ge2 : 2 ≤ trail.length := by
    by_contra hlt; push_neg at hlt
    have hlen1 : trail.length = 1 := by have := List.length_pos.mpr htrail_ne; omega
    obtain ⟨a, ha⟩ := List.length_eq_one.mp hlen1
    have ha_eq : a = v := by rw [ha] at htrail_head; simp at htrail_head; exact htrail_head.symm
    have : last_v = v := by simp only [last_v, ha, ha_eq, List.getLast_singleton]
    exact hvw this.symm
  set m := trail.length - 1
  have hm_pos : 0 < m := by omega
  have htrail_len : trail.length = m + 1 := by omega
  have hget0 : trail.get ⟨0, by omega⟩ = v := by
    cases trail with
    | nil => exact absurd rfl htrail_ne
    | cons a _ =>
      simp only [List.head?_cons, Option.some.injEq] at htrail_head
      simp [htrail_head]
  have hgetm : trail.get ⟨m, by omega⟩ = last_v := by
    simp only [last_v]
    have h : trail.getLast? = some (trail.get ⟨m, by omega⟩) := by
      rw [List.getLast?_eq_getLast htrail_ne]; congr 1
      simp only [List.getLast_eq_getElem, List.get_eq_getElem]; congr 1; omega
    rw [hlast_some] at h; exact (Option.some.inj h).symm
  set src_filter := (Finset.range m).filter (fun i => trail.get ⟨i, by omega⟩ = last_v)
  set tgt_filter := (Finset.range m).filter (fun i => trail.get ⟨i + 1, by omega⟩ = last_v)
  -- tgt_count = src_count + 1 (open walk counting lemma)
  have h_tgt_excess : tgt_filter.card = src_filter.card + 1 :=
    open_walk_last_target_excess trail m hm_pos htrail_len last_v (hget0 ▸ hvw) hgetm
  -- src_count = outDegree G last_v (bijection via maxTrail_last_exhausted + maxTrail_steps_distinct)
  have hsrc_eq : src_filter.card = outDegree G last_v := by
    unfold outDegree
    apply Finset.card_bij (fun i hi =>
      let hi' := (Finset.mem_filter.mp hi)
      (trail.get ⟨i, by simp only [Finset.mem_range] at hi'; omega⟩,
       trail.get ⟨i + 1, by simp only [Finset.mem_filter, Finset.mem_range] at hi; omega⟩))
    · intro i hi
      simp only [src_filter, Finset.mem_filter, Finset.mem_range] at hi
      simp only [Finset.mem_filter]
      exact ⟨maxTrail_steps_in_E G.edges v i (by omega), hi.2⟩
    · intro i hi j hj heq
      simp only [src_filter, Finset.mem_filter, Finset.mem_range] at hi hj
      by_contra hij
      exact maxTrail_steps_distinct G.edges v i j (by omega) (by omega) hij heq
    · intro e he
      simp only [Finset.mem_filter] at he
      obtain ⟨k, hk, hke1, hke2⟩ := maxTrail_last_exhausted G.edges v e he.1 he.2
      exact ⟨k, by simp [src_filter, Finset.mem_filter, Finset.mem_range, hke1]; omega,
             Prod.ext hke1 hke2⟩
  -- tgt_count ≤ inDegree G last_v (injection via maxTrail_steps_in_E + maxTrail_steps_distinct)
  have htgt_le : tgt_filter.card ≤ inDegree G last_v := by
    unfold inDegree
    apply Finset.card_le_card_of_injOn
      (fun i => (trail.get ⟨i, by
          simp only [tgt_filter, Finset.mem_filter, Finset.mem_range]
          intro h; exact ⟨h.1, h.2⟩⟩,
        trail.get ⟨i + 1, by
          simp only [tgt_filter, Finset.mem_filter, Finset.mem_range]
          intro h; exact ⟨h.1, h.2⟩⟩))
    · intro i hi
      simp only [tgt_filter, Finset.mem_filter, Finset.mem_range] at hi
      simp only [Finset.mem_filter]
      exact ⟨maxTrail_steps_in_E G.edges v i (by omega), hi.2⟩
    · intro i hi j hj heq
      simp only [Set.mem_coe, tgt_filter, Finset.mem_filter, Finset.mem_range] at hi hj
      by_contra hij
      exact maxTrail_steps_distinct G.edges v i j (by omega) (by omega) hij heq
  have hbal_lv : outDegree G last_v = inDegree G last_v := hbal last_v
  omega

/-
  STEP 4: CIRCUIT EXISTENCE

  Every non-empty balanced digraph contains a directed circuit.
  Proof: Run maxTrail from any vertex with outgoing edges; by maxTrail_closed
  the trail is a closed walk, and it uses at least one edge (non-trivial circuit).
-/

/-- A directed circuit: a closed trail of length ≥ 2 (at least one edge). -/
structure DirectedCircuit (G : DiGraph V) where
  walk : List V
  head_eq_last : walk.head? = walk.getLast?
  length_ge_2  : 2 ≤ walk.length
  steps_in_G   : ∀ i (h : i + 1 < walk.length),
    (walk.get ⟨i, by omega⟩, walk.get ⟨i + 1, h⟩) ∈ G.edges

/-- Every non-empty balanced digraph has a directed circuit. -/
theorem circuit_exists (G : DiGraph V) (hbal : IsEulerianBalanced G)
    (hne : G.edges.Nonempty) : Nonempty (DirectedCircuit G) := by
  obtain ⟨e₀, he₀⟩ := hne
  set v := e₀.1
  have hout : (G.edges.filter (fun e => e.1 = v)).Nonempty :=
    ⟨e₀, Finset.mem_filter.mpr ⟨he₀, rfl⟩⟩
  have hinner_ne : maxTrail (G.edges.erase hout.choose) hout.choose.2 ≠ [] :=
    maxTrail_nonempty' _ _
  have hlen_ge2 : 2 ≤ (maxTrail G.edges v).length := by
    unfold maxTrail
    simp only [hout, ↓reduceDite, List.length_cons]
    exact Nat.succ_le_succ (List.length_pos.mpr hinner_ne)
  exact ⟨{
    walk := maxTrail G.edges v,
    head_eq_last := maxTrail_closed G hbal v,
    length_ge_2 := hlen_ge2,
    steps_in_G := fun i h => maxTrail_steps_in_E G.edges v i h
  }⟩

/-
  STEP 5: REMOVING A CIRCUIT PRESERVES BALANCE

  If C is a directed circuit in G, then G' = G minus the edges of C is balanced.
  Proof: For each vertex v, removing the edges of C decreases both inDegree and
  outDegree by the same amount (the number of times C passes through v).
-/

/-- Extract the edge multiset of a walk. -/
private def walkEdges (walk : List V) : List (V × V) :=
  (List.range (walk.length - 1)).filterMap (fun i =>
    if h : i + 1 < walk.length then
      some (walk.get ⟨i, by omega⟩, walk.get ⟨i + 1, by omega⟩)
    else none)

/-- The subgraph obtained by removing a specific set of edges. -/
private def DiGraph.removeEdgeSet (G : DiGraph V) (S : Finset (V × V)) : DiGraph V where
  edges := G.edges \ S
  noSelfLoops := fun e he => G.noSelfLoops e (Finset.sdiff_subset he)

/-- Removing the edges of a circuit from a balanced graph gives a balanced graph.
    Key: a circuit uses each vertex the same number of times as a source and as a target,
    so inDegree and outDegree both decrease by the same amount. -/
theorem remove_circuit_balanced (G : DiGraph V) (hbal : IsEulerianBalanced G)
    (C : DirectedCircuit G)
    (hdist : ∀ i j, i + 1 < C.walk.length → j + 1 < C.walk.length → i ≠ j →
      (C.walk.get ⟨i, by omega⟩, C.walk.get ⟨i + 1, by omega⟩) ≠
      (C.walk.get ⟨j, by omega⟩, C.walk.get ⟨j + 1, by omega⟩)) :
    IsEulerianBalanced (G.removeEdgeSet (walkEdges C.walk).toFinset) := by
  intro v
  unfold IsBalanced inDegree outDegree
  set walk := C.walk with hwalk_def
  set n := walk.length - 1 with hn_def
  set S := (walkEdges walk).toFinset with hS_def
  have hlen : walk.length = n + 1 := by have := C.length_ge_2; omega
  -- Reduce to goal about G.edges \ S
  show ((G.edges \ S).filter fun e => e.2 = v).card =
       ((G.edges \ S).filter fun e => e.1 = v).card
  -- S ⊆ G.edges (circuit edges are graph edges)
  have hS_sub : S ⊆ G.edges := by
    intro e he
    rw [hS_def, List.mem_toFinset] at he
    simp only [walkEdges, List.mem_filterMap, List.mem_range] at he
    obtain ⟨i, hi, h⟩ := he
    have hlt : i + 1 < walk.length := by omega
    simp only [hlt, ↓reduceDite, Option.some.injEq] at h
    rw [← h]; exact C.steps_in_G i hlt
  -- Closed walk: walk[0] = walk[n]
  have hclosed : walk.get ⟨0, by omega⟩ = walk.get ⟨n, by omega⟩ := by
    have hne : walk ≠ [] := by intro h; simp [h] at hlen
    have h1 : walk.head? = some (walk.get ⟨0, by omega⟩) := by
      cases walk with | nil => contradiction | cons a t => rfl
    have h2 : walk.getLast? = some (walk.get ⟨n, by omega⟩) := by
      rw [List.getLast?_eq_getLast hne]; congr 1
      simp only [List.getLast_eq_getElem, List.get_eq_getElem]; congr 1; omega
    rw [h1, h2] at C.head_eq_last; exact Option.some.inj C.head_eq_last
  -- (A \ B).filter p = A.filter p \ B.filter p
  have hfilt_in : (G.edges \ S).filter (fun e => e.2 = v) =
                  G.edges.filter (fun e => e.2 = v) \ S.filter (fun e => e.2 = v) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hx, hxS⟩, hpx⟩; exact ⟨⟨hx, hpx⟩, fun ⟨h1, _⟩ => hxS h1⟩
    · rintro ⟨⟨hx, hpx⟩, hxSp⟩; exact ⟨⟨hx, fun hxS => hxSp ⟨hxS, hpx⟩⟩, hpx⟩
  have hfilt_out : (G.edges \ S).filter (fun e => e.1 = v) =
                   G.edges.filter (fun e => e.1 = v) \ S.filter (fun e => e.1 = v) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hx, hxS⟩, hpx⟩; exact ⟨⟨hx, hpx⟩, fun ⟨h1, _⟩ => hxS h1⟩
    · rintro ⟨⟨hx, hpx⟩, hxSp⟩; exact ⟨⟨hx, fun hxS => hxSp ⟨hxS, hpx⟩⟩, hpx⟩
  rw [hfilt_in, hfilt_out]
  -- Subset conditions for card_sdiff
  have hSin_sub : S.filter (fun e => e.2 = v) ⊆ G.edges.filter (fun e => e.2 = v) :=
    Finset.filter_subset_filter _ hS_sub
  have hSout_sub : S.filter (fun e => e.1 = v) ⊆ G.edges.filter (fun e => e.1 = v) :=
    Finset.filter_subset_filter _ hS_sub
  rw [Finset.card_sdiff hSin_sub, Finset.card_sdiff hSout_sub]
  -- Cardinality bounds for omega
  have hSin_le : (S.filter fun e => e.2 = v).card ≤ (G.edges.filter fun e => e.2 = v).card :=
    Finset.card_le_card hSin_sub
  have hSout_le : (S.filter fun e => e.1 = v).card ≤ (G.edges.filter fun e => e.1 = v).card :=
    Finset.card_le_card hSout_sub
  -- G is balanced at v
  have hbalv : (G.edges.filter fun e => e.2 = v).card = (G.edges.filter fun e => e.1 = v).card :=
    hbal v
  -- Membership in S: e ∈ S ↔ ∃ i < n, e = (walk[i], walk[i+1])
  have hmem_S : ∀ e : V × V, e ∈ S ↔ ∃ i, i + 1 < walk.length ∧
      e = (walk.get ⟨i, by omega⟩, walk.get ⟨i + 1, by omega⟩) := fun e => by
    constructor
    · intro he
      rw [hS_def, List.mem_toFinset] at he
      simp only [walkEdges, List.mem_filterMap, List.mem_range] at he
      obtain ⟨i, hi, h⟩ := he
      have hlt : i + 1 < walk.length := by omega
      simp only [hlt, ↓reduceDite, Option.some.injEq] at h
      exact ⟨i, hlt, h.symm⟩
    · rintro ⟨i, hlt, rfl⟩
      rw [hS_def, List.mem_toFinset]
      simp only [walkEdges, List.mem_filterMap, List.mem_range]
      exact ⟨i, by omega, by simp only [hlt, ↓reduceDite]⟩
  -- Position bijection: {i<n : walk[i]=v} ≅ S.filter(·.1=v)
  have hsrc : ((Finset.range n).filter (fun i => walk.get ⟨i, by omega⟩ = v)).card =
              (S.filter (fun e => e.1 = v)).card :=
    Finset.card_bij
      (fun i hi =>
        (walk.get ⟨i, by have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1; omega⟩,
         walk.get ⟨i + 1, by have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1; omega⟩))
      (fun i hi => Finset.mem_filter.mpr
        ⟨(hmem_S _).mpr ⟨i,
           by have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1; omega, rfl⟩,
         (Finset.mem_filter.mp hi).2⟩)
      (fun i hi j hj heq => by
        by_contra hne
        exact absurd heq (hdist i j
          (by have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1; omega)
          (by have := Finset.mem_range.mp (Finset.mem_filter.mp hj).1; omega) hne))
      (fun e he => by
        simp only [Finset.mem_filter] at he
        obtain ⟨i, hlt, rfl⟩ := (hmem_S e).mp he.1
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), he.2⟩, rfl⟩)
  -- Position bijection: {i<n : walk[i+1]=v} ≅ S.filter(·.2=v)
  have htgt : ((Finset.range n).filter (fun i => walk.get ⟨i + 1, by omega⟩ = v)).card =
              (S.filter (fun e => e.2 = v)).card :=
    Finset.card_bij
      (fun i hi =>
        (walk.get ⟨i, by have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1; omega⟩,
         walk.get ⟨i + 1, by have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1; omega⟩))
      (fun i hi => Finset.mem_filter.mpr
        ⟨(hmem_S _).mpr ⟨i,
           by have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1; omega, rfl⟩,
         (Finset.mem_filter.mp hi).2⟩)
      (fun i hi j hj heq => by
        by_contra hne
        exact absurd heq (hdist i j
          (by have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1; omega)
          (by have := Finset.mem_range.mp (Finset.mem_filter.mp hj).1; omega) hne))
      (fun e he => by
        simp only [Finset.mem_filter] at he
        obtain ⟨i, hlt, rfl⟩ := (hmem_S e).mp he.1
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), he.2⟩, rfl⟩)
  -- Circuit balance: source count = target count at v (closed_walk_balance)
  have hS_bal : (S.filter fun e => e.1 = v).card = (S.filter fun e => e.2 = v).card := by
    have hpos := closed_walk_balance walk n hlen hclosed v
    omega
  omega

/-
  STEP 6: NECESSITY DIRECTION FOR EULERIAN PATHS

  If G has an Eulerian path from s to t (s ≠ t), then:
    outDegree s = inDegree s + 1
    inDegree t  = outDegree t + 1
    All other vertices are balanced.
  Proof: Same bijection argument as eulerian_circuit_implies_balanced, but for open walks.
-/

/-- **Necessity for Eulerian paths**: a graph with an Eulerian path from s to t
    satisfies the asymmetric degree conditions. -/
theorem euler_path_implies_degree_balance (G : DiGraph V) (s t : V) (hst : s ≠ t)
    (hpath : HasEulerianPath G s t) :
    outDegree G s = inDegree G s + 1 ∧
    inDegree G t = outDegree G t + 1 ∧
    ∀ v : V, v ≠ s → v ≠ t → IsBalanced G v := by
  obtain ⟨walk, hhead, hlast, hwlen, hcov⟩ := hpath
  set n := G.edges.card with hn_def
  have hlen : walk.length = n + 1 := hwlen
  have hn_ge_1 : 1 ≤ n := by
    -- If n = 0, walk has length 1, so head = last, meaning s = t — contradiction.
    by_contra h; push_neg at h
    have hn0 : n = 0 := by omega
    have hlen1 : walk.length = 1 := by omega
    have hhead_last : walk.head? = walk.getLast? := by
      cases walk with
      | nil => simp at hlen1
      | cons a t =>
        cases t with
        | nil => simp
        | cons b l => simp [List.length_cons] at hlen1
    rw [hhead, hlast] at hhead_last
    exact hst (Option.some.inj hhead_last)
  have hget_head : walk.get ⟨0, by omega⟩ = s := by
    cases walk with
    | nil => simp [List.length_nil] at hlen
    | cons a v => simp at hhead; exact hhead
  have hget_last : walk.get ⟨n, by omega⟩ = t := by
    have hne : walk ≠ [] := by intro h; simp [h] at hlen
    have h2 : walk.getLast? = some (walk.get ⟨n, by omega⟩) := by
      rw [List.getLast?_eq_getLast hne]
      congr 1
      simp only [List.getLast_eq_getElem, List.get_eq_getElem]
      congr 1; omega
    rw [h2] at hlast; exact Option.some.inj hlast
  -- S = image of range n under the step function f
  let f : ℕ → V × V := fun i =>
    if h : i < n then (walk.get ⟨i, by omega⟩, walk.get ⟨i + 1, by omega⟩) else default
  set S := (Finset.range n).image f with hS_def
  -- Lift hcov to use n instead of walk.length - 1
  have hcov_n : ∀ e ∈ G.edges, ∃ i, i < n ∧
      walk.get ⟨i, by omega⟩ = e.1 ∧ walk.get ⟨i + 1, by omega⟩ = e.2 := by
    intro e he
    obtain ⟨i, hi, h1, h2⟩ := hcov e he
    exact ⟨i, by omega, h1, h2⟩
  -- G.edges ⊆ S (from coverage)
  have hGS : G.edges ⊆ S := by
    intro e he
    obtain ⟨i, hi, h1, h2⟩ := hcov_n e he
    refine Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, ?_⟩
    simp only [f, hi, ↓reduceDite]; exact Prod.ext h1 h2
  -- S.card ≤ n (image of set of size n)
  have hSn : S.card ≤ n :=
    Finset.card_image_le.trans (Finset.card_range n).le
  -- G.edges = S
  have hGS_eq : G.edges = S :=
    Finset.eq_of_subset_of_card_le hGS (by omega)
  -- S.card = n
  have hScard : S.card = n := by rw [← hGS_eq]; omega
  -- f is injective on range n (pigeonhole: surjective map of equal-size sets)
  have hinj : Set.InjOn f ↑(Finset.range n) := by
    apply Finset.card_image_iff_injOn.mp
    rw [← hS_def, hScard, Finset.card_range]
  -- hsteps: every step (walk[i], walk[i+1]) is in G.edges
  have hsteps : ∀ i (hi : i < n),
      (walk.get ⟨i, by omega⟩, walk.get ⟨i + 1, by omega⟩) ∈ G.edges := by
    intro i hi
    rw [hGS_eq]
    refine Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, ?_⟩
    simp [f, hi]
  -- Injectivity of the step function
  have hstep_inj : ∀ i j, i < n → j < n →
      (walk.get ⟨i, by omega⟩, walk.get ⟨i + 1, by omega⟩) =
      (walk.get ⟨j, by omega⟩, walk.get ⟨j + 1, by omega⟩) → i = j := by
    intro i j hi hj heq
    have hfi : f i = (walk.get ⟨i, by omega⟩, walk.get ⟨i + 1, by omega⟩) := by
      simp [f, hi]
    have hfj : f j = (walk.get ⟨j, by omega⟩, walk.get ⟨j + 1, by omega⟩) := by
      simp [f, hj]
    exact hinj (Finset.mem_coe.mpr (Finset.mem_range.mpr hi))
               (Finset.mem_coe.mpr (Finset.mem_range.mpr hj))
               (hfi.trans (heq.trans hfj.symm))
  -- Derive unique coverage (∃!) from ordinary coverage + injectivity
  have hcov' : ∀ e ∈ G.edges, ∃! i : ℕ, i < n ∧
      walk.get ⟨i, by omega⟩ = e.1 ∧ walk.get ⟨i + 1, by omega⟩ = e.2 := by
    intro e he
    obtain ⟨i, hi, h1, h2⟩ := hcov_n e he
    refine ⟨i, ⟨hi, h1, h2⟩, ?_⟩
    intro j ⟨hj, hj1, hj2⟩
    exact (hstep_inj i j hi hj (Prod.ext (h1.trans hj1.symm) (h2.trans hj2.symm))).symm
  -- Express degrees as position-filter cardinalities
  have h_out_s :
      ((Finset.range n).filter fun i => walk.get ⟨i, by omega⟩ = s).card = outDegree G s :=
    walk_source_eq_outDegree G walk n s hlen hcov' hsteps
  have h_in_s :
      ((Finset.range n).filter fun i => walk.get ⟨i + 1, by omega⟩ = s).card = inDegree G s :=
    walk_target_eq_inDegree G walk n s hlen hcov' hsteps
  have h_out_t :
      ((Finset.range n).filter fun i => walk.get ⟨i, by omega⟩ = t).card = outDegree G t :=
    walk_source_eq_outDegree G walk n t hlen hcov' hsteps
  have h_in_t :
      ((Finset.range n).filter fun i => walk.get ⟨i + 1, by omega⟩ = t).card = inDegree G t :=
    walk_target_eq_inDegree G walk n t hlen hcov' hsteps
  -- Open-walk excess counting at endpoints
  have h_s_excess :
      ((Finset.range n).filter fun i => walk.get ⟨i, by omega⟩ = s).card =
      ((Finset.range n).filter fun i => walk.get ⟨i + 1, by omega⟩ = s).card + 1 :=
    open_walk_first_source_excess walk n hn_ge_1 hlen s hget_head
      (ne_of_eq_of_ne hget_last hst.symm)
  have h_t_excess :
      ((Finset.range n).filter fun i => walk.get ⟨i + 1, by omega⟩ = t).card =
      ((Finset.range n).filter fun i => walk.get ⟨i, by omega⟩ = t).card + 1 :=
    open_walk_last_target_excess walk n hn_ge_1 hlen t
      (ne_of_eq_of_ne hget_head hst) hget_last
  -- Parts 1 and 2 follow by arithmetic
  refine ⟨by omega, by omega, ?_⟩
  -- Part 3: interior vertices are balanced
  intro v hvs hvt
  unfold IsBalanced
  have h_out_v :
      ((Finset.range n).filter fun i => walk.get ⟨i, by omega⟩ = v).card = outDegree G v :=
    walk_source_eq_outDegree G walk n v hlen hcov' hsteps
  have h_in_v :
      ((Finset.range n).filter fun i => walk.get ⟨i + 1, by omega⟩ = v).card = inDegree G v :=
    walk_target_eq_inDegree G walk n v hlen hcov' hsteps
  -- Source count = target count at interior vertex (bijection i ↦ i-1)
  have h_v_bal :
      ((Finset.range n).filter fun i => walk.get ⟨i, by omega⟩ = v).card =
      ((Finset.range n).filter fun i => walk.get ⟨i + 1, by omega⟩ = v).card := by
    set src_v := (Finset.range n).filter (fun i => walk.get ⟨i, by omega⟩ = v)
    set tgt_v := (Finset.range n).filter (fun i => walk.get ⟨i + 1, by omega⟩ = v)
    apply Finset.card_bij (fun i _ => i - 1)
    · intro i hi
      simp only [src_v, Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨hi_lt, hi_v⟩ := hi
      -- walk[0] = s ≠ v, so i ≥ 1
      have hi1 : 1 ≤ i := by
        by_contra h; push_neg at h
        have hi0 : i = 0 := by omega
        rw [hi0] at hi_v
        exact hvs (hget_head.symm.trans hi_v).symm
      simp only [tgt_v, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      have heq : i - 1 + 1 = i := by omega
      rw [heq]; exact hi_v
    · intro i _ j _ h; omega
    · intro j hj
      simp only [tgt_v, Finset.mem_filter, Finset.mem_range] at hj
      obtain ⟨hj_lt, hj_v⟩ := hj
      -- walk[n] = t ≠ v, so j+1 < n
      have hjn : j + 1 < n := by
        by_contra h; push_neg at h
        have hjn1 : j + 1 = n := by omega
        have hwalkeq : walk.get ⟨j + 1, by omega⟩ = walk.get ⟨n, by omega⟩ :=
          congr_arg walk.get (Fin.ext hjn1)
        exact hvt (hj_v.symm.trans (hwalkeq.trans hget_last))
      refine ⟨j + 1, ?_, by omega⟩
      simp only [src_v, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hj_v⟩
  omega

end HierholzerInfrastructure

end KonigsbergOQ01OQ02
