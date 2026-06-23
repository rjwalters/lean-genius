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

/-- A directed graph has an Eulerian PATH from s to t (s ≠ t).
    Mirrors `HasEulerianCircuit`: each edge is covered by a unique walk position
    (∃!), and every consecutive pair in the walk is a graph edge. The strong
    formulation enables the necessity proof via the walk-position bijection. -/
def HasEulerianPath (G : DiGraph V) (s t : V) : Prop :=
  ∃ (walk : List V), walk.head? = some s ∧ walk.getLast? = some t ∧
    walk.length = G.edges.card + 1 ∧
    (∀ e ∈ G.edges, ∃! i : ℕ, i < walk.length - 1 ∧
      walk.get ⟨i, by omega⟩ = e.1 ∧ walk.get ⟨i + 1, by omega⟩ = e.2) ∧
    (∀ i (hi : i < walk.length - 1),
      (walk.get ⟨i, by omega⟩, walk.get ⟨i + 1, by omega⟩) ∈ G.edges)

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

/-- For an OPEN walk where neither endpoint equals an interior vertex `v`,
    the source-count of `v` equals its target-count.
    Proof: bijection `i ↦ i - 1` maps source positions to target positions.
    The endpoint hypotheses ensure `i = 0` is not a source position and
    `j = n - 1` is not the largest target position, keeping the bijection
    well-defined on `[0, n-1]`. -/
private lemma open_walk_interior_balanced (walk : List V) (n : ℕ)
    (hlen : walk.length = n + 1)
    (v : V)
    (hw0 : walk.get ⟨0, by omega⟩ ≠ v)
    (hwn : walk.get ⟨n, by omega⟩ ≠ v) :
    ((Finset.range n).filter fun i => walk.get ⟨i, by omega⟩ = v).card =
    ((Finset.range n).filter fun i => walk.get ⟨i + 1, by omega⟩ = v).card := by
  -- Bijection: source position i ↦ target position i - 1
  apply Finset.card_bij (fun i _ => i - 1)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    obtain ⟨hi_lt, hi_v⟩ := hi
    -- i ≥ 1: walk[0] ≠ v, so i = 0 contradicts walk[i] = v
    have hi1 : 1 ≤ i := by
      by_contra h; push_neg at h
      have : i = 0 := by omega
      exact hw0 (this ▸ hi_v)
    refine ⟨by omega, ?_⟩
    -- walk[(i-1)+1] = walk[i] = v
    convert hi_v using 2; omega
  · -- Injective: i - 1 = j - 1 with i, j ≥ 1 ⟹ i = j
    intro i hi j hj heq
    simp only [Finset.mem_filter, Finset.mem_range] at hi hj
    obtain ⟨_, hi_v⟩ := hi
    obtain ⟨_, hj_v⟩ := hj
    have hi1 : 1 ≤ i := by
      by_contra h; push_neg at h; have : i = 0 := by omega
      exact hw0 (this ▸ hi_v)
    have hj1 : 1 ≤ j := by
      by_contra h; push_neg at h; have : j = 0 := by omega
      exact hw0 (this ▸ hj_v)
    omega
  · -- Surjective: target position j has preimage j + 1 (and j + 1 < n since walk[n] ≠ v)
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    obtain ⟨hj_lt, hj_v⟩ := hj
    have hjn : j + 1 < n := by
      by_contra h; push_neg at h
      have : j + 1 = n := by omega
      exact hwn (this ▸ hj_v)
    refine ⟨j + 1, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hj_v⟩

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

/-- The edges used by maxTrail (= E \ remaining) are exactly E minus maxTrailRem.
    Direct induction on E.card. In the recursive case, pick c, then
    maxTrail E v = v :: maxTrail (E.erase c) c.2 and maxTrailRem E v =
    maxTrailRem (E.erase c) c.2. The trail steps decompose as {step 0 = c} ∪
    {steps shifted from inner trail}. Use IH on (E.erase c) and the fact that
    c ∉ maxTrailRem (since maxTrailRem ⊆ E.erase c). -/
private lemma maxTrail_used_eq (E : Finset (V × V)) (v : V) :
    E \ maxTrailRem E v =
    (Finset.range ((maxTrail E v).length - 1)).image (fun i =>
      ((maxTrail E v).get ⟨i, by omega⟩, (maxTrail E v).get ⟨i + 1, by omega⟩)) := by
  induction h_n : E.card using Nat.strong_rec_on generalizing E v with
  | _ n ih =>
    by_cases hout : (E.filter (fun e => e.1 = v)).Nonempty
    · -- Recursive case: maxTrail E v = v :: maxTrail (E.erase c) c.2
      set c := hout.choose with hc_def
      have hc_spec := hout.choose_spec
      have hc_E : c ∈ E := (Finset.mem_filter.mp hc_spec).1
      have hc_v : c.1 = v := (Finset.mem_filter.mp hc_spec).2
      have hcard : (E.erase c).card < n := h_n ▸ Finset.card_erase_lt_of_mem hc_E
      have hmtail : maxTrail E v = v :: maxTrail (E.erase c) c.2 := by
        unfold maxTrail; simp only [hout, ↓reduceDite]
      have hmrem : maxTrailRem E v = maxTrailRem (E.erase c) c.2 := by
        unfold maxTrailRem; simp only [hout, ↓reduceDite]
      have hne_inner : maxTrail (E.erase c) c.2 ≠ [] := maxTrail_nonempty' _ _
      have h_inner_pos : 0 < (maxTrail (E.erase c) c.2).length := by
        cases h_inner : maxTrail (E.erase c) c.2 with
        | nil => exact absurd h_inner hne_inner
        | cons _ _ => simp [h_inner]
      have hinner_start : (maxTrail (E.erase c) c.2).get ⟨0, h_inner_pos⟩ = c.2 := by
        have hmh := maxTrail_head' (E.erase c) c.2
        cases h_inner : maxTrail (E.erase c) c.2 with
        | nil => exact absurd h_inner hne_inner
        | cons hd t =>
          rw [h_inner] at hmh
          simp only [List.head?_cons, Option.some.injEq] at hmh
          rw [h_inner, List.get_cons_zero]; exact hmh
      have hcRem : c ∉ maxTrailRem (E.erase c) c.2 :=
        fun hmem => Finset.not_mem_erase c E (maxTrailRem_subset _ _ hmem)
      have hIH := ih _ hcard (E.erase c) c.2 rfl
      ext x
      rw [hmrem]
      simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨hxE, hxRem⟩
        by_cases hxc : x = c
        · -- x = c: outer step 0 is c
          subst hxc
          refine ⟨0, ?_, ?_⟩
          · simp only [hmtail, List.length_cons]; omega
          · simp only [hmtail, List.get_cons_zero, List.get_cons_succ, hinner_start]
            exact Prod.ext hc_v.symm rfl
        · -- x ≠ c: x ∈ E.erase c, apply IH and shift index by 1
          have hxE' : x ∈ E.erase c := Finset.mem_erase.mpr ⟨hxc, hxE⟩
          have hxIn : x ∈ (E.erase c) \ maxTrailRem (E.erase c) c.2 :=
            Finset.mem_sdiff.mpr ⟨hxE', hxRem⟩
          rw [hIH] at hxIn
          simp only [Finset.mem_image, Finset.mem_range] at hxIn
          obtain ⟨j, hj_lt, hj_eq⟩ := hxIn
          refine ⟨j + 1, ?_, ?_⟩
          · simp only [hmtail, List.length_cons]; omega
          · simp only [hmtail, List.get_cons_succ]; exact hj_eq
      · rintro ⟨i, hi_lt, hi_eq⟩
        cases i with
        | zero =>
          -- step_outer 0 = c
          have hstep0 : ((maxTrail E v).get ⟨0, by simp only [hmtail, List.length_cons]; omega⟩,
              (maxTrail E v).get ⟨0 + 1, by simp only [hmtail, List.length_cons]; omega⟩) = c := by
            simp only [hmtail, List.get_cons_zero, List.get_cons_succ, hinner_start]
            exact Prod.ext hc_v.symm rfl
          rw [hstep0] at hi_eq
          subst hi_eq
          exact ⟨hc_E, hcRem⟩
        | succ i' =>
          have hi'_lt : i' < (maxTrail (E.erase c) c.2).length - 1 := by
            simp only [hmtail, List.length_cons] at hi_lt; omega
          have hstep_eq : ((maxTrail E v).get ⟨i' + 1,
                by simp only [hmtail, List.length_cons]; omega⟩,
              (maxTrail E v).get ⟨i' + 1 + 1,
                by simp only [hmtail, List.length_cons]; omega⟩) =
              ((maxTrail (E.erase c) c.2).get ⟨i', by omega⟩,
               (maxTrail (E.erase c) c.2).get ⟨i' + 1, by omega⟩) := by
            simp only [hmtail, List.get_cons_succ]
          rw [hstep_eq] at hi_eq
          have hxIn : x ∈ (E.erase c) \ maxTrailRem (E.erase c) c.2 := by
            rw [hIH]
            simp only [Finset.mem_image, Finset.mem_range]
            exact ⟨i', hi'_lt, hi_eq⟩
          obtain ⟨hxE', hxRem'⟩ := Finset.mem_sdiff.mp hxIn
          exact ⟨Finset.mem_of_mem_erase hxE', hxRem'⟩
    · -- Base case: no outgoing edges, maxTrail = [v], maxTrailRem = E
      have hmtail : maxTrail E v = [v] := by unfold maxTrail; simp [hout]
      have hmrem : maxTrailRem E v = E := by unfold maxTrailRem; simp [hout]
      rw [hmrem, Finset.sdiff_self]
      ext x
      simp only [Finset.not_mem_empty, Finset.mem_image, Finset.mem_range, false_iff,
                 not_exists, not_and]
      intro i hi_lt _
      rw [hmtail] at hi_lt
      simp at hi_lt

/-- Every edge from the last vertex in E appears as a trail step.
    Equivalently: maxTrailRem has no outgoing edges from the last vertex in E.
    Direct induction on E.card: in the recursive case, pick the first outgoing edge c
    (so maxTrail E v = v :: maxTrail (E.erase c) c.2); the last vertex of the outer
    trail equals the last vertex of the inner trail. Either e = c (use step 0) or
    e ∈ E.erase c (apply IH and shift index by 1). -/
private lemma maxTrail_last_exhausted (E : Finset (V × V)) (v : V) :
    let last_v := (maxTrail E v).getLast (maxTrail_nonempty' E v)
    ∀ e ∈ E, e.1 = last_v →
      ∃ i, i + 1 < (maxTrail E v).length ∧
        (maxTrail E v).get ⟨i, by omega⟩ = e.1 ∧
        (maxTrail E v).get ⟨i + 1, by omega⟩ = e.2 := by
  induction h_n : E.card using Nat.strong_rec_on generalizing E v with
  | _ n ih =>
    intro e he hev
    by_cases hout : (E.filter (fun e => e.1 = v)).Nonempty
    · -- Recursive case: maxTrail E v = v :: maxTrail (E.erase c) c.2
      set c := hout.choose with hc_def
      have hc_spec := hout.choose_spec
      have hc_E : c ∈ E := (Finset.mem_filter.mp hc_spec).1
      have hc_v : c.1 = v := (Finset.mem_filter.mp hc_spec).2
      have hcard : (E.erase c).card < n := h_n ▸ Finset.card_erase_lt_of_mem hc_E
      have hmtail : maxTrail E v = v :: maxTrail (E.erase c) c.2 := by
        unfold maxTrail; simp only [hout, ↓reduceDite]
      have hne_inner : maxTrail (E.erase c) c.2 ≠ [] := maxTrail_nonempty' _ _
      have h_inner_pos : 0 < (maxTrail (E.erase c) c.2).length := by
        cases h_inner : maxTrail (E.erase c) c.2 with
        | nil => exact absurd h_inner hne_inner
        | cons _ _ => simp [h_inner]
      have hinner_start : (maxTrail (E.erase c) c.2).get ⟨0, h_inner_pos⟩ = c.2 := by
        have hmh := maxTrail_head' (E.erase c) c.2
        cases h_inner : maxTrail (E.erase c) c.2 with
        | nil => exact absurd h_inner hne_inner
        | cons hd t =>
          rw [h_inner] at hmh
          simp only [List.head?_cons, Option.some.injEq] at hmh
          rw [h_inner, List.get_cons_zero]; exact hmh
      have hlast_eq : (maxTrail E v).getLast (maxTrail_nonempty' E v) =
          (maxTrail (E.erase c) c.2).getLast hne_inner := by
        rw [hmtail]; exact List.getLast_cons hne_inner
      by_cases h_ec : e = c
      · -- Step 0 of outer trail is exactly the edge c = e.
        subst h_ec
        refine ⟨0, ?_, ?_, ?_⟩
        · simp only [hmtail, List.length_cons]; omega
        · simp only [hmtail, List.get_cons_zero]; exact hc_v.symm
        · simp only [hmtail, List.get_cons_succ]
          exact hinner_start
      · -- e ∈ E.erase c: apply IH at (E.erase c, c.2), shift index by 1.
        have he_erase : e ∈ E.erase c := Finset.mem_erase.mpr ⟨h_ec, he⟩
        have hev_inner : e.1 = (maxTrail (E.erase c) c.2).getLast hne_inner := by
          rw [← hlast_eq]; exact hev
        obtain ⟨i, hi_lt, hi_src, hi_tgt⟩ :=
          ih _ hcard (E.erase c) c.2 rfl e he_erase hev_inner
        refine ⟨i + 1, ?_, ?_, ?_⟩
        · simp only [hmtail, List.length_cons]; omega
        · simp only [hmtail, List.get_cons_succ]; exact hi_src
        · simp only [hmtail, List.get_cons_succ]; exact hi_tgt
    · -- Base case: maxTrail E v = [v], so last_v = v, but no edge from v exists in E.
      exfalso
      have hmtail : maxTrail E v = [v] := by unfold maxTrail; simp [hout]
      have hlast_v : (maxTrail E v).getLast (maxTrail_nonempty' E v) = v := by
        rw [hmtail]; rfl
      rw [hlast_v] at hev
      exact hout ⟨e, Finset.mem_filter.mpr ⟨he, hev⟩⟩

/-- All steps of maxTrail E v use edges from E. -/
private lemma maxTrail_steps_in_E (E : Finset (V × V)) (v : V) :
    ∀ i, i + 1 < (maxTrail E v).length →
      ((maxTrail E v).get ⟨i, by omega⟩, (maxTrail E v).get ⟨i + 1, by omega⟩) ∈ E := by
  induction h_n : E.card using Nat.strong_rec_on generalizing E v with
  | _ n ih =>
    intro i hi
    by_cases hout : (E.filter (fun e => e.1 = v)).Nonempty
    · set e := hout.choose with he_def
      have he_spec := hout.choose_spec
      have he_E : e ∈ E := (Finset.mem_filter.mp he_spec).1
      have he_v : e.1 = v := (Finset.mem_filter.mp he_spec).2
      have hcard : (E.erase e).card < n := h_n ▸ Finset.card_erase_lt_of_mem he_E
      have hmtail : maxTrail E v = v :: maxTrail (E.erase e) e.2 := by
        unfold maxTrail; simp only [hout, ↓reduceDite]
      cases i with
      | zero =>
        have h_inner_pos : 0 < (maxTrail (E.erase e) e.2).length := by
          simp only [hmtail, List.length_cons] at hi; omega
        have hinner_start : (maxTrail (E.erase e) e.2).get ⟨0, h_inner_pos⟩ = e.2 := by
          have hmh := maxTrail_head' (E.erase e) e.2
          cases h_inner : maxTrail (E.erase e) e.2 with
          | nil => exact absurd h_inner (maxTrail_nonempty' _ _)
          | cons hd t =>
            rw [h_inner] at hmh
            simp only [List.head?_cons, Option.some.injEq] at hmh
            rw [h_inner, List.get_cons_zero]; exact hmh
        simp only [hmtail, List.get_cons_zero, List.get_cons_succ, hinner_start, ← he_v]
        exact he_E
      | succ i' =>
        have hlen : i' + 1 < (maxTrail (E.erase e) e.2).length := by
          simp only [hmtail, List.length_cons] at hi; omega
        simp only [hmtail, List.get_cons_succ]
        exact Finset.mem_of_mem_erase (ih _ hcard _ _ rfl i' hlen)
    · have hmtail : maxTrail E v = [v] := by unfold maxTrail; simp [hout]
      simp only [hmtail, List.length_singleton] at hi; omega

/-- No edge is used twice in maxTrail (distinct edges). -/
private lemma maxTrail_steps_distinct (E : Finset (V × V)) (v : V) :
    ∀ i j, i + 1 < (maxTrail E v).length → j + 1 < (maxTrail E v).length → i ≠ j →
      ((maxTrail E v).get ⟨i, by omega⟩, (maxTrail E v).get ⟨i + 1, by omega⟩) ≠
      ((maxTrail E v).get ⟨j, by omega⟩, (maxTrail E v).get ⟨j + 1, by omega⟩) := by
  induction h_n : E.card using Nat.strong_rec_on generalizing E v with
  | _ n ih =>
    intro i j hi hj hij
    by_cases hout : (E.filter (fun e => e.1 = v)).Nonempty
    · set e := hout.choose with he_def
      have he_spec := hout.choose_spec
      have he_E : e ∈ E := (Finset.mem_filter.mp he_spec).1
      have hcard : (E.erase e).card < n := h_n ▸ Finset.card_erase_lt_of_mem he_E
      have hmtail : maxTrail E v = v :: maxTrail (E.erase e) e.2 := by
        unfold maxTrail; simp only [hout, ↓reduceDite]
      cases i with
      | zero =>
        cases j with
        | zero => exact absurd rfl hij
        | succ j' =>
          -- Step 0 uses e ∈ E; step j'+1 uses an edge in E.erase e (not e)
          intro heq
          have h_inner_pos : 0 < (maxTrail (E.erase e) e.2).length := by
            simp only [hmtail, List.length_cons] at hi; omega
          have hlen_j : j' + 1 < (maxTrail (E.erase e) e.2).length := by
            simp only [hmtail, List.length_cons] at hj; omega
          -- Step 0 produces e
          have hstep0 : ((maxTrail E v).get ⟨0, by omega⟩,
              (maxTrail E v).get ⟨1, by omega⟩) = e := by
            simp only [hmtail, List.get_cons_zero, List.get_cons_succ]
            have hinner_start : (maxTrail (E.erase e) e.2).get ⟨0, h_inner_pos⟩ = e.2 := by
              have hmh := maxTrail_head' (E.erase e) e.2
              cases h_inner : maxTrail (E.erase e) e.2 with
              | nil => exact absurd h_inner (maxTrail_nonempty' _ _)
              | cons hd t =>
                rw [h_inner] at hmh
                simp only [List.head?_cons, Option.some.injEq] at hmh
                rw [h_inner, List.get_cons_zero]; exact hmh
            rw [hinner_start]
            exact Prod.mk.inj_iff.mpr ⟨(Finset.mem_filter.mp he_spec).2.symm, rfl⟩
          -- Step j'+1 produces an edge in E.erase e
          have hstepj : ((maxTrail E v).get ⟨j' + 1, by omega⟩,
              (maxTrail E v).get ⟨j' + 2, by omega⟩) ∈ E.erase e := by
            simp only [hmtail, List.get_cons_succ]
            exact ih _ hcard (E.erase e) e.2 rfl j' hlen_j
          rw [hstep0] at heq
          exact absurd (heq ▸ hstepj) (Finset.not_mem_erase e E)
      | succ i' =>
        cases j with
        | zero =>
          -- i = i'+1, j = 0: symmetric to i=0, j=succ case
          intro heq
          have h_inner_pos : 0 < (maxTrail (E.erase e) e.2).length := by
            simp only [hmtail, List.length_cons] at hj; omega
          have hlen_i : i' + 1 < (maxTrail (E.erase e) e.2).length := by
            simp only [hmtail, List.length_cons] at hi; omega
          have hstep0 : ((maxTrail E v).get ⟨0, by omega⟩,
              (maxTrail E v).get ⟨1, by omega⟩) = e := by
            simp only [hmtail, List.get_cons_zero, List.get_cons_succ]
            have hinner_start : (maxTrail (E.erase e) e.2).get ⟨0, h_inner_pos⟩ = e.2 := by
              have hmh := maxTrail_head' (E.erase e) e.2
              cases h_inner : maxTrail (E.erase e) e.2 with
              | nil => exact absurd h_inner (maxTrail_nonempty' _ _)
              | cons hd t =>
                rw [h_inner] at hmh
                simp only [List.head?_cons, Option.some.injEq] at hmh
                rw [h_inner, List.get_cons_zero]; exact hmh
            rw [hinner_start]
            exact Prod.mk.inj_iff.mpr ⟨(Finset.mem_filter.mp he_spec).2.symm, rfl⟩
          have hstepi : ((maxTrail E v).get ⟨i' + 1, by omega⟩,
              (maxTrail E v).get ⟨i' + 2, by omega⟩) ∈ E.erase e := by
            simp only [hmtail, List.get_cons_succ]
            exact ih _ hcard (E.erase e) e.2 rfl i' hlen_i
          rw [hstep0] at heq
          exact absurd (heq.symm ▸ hstepi) (Finset.not_mem_erase e E)
        | succ j' =>
          -- Both steps are in inner trail
          simp only [hmtail, List.get_cons_succ]
          have hlen_i : i' + 1 < (maxTrail (E.erase e) e.2).length := by
            simp only [hmtail, List.length_cons] at hi; omega
          have hlen_j : j' + 1 < (maxTrail (E.erase e) e.2).length := by
            simp only [hmtail, List.length_cons] at hj; omega
          exact ih _ hcard _ _ rfl i' j' hlen_i hlen_j (by omega)
    · have hmtail : maxTrail E v = [v] := by unfold maxTrail; simp [hout]
      simp only [hmtail, List.length_singleton] at hi; omega

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
  set trail := maxTrail G.edges v with htrail
  set n := trail.length - 1 with hn_def
  -- If trail has length 1, it's trivially [v] and closed.
  by_cases hlen : trail.length ≤ 1
  · have : trail = [v] := by
      have hne := maxTrail_nonempty' G.edges v
      interval_cases h : trail.length
      · exact absurd rfl hne
      · exact List.length_eq_one.mp (by omega)
    simp [this, maxTrail_head' G.edges v]
  -- Otherwise n ≥ 1 and we apply the balance argument.
  push_neg at hlen
  have hn : 1 ≤ n := by omega
  have htrail_len : trail.length = n + 1 := by omega
  -- head = v
  have hhead_v : trail.get ⟨0, by omega⟩ = v := by
    have := maxTrail_head' G.edges v
    cases trail with
    | nil => simp at hlen
    | cons a t => simp at this ⊢; exact this
  -- Let last_v = trail[n]
  set last_v := trail.get ⟨n, by omega⟩ with hlast_def
  -- We need: head? = getLast?, i.e., v = last_v
  suffices h : v = last_v by
    rw [show trail.getLast? = some last_v from by
      rw [List.getLast?_eq_getLast (maxTrail_nonempty' G.edges v)]
      congr 1
      simp [List.getLast_eq_getElem, List.get_eq_getElem, hlast_def]
      congr 1; omega]
    rw [maxTrail_head' G.edges v]
    exact congrArg some h
  -- Assume for contradiction that last_v ≠ v.
  by_contra hne
  -- Count source/target occurrences of last_v in the trail steps
  set src_count := ((Finset.range n).filter (fun i =>
    trail.get ⟨i, by omega⟩ = last_v)).card
  set tgt_count := ((Finset.range n).filter (fun i =>
    trail.get ⟨i + 1, by omega⟩ = last_v)).card
  -- STEP A: All outgoing edges of last_v in G were used in the trail
  -- (maximality: last_v has no remaining outgoing edges).
  have hmax : ∀ e ∈ G.edges, e.1 = last_v →
      ∃ i, i + 1 < trail.length ∧
        trail.get ⟨i, by omega⟩ = e.1 ∧ trail.get ⟨i + 1, by omega⟩ = e.2 :=
    maxTrail_last_exhausted G.edges v
  -- STEP B: src_count = outDegree G last_v
  -- Each outgoing edge of last_v corresponds to a unique source-position in the trail.
  have h_src_eq_out : src_count = outDegree G last_v := by
    unfold outDegree
    symm
    -- Bijection: edges from last_v ↔ source positions of last_v
    apply Finset.card_bij (fun e he =>
      Classical.choose (hmax e (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2))
    · -- Maps into source filter
      intro e he
      have hmem := (Finset.mem_filter.mp he).1
      have hv := (Finset.mem_filter.mp he).2
      set i := Classical.choose (hmax e hmem hv)
      have hi := Classical.choose_spec (hmax e hmem hv)
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hi.2.1⟩
    · -- Injective (same edge position)
      intro e1 he1 e2 he2 heq
      have hm1 := (Finset.mem_filter.mp he1)
      have hm2 := (Finset.mem_filter.mp he2)
      have hs1 := Classical.choose_spec (hmax e1 hm1.1 hm1.2)
      have hs2 := Classical.choose_spec (hmax e2 hm2.1 hm2.2)
      rw [← heq] at hs2
      exact Prod.ext (hs1.2.1.symm.trans hs2.2.1) (hs1.2.2.symm.trans hs2.2.2)
    · -- Surjective
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨hi_lt, hi_v⟩ := hi
      set e := (trail.get ⟨i, by omega⟩, trail.get ⟨i + 1, by omega⟩)
      have he_mem : e ∈ G.edges := maxTrail_steps_in_E G.edges v i (by omega)
      have he_src : e.1 = last_v := hi_v
      refine ⟨e, Finset.mem_filter.mpr ⟨he_mem, he_src⟩, ?_⟩
      set j := Classical.choose (hmax e he_mem he_src)
      have hj := Classical.choose_spec (hmax e he_mem he_src)
      -- Uniqueness: positions i and j both witness the edge e
      -- By maxTrail_steps_distinct, e can only appear once
      have h_distinct := maxTrail_steps_distinct G.edges v i j (by omega) hj.1
      by_contra h_ne
      exact h_distinct h_ne ⟨hi_v.symm.trans hj.2.1, rfl.symm.trans hj.2.2⟩
  -- STEP C: tgt_count ≤ inDegree G last_v
  -- Each target position of last_v uses a unique incoming edge of G.
  have h_tgt_le_in : tgt_count ≤ inDegree G last_v := by
    unfold inDegree
    apply Finset.card_le_card_of_injOn
      (fun i => (trail.get ⟨i, by omega⟩, trail.get ⟨i + 1, by omega⟩))
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      simp only [Finset.mem_filter]
      exact ⟨maxTrail_steps_in_E G.edges v i (by omega), hi.2⟩
    · intro i1 hi1 i2 hi2 heq
      simp only [Finset.mem_filter, Finset.mem_range] at hi1 hi2
      have h_ne : i1 ≠ i2 → False := fun hne =>
        maxTrail_steps_distinct G.edges v i1 i2 (by omega) (by omega) hne heq
      omega
  -- STEP D: Open-walk counting: tgt_count = src_count + 1 (since last_v ≠ v = trail[0])
  have h_count : tgt_count = src_count + 1 := by
    apply open_walk_last_target_excess trail n hn htrail_len last_v
    · rwa [← hhead_v, ← hlast_def]; exact hne ∘ Eq.symm
    · exact hlast_def
  -- STEP E: Balance gives contradiction
  have hbal_last : inDegree G last_v = outDegree G last_v :=
    hbal last_v
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
    (walk.get ⟨i, by omega⟩, walk.get ⟨i + 1, by omega⟩) ∈ G.edges

/-- Every non-empty balanced digraph has a directed circuit. -/
theorem circuit_exists (G : DiGraph V) (hbal : IsEulerianBalanced G)
    (hne : G.edges.Nonempty) : Nonempty (DirectedCircuit G) := by
  -- Any vertex v with an outgoing edge serves as the starting point.
  obtain ⟨e₀, he₀⟩ := hne
  set v := e₀.1 with hv_def
  -- The maximal trail from v is closed by the balance theorem.
  set trail := maxTrail G.edges v with htrail_def
  have hclosed := maxTrail_closed G hbal v
  have hne_trail := maxTrail_nonempty' G.edges v
  -- v has an outgoing edge e₀, so the trail has length ≥ 2.
  have hlen : 2 ≤ trail.length := by
    show 2 ≤ (maxTrail G.edges v).length
    unfold maxTrail
    have hout : (G.edges.filter (fun e => e.1 = v)).Nonempty :=
      ⟨e₀, Finset.mem_filter.mpr ⟨he₀, hv_def⟩⟩
    simp only [hout, ↓reduceDite, List.length_cons]
    exact Nat.succ_le_succ (Nat.one_le_iff_ne_zero.mpr
      (List.length_ne_zero.mpr (maxTrail_nonempty' _ _)))
  exact ⟨⟨trail, hclosed, hlen, maxTrail_steps_in_E G.edges v⟩⟩

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
theorem remove_circuit_balanced (G : DiGraph V) (C : DirectedCircuit G) :
    IsEulerianBalanced (G.removeEdgeSet (walkEdges C.walk).toFinset) := by
  sorry -- TODO: circuit passes through each vertex same #times as src and tgt;
        -- inDeg/outDeg each decrease by same amount. Requires Finset sdiff/filter
        -- distributivity API and closed_walk_balance on C.walk.

/-
  STEP 6: NECESSITY DIRECTION FOR EULERIAN PATHS

  If G has an Eulerian path from s to t (s ≠ t), then:
    outDegree s = inDegree s + 1
    inDegree t  = outDegree t + 1
    All other vertices are balanced.
  Proof: Same bijection argument as eulerian_circuit_implies_balanced, but for open walks.
-/

/-- **Necessity for Eulerian paths**: a graph with an Eulerian path from s to t
    satisfies the asymmetric degree conditions.
    Proof: walk-position bijections (`walk_source_eq_outDegree`, `walk_target_eq_inDegree`)
    convert degree counts to position counts; then `open_walk_first_source_excess`,
    `open_walk_last_target_excess`, and `open_walk_interior_balanced` give the
    three required equalities. -/
theorem euler_path_implies_degree_balance (G : DiGraph V) (s t : V) (hst : s ≠ t)
    (hpath : HasEulerianPath G s t) :
    outDegree G s = inDegree G s + 1 ∧
    inDegree G t = outDegree G t + 1 ∧
    ∀ v : V, v ≠ s → v ≠ t → IsBalanced G v := by
  obtain ⟨walk, hhead, hlast, hwlen, hcov, hsteps⟩ := hpath
  set n := G.edges.card with hn_def
  have hlen : walk.length = n + 1 := hwlen
  have hn_eq : walk.length - 1 = n := by omega
  have hn_ge_1 : 1 ≤ n := by
    -- If n = 0, walk has length 1, so head = last, meaning s = t — contradiction.
    by_contra h; push_neg at h
    have hn0 : n = 0 := by omega
    have hlen1 : walk.length = 1 := by omega
    have hhead_last : walk.head? = walk.getLast? := by
      rcases walk with _ | ⟨a, _ | ⟨b, l⟩⟩
      · simp at hlen1
      · rfl
      · simp at hlen1
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
  -- Normalize hcov and hsteps to range over `n` instead of `walk.length - 1`
  have hcov' : ∀ e ∈ G.edges, ∃! i : ℕ, i < n ∧
      walk.get ⟨i, by omega⟩ = e.1 ∧ walk.get ⟨i + 1, by omega⟩ = e.2 := by
    intro e he
    have h := hcov e he
    rwa [hn_eq] at h
  have hsteps' : ∀ i (hi : i < n),
      (walk.get ⟨i, by omega⟩, walk.get ⟨i + 1, by omega⟩) ∈ G.edges :=
    fun i hi => hsteps i (hn_eq ▸ hi)
  -- Bridge: source-position count = outDegree, target-position count = inDegree.
  have hsrc_eq_out : ∀ v,
      ((Finset.range n).filter (fun i => walk.get ⟨i, by omega⟩ = v)).card =
        outDegree G v :=
    fun v => walk_source_eq_outDegree G walk n v hlen hcov' hsteps'
  have htgt_eq_in : ∀ v,
      ((Finset.range n).filter (fun i => walk.get ⟨i + 1, by omega⟩ = v)).card =
        inDegree G v :=
    fun v => walk_target_eq_inDegree G walk n v hlen hcov' hsteps'
  refine ⟨?_, ?_, ?_⟩
  · -- outDegree s = inDegree s + 1: open-walk source excess at s.
    have hns : walk.get ⟨n, by omega⟩ ≠ s := by rw [hget_last]; exact fun h => hst h.symm
    have hexc :=
      open_walk_first_source_excess walk n hn_ge_1 hlen s hget_head hns
    rw [hsrc_eq_out s, htgt_eq_in s] at hexc
    exact hexc
  · -- inDegree t = outDegree t + 1: open-walk target excess at t.
    have h0t : walk.get ⟨0, by omega⟩ ≠ t := by rw [hget_head]; exact hst
    have hexc :=
      open_walk_last_target_excess walk n hn_ge_1 hlen t h0t hget_last
    rw [htgt_eq_in t, hsrc_eq_out t] at hexc
    exact hexc
  · -- Interior v ≠ s, t: source-count = target-count.
    intro v hvs hvt
    unfold IsBalanced
    have hv0 : walk.get ⟨0, by omega⟩ ≠ v := by
      rw [hget_head]; exact fun h => hvs h.symm
    have hvn : walk.get ⟨n, by omega⟩ ≠ v := by
      rw [hget_last]; exact fun h => hvt h.symm
    have hbal := open_walk_interior_balanced walk n hlen v hv0 hvn
    rw [hsrc_eq_out v, htgt_eq_in v] at hbal
    exact hbal.symm

end HierholzerInfrastructure

end KonigsbergOQ01OQ02
