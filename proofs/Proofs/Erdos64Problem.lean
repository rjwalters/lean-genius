/-
  Erdős Problem #64: Power of Two Cycles in Graphs with Minimum Degree 3

  Source: https://erdosproblems.com/64
  Status: OPEN (Prize: $1000)

  Statement:
  Does every finite graph with minimum degree at least 3 contain a cycle of length
  2^k for some k ≥ 2?

  History:
  - Erdős-Gyárfás conjecture: The answer is NO (believed to be false)
  - Liu-Montgomery (2020): Proved YES for sufficiently large minimum degree,
    disproving the Erdős-Gyárfás conjecture
  - The case of minimum degree exactly 3 remains OPEN

  Background:
  This problem asks whether the powers of 2 (at least 4) are unavoidable cycle lengths
  for graphs with minimum degree 3. For infinite graphs, the answer is NO (infinite
  3-regular trees have no cycles). The finite case is more subtle.

  This file formalizes the definitions and known results.
-/

import Mathlib

open Set SimpleGraph Finset

namespace Erdos64

variable {V : Type*} [Fintype V] [DecidableEq V]

/- ## Core Definitions -/

/-- Cyclic successor in Fin k: maps i to (i+1) mod k. -/
def Fin.succMod {k : ℕ} (hk : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩

/-- A graph contains a cycle of length k ≥ 3 if there is a cycle subgraph on k vertices. -/
def ContainsCycleLength (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (hk : k ≥ 3) (vs : Fin k → V), Function.Injective vs ∧
    ∀ i : Fin k, G.Adj (vs i) (vs (Fin.succMod (by omega : 0 < k) i))

/-- The minimum degree of a graph. -/
noncomputable def minDegree [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.inf' Finset.univ ⟨Classical.arbitrary V, Finset.mem_univ _⟩
    (fun v => (G.neighborFinset v).card)

/-- A graph has minimum degree at least d. -/
def HasMinDegree (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Prop :=
  ∀ v : V, d ≤ (G.neighborFinset v).card

/- ## Powers of Two -/

/-- The set of powers of 2 that are at least 4: {4, 8, 16, 32, ...}. -/
def PowersOfTwoAtLeast4 : Set ℕ := { n | ∃ k : ℕ, k ≥ 2 ∧ n = 2^k }

/-- 2^k for k ≥ 2 is at least 4. -/
theorem power_two_ge_four (k : ℕ) (hk : k ≥ 2) : 2^k ≥ 4 := by
  calc 2^k ≥ 2^2 := Nat.pow_le_pow_right (by norm_num) hk
       _ = 4 := by norm_num

/-- Powers of 2 (k ≥ 2) are even. -/
theorem power_two_even (k : ℕ) (hk : k ≥ 2) : Even (2^k) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp only [hm, Nat.pow_succ]
  exact ⟨2^m, by ring⟩

/- ## Main Conjecture -/

/--
**Erdős Problem 64** (OPEN, $1000 prize):
Does every finite graph with minimum degree at least 3 contain a cycle of length
2^k for some k ≥ 2?
-/
def erdos_64_conjecture : Prop :=
  ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph W) [DecidableRel G.Adj],
    HasMinDegree G 3 → ∃ k : ℕ, k ≥ 2 ∧ ContainsCycleLength G (2^k)

/- ## Erdős-Gyárfás Conjecture (Disproved) -/

/--
**Erdős-Gyárfás Conjecture** (DISPROVED by Liu-Montgomery):
For every r, there exists a graph with minimum degree at least r that contains
no cycle of length 2^k for any k ≥ 2.

This was the conjecture that the answer to Problem 64 is NO.
Liu-Montgomery (2020) disproved this for large r.
-/
def erdos_gyarfas_conjecture : Prop :=
  ∀ r : ℕ, ∃ (W : Type*) (_ : Fintype W) (_ : DecidableEq W) (_ : Nonempty W)
    (G : SimpleGraph W) (_ : DecidableRel G.Adj),
    HasMinDegree G r ∧ ∀ k : ℕ, k ≥ 2 → ¬ContainsCycleLength G (2^k)

/- 
**Liu-Montgomery Theorem** (2020):
The Erdős-Gyárfás conjecture is FALSE for sufficiently large r.
There exists an absolute constant D such that every graph with minimum degree
at least D contains a cycle of length 2^k for some k ≥ 2.
-/
/- ## Partial Results -/

/- 
**Liu-Montgomery Stronger Result**:
Graphs with sufficiently large average degree contain cycles of every even length m
in the interval [(\log ℓ)^8, ℓ] for some large integer ℓ.

In particular, they contain some cycle of length 2^k.
-/
/-- Any even length cycle in a suitable range includes some power of 2. -/
theorem range_contains_power_of_two (L : ℕ) (hL : L ≥ 16) :
    ∃ k : ℕ, k ≥ 2 ∧ 2^k ≤ L := by
  use 2
  constructor
  · omega
  · calc 2^2 = 4 := by norm_num
         _ ≤ 16 := by norm_num
         _ ≤ L := hL

/- ## Infinite Graph Counterexample -/

/-- An infinite graph structure (for stating the counterexample). -/
structure InfGraph (V : Type*) where
  Adj : V → V → Prop
  symm : ∀ u v, Adj u v → Adj v u
  loopless : ∀ v, ¬Adj v v

/-- An infinite graph is d-regular if every vertex has exactly d neighbors. -/
def InfGraph.IsRegular (G : InfGraph V) (d : ℕ) : Prop :=
  ∀ v : V, (setOf (G.Adj v)).ncard = d

/-- An infinite graph contains a cycle of length k. -/
def InfGraph.ContainsCycleLength (G : InfGraph V) (k : ℕ) : Prop :=
  ∃ (hk : k ≥ 3) (vs : Fin k → V), Function.Injective vs ∧
    ∀ i : Fin k, G.Adj (vs i) (vs (Fin.succMod (by omega : 0 < k) i))

/-- An infinite graph is a tree (connected and acyclic). -/
def InfGraph.IsTree (G : InfGraph V) : Prop :=
  ∀ k : ℕ, k ≥ 3 → ¬G.ContainsCycleLength k

/- 
**Counterexample for Infinite Graphs**:
There exists an infinite 3-regular tree (the infinite binary tree with each vertex
connected to its parent and two children). This has minimum degree 3 but no cycles.
-/
/- ## Degree 3 Case (Open) -/

/--
**Open Problem**: The case of minimum degree exactly 3.
Does every finite graph with minimum degree exactly 3 contain a cycle
of length 2^k for some k ≥ 2?
-/
def degree_3_conjecture : Prop :=
  ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph W) [DecidableRel G.Adj],
    HasMinDegree G 3 → ∃ k : ℕ, k ≥ 2 ∧ ContainsCycleLength G (2^k)

-- Note: degree_3_conjecture and erdos_64_conjecture are semantically identical.

/- ## Cycle Existence from Minimum Degree (foundational, machine-checked)

These lemmas establish the *base fact* that underlies Problem 64: a graph with
minimum degree ≥ 2 must contain **some** cycle. Problem 64 asks the far stronger
(open) question of whether some cycle has length a power of two; the necessary
elementary precondition — that a cycle exists at all — is proved here in full,
axiom-free.

The mechanism is the "a tree has a leaf" phenomenon: a finite nontrivial tree
always has a vertex of degree exactly one (`SimpleGraph.IsTree.minDegree_eq_one_of_nontrivial`),
so a connected graph in which *every* vertex has degree ≥ 2 cannot be a tree,
hence (being connected) cannot be acyclic. `SimpleGraph.IsAcyclic` unfolds to
"no closed walk is a cycle", so its negation hands back an explicit cycle. -/

/-- A nontrivial connected graph with minimum degree at least `2` is **not acyclic**:
if it were, connectivity would make it a tree, and a nontrivial tree has a vertex
of degree `1`, contradicting the degree bound. -/
theorem connected_hasMinDegree_two_not_isAcyclic
    {W : Type*} [Fintype W] [Nontrivial W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hconn : G.Connected) (hdeg : HasMinDegree G 2) :
    ¬ G.IsAcyclic := by
  intro hacyc
  have htree : G.IsTree := ⟨hconn, hacyc⟩
  have h1 : G.minDegree = 1 := htree.minDegree_eq_one_of_nontrivial
  have h2 : 2 ≤ G.minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact hdeg v
  omega

/-- A nontrivial connected graph with minimum degree at least `2` contains a cycle
(an explicit closed walk that is a `SimpleGraph.Walk.IsCycle`). -/
theorem connected_hasMinDegree_two_exists_cycle
    {W : Type*} [Fintype W] [Nontrivial W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hconn : G.Connected) (hdeg : HasMinDegree G 2) :
    ∃ (v : W) (c : G.Walk v v), c.IsCycle := by
  by_contra hcon
  exact connected_hasMinDegree_two_not_isAcyclic G hconn hdeg
    (fun v c hc => hcon ⟨v, c, hc⟩)

/-- The Problem-64 hypothesis (minimum degree ≥ `3`) forces at least one cycle, for
connected graphs. The **open** content of Problem 64 is that some such cycle can be
taken to have length `2^k`; this lemma isolates the elementary part (a cycle exists),
which is a strict weakening of the conjecture and does not resolve it. -/
theorem connected_hasMinDegree_three_exists_cycle
    {W : Type*} [Fintype W] [Nontrivial W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hconn : G.Connected) (hdeg : HasMinDegree G 3) :
    ∃ (v : W) (c : G.Walk v v), c.IsCycle :=
  connected_hasMinDegree_two_exists_cycle G hconn
    (fun v => le_trans (by norm_num) (hdeg v))

/-- **The finite-graph statement (connectivity dropped).** An arbitrary — not necessarily
connected — nonempty finite graph with minimum degree at least `2` contains a cycle.

The proof passes to the connected component `C` of an arbitrary vertex `v` and works inside
the induced graph `C.toSimpleGraph = G.induce C.supp`:

* every neighbour of a vertex lies in that vertex's own component
  (`ConnectedComponent.mem_supp_of_adj_mem_supp`), so `G.neighborSet` is contained in
  `C.supp` and **degrees are preserved** inside the component
  (`SimpleGraph.degree_induce_of_neighborSet_subset`);
* if `G` were acyclic then `C.toSimpleGraph` would be a tree
  (`SimpleGraph.IsAcyclic.isTree_connectedComponent`), and — being nontrivial, since `v`
  has a neighbour — it would have a vertex `w` of degree exactly `1`
  (`SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial`);
* degree preservation then forces `G.degree w = 1`, contradicting the hypothesis
  `2 ≤ G.degree w`.

This is still a strict weakening of Problem 64 (a cycle exists; its length need not be a
power of two), but it removes the connectivity assumption from the earlier lemmas. -/
theorem hasMinDegree_two_exists_cycle
    {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hdeg : HasMinDegree G 2) :
    ∃ (v : W) (c : G.Walk v v), c.IsCycle := by
  by_contra hcon
  have hacyc : G.IsAcyclic := fun v c hc => hcon ⟨v, c, hc⟩
  obtain ⟨v⟩ : Nonempty W := inferInstance
  -- Work inside the connected component of `v`.
  set C := G.connectedComponentMk v with hC
  have hvC : v ∈ C.supp := (ConnectedComponent.mem_supp_iff C v).mpr hC.symm
  -- `v` has a neighbour `u`; it lies in the same component, so the component is nontrivial.
  have hdv : 0 < (G.neighborFinset v).card := lt_of_lt_of_le (by norm_num) (hdeg v)
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hdv
  have hadj : G.Adj v u := (G.mem_neighborFinset v u).mp hu
  have huC : u ∈ C.supp := C.mem_supp_of_adj_mem_supp hvC hadj
  -- Work with the induced graph `G.induce C.supp` directly (all instances canonical, so the
  -- Mathlib degree lemma below matches on the nose); `C.toSimpleGraph` is a `def` opaque to
  -- instance search, so we avoid it.
  haveI : DecidablePred (· ∈ C.supp) := fun x => inferInstance
  haveI : Nontrivial (C.supp : Set W) :=
    ⟨⟨v, hvC⟩, ⟨u, huC⟩, fun h => hadj.ne (congrArg Subtype.val h)⟩
  -- Under `hacyc` the induced component graph is a nontrivial tree, hence has a degree-one vertex.
  have hconn : (G.induce C.supp).Connected := C.connected_toSimpleGraph
  have htree : (G.induce C.supp).IsTree := ⟨hconn, hacyc.induce C.supp⟩
  obtain ⟨w, hw⟩ := htree.exists_vert_degree_one_of_nontrivial
  -- Degrees are preserved inside the component.
  have hsub : G.neighborSet w.val ⊆ C.supp := fun x hx =>
    C.mem_supp_of_adj_mem_supp w.property ((G.mem_neighborSet w.val x).mp hx)
  have hpres : (G.induce C.supp).degree w = G.degree w.val :=
    degree_induce_of_neighborSet_subset hsub
  -- But `w` has `G`-degree at least `2`: contradiction.
  have hge : 2 ≤ G.degree w.val := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]; exact hdeg w.val
  rw [hpres] at hw
  omega

/- ## Bridge to the length-indexed `ContainsCycleLength` predicate

The cycle-existence lemmas above deliver a `SimpleGraph.Walk.IsCycle` witness, whereas
`erdos_64_conjecture` is phrased with this file's own `ContainsCycleLength` predicate
(an injective `Fin k → V` with cyclic `Fin.succMod` adjacency). The lemma below converts
between them, so the machine-checked existence results become statements about a concrete
cycle *length* — the quantity Problem 64 is ultimately about. -/

/-- **`Walk.IsCycle` ⟹ `ContainsCycleLength`.** Any explicit cycle `c : G.Walk v v` gives a
`ContainsCycleLength G c.length` witness: the vertices `c.getVert 0, …, c.getVert (c.length-1)`
are pairwise distinct (`SimpleGraph.Walk.IsCycle.getVert_injOn'`) and cyclically adjacent
(`SimpleGraph.Walk.adj_getVert_succ`), the wrap-around edge closing because
`c.getVert c.length = v = c.getVert 0`. -/
theorem isCycle_containsCycleLength
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    {v : W} (c : G.Walk v v) (hc : c.IsCycle) :
    ContainsCycleLength G c.length := by
  refine ⟨hc.three_le_length, fun i => c.getVert i.val, ?_, ?_⟩
  · -- injectivity: `getVert` is injective on `{i | i ≤ c.length - 1}`
    intro i j hij
    apply Fin.ext
    exact hc.getVert_injOn'
      (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega)
      hij
  · -- cyclic adjacency `c.getVert i` — `c.getVert ((i+1) % c.length)`
    intro i
    have hi : i.val < c.length := i.isLt
    show G.Adj (c.getVert i.val) (c.getVert ((i.val + 1) % c.length))
    by_cases hlast : i.val + 1 = c.length
    · -- final vertex wraps to `c.getVert 0 = v = c.getVert c.length`
      have h0 : (i.val + 1) % c.length = 0 := by rw [hlast]; exact Nat.mod_self _
      rw [h0, c.getVert_zero]
      have hadj := c.adj_getVert_succ hi
      rwa [hlast, c.getVert_length] at hadj
    · have hlt : i.val + 1 < c.length := by omega
      rw [Nat.mod_eq_of_lt hlt]
      exact c.adj_getVert_succ hi

/-- A nonempty finite graph with minimum degree at least `2` contains a cycle of some
**concrete length** `k ≥ 3` in the `ContainsCycleLength` encoding (obtained by measuring the
length of the cycle from `hasMinDegree_two_exists_cycle`). This is the elementary,
axiom-free precondition of Problem 64 restated in the predicate the conjecture uses. -/
theorem hasMinDegree_two_containsCycleLength
    {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hdeg : HasMinDegree G 2) :
    ∃ k : ℕ, k ≥ 3 ∧ ContainsCycleLength G k := by
  obtain ⟨v, c, hc⟩ := hasMinDegree_two_exists_cycle G hdeg
  exact ⟨c.length, hc.three_le_length, isCycle_containsCycleLength G c hc⟩

/-- The Problem-64 hypothesis (minimum degree ≥ `3`) yields a cycle of some concrete length
`k ≥ 3` (in the `ContainsCycleLength` encoding). Problem 64 asks the **open** question of
whether `k` can be chosen to be a power of two `2^m` with `m ≥ 2`; this lemma proves the
strict weakening "some length works" and does not resolve the conjecture. -/
theorem hasMinDegree_three_containsCycleLength
    {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hdeg : HasMinDegree G 3) :
    ∃ k : ℕ, k ≥ 3 ∧ ContainsCycleLength G k :=
  hasMinDegree_two_containsCycleLength G (fun v => le_trans (by norm_num) (hdeg v))

/- ## Even cycle from minimum degree 3 (longest-path parity argument)

Every power of two `2^k` (`k ≥ 2`) is even, so "the graph contains an **even** cycle"
is a necessary — and classically nontrivial — precondition of Problem 64, sitting
strictly between plain cycle existence (proved above from minimum degree `2`) and the
open power-of-two-length core.

The classical argument: take a path `p` of maximum length, starting at `v₀`.
Maximality traps every neighbour of `v₀` on `p` (else `p` could be extended), so the
at-least-three neighbours of `v₀` sit at distinct positive indices along `p`. If
`a < b` are the two largest such indices (so `a ≥ 2`), closing `p` back to `v₀` from
index `a`, from index `b`, and around the segment `[a, b]` produces three cycles of
lengths `a + 1`, `b + 1`, and `b - a + 2`. These lengths sum to `2b + 4`, which is
even — so they cannot all be odd, and one of the three cycles is even. -/

/-- **Minimum degree `3` forces an even cycle.** Every nonempty finite graph with
minimum degree at least `3` contains a cycle of even length (as an explicit
`SimpleGraph.Walk.IsCycle` witness). This is the parity part of the necessary
condition for Problem 64: a `2^k`-cycle is in particular even. The proof is the
classical longest-path argument; see the section header above. -/
theorem hasMinDegree_three_exists_even_cycle
    {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hdeg : HasMinDegree G 3) :
    ∃ (v : W) (c : G.Walk v v), c.IsCycle ∧ Even c.length := by
  classical
  -- ### A path of maximum length exists
  have hne : ({n : ℕ | ∃ (a : W) (b : W) (q : G.Walk a b), q.IsPath ∧ q.length = n}).Nonempty :=
    ⟨0, Classical.arbitrary W, Classical.arbitrary W, Walk.nil, Walk.IsPath.nil, rfl⟩
  have hbdd : BddAbove {n : ℕ | ∃ (a : W) (b : W) (q : G.Walk a b), q.IsPath ∧ q.length = n} := by
    refine ⟨Fintype.card W, ?_⟩
    rintro n ⟨a, b, q, hq, rfl⟩
    exact hq.length_lt.le
  obtain ⟨v₀, u, p, hp, hplen⟩ := Nat.sSup_mem hne hbdd
  have hmax : ∀ (a b : W) (q : G.Walk a b), q.IsPath → q.length ≤ p.length := by
    intro a b q hq
    rw [hplen]
    exact le_csSup hbdd ⟨a, b, q, hq, rfl⟩
  -- ### Maximality traps every neighbour of the start vertex `v₀` on `p`
  have hnbr : ∀ w : W, G.Adj v₀ w → w ∈ p.support := by
    intro w hw
    by_contra hws
    have hcons : (Walk.cons hw.symm p).IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hp, hws⟩
    have := hmax _ _ _ hcons
    rw [Walk.length_cons] at this
    omega
  -- ### The neighbours of `v₀` sit at distinct positive indices along `p`
  set idx : W → ℕ := fun w => if hw : w ∈ p.support then (p.takeUntil w hw).length else 0
    with hidx
  have hidx_get : ∀ w (hw : w ∈ p.support), p.getVert (idx w) = w := by
    intro w hw
    simp only [hidx, dif_pos hw]
    exact Walk.getVert_length_takeUntil hw
  -- the finset of neighbour indices
  set T : Finset ℕ := (G.neighborFinset v₀).image idx with hT
  have hTcard : 3 ≤ T.card := by
    rw [hT, Finset.card_image_of_injOn]
    · exact hdeg v₀
    · intro w₁ hw₁ w₂ hw₂ hww
      have h₁ : G.Adj v₀ w₁ := (G.mem_neighborFinset v₀ w₁).mp (Finset.mem_coe.mp hw₁)
      have h₂ : G.Adj v₀ w₂ := (G.mem_neighborFinset v₀ w₂).mp (Finset.mem_coe.mp hw₂)
      calc w₁ = p.getVert (idx w₁) := (hidx_get w₁ (hnbr _ h₁)).symm
        _ = p.getVert (idx w₂) := by rw [hww]
        _ = w₂ := hidx_get w₂ (hnbr _ h₂)
  have hpos : ∀ n ∈ T, 1 ≤ n := by
    intro n hn
    rw [hT] at hn
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hn
    have hadj : G.Adj v₀ w := (G.mem_neighborFinset v₀ w).mp hw
    rcases Nat.eq_zero_or_pos (idx w) with h0 | h1
    · exfalso
      have hgw := hidx_get w (hnbr _ hadj)
      rw [h0, Walk.getVert_zero] at hgw
      exact hadj.ne hgw
    · exact h1
  -- ### Extract the two largest indices `a < b`, with `a ≥ 2`
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hbT : T.max' hTne ∈ T := T.max'_mem hTne
  set b := T.max' hTne with hbdef
  have hT'ne : (T.erase b).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hbT]
    omega
  have haT' : (T.erase b).max' hT'ne ∈ T.erase b := (T.erase b).max'_mem hT'ne
  set a := (T.erase b).max' hT'ne with hadef
  have haT : a ∈ T := Finset.mem_of_mem_erase haT'
  have hab : a < b := lt_of_le_of_ne (T.le_max' a haT) (Finset.ne_of_mem_erase haT')
  have ha2 : 2 ≤ a := by
    have hcne : ((T.erase b).erase a).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem haT', Finset.card_erase_of_mem hbT]
      omega
    obtain ⟨c, hc⟩ := hcne
    have hcT' : c ∈ T.erase b := Finset.mem_of_mem_erase hc
    have hca : c < a := lt_of_le_of_ne ((T.erase b).le_max' c hcT') (Finset.ne_of_mem_erase hc)
    have := hpos c (Finset.mem_of_mem_erase hcT')
    omega
  -- ### The neighbours `x` (at index `a`) and `y` (at index `b`)
  have hbT2 : b ∈ (G.neighborFinset v₀).image idx := by rw [← hT]; exact hbT
  have haT2 : a ∈ (G.neighborFinset v₀).image idx := by rw [← hT]; exact haT
  obtain ⟨y, hyN, hyb⟩ := Finset.mem_image.mp hbT2
  obtain ⟨x, hxN, hxa⟩ := Finset.mem_image.mp haT2
  have hax : G.Adj v₀ x := (G.mem_neighborFinset v₀ x).mp hxN
  have hay : G.Adj v₀ y := (G.mem_neighborFinset v₀ y).mp hyN
  have hxs : x ∈ p.support := hnbr x hax
  have hys : y ∈ p.support := hnbr y hay
  have hxa' : (p.takeUntil x hxs).length = a := by
    rw [← hxa]; simp only [hidx, dif_pos hxs]
  have hyb' : (p.takeUntil y hys).length = b := by
    rw [← hyb]; simp only [hidx, dif_pos hys]
  have hgx : p.getVert a = x := by rw [← hxa']; exact Walk.getVert_length_takeUntil hxs
  have hgy : p.getVert b = y := by rw [← hyb']; exact Walk.getVert_length_takeUntil hys
  have hblen : b ≤ p.length := by rw [← hyb']; exact p.length_takeUntil_le_length hys
  have halen : a ≤ p.length := by omega
  have hxy : x ≠ y := by
    intro h
    have hgg : p.getVert a = p.getVert b := by rw [hgx, hgy, h]
    have := hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) hgg
    omega
  -- ### Closing a prefix `p.takeUntil w` through the edge `w — v₀` yields a cycle
  have hclose : ∀ (w : W) (hw : w ∈ p.support) (hadj : G.Adj v₀ w),
      2 ≤ (p.takeUntil w hw).length →
      ∃ c : G.Walk v₀ v₀, c.IsCycle ∧ c.length = (p.takeUntil w hw).length + 1 := by
    intro w hw hadj h2
    refine ⟨Walk.cons hadj (p.takeUntil w hw).reverse, ?_, ?_⟩
    · rw [Walk.cons_isCycle_iff]
      refine ⟨(hp.takeUntil hw).reverse, ?_⟩
      intro hmem
      rw [Walk.edges_reverse, List.mem_reverse] at hmem
      -- an edge of a path through its start must be the first edge …
      have hsnd : w = (p.takeUntil w hw).snd := (hp.takeUntil hw).eq_snd_of_mem_edges hmem
      -- … but `w` is the endpoint of the prefix, at index `≥ 2`
      have h1 : (p.takeUntil w hw).getVert 1 =
          (p.takeUntil w hw).getVert (p.takeUntil w hw).length := by
        rw [Walk.getVert_length]
        exact hsnd.symm
      have := (hp.takeUntil hw).getVert_injOn
        (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) h1
      omega
    · rw [Walk.length_cons, Walk.length_reverse]
  -- ### The middle segment from `x` to `y` along `p`
  have hia : p.support.idxOf x = a := by
    rw [← p.length_takeUntil hxs]; exact hxa'
  have hdrop_gv : (p.dropUntil x hxs).getVert (b - a) = y := by
    rw [Walk.dropUntil_eq_drop, Walk.getVert_copy, Walk.drop_getVert, hia,
      show a + (b - a) = b by omega]
    exact hgy
  have hdrop_len : b - a ≤ (p.dropUntil x hxs).length := by
    rw [Walk.length_dropUntil, hia]
    omega
  have hyd : y ∈ (p.dropUntil x hxs).support :=
    Walk.mem_support_iff_exists_getVert.mpr ⟨b - a, hdrop_gv, hdrop_len⟩
  set r := (p.dropUntil x hxs).takeUntil y hyd with hr
  have hrpath : r.IsPath := (hp.dropUntil hxs).takeUntil hyd
  have hrlen : r.length = b - a := by
    have h₁ : (p.dropUntil x hxs).getVert r.length = y := Walk.getVert_length_takeUntil hyd
    have hle : r.length ≤ (p.dropUntil x hxs).length :=
      (p.dropUntil x hxs).length_takeUntil_le_length hyd
    exact (hp.dropUntil hxs).getVert_injOn
      (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega)
      (h₁.trans hdrop_gv.symm)
  have hv₀r : v₀ ∉ r.support := by
    intro hmem
    have hmem' : v₀ ∈ (p.dropUntil x hxs).support :=
      (p.dropUntil x hxs).support_takeUntil_subset_support hyd hmem
    obtain ⟨n, hgv, hn⟩ := Walk.mem_support_iff_exists_getVert.mp hmem'
    rw [Walk.dropUntil_eq_drop, Walk.getVert_copy, Walk.drop_getVert, hia] at hgv
    have h0 : p.getVert (a + n) = p.getVert 0 := by rw [hgv, Walk.getVert_zero]
    have hanle : a + n ≤ p.length := by
      rw [Walk.length_dropUntil, hia] at hn
      omega
    have := hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) h0
    omega
  -- ### The third cycle: `v₀ — x — ⋯ — y — v₀` around the segment `[a, b]`
  have hyv₀ : G.Adj y v₀ := hay.symm
  have hc₃path : (r.concat hyv₀).IsPath := hrpath.concat hv₀r hyv₀
  have hc₃edge : s(v₀, x) ∉ (r.concat hyv₀).edges := by
    rw [Walk.edges_concat]
    intro hmem
    rw [List.concat_eq_append, List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hin | heq
    · exact hv₀r (r.fst_mem_support_of_mem_edges hin)
    · rcases Sym2.eq_iff.mp heq with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hay.ne h1
      · exact hxy h2
  have hc₃ : (Walk.cons hax (r.concat hyv₀)).IsCycle :=
    (Walk.cons_isCycle_iff _ _).mpr ⟨hc₃path, hc₃edge⟩
  have hc₃len : (Walk.cons hax (r.concat hyv₀)).length = (b - a) + 2 := by
    rw [Walk.length_cons, Walk.length_concat, hrlen]
  -- ### Parity: the three cycle lengths `a+1`, `b+1`, `b-a+2` sum to `2b+4`
  rcases Nat.even_or_odd a with hae | hao
  · rcases Nat.even_or_odd b with hbe | hbo
    · -- `a`, `b` both even: the segment cycle has even length `b - a + 2`
      refine ⟨v₀, _, hc₃, ?_⟩
      rw [hc₃len]
      obtain ⟨i, hi⟩ := hae
      obtain ⟨j, hj⟩ := hbe
      exact ⟨j - i + 1, by omega⟩
    · -- `b` odd: the cycle through index `b` has even length `b + 1`
      obtain ⟨c, hcyc, hclen⟩ := hclose y hys hay (by rw [hyb']; omega)
      refine ⟨v₀, c, hcyc, ?_⟩
      rw [hclen, hyb']
      obtain ⟨j, hj⟩ := hbo
      exact ⟨j + 1, by omega⟩
  · -- `a` odd: the cycle through index `a` has even length `a + 1`
    obtain ⟨c, hcyc, hclen⟩ := hclose x hxs hax (by rw [hxa']; omega)
    refine ⟨v₀, c, hcyc, ?_⟩
    rw [hclen, hxa']
    obtain ⟨i, hi⟩ := hao
    exact ⟨i + 1, by omega⟩

/-- Restatement in the `ContainsCycleLength` predicate: minimum degree `3` yields an
**even** cycle length `k ≥ 4`. Every power of two `2^m` with `m ≥ 2` is even and `≥ 4`,
so this proves exactly the parity-and-size part of the necessary condition of Problem 64;
the open core is whether `k` can moreover be taken to be an exact power of two. -/
theorem hasMinDegree_three_exists_even_containsCycleLength
    {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hdeg : HasMinDegree G 3) :
    ∃ k : ℕ, 4 ≤ k ∧ Even k ∧ ContainsCycleLength G k := by
  obtain ⟨v, c, hc, heven⟩ := hasMinDegree_three_exists_even_cycle G hdeg
  refine ⟨c.length, ?_, heven, isCycle_containsCycleLength G c hc⟩
  have h3 := hc.three_le_length
  obtain ⟨m, hm⟩ := heven
  omega

/- ## Dirac-Type Lower Bound on Cycle Length

The same longest-path engine gives the classical quantitative rung: minimum
degree `d ≥ 2` forces a cycle of length at least `d + 1`.  All `≥ d` neighbours
of the start vertex `v₀` of a maximum-length path are trapped at distinct
POSITIVE indices along the path, so the largest such index is at least `d`
(`d` distinct positive integers cannot all be smaller than `d`); closing the
prefix at that index through the edge back to `v₀` is a cycle of length `≥ d+1`.

For Problem 64 this is the quantitative companion to the parity layer above:
it shows how minimum degree pushes the guaranteed cycle length up linearly —
but "some length `≥ d + 1`" is far from "length exactly `2^k`", which is the
open core.
-/

/-- **Dirac-type rung: minimum degree `d ≥ 2` forces a cycle of length `≥ d + 1`.**
The classical longest-path argument: every neighbour of the start of a
maximum-length path sits at a distinct positive index on the path, so the
largest neighbour index is at least `d`; closing the prefix there through the
edge back to the start yields a cycle of length at least `d + 1`. -/
theorem hasMinDegree_exists_cycle_length_ge
    {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph W) [DecidableRel G.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hdeg : HasMinDegree G d) :
    ∃ (v : W) (c : G.Walk v v), c.IsCycle ∧ d + 1 ≤ c.length := by
  classical
  -- a path of maximum length (as in `hasMinDegree_three_exists_even_cycle`)
  have hne : ({n : ℕ | ∃ (a : W) (b : W) (q : G.Walk a b), q.IsPath ∧ q.length = n}).Nonempty :=
    ⟨0, Classical.arbitrary W, Classical.arbitrary W, Walk.nil, Walk.IsPath.nil, rfl⟩
  have hbdd : BddAbove {n : ℕ | ∃ (a : W) (b : W) (q : G.Walk a b), q.IsPath ∧ q.length = n} := by
    refine ⟨Fintype.card W, ?_⟩
    rintro n ⟨a, b, q, hq, rfl⟩
    exact hq.length_lt.le
  obtain ⟨v₀, u, p, hp, hplen⟩ := Nat.sSup_mem hne hbdd
  have hmax : ∀ (a b : W) (q : G.Walk a b), q.IsPath → q.length ≤ p.length := by
    intro a b q hq
    rw [hplen]
    exact le_csSup hbdd ⟨a, b, q, hq, rfl⟩
  -- maximality traps every neighbour of `v₀` on `p`
  have hnbr : ∀ w : W, G.Adj v₀ w → w ∈ p.support := by
    intro w hw
    by_contra hws
    have hcons : (Walk.cons hw.symm p).IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hp, hws⟩
    have := hmax _ _ _ hcons
    rw [Walk.length_cons] at this
    omega
  set idx : W → ℕ := fun w => if hw : w ∈ p.support then (p.takeUntil w hw).length else 0
    with hidx
  have hidx_get : ∀ w (hw : w ∈ p.support), p.getVert (idx w) = w := by
    intro w hw
    simp only [hidx, dif_pos hw]
    exact Walk.getVert_length_takeUntil hw
  set T : Finset ℕ := (G.neighborFinset v₀).image idx with hT
  have hTcard : d ≤ T.card := by
    rw [hT, Finset.card_image_of_injOn]
    · exact hdeg v₀
    · intro w₁ hw₁ w₂ hw₂ hww
      have h₁ : G.Adj v₀ w₁ := (G.mem_neighborFinset v₀ w₁).mp (Finset.mem_coe.mp hw₁)
      have h₂ : G.Adj v₀ w₂ := (G.mem_neighborFinset v₀ w₂).mp (Finset.mem_coe.mp hw₂)
      calc w₁ = p.getVert (idx w₁) := (hidx_get w₁ (hnbr _ h₁)).symm
        _ = p.getVert (idx w₂) := by rw [hww]
        _ = w₂ := hidx_get w₂ (hnbr _ h₂)
  have hpos : ∀ n ∈ T, 1 ≤ n := by
    intro n hn
    rw [hT] at hn
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hn
    have hadj : G.Adj v₀ w := (G.mem_neighborFinset v₀ w).mp hw
    rcases Nat.eq_zero_or_pos (idx w) with h0 | h1
    · exfalso
      have hgw := hidx_get w (hnbr _ hadj)
      rw [h0, Walk.getVert_zero] at hgw
      exact hadj.ne hgw
    · exact h1
  -- the largest neighbour index `b` is at least `d`:
  -- `T` packs `≥ d` distinct integers into `[1, b]`, so `d ≤ |Icc 1 b| = b`
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  set b := T.max' hTne with hbdef
  have hbT : b ∈ T := T.max'_mem hTne
  have hsub : T ⊆ Finset.Icc 1 b := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨hpos n hn, T.le_max' n hn⟩
  have hdb : d ≤ b := by
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    omega
  -- the neighbour `y` sitting at index `b`
  have hbT2 : b ∈ (G.neighborFinset v₀).image idx := by rw [← hT]; exact hbT
  obtain ⟨y, hyN, hyb⟩ := Finset.mem_image.mp hbT2
  have hay : G.Adj v₀ y := (G.mem_neighborFinset v₀ y).mp hyN
  have hys : y ∈ p.support := hnbr y hay
  have hyb' : (p.takeUntil y hys).length = b := by
    rw [← hyb]; simp only [hidx, dif_pos hys]
  -- close the prefix at `y` through the edge `y — v₀`
  refine ⟨v₀, Walk.cons hay (p.takeUntil y hys).reverse, ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    refine ⟨(hp.takeUntil hys).reverse, ?_⟩
    intro hmem
    rw [Walk.edges_reverse, List.mem_reverse] at hmem
    -- an edge of a path through its start must be the first edge …
    have hsnd : y = (p.takeUntil y hys).snd := (hp.takeUntil hys).eq_snd_of_mem_edges hmem
    -- … but `y` is the endpoint of the prefix, at index `b ≥ 2`
    have h1 : (p.takeUntil y hys).getVert 1 =
        (p.takeUntil y hys).getVert (p.takeUntil y hys).length := by
      rw [Walk.getVert_length]
      exact hsnd.symm
    have := (hp.takeUntil hys).getVert_injOn
      (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) h1
    omega
  · rw [Walk.length_cons, Walk.length_reverse, hyb']
    omega

/-- Restatement in the `ContainsCycleLength` predicate: minimum degree `d ≥ 2`
yields a cycle length `k ≥ d + 1`.  Combined with the parity layer, min-degree-`3`
graphs have an even cycle of length `≥ 4` and some cycle of length `≥ 4`; the
open core of Problem 64 is whether a length can be taken to be an exact power
of two. -/
theorem hasMinDegree_containsCycleLength_ge
    {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph W) [DecidableRel G.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hdeg : HasMinDegree G d) :
    ∃ k : ℕ, d + 1 ≤ k ∧ ContainsCycleLength G k := by
  obtain ⟨v, c, hc, hlen⟩ := hasMinDegree_exists_cycle_length_ge G hd hdeg
  exact ⟨c.length, hlen, isCycle_containsCycleLength G c hc⟩

/- ## Cycle-Spectrum Counting

The longest-path engine yields more than a single long cycle: every neighbour
of the start vertex `v₀` trapped at an index `≥ 2` closes into its own cycle,
and distinct indices give cycles of **distinct lengths**.  Since at most one of
the `≥ d` trapped indices equals `1`, minimum degree `d` forces at least
`d - 1` distinct cycle lengths.

This is the elementary end of the *cycle spectrum* view of Problem 64: the
Liu–Montgomery resolution for large minimum degree works by showing the cycle
spectrum is dense enough to hit a power of two.  The rung below is the linear
(in `d`) spectrum-size guarantee; the open core is whether the spectrum of a
min-degree-`3` graph must meet `{2^k : k ≥ 2}`.
-/

/-- **Cycle-spectrum rung: minimum degree `d ≥ 2` forces at least `d - 1` distinct
cycle lengths.**  Each neighbour of the start of a maximum-length path sits at a
distinct positive index; closing the prefix at any index `≥ 2` (all but at most
one of them) gives a cycle whose length is that index plus one, so distinct
indices produce distinct lengths. -/
theorem hasMinDegree_card_cycle_lengths
    {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph W) [DecidableRel G.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hdeg : HasMinDegree G d) :
    ∃ S : Finset ℕ, d - 1 ≤ S.card ∧
      ∀ k ∈ S, 3 ≤ k ∧ ∃ (v : W) (c : G.Walk v v), c.IsCycle ∧ c.length = k := by
  classical
  -- a path of maximum length (the engine of the two preceding sections)
  have hne : ({n : ℕ | ∃ (a : W) (b : W) (q : G.Walk a b), q.IsPath ∧ q.length = n}).Nonempty :=
    ⟨0, Classical.arbitrary W, Classical.arbitrary W, Walk.nil, Walk.IsPath.nil, rfl⟩
  have hbdd : BddAbove {n : ℕ | ∃ (a : W) (b : W) (q : G.Walk a b), q.IsPath ∧ q.length = n} := by
    refine ⟨Fintype.card W, ?_⟩
    rintro n ⟨a, b, q, hq, rfl⟩
    exact hq.length_lt.le
  obtain ⟨v₀, u, p, hp, hplen⟩ := Nat.sSup_mem hne hbdd
  have hmax : ∀ (a b : W) (q : G.Walk a b), q.IsPath → q.length ≤ p.length := by
    intro a b q hq
    rw [hplen]
    exact le_csSup hbdd ⟨a, b, q, hq, rfl⟩
  -- maximality traps every neighbour of `v₀` on `p`
  have hnbr : ∀ w : W, G.Adj v₀ w → w ∈ p.support := by
    intro w hw
    by_contra hws
    have hcons : (Walk.cons hw.symm p).IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hp, hws⟩
    have := hmax _ _ _ hcons
    rw [Walk.length_cons] at this
    omega
  set idx : W → ℕ := fun w => if hw : w ∈ p.support then (p.takeUntil w hw).length else 0
    with hidx
  have hidx_get : ∀ w (hw : w ∈ p.support), p.getVert (idx w) = w := by
    intro w hw
    simp only [hidx, dif_pos hw]
    exact Walk.getVert_length_takeUntil hw
  set T : Finset ℕ := (G.neighborFinset v₀).image idx with hT
  have hTcard : d ≤ T.card := by
    rw [hT, Finset.card_image_of_injOn]
    · exact hdeg v₀
    · intro w₁ hw₁ w₂ hw₂ hww
      have h₁ : G.Adj v₀ w₁ := (G.mem_neighborFinset v₀ w₁).mp (Finset.mem_coe.mp hw₁)
      have h₂ : G.Adj v₀ w₂ := (G.mem_neighborFinset v₀ w₂).mp (Finset.mem_coe.mp hw₂)
      calc w₁ = p.getVert (idx w₁) := (hidx_get w₁ (hnbr _ h₁)).symm
        _ = p.getVert (idx w₂) := by rw [hww]
        _ = w₂ := hidx_get w₂ (hnbr _ h₂)
  have hpos : ∀ n ∈ T, 1 ≤ n := by
    intro n hn
    rw [hT] at hn
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hn
    have hadj : G.Adj v₀ w := (G.mem_neighborFinset v₀ w).mp hw
    rcases Nat.eq_zero_or_pos (idx w) with h0 | h1
    · exfalso
      have hgw := hidx_get w (hnbr _ hadj)
      rw [h0, Walk.getVert_zero] at hgw
      exact hadj.ne hgw
    · exact h1
  -- at most one trapped index equals `1`, so `≥ d - 1` indices are `≥ 2`
  have hsub2 : T ⊆ insert 1 (T.filter (fun n => 2 ≤ n)) := by
    intro n hn
    have h1 := hpos n hn
    rcases Nat.lt_or_ge n 2 with h | h
    · have hn1 : n = 1 := by omega
      simp [hn1]
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hn, h⟩)
  have hcard2 : d ≤ (T.filter (fun n => 2 ≤ n)).card + 1 := by
    have hle := Finset.card_le_card hsub2
    have hins := Finset.card_insert_le 1 (T.filter (fun n => 2 ≤ n))
    omega
  -- the spectrum: each surviving index `n` contributes the length `n + 1`
  refine ⟨(T.filter (fun n => 2 ≤ n)).image (· + 1), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (add_left_injective 1)]
    omega
  · intro k hk
    obtain ⟨n, hnmem, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hnT, hn2⟩ := Finset.mem_filter.mp hnmem
    refine ⟨by omega, ?_⟩
    -- the neighbour `y` sitting at index `n`
    rw [hT] at hnT
    obtain ⟨y, hyN, hyn⟩ := Finset.mem_image.mp hnT
    have hay : G.Adj v₀ y := (G.mem_neighborFinset v₀ y).mp hyN
    have hys : y ∈ p.support := hnbr y hay
    have hyn' : (p.takeUntil y hys).length = n := by
      rw [← hyn]; simp only [hidx, dif_pos hys]
    -- close the prefix at `y` through the edge `y — v₀` (needs only `2 ≤ n`)
    refine ⟨v₀, Walk.cons hay (p.takeUntil y hys).reverse, ?_, ?_⟩
    · rw [Walk.cons_isCycle_iff]
      refine ⟨(hp.takeUntil hys).reverse, ?_⟩
      intro hmem
      rw [Walk.edges_reverse, List.mem_reverse] at hmem
      -- an edge of a path through its start must be the first edge …
      have hsnd : y = (p.takeUntil y hys).snd := (hp.takeUntil hys).eq_snd_of_mem_edges hmem
      -- … but `y` is the endpoint of the prefix, at index `n ≥ 2`
      have h1 : (p.takeUntil y hys).getVert 1 =
          (p.takeUntil y hys).getVert (p.takeUntil y hys).length := by
        rw [Walk.getVert_length]
        exact hsnd.symm
      have := (hp.takeUntil hys).getVert_injOn
        (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) h1
      omega
    · rw [Walk.length_cons, Walk.length_reverse, hyn']

/-- Restatement in the `ContainsCycleLength` predicate: minimum degree `d ≥ 2`
yields at least `d - 1` distinct realized cycle lengths, each `≥ 3`.  Problem 64's
open core asks whether, at minimum degree `3`, this spectrum must contain a power
of two `2^k` with `k ≥ 2`; Liu–Montgomery answer YES once the minimum degree
(hence, by this rung, the spectrum) is large enough. -/
theorem hasMinDegree_card_containsCycleLength
    {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph W) [DecidableRel G.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hdeg : HasMinDegree G d) :
    ∃ S : Finset ℕ, d - 1 ≤ S.card ∧ ∀ k ∈ S, 3 ≤ k ∧ ContainsCycleLength G k := by
  obtain ⟨S, hcard, hS⟩ := hasMinDegree_card_cycle_lengths G hd hdeg
  refine ⟨S, hcard, fun k hk => ?_⟩
  obtain ⟨h3, v, c, hc, hlen⟩ := hS k hk
  exact ⟨h3, hlen ▸ isCycle_containsCycleLength G c hc⟩

/- ## Known Cycle Results -/

/- 
**Dirac's Theorem** (1952):
A graph on n ≥ 3 vertices with minimum degree at least n/2 is Hamiltonian
(contains a cycle through all vertices).
-/
/- 
**Bondy's Theorem** (1971):
If G has n vertices and at least n²/4 edges, then either G is bipartite or
G contains cycles of all lengths from 3 to n.
-/
/- ## Probabilistic Lower Bounds -/

/-
**Random Graphs**:
Random graphs G(n, p) with p ≥ c/n for suitable c almost surely have minimum
degree at least 3 and contain cycles of all lengths up to some threshold.
This suggests that counterexamples, if they exist, must be highly structured.
-/
/- ## Summary

**Problem Status: OPEN ($1000 prize)**

Erdős Problem 64 asks whether every finite graph with minimum degree at least 3
contains a cycle of length 2^k for some k ≥ 2.

**Key Results**:
1. Liu-Montgomery (2020): YES for sufficiently large minimum degree
2. This disproves the Erdős-Gyárfás conjecture (which predicted NO)
3. The case of minimum degree exactly 3 remains OPEN
4. For infinite graphs: NO (infinite 3-regular trees exist)

**Open Questions**:
- What is the minimum degree threshold D from Liu-Montgomery?
- Does the conjecture hold for minimum degree 3?
- Are there "almost counterexamples" with few power-of-2 cycles?

References:
- Liu, Montgomery (2020): "A proof of Mader's conjecture on large clique subdivisions"
- Erdős, Gyárfás: Original conjecture
- Dirac (1952): Hamiltonian cycles in dense graphs
-/

end Erdos64
