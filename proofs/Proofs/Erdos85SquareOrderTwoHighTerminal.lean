import Proofs.Erdos85SquareOrderDefectNeighborhoodDesign

/-!
# The parity terminal behind the two-high square-order profile

The exact order-64 scout exposed a short uniform endpoint.  A saturated
high-root class of even size `q`, after deleting its unique point in the miss
set, would induce a one-regular graph on `q-1` vertices.  Handshaking forbids
that odd order.

This file proves the abstract terminal.  Applying it to the square-order
two-high profile only requires the preceding owner-count argument that
identifies the miss set and its unique point in the high-root class.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The induced degree on a finite vertex set is the cardinality of the
ambient neighbor set intersected with that vertex set. -/
theorem degree_induce_finset_eq_card_inter
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    (x : ↥(↑A : Set V)) :
    (G.induce (↑A : Set V)).degree x =
      (G.neighborFinset x.1 ∩ A).card := by
  classical
  rw [← (G.induce (↑A : Set V)).card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun y _ => y.1)
  · intro y hy
    have hxy : G.Adj x.1 y.1 := by
      exact ((G.induce (↑A : Set V)).mem_neighborFinset x y).mp hy
    exact Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset x.1 y.1).mpr hxy, Finset.mem_coe.mp y.2⟩
  · intro y₁ _ y₂ _ heq
    exact Subtype.ext heq
  · intro y hy
    have hy' := Finset.mem_inter.mp hy
    refine ⟨⟨y, Finset.mem_coe.mpr hy'.2⟩, ?_, rfl⟩
    exact ((G.induce (↑A : Set V)).mem_neighborFinset _ _).mpr
      ((G.mem_neighborFinset x.1 y).mp hy'.1)

/-- A finite simple graph that is one-regular on a vertex set has an even
number of vertices. -/
theorem even_card_of_card_neighbors_inter_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    (hone : ∀ x ∈ A, (G.neighborFinset x ∩ A).card = 1) :
    Even A.card := by
  classical
  let H := G.induce (↑A : Set V)
  have hdegree : ∀ x : ↥(↑A : Set V), H.degree x = 1 := by
    intro x
    exact (degree_induce_finset_eq_card_inter G A x).trans (hone x.1 x.2)
  have hsum : ∑ x : ↥(↑A : Set V), H.degree x = A.card := by
    simp_rw [hdegree]
    simp
  have hhand := H.sum_degrees_eq_twice_card_edges
  rw [hsum] at hhand
  exact ⟨H.edgeFinset.card, by omega⟩

/-- Abstract even-order saturation terminal.  If `A` has even size, `S` is a
miss set meeting `A` only at `p`, no point of `S` is adjacent into `A`, and
every point of the ambient low set outside `S` has exactly one neighbor in
`A`, then deleting `p` makes `A` one-regular on an odd number of vertices. -/
theorem false_of_even_highRoot_saturation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (heven : Even q) (L A S : Finset V) (p : V)
    (hAcard : A.card = q) (hpA : p ∈ A) (hpS : p ∈ S)
    (hinter : A ∩ S = {p}) (hAsub : A ⊆ L)
    (hno : ∀ s ∈ S, ∀ a ∈ A, ¬ G.Adj s a)
    (hone : ∀ y ∈ L \ S, (G.neighborFinset y ∩ A).card = 1) :
    False := by
  classical
  let T := A.erase p
  have hTcard : T.card + 1 = q := by
    have hApos : 0 < A.card := Finset.card_pos.mpr ⟨p, hpA⟩
    dsimp [T]
    rw [Finset.card_erase_of_mem hpA]
    omega
  have hToutside : ∀ y ∈ T, y ∈ L \ S := by
    intro y hy
    have hyA : y ∈ A := (Finset.mem_erase.mp hy).2
    have hyp : y ≠ p := (Finset.mem_erase.mp hy).1
    refine Finset.mem_sdiff.mpr ⟨hAsub hyA, ?_⟩
    intro hyS
    have : y ∈ ({p} : Finset V) := by
      rw [← hinter]
      exact Finset.mem_inter.mpr ⟨hyA, hyS⟩
    exact hyp (Finset.mem_singleton.mp this)
  have hinterEq : ∀ y ∈ T,
      G.neighborFinset y ∩ T = G.neighborFinset y ∩ A := by
    intro y hy
    ext z
    constructor
    · intro hz
      have hz' := Finset.mem_inter.mp hz
      exact Finset.mem_inter.mpr ⟨hz'.1, (Finset.mem_erase.mp hz'.2).2⟩
    · intro hz
      have hz' := Finset.mem_inter.mp hz
      refine Finset.mem_inter.mpr ⟨hz'.1, Finset.mem_erase.mpr ⟨?_, hz'.2⟩⟩
      intro hzp
      subst z
      have hyA : y ∈ A := (Finset.mem_erase.mp hy).2
      exact (hno p hpS y hyA)
        ((G.adj_comm y p).mp ((G.mem_neighborFinset y p).mp hz'.1))
  have hTone : ∀ y ∈ T, (G.neighborFinset y ∩ T).card = 1 := by
    intro y hy
    rw [hinterEq y hy]
    exact hone y (hToutside y hy)
  have hTeven := even_card_of_card_neighbors_inter_eq_one G T hTone
  obtain ⟨a, ha⟩ := heven
  obtain ⟨b, hb⟩ := hTeven
  omega

/-- At square order, the existence of a degree-`q+1` vertex forces `q` odd.
The zero-slack high-root theorem makes its open neighborhood one-regular, so
handshaking makes the neighborhood size `q+1` even. -/
theorem squareOrder_degree_succ_forces_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 2 ≤ q)
    (hmin : ∀ x : V, q ≤ G.degree x)
    (hcard : Fintype.card V = q * q) {v : V}
    (hv : G.degree v = q + 1) :
    Odd q := by
  let H := G.induce (G.neighborSet v)
  have hlocal :=
    (squareOrder_degree_succ_highRoot_structure
      G hfree hq hmin hcard hv).2.2
  have hsum : ∑ x : {z : V // z ∈ G.neighborSet v}, H.degree x = q + 1 := by
    calc
      (∑ x : {z : V // z ∈ G.neighborSet v}, H.degree x) =
          ∑ _x : {z : V // z ∈ G.neighborSet v}, 1 := by
        apply Finset.sum_congr rfl
        intro x _
        exact hlocal x
      _ = Fintype.card {z : V // z ∈ G.neighborSet v} := by simp
      _ = G.degree v := by
        rw [Fintype.card_subtype]
        have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet v) =
            G.neighborFinset v := by ext z; simp
        rw [heq, G.card_neighborFinset_eq_degree]
      _ = q + 1 := hv
  have hhand := H.sum_degrees_eq_twice_card_edges
  rw [hsum] at hhand
  obtain ⟨k, hk⟩ : Even (q + 1) :=
    ⟨H.edgeFinset.card, by omega⟩
  refine ⟨k - 1, ?_⟩
  omega

/-- Consequently an even square-order candidate has no degree-`q+1` vertex. -/
theorem squareOrder_no_degree_succ_of_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 2 ≤ q) (heven : Even q)
    (hmin : ∀ x : V, q ≤ G.degree x)
    (hcard : Fintype.card V = q * q) (v : V) :
    G.degree v ≠ q + 1 := by
  intro hv
  have hodd := squareOrder_degree_succ_forces_odd
    G hfree hq hmin hcard hv
  obtain ⟨a, ha⟩ := heven
  obtain ⟨b, hb⟩ := hodd
  omega

/-- **Uniform even square-order nonregular exclusion.**  Under the tight-edge
cover, every degree is `q` or `q+1`; the preceding parity terminal removes the
second case for even `q`, so the graph is regular. -/
theorem squareOrder_regular_of_even_tightEdgeCover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 2 ≤ q) (heven : Even q)
    (hmin : ∀ x : V, q ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = q ∨ G.degree v = q)
    (hcard : Fintype.card V = q * q) :
    ∀ x : V, G.degree x = q := by
  intro x
  rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
    G hfree hq hmin hcover hcard x with hx | hx
  · exact hx
  · exact (squareOrder_no_degree_succ_of_even
      G hfree hq heven hmin hcard x hx).elim

end

end Erdos85
