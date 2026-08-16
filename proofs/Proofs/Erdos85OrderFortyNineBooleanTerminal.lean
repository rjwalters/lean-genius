import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Batteries.Data.BitVec.Lemmas
import Proofs.Erdos85OrderFortyNineSupportPartitions

/-!
# Kernel-checkable Boolean terminal for the order-49 branch

This file gives a compact, label-level encoding of a graph on 49 vertices.
Only the `choose(49,2) = 1176` unordered edge bits are stored.  Symmetry and
looplessness are therefore true by construction.  The remaining conditions
are exactly those used by the independently generated DIMACS instances:

* the prescribed high-support of every vertex;
* degrees eight on the initial high segment and seven elsewhere;
* at most one common neighbor for every two distinct vertices;
* every low neighborhood meets every high neighborhood.

The final condition is the graph-facing support-partition law.  Its
uniqueness is already implied by the common-neighbor bound.
-/

namespace Erdos85

open SimpleGraph

set_option maxRecDepth 100000

/-- Zero-based position of `{i,j}` in the lexicographic list of the 1176
unordered pairs from `Fin 49`, for `i ≠ j`. -/
def orderFortyNineEdgeIndex (i j : Fin 49) : Nat :=
  let a := min i.val j.val
  let b := max i.val j.val
  1176 - ((49 - a) * (48 - a) / 2) + (b - a) - 1

/-- Symmetric loopless adjacency read from the 1176 unordered edge bits. -/
def orderFortyNineBitAdj (edges : BitVec 1176) (i j : Fin 49) : Bool :=
  if i = j then false else edges.getLsbD (orderFortyNineEdgeIndex i j)

/-- Number of unordered pairs of `Fin 49` whose smaller element is below `a`;
the position at which row `a` of the lexicographic pair list begins. -/
def orderFortyNineRowStart (a : Nat) : Nat := 1176 - (49 - a) * (48 - a) / 2

/-- Consecutive row starts differ by exactly the row length `48 - a`.
Finite arithmetic over `Fin 49`, checked by the kernel. -/
theorem orderFortyNineRowStart_succ (a : Fin 49) :
    orderFortyNineRowStart (a.val + 1) = orderFortyNineRowStart a.val + (48 - a.val) := by
  revert a; decide

theorem orderFortyNineRowStart_le (a : Fin 49) :
    orderFortyNineRowStart a.val ≤ 1176 := by
  revert a; decide

/-- Rows are laid out in increasing order: the row after `a` starts no later
than any row `b > a`. -/
theorem orderFortyNineRowStart_mono (a b : Fin 49) (h : a < b) :
    orderFortyNineRowStart (a.val + 1) ≤ orderFortyNineRowStart b.val := by
  revert a b; decide

/-- Lex rank of an ordered pair `i < j`: row start plus offset within the row. -/
theorem orderFortyNineEdgeIndex_eq_rowStart (i j : Fin 49) (h : i.val < j.val) :
    orderFortyNineEdgeIndex i j = orderFortyNineRowStart i.val + (j.val - i.val - 1) := by
  unfold orderFortyNineEdgeIndex orderFortyNineRowStart
  have h1 : min i.val j.val = i.val := Nat.min_eq_left h.le
  have h2 : max i.val j.val = j.val := Nat.max_eq_right h.le
  simp only [h1, h2]
  have := orderFortyNineRowStart_le i
  unfold orderFortyNineRowStart at this
  omega

theorem orderFortyNineEdgeIndex_comm (i j : Fin 49) :
    orderFortyNineEdgeIndex i j = orderFortyNineEdgeIndex j i := by
  unfold orderFortyNineEdgeIndex
  rw [Nat.min_comm, Nat.max_comm]

/-- Injectivity of the lex rank on ordered pairs `i < j`: distinct rows occupy
disjoint index intervals, and within a row the offset determines `j`. -/
theorem orderFortyNineEdgeIndex_inj_of_lt (i j k l : Fin 49)
    (hij : i.val < j.val) (hkl : k.val < l.val)
    (h : orderFortyNineEdgeIndex i j = orderFortyNineEdgeIndex k l) :
    i = k ∧ j = l := by
  rw [orderFortyNineEdgeIndex_eq_rowStart i j hij,
    orderFortyNineEdgeIndex_eq_rowStart k l hkl] at h
  have hik : i = k := by
    rcases lt_trichotomy i k with hlt | heq | hgt
    · exfalso
      have h1 := orderFortyNineRowStart_mono i k hlt
      have h2 := orderFortyNineRowStart_succ i
      have := j.isLt
      omega
    · exact heq
    · exfalso
      have h1 := orderFortyNineRowStart_mono k i hgt
      have h2 := orderFortyNineRowStart_succ k
      have := l.isLt
      omega
  subst hik
  refine ⟨rfl, Fin.ext ?_⟩
  omega

/-- The edge index is in range away from the diagonal.  Standard-axiom proof:
the index lies below the start of the next row, which is at most `1176`. -/
theorem orderFortyNineEdgeIndex_lt
    (i j : Fin 49) (hij : i ≠ j) : orderFortyNineEdgeIndex i j < 1176 := by
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · rw [orderFortyNineEdgeIndex_eq_rowStart i j h]
    have h1 := orderFortyNineRowStart_succ i
    have h2 : orderFortyNineRowStart (i.val + 1) ≤ 1176 := by
      rcases Nat.lt_or_ge (i.val + 1) 49 with hi | hi
      · exact orderFortyNineRowStart_le ⟨i.val + 1, hi⟩
      · have : i.val = 48 := by omega
        simp [orderFortyNineRowStart, this]
    have := j.isLt
    omega
  · rw [orderFortyNineEdgeIndex_comm, orderFortyNineEdgeIndex_eq_rowStart j i h]
    have h1 := orderFortyNineRowStart_succ j
    have h2 : orderFortyNineRowStart (j.val + 1) ≤ 1176 := by
      rcases Nat.lt_or_ge (j.val + 1) 49 with hj | hj
      · exact orderFortyNineRowStart_le ⟨j.val + 1, hj⟩
      · have : j.val = 48 := by omega
        simp [orderFortyNineRowStart, this]
    have := i.isLt
    omega

/-- Equality of edge indices is precisely equality of unordered pairs.
Standard-axiom proof via `orderFortyNineEdgeIndex_inj_of_lt` and symmetry. -/
theorem orderFortyNineEdgeIndex_eq_iff
    (i j k l : Fin 49) (hij : i ≠ j) (hkl : k ≠ l) :
    orderFortyNineEdgeIndex i j = orderFortyNineEdgeIndex k l ↔
      (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  constructor
  · intro h
    have hij' : i.val ≠ j.val := fun e => hij (Fin.ext e)
    have hkl' : k.val ≠ l.val := fun e => hkl (Fin.ext e)
    rcases Nat.lt_or_gt_of_ne hij' with h1 | h1 <;>
      rcases Nat.lt_or_gt_of_ne hkl' with h2 | h2
    · exact Or.inl (orderFortyNineEdgeIndex_inj_of_lt i j k l h1 h2 h)
    · rw [orderFortyNineEdgeIndex_comm k l] at h
      obtain ⟨e1, e2⟩ := orderFortyNineEdgeIndex_inj_of_lt i j l k h1 h2 h
      exact Or.inr ⟨e1, e2⟩
    · rw [orderFortyNineEdgeIndex_comm i j] at h
      obtain ⟨e1, e2⟩ := orderFortyNineEdgeIndex_inj_of_lt j i k l h1 h2 h
      exact Or.inr ⟨e2, e1⟩
    · rw [orderFortyNineEdgeIndex_comm i j, orderFortyNineEdgeIndex_comm k l] at h
      obtain ⟨e1, e2⟩ := orderFortyNineEdgeIndex_inj_of_lt j i l k h1 h2 h
      exact Or.inl ⟨e2, e1⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact orderFortyNineEdgeIndex_comm _ _

/-- Encode a labeled simple graph using exactly one bit per unordered pair. -/
def orderFortyNineGraphEdges
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] : BitVec 1176 :=
  BitVec.ofFnLE fun k => decide (∃ i j : Fin 49,
    i ≠ j ∧ orderFortyNineEdgeIndex i j = k.val ∧ G.Adj i j)

/-- Reading the encoded edge bits recovers graph adjacency exactly. -/
theorem orderFortyNineBitAdj_graphEdges
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] (i j : Fin 49) :
    orderFortyNineBitAdj (orderFortyNineGraphEdges G) i j = decide (G.Adj i j) := by
  by_cases hij : i = j
  · subst j
    simp [orderFortyNineBitAdj]
  · have hlt := orderFortyNineEdgeIndex_lt i j hij
    simp only [orderFortyNineBitAdj, hij, if_false, orderFortyNineGraphEdges,
      BitVec.getLsbD_ofFnLE]
    rw [dif_pos (by exact hlt)]
    apply Bool.decide_congr
    constructor
    · rintro ⟨k, l, hkl, hindex, hklAdj⟩
      rcases (orderFortyNineEdgeIndex_eq_iff k l i j hkl hij).mp hindex with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hklAdj
      · exact (G.adj_comm _ _).mp hklAdj
    · intro hadj
      exact ⟨i, j, hij, rfl, hadj⟩

/-- The 49-bit adjacency row of a vertex. -/
def orderFortyNineBitRow (edges : BitVec 1176) (i : Fin 49) : BitVec 49 :=
  BitVec.ofFnLE fun j : Fin 49 => orderFortyNineBitAdj edges i j

/-- The prescribed high-support masks, read as nine-bit vectors. -/
def orderFortyNineSupportMask (masks : Array Nat) (i : Fin 49) : BitVec 9 :=
  BitVec.ofNat 9 (masks.getD i.val 0)

/-- The 49-bit indicator of the vertices incident with high point `w`. -/
def orderFortyNineSupportColumn (masks : Array Nat) (w : Fin 9) : BitVec 49 :=
  BitVec.ofFnLE fun i : Fin 49 =>
    (orderFortyNineSupportMask masks i).getLsbD w.val

/-- Relation-level form of the terminal constraints.  Keeping this layer
separate makes the graph-to-CNF faithfulness theorem independent of the
particular edge-bit representation. -/
def orderFortyNineRelationConstraints
    (h : Nat) (masks : Array Nat) (adj : Fin 49 → Fin 49 → Bool) : Prop :=
  masks.size = 49 ∧ h ≤ 9 ∧
  (∀ i : Fin 49,
    (Finset.univ.filter fun j => adj i j).card =
      if i.val < h then 8 else 7) ∧
  (∀ i j : Fin 49, i ≠ j →
    (Finset.univ.filter fun k => adj i k && adj j k).card ≤ 1) ∧
  (∀ i : Fin 49, ∀ w : Fin 9, w.val < h →
    adj i ⟨w.val, by omega⟩ =
      (orderFortyNineSupportMask masks i).getLsbD w.val) ∧
  (∀ i : Fin 49, h ≤ i.val → ∀ w : Fin 9, w.val < h →
    (Finset.univ.filter fun k => adj i k &&
      (orderFortyNineSupportMask masks k).getLsbD w.val).card = 1)

/-- Boolean constraints common to every classified high-support instance. -/
def orderFortyNineBooleanConstraints
    (h : Nat) (masks : Array Nat) (edges : BitVec 1176) : Prop :=
  orderFortyNineRelationConstraints h masks (orderFortyNineBitAdj edges)

/-- A labeled graph satisfies the Boolean terminal exactly when its decided
adjacency relation satisfies the relation-level constraints. -/
theorem orderFortyNineBooleanConstraints_graphEdges_iff
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (h : Nat) (masks : Array Nat) :
    orderFortyNineBooleanConstraints h masks (orderFortyNineGraphEdges G) ↔
      orderFortyNineRelationConstraints h masks
        (fun i j => decide (G.Adj i j)) := by
  unfold orderFortyNineBooleanConstraints orderFortyNineRelationConstraints
  simp_rw [orderFortyNineBitAdj_graphEdges]

/-- The labeled vertices carrying high point `w` in a prescribed support
array. -/
def orderFortyNineSupportFiber (masks : Array Nat) (w : Fin 9) : Finset (Fin 49) :=
  Finset.univ.filter fun i =>
    (orderFortyNineSupportMask masks i).getLsbD w.val

/-- Graph-facing faithfulness theorem for the Boolean terminal.  The four
hypotheses correspond exactly to the structural layers proved before the
finite classification: degree stratification, C4-freeness, fixed high
supports, and the exact low-neighborhood partition law. -/
theorem orderFortyNineGraphEdges_satisfy
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (h : Nat) (masks : Array Nat)
    (hsize : masks.size = 49) (hh : h ≤ 9)
    (hdegree : ∀ i : Fin 49, G.degree i = if i.val < h then 8 else 7)
    (hfree : ¬ containsC4 (Fin 49) G)
    (hsupport : ∀ i : Fin 49, ∀ w : Fin 9, w.val < h →
      decide (G.Adj i ⟨w.val, by omega⟩) =
        (orderFortyNineSupportMask masks i).getLsbD w.val)
    (hpartition : ∀ i : Fin 49, h ≤ i.val → ∀ w : Fin 9, w.val < h →
      (G.neighborFinset i ∩ orderFortyNineSupportFiber masks w).card = 1) :
    orderFortyNineBooleanConstraints h masks (orderFortyNineGraphEdges G) := by
  rw [orderFortyNineBooleanConstraints_graphEdges_iff]
  refine ⟨hsize, hh, ?_, ?_, hsupport, ?_⟩
  · intro i
    simpa [SimpleGraph.degree, SimpleGraph.neighborFinset] using hdegree i
  · intro i j hij
    have hc := common_le_one_of_not_containsC4 hfree i j hij
    have heq : (Finset.univ.filter fun k =>
        decide (G.Adj i k) && decide (G.Adj j k)) =
        G.neighborFinset i ∩ G.neighborFinset j := by
      ext k
      simp [SimpleGraph.mem_neighborFinset, Bool.and_eq_true,
        decide_eq_true_eq]
    rw [heq]
    exact hc
  · intro i hi w hw
    have hp := hpartition i hi w hw
    have heq : (Finset.univ.filter fun k => decide (G.Adj i k) &&
        (orderFortyNineSupportMask masks k).getLsbD w.val) =
        G.neighborFinset i ∩ orderFortyNineSupportFiber masks w := by
      ext k
      simp [orderFortyNineSupportFiber, SimpleGraph.mem_neighborFinset,
        Bool.and_eq_true, decide_eq_true_eq]
    rw [heq]
    exact hp

/-- First canonical four-triple support system at `h=9`:
`012, 345, 367, 468`.  Vertices are ordered as in the certification
manifest: highs, triples, uncovered pairs, then singleton repetitions. -/
def orderFortyNineH9T4Rep0Masks : Array Nat :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0,
    7, 56, 200, 336,
    9, 17, 33, 65, 129, 257, 10, 18, 34, 66, 130, 258,
    12, 20, 36, 68, 132, 260, 264, 144, 96, 160, 288, 384,
    1, 2, 4, 8, 8, 16, 16, 32, 64, 64, 128, 256]

end Erdos85
