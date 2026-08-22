import Proofs.Erdos85BinarySquareAdjacencySquareAction
import Proofs.Erdos85BranchDeficitSymmetry
import Proofs.Erdos85C4FreeNeighborBlockPartition

/-!
# Sparse signed terminal for the binary square-order branch

This file formalizes the load-bearing algebraic core of the final dyadic
occupancy layer.  If a sign vector `x` satisfies `A x = q z`, then the exact
square-order identity transports it to a pointwise equation for the defect
graph.  The support and sign restrictions on `z` are separate combinatorial
inputs; this theorem certifies the matrix-to-defect transport they consume.
-/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Multiplying the adjacency matrix by the `±1` sign vector of a shore is
twice the local shore occupancy minus the degree. -/
theorem cutSign_adjMatrix_mulVec_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hreg : ∀ v, G.degree v = q)
    (S : Finset V) (v : V) :
    (G.adjMatrix ℤ).mulVec (fun w => if w ∈ S then (1 : ℤ) else -1) v =
      2 * ((G.neighborFinset v ∩ S).card : ℤ) - q := by
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  have hpoint (w : V) :
      (if w ∈ S then (1 : ℤ) else -1) =
        2 * (if w ∈ S then (1 : ℤ) else 0) - 1 := by
    by_cases hw : w ∈ S <;> simp [hw]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib]
  simp [G.card_neighborFinset_eq_degree, hreg]
  ring

/-- If every local shore occupancy is empty, balanced, or full, then the
shore sign vector has a sparse signed adjacency image.  The value `+1`
marks full lines, `-1` marks empty lines, and zero marks balanced lines. -/
theorem cutSign_adjMatrix_mulVec_eq_sparseSigned
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hq : 0 < q) (hreg : ∀ v, G.degree v = q)
    (S : Finset V)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      2 * (G.neighborFinset v ∩ S).card = q ∨
      (G.neighborFinset v ∩ S).card = q) :
    (G.adjMatrix ℤ).mulVec (fun w => if w ∈ S then (1 : ℤ) else -1) =
      (q : ℤ) • fun v =>
        if (G.neighborFinset v ∩ S).card = q then (1 : ℤ)
        else if (G.neighborFinset v ∩ S).card = 0 then -1 else 0 := by
  funext v
  rw [cutSign_adjMatrix_mulVec_apply G hreg S v]
  change
    2 * ((G.neighborFinset v ∩ S).card : ℤ) - q =
      (q : ℤ) *
        (if (G.neighborFinset v ∩ S).card = q then 1
         else if (G.neighborFinset v ∩ S).card = 0 then -1 else 0)
  rcases htri v with hzero | hhalf | hfull
  · have h0q : 0 ≠ q := by omega
    simp [hzero, h0q]
  · have hneZero : (G.neighborFinset v ∩ S).card ≠ 0 := by omega
    have hneFull : (G.neighborFinset v ∩ S).card ≠ q := by omega
    have hhalfZ :
        (2 : ℤ) * (G.neighborFinset v ∩ S).card = q := by
      exact_mod_cast hhalf
    simp [hneZero, hneFull, hhalfZ]
  · simp [hfull]
    ring

/-- The coordinate sum of a shore sign vector records its displacement from
half the ambient order. -/
theorem sum_cutSign
    {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) :
    ∑ v : V, (if v ∈ S then (1 : ℤ) else -1) =
      2 * (S.card : ℤ) - Fintype.card V := by
  have hpoint (v : V) :
      (if v ∈ S then (1 : ℤ) else -1) =
        2 * (if v ∈ S then (1 : ℤ) else 0) - 1 := by
    by_cases hv : v ∈ S <;> simp [hv]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib]
  simp
  ring

/-- The sparse signed equation `A x = q z`, together with the coordinate sum
of `x`, gives the companion defect equation pointwise. -/
theorem binarySquare_sparseSigned_companionDefect_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ v, G.degree v = q)
    (x z : V → ℤ) (d : ℤ)
    (hAx : (G.adjMatrix ℤ).mulVec x = (q : ℤ) • z)
    (hsum : ∑ v, x v = 2 * d) (v : V) :
    ∑ w ∈ (secondOrderDefectGraph G).neighborFinset v, x w =
      ((q : ℤ) - 1) * x v + 2 * d -
        (q : ℤ) * ∑ w ∈ G.neighborFinset v, z w := by
  have hsq := binarySquare_regular_adjMatrix_sq_mulVec_apply
    G hfree hreg x v
  have hAA := congrArg (fun u => (G.adjMatrix ℤ).mulVec u) hAx
  have hleft :
      ((G.adjMatrix ℤ * G.adjMatrix ℤ) *ᵥ x) v =
        (q : ℤ) * ∑ w ∈ G.neighborFinset v, z w := by
    rw [← Matrix.mulVec_mulVec]
    calc
      (G.adjMatrix ℤ).mulVec ((G.adjMatrix ℤ).mulVec x) v =
          (G.adjMatrix ℤ).mulVec ((q : ℤ) • z) v := by
            rw [hAx]
      _ = (q : ℤ) * ∑ w ∈ G.neighborFinset v, z w := by
            rw [Matrix.mulVec_smul]
            simp [SimpleGraph.adjMatrix_mulVec_apply]
  rw [hsum] at hsq
  linarith

/-- Capstone form: an empty/half/full occupancy shore at square order obeys
the canonical sparse signed defect equation, with `d` its displacement from
half the vertex set. -/
theorem binarySquare_trichotomy_companionDefect_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 0 < q)
    (hreg : ∀ v, G.degree v = q) (hcard : Fintype.card V = q * q)
    (S : Finset V) (d : ℤ)
    (hd : 2 * (S.card : ℤ) - (q * q : ℕ) = 2 * d)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      2 * (G.neighborFinset v ∩ S).card = q ∨
      (G.neighborFinset v ∩ S).card = q)
    (v : V) :
    ∑ w ∈ (secondOrderDefectGraph G).neighborFinset v,
        (if w ∈ S then (1 : ℤ) else -1) =
      ((q : ℤ) - 1) * (if v ∈ S then (1 : ℤ) else -1) + 2 * d -
        (q : ℤ) * ∑ w ∈ G.neighborFinset v,
          (if (G.neighborFinset w ∩ S).card = q then (1 : ℤ)
           else if (G.neighborFinset w ∩ S).card = 0 then -1 else 0) := by
  let x : V → ℤ := fun w => if w ∈ S then 1 else -1
  let z : V → ℤ := fun w =>
    if (G.neighborFinset w ∩ S).card = q then 1
    else if (G.neighborFinset w ∩ S).card = 0 then -1 else 0
  have hAx : (G.adjMatrix ℤ).mulVec x = (q : ℤ) • z := by
    simpa [x, z] using
      cutSign_adjMatrix_mulVec_eq_sparseSigned G hq hreg S htri
  have hsum : ∑ w, x w = 2 * d := by
    rw [show (∑ w, x w) = 2 * (S.card : ℤ) - Fintype.card V by
      simpa [x] using sum_cutSign S]
    rw [hcard]
    exact hd
  simpa [x, z] using
    binarySquare_sparseSigned_companionDefect_apply
      G hfree hreg x z d hAx hsum v

/-- Arithmetic capstone behind the mixed exceptional-support bound.  At
`q = 4m`, write the two line-type sizes as `u` and `u + 2a`; the minority
replication bound and the complete bipartite defect core force total support
at most `3q/2 - 2 = 6m - 2`. -/
theorem binarySquare_mixedExceptional_card_le
    {m a u c : ℕ} (hm : 1 ≤ m)
    (hc : c = 2 * (u + a))
    (huBalanced : a = 0 → u ≤ 2 * m)
    (huUnbalanced : 0 < a → u ≤ 2 * m - 1)
    (hcore : u + 2 * a ≤ 4 * m - 1) :
    c ≤ 6 * m - 2 := by
  by_cases ha : a = 0
  · have hu := huBalanced ha
    omega
  · have haPos : 0 < a := Nat.pos_of_ne_zero ha
    have hu := huUnbalanced haPos
    omega

/-- Arithmetic terminal for the large pure exceptional branch.  If every
shore point has exceptional replication two or three, incidence balance and
the linear-design pair bound are incompatible with `q < c ≤ 2q-2` once
`q ≥ 8`.  The variables `n₂,n₃` count the two replication classes. -/
theorem binarySquare_pureLargeExceptional_impossible
    {q c s n₂ n₃ : ℕ} (hq : 8 ≤ q) (hqc : q < c)
    (hc : c ≤ 2 * q - 2)
    (hshore : 2 * s = q * q + c)
    (hclasses : n₂ + n₃ = s)
    (hincidence : 2 * n₂ + 3 * n₃ = q * c)
    (hpairs : 2 * n₂ + 6 * n₃ ≤ c * (c - 1)) : False := by
  have hcpos : 1 ≤ c := by omega
  have hcsub : c - 1 + 1 = c := Nat.sub_add_cancel hcpos
  have hcupper : c + 2 ≤ 2 * q := by omega
  have hcprod : c * (c - 1) + c = c * c := by
    calc
      c * (c - 1) + c = c * ((c - 1) + 1) := by ring
      _ = c * c := by rw [hcsub]
  have hn₃ : n₃ + q * q + c = q * c := by omega
  have hpoly : 4 * q * c ≤ 3 * q * q + c * c + 2 * c := by
    nlinarith
  let r := c - q
  have hcr : c = q + r := by
    dsimp [r]
    omega
  have hrupper : r ≤ q - 2 := by omega
  have hn₃r : n₃ + q + r = q * r := by
    rw [hcr] at hn₃
    nlinarith
  have hr : 2 ≤ r := by
    by_contra h
    have : r ≤ 1 := by omega
    interval_cases r <;> simp at hn₃r <;> omega
  rw [hcr] at hpoly
  nlinarith [mul_nonneg (show (0 : ℤ) ≤ r - 2 by omega)
    (show (0 : ℤ) ≤ q - r - 2 by omega)]

/-- A full exceptional line and an empty exceptional line form a defect
edge: otherwise their unique common ambient neighbor would have to lie both
inside and outside the shore. -/
theorem binarySquare_full_empty_secondOrderDefect_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 0 < q)
    (hreg : ∀ v, G.degree v = q) (S : Finset V)
    {x y : V}
    (hfull : (G.neighborFinset x ∩ S).card = q)
    (hempty : (G.neighborFinset y ∩ S).card = 0) :
    (secondOrderDefectGraph G).Adj x y := by
  have hxy : x ≠ y := by
    intro h
    subst y
    omega
  by_contra hD
  have hnotMem : y ∉ (secondOrderDefectGraph G).neighborFinset x := by
    simpa [SimpleGraph.mem_neighborFinset] using hD
  have hcommon := card_common_eq_if_secondOrderDefect G hfree x y hxy
  rw [if_neg hnotMem] at hcommon
  obtain ⟨z, hz⟩ :
      ∃ z, z ∈ G.neighborFinset x ∩ G.neighborFinset y :=
    Finset.card_pos.mp (by omega)
  have hzData := Finset.mem_inter.mp hz
  have hNxCard : (G.neighborFinset x).card = q := by
    rw [G.card_neighborFinset_eq_degree, hreg]
  have hfullEq : G.neighborFinset x ∩ S = G.neighborFinset x := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
    omega
  have hzS : z ∈ S := by
    have hzInter : z ∈ G.neighborFinset x ∩ S := by
      rw [hfullEq]
      exact hzData.1
    exact (Finset.mem_inter.mp hzInter).2
  have hzEmpty : z ∈ G.neighborFinset y ∩ S :=
    Finset.mem_inter.mpr ⟨hzData.2, hzS⟩
  have : 0 < (G.neighborFinset y ∩ S).card :=
    Finset.card_pos.mpr ⟨z, hzEmpty⟩
  omega

/-- At regular square order the second-order defect graph is `(q-1)`-regular. -/
theorem binarySquare_regular_secondOrderDefect_degree_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (v : V) :
    (secondOrderDefectGraph G).degree v = q - 1 := by
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have h := secondOrderDefectGraph_degree_eq_excess_add_two
    G hfree hreg hcensus v
  change (secondOrderDefectGraph G).degree v = (q - 3) + 2 at h
  omega

/-- Capacity form of the full--empty defect core.  If both exceptional line
types occur and the defect graph has degree `q-1`, each type has at most
`q-1` vertices. -/
theorem binarySquare_full_empty_card_le_of_defectRegular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 0 < q)
    (hreg : ∀ v, G.degree v = q)
    (hDreg : ∀ v, (secondOrderDefectGraph G).degree v = q - 1)
    (S F E : Finset V)
    (hF : ∀ x ∈ F, (G.neighborFinset x ∩ S).card = q)
    (hE : ∀ y ∈ E, (G.neighborFinset y ∩ S).card = 0)
    (hFnonempty : F.Nonempty) (hEnonempty : E.Nonempty) :
    F.card ≤ q - 1 ∧ E.card ≤ q - 1 := by
  obtain ⟨x, hxF⟩ := hFnonempty
  obtain ⟨y, hyE⟩ := hEnonempty
  have hEsub : E ⊆ (secondOrderDefectGraph G).neighborFinset x := by
    intro z hzE
    exact ((secondOrderDefectGraph G).mem_neighborFinset x z).mpr
      (binarySquare_full_empty_secondOrderDefect_adj
        G hfree hq hreg S (hF x hxF) (hE z hzE))
  have hFsub : F ⊆ (secondOrderDefectGraph G).neighborFinset y := by
    intro z hzF
    exact ((secondOrderDefectGraph G).mem_neighborFinset y z).mpr
      (binarySquare_full_empty_secondOrderDefect_adj
        G hfree hq hreg S (hF z hzF) (hE y hyE)).symm
  constructor
  · calc
      F.card ≤ ((secondOrderDefectGraph G).neighborFinset y).card :=
        Finset.card_le_card hFsub
      _ = q - 1 := by
        rw [(secondOrderDefectGraph G).card_neighborFinset_eq_degree, hDreg]
  · calc
      E.card ≤ ((secondOrderDefectGraph G).neighborFinset x).card :=
        Finset.card_le_card hEsub
      _ = q - 1 := by
        rw [(secondOrderDefectGraph G).card_neighborFinset_eq_degree, hDreg]

/-- Graph-facing square-order specialization of the full--empty capacity
bound, discharging defect regularity from the ambient hypotheses. -/
theorem binarySquare_full_empty_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S F E : Finset V)
    (hF : ∀ x ∈ F, (G.neighborFinset x ∩ S).card = q)
    (hE : ∀ y ∈ E, (G.neighborFinset y ∩ S).card = 0)
    (hFnonempty : F.Nonempty) (hEnonempty : E.Nonempty) :
    F.card ≤ q - 1 ∧ E.card ≤ q - 1 := by
  exact binarySquare_full_empty_card_le_of_defectRegular
    G hfree (by omega) hreg
    (binarySquare_regular_secondOrderDefect_degree_eq
      G hfree hq hreg hcard)
    S F E hF hE hFnonempty hEnonempty

/-- Incidence form of the minority replication bound.  A family `E` of
q-valent lines disjoint from a shore `S`, with replication at most one on
the complementary shore, has at most the complementary-shore incidence
capacity. -/
theorem regular_emptyLines_mul_card_le_complement_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hreg : ∀ v, G.degree v = q)
    (S E : Finset V)
    (hE : ∀ e ∈ E, (G.neighborFinset e ∩ S).card = 0)
    (hcap : ∀ v ∉ S, (G.neighborFinset v ∩ E).card ≤ 1) :
    q * E.card ≤ Fintype.card V - S.card := by
  let T : Finset V := Finset.univ \ S
  have hline : ∀ e ∈ E, (G.neighborFinset e ∩ T).card = q := by
    intro e he
    have hempty : G.neighborFinset e ∩ S = ∅ :=
      Finset.card_eq_zero.mp (hE e he)
    have heq : G.neighborFinset e ∩ T = G.neighborFinset e := by
      ext v
      constructor
      · intro hv
        exact (Finset.mem_inter.mp hv).1
      · intro hv
        have hvNotS : v ∉ S := by
          intro hvS
          have : v ∈ G.neighborFinset e ∩ S :=
            Finset.mem_inter.mpr ⟨hv, hvS⟩
          rw [hempty] at this
          simp at this
        exact Finset.mem_inter.mpr
          ⟨hv, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hvNotS⟩⟩
    rw [heq, G.card_neighborFinset_eq_degree, hreg]
  have hswap := sum_card_neighbor_inter_comm G E T
  calc
    q * E.card = ∑ e ∈ E, (G.neighborFinset e ∩ T).card := by
      rw [show (∑ e ∈ E, (G.neighborFinset e ∩ T).card) =
          ∑ _e ∈ E, q by
        apply Finset.sum_congr rfl
        intro e he
        exact hline e he]
      simp [Nat.mul_comm]
    _ = ∑ v ∈ T, (G.neighborFinset v ∩ E).card := hswap
    _ ≤ ∑ _v ∈ T, 1 := by
      apply Finset.sum_le_sum
      intro v hv
      exact hcap v (Finset.mem_sdiff.mp hv).2
    _ = T.card := by simp
    _ = Fintype.card V - S.card := by
      simp [T, Finset.card_sdiff]

/-- Local C4-free packing around a shore point: the punctured shore parts of
the neighbor blocks are disjoint, so their total size is at most the rest of
the shore. -/
theorem c4Free_sum_punctured_shore_blocks_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (S : Finset V) {p : V} (hp : p ∈ S) :
    (∑ w ∈ G.neighborFinset p,
        (G.neighborFinset w ∩ S.erase p).card) ≤ S.card - 1 := by
  have hsum := c4Free_sum_neighbor_block_cards_eq_common_targets
    G hfree p (S.erase p) (by simp)
  calc
    (∑ w ∈ G.neighborFinset p,
        (G.neighborFinset w ∩ S.erase p).card) =
        ((S.erase p).filter fun y =>
          (G.neighborFinset p ∩ G.neighborFinset y).Nonempty).card := hsum
    _ ≤ (S.erase p).card := Finset.card_filter_le _ _
    _ = S.card - 1 := Finset.card_erase_of_mem hp

/-- At the final dyadic layer `q = 2m`, every row through a shore point is
balanced or full.  A balanced row contributes `m-1` points after puncturing
at that point, while a full row contributes one further block of size `m`.
The C4-free local packing therefore bounds the number of full rows through
the point.  This is the quantitative occupancy conversion used in (57)--(58). -/
theorem binarySquare_finalLayer_fullRows_local_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {m : ℕ}
    (hreg : ∀ v, G.degree v = 2 * m)
    (S : Finset V) {p : V} (hp : p ∈ S)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = 2 * m) :
    2 * m * (m - 1) +
        m * ((G.neighborFinset p).filter fun w =>
          (G.neighborFinset w ∩ S).card = 2 * m).card + 1 ≤ S.card := by
  by_cases hmzero : m = 0
  · have hScard : 1 ≤ S.card := Finset.one_le_card.mpr ⟨p, hp⟩
    simp [hmzero, hScard]
  · have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hmzero
    have hrow (w : V) (hw : w ∈ G.neighborFinset p) :
      (m - 1) +
          (if (G.neighborFinset w ∩ S).card = 2 * m then m else 0) ≤
        (G.neighborFinset w ∩ S.erase p).card := by
      have hpNw : p ∈ G.neighborFinset w := by
        exact (G.mem_neighborFinset w p).mpr
          ((G.mem_neighborFinset p w).mp hw).symm
      have hpInter : p ∈ G.neighborFinset w ∩ S :=
        Finset.mem_inter.mpr ⟨hpNw, hp⟩
      have herase :
          G.neighborFinset w ∩ S.erase p =
            (G.neighborFinset w ∩ S).erase p := by
        ext x
        simp [and_assoc, and_comm]
      rw [herase, Finset.card_erase_of_mem hpInter]
      rcases htri w with hzero | hhalf | hfull
      · have : 0 < (G.neighborFinset w ∩ S).card :=
          Finset.card_pos.mpr ⟨p, hpInter⟩
        omega
      · have hnotFull : (G.neighborFinset w ∩ S).card ≠ 2 * m := by
          omega
        rw [if_neg hnotFull, hhalf]
        omega
      · simp [hfull]
        omega
    have hweighted :
      2 * m * (m - 1) +
          m * ((G.neighborFinset p).filter fun w =>
            (G.neighborFinset w ∩ S).card = 2 * m).card ≤
        ∑ w ∈ G.neighborFinset p,
          (G.neighborFinset w ∩ S.erase p).card := by
      calc
        2 * m * (m - 1) +
            m * ((G.neighborFinset p).filter fun w =>
              (G.neighborFinset w ∩ S).card = 2 * m).card =
            ∑ w ∈ G.neighborFinset p,
              ((m - 1) +
                if (G.neighborFinset w ∩ S).card = 2 * m then m else 0) := by
                  rw [Finset.sum_add_distrib]
                  simp [Finset.sum_ite, G.card_neighborFinset_eq_degree, hreg,
                    Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ ∑ w ∈ G.neighborFinset p,
            (G.neighborFinset w ∩ S.erase p).card := by
              exact Finset.sum_le_sum fun w hw => hrow w hw
    have hpack := c4Free_sum_punctured_shore_blocks_le G hfree S hp
    have hScard : 1 ≤ S.card := Finset.one_le_card.mpr ⟨p, hp⟩
    omega

/-- The complement-shore occupancy is the degree minus the original shore
occupancy. -/
theorem neighbor_inter_complement_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) :
    (G.neighborFinset v ∩ (Finset.univ \ S)).card =
      G.degree v - (G.neighborFinset v ∩ S).card := by
  have heq :
      G.neighborFinset v ∩ (Finset.univ \ S) =
        G.neighborFinset v \ (G.neighborFinset v ∩ S) := by
    ext x
    simp
  rw [heq, Finset.card_sdiff_of_subset Finset.inter_subset_left,
    G.card_neighborFinset_eq_degree]

/-- In the final shore window, every point has at most three exceptional
neighbors (empty or full lines).  This is the subcubic conclusion (59),
obtained on the two shores by applying the weighted local bound to `S` and
to its complement. -/
theorem binarySquare_finalLayer_exceptionalNeighbors_card_le_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {m : ℕ} (hm : 2 ≤ m)
    (hreg : ∀ v, G.degree v = 2 * m)
    (hcard : Fintype.card V = 4 * m * m)
    (S : Finset V)
    (hlower : 2 * m * m - 2 * m + 1 ≤ S.card)
    (hupper : S.card ≤ 2 * m * m + 2 * m - 1)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = 2 * m)
    (p : V) :
    ((G.neighborFinset p).filter fun w =>
      (G.neighborFinset w ∩ S).card = 0 ∨
      (G.neighborFinset w ∩ S).card = 2 * m).card ≤ 3 := by
  by_cases hp : p ∈ S
  · have hfilter :
        (G.neighborFinset p).filter (fun w =>
          (G.neighborFinset w ∩ S).card = 0 ∨
          (G.neighborFinset w ∩ S).card = 2 * m) =
        (G.neighborFinset p).filter (fun w =>
          (G.neighborFinset w ∩ S).card = 2 * m) := by
      ext w
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hwp, hzero | hfull⟩
        · have hpNw : p ∈ G.neighborFinset w :=
            (G.mem_neighborFinset w p).mpr
              ((G.mem_neighborFinset p w).mp hwp).symm
          have : 0 < (G.neighborFinset w ∩ S).card :=
            Finset.card_pos.mpr ⟨p, Finset.mem_inter.mpr ⟨hpNw, hp⟩⟩
          omega
        · exact ⟨hwp, hfull⟩
      · rintro ⟨hwp, hfull⟩
        exact ⟨hwp, Or.inr hfull⟩
    rw [hfilter]
    have hlocal := binarySquare_finalLayer_fullRows_local_bound
      G hfree hreg S hp htri
    have hbase : 2 * m * (m - 1) + 2 * m = 2 * m * m := by
      calc
        2 * m * (m - 1) + 2 * m = 2 * m * ((m - 1) + 1) := by ring
        _ = 2 * m * m := by rw [Nat.sub_add_cancel (by omega)]
    by_contra hnot
    have ht : 4 ≤ ((G.neighborFinset p).filter fun w =>
        (G.neighborFinset w ∩ S).card = 2 * m).card := by omega
    have hfour : 4 * m ≤
        m * ((G.neighborFinset p).filter fun w =>
          (G.neighborFinset w ∩ S).card = 2 * m).card := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left m ht
    omega
  · let T : Finset V := Finset.univ \ S
    have hpT : p ∈ T := Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, hp⟩
    have hTcard : T.card = Fintype.card V - S.card := by
      simp [T, Finset.card_sdiff]
    have hTupper : T.card ≤ 2 * m * m + 2 * m - 1 := by
      rw [hTcard, hcard]
      have hsplit : 4 * m * m = 2 * m * m + 2 * m * m := by ring
      rw [hsplit]
      omega
    have htriT : ∀ v,
        (G.neighborFinset v ∩ T).card = 0 ∨
        (G.neighborFinset v ∩ T).card = m ∨
        (G.neighborFinset v ∩ T).card = 2 * m := by
      intro v
      have hcomp := neighbor_inter_complement_card G S v
      change (G.neighborFinset v ∩ T).card = _ at hcomp
      rw [hreg] at hcomp
      rcases htri v with hzero | hhalf | hfull
      · exact Or.inr (Or.inr (by omega))
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inl (by omega)
    have hfilter :
        (G.neighborFinset p).filter (fun w =>
          (G.neighborFinset w ∩ S).card = 0 ∨
          (G.neighborFinset w ∩ S).card = 2 * m) =
        (G.neighborFinset p).filter (fun w =>
          (G.neighborFinset w ∩ T).card = 2 * m) := by
      ext w
      simp only [Finset.mem_filter]
      have hcomp := neighbor_inter_complement_card G S w
      change (G.neighborFinset w ∩ T).card = _ at hcomp
      rw [hreg] at hcomp
      constructor
      · rintro ⟨hwp, hzero | hfull⟩
        · exact ⟨hwp, by omega⟩
        · have hpNw : p ∈ G.neighborFinset w :=
            (G.mem_neighborFinset w p).mpr
              ((G.mem_neighborFinset p w).mp hwp).symm
          have hcardPos : 0 < (G.neighborFinset w ∩ T).card :=
            Finset.card_pos.mpr ⟨p, Finset.mem_inter.mpr ⟨hpNw, hpT⟩⟩
          omega
      · rintro ⟨hwp, hfullT⟩
        exact ⟨hwp, Or.inl (by omega)⟩
    rw [hfilter]
    have hlocal := binarySquare_finalLayer_fullRows_local_bound
      G hfree hreg T hpT htriT
    have hbase : 2 * m * (m - 1) + 2 * m = 2 * m * m := by
      calc
        2 * m * (m - 1) + 2 * m = 2 * m * ((m - 1) + 1) := by ring
        _ = 2 * m * m := by rw [Nat.sub_add_cancel (by omega)]
    by_contra hnot
    have ht : 4 ≤ ((G.neighborFinset p).filter fun w =>
        (G.neighborFinset w ∩ T).card = 2 * m).card := by omega
    have hfour : 4 * m ≤
        m * ((G.neighborFinset p).filter fun w =>
          (G.neighborFinset w ∩ T).card = 2 * m).card := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left m ht
    omega

end

end Erdos85

#print axioms Erdos85.cutSign_adjMatrix_mulVec_apply
#print axioms Erdos85.cutSign_adjMatrix_mulVec_eq_sparseSigned
#print axioms Erdos85.sum_cutSign
#print axioms Erdos85.binarySquare_sparseSigned_companionDefect_apply
#print axioms Erdos85.binarySquare_trichotomy_companionDefect_apply
#print axioms Erdos85.binarySquare_mixedExceptional_card_le
#print axioms Erdos85.binarySquare_pureLargeExceptional_impossible
#print axioms Erdos85.binarySquare_full_empty_secondOrderDefect_adj
#print axioms Erdos85.binarySquare_regular_secondOrderDefect_degree_eq
#print axioms Erdos85.binarySquare_full_empty_card_le_of_defectRegular
#print axioms Erdos85.binarySquare_full_empty_card_le
#print axioms Erdos85.regular_emptyLines_mul_card_le_complement_card
#print axioms Erdos85.c4Free_sum_punctured_shore_blocks_le
#print axioms Erdos85.binarySquare_finalLayer_fullRows_local_bound
#print axioms Erdos85.neighbor_inter_complement_card
#print axioms Erdos85.binarySquare_finalLayer_exceptionalNeighbors_card_le_three
