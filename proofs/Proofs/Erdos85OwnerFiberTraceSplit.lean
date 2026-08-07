import Proofs.Erdos85OwnerFiberRelationOperator
import Proofs.Erdos85NonprincipalCharpoly

/-!
# Trace splitting across uniform owner fibers

For a uniform locally bijective relation cover, the normalized owner Gram
matrix is the projection onto functions constant on owner fibers.  The
intertwining identity computes the trace on this quotient sector without
choosing a basis.  The complementary trace is therefore forced as well.
-/

namespace Erdos85

noncomputable section

open Matrix
open scoped Matrix

/-- The reflexive complement relation has one on every diagonal entry. -/
theorem trace_relationMatrix_not_adj
    {Y K : Type*} [Fintype Y] [DecidableEq Y] [Semiring K]
    (H : SimpleGraph Y) [DecidableRel H.Adj] :
    Matrix.trace (relationMatrix (K := K) (fun a b => ¬H.Adj a b)) =
      (Fintype.card Y : K) := by
  simp [Matrix.trace, relationMatrix, H.loopless]

def normalizedOwnerProjection
    {X Y K : Type*} [Fintype Y] [DecidableEq X] [DecidableEq Y]
    [Field K] (owner : X → Y) (m : ℕ) : Matrix X X K :=
  ((m : K)⁻¹) •
    (Matrix.transpose (ownerIncidenceMatrix (K := K) owner) *
      ownerIncidenceMatrix (K := K) owner)

/-- The trace of the cover adjacency on the fiber-constant projection is
the trace of the base relation matrix. -/
theorem trace_mul_normalizedOwnerProjection_eq_trace_base
    {X Y K : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [Field K]
    (A : Matrix X X K) (B : Matrix Y Y K) (owner : X → Y) (m : ℕ)
    (hm : (m : K) ≠ 0)
    (hintertwine : A * Matrix.transpose
        (ownerIncidenceMatrix (K := K) owner) =
      Matrix.transpose (ownerIncidenceMatrix (K := K) owner) * B)
    (huniform : ∀ a, (ownerFiberFinset owner a).card = m) :
    Matrix.trace (A * normalizedOwnerProjection owner m) =
      Matrix.trace B := by
  let C := ownerIncidenceMatrix (K := K) owner
  have hCC : C * Matrix.transpose C = (m : K) • (1 : Matrix Y Y K) :=
    ownerIncidence_mul_transpose_eq_smul_one owner m huniform
  calc
    Matrix.trace (A * normalizedOwnerProjection owner m) =
        (m : K)⁻¹ * Matrix.trace ((A * Matrix.transpose C) * C) := by
          simp only [normalizedOwnerProjection, C, Matrix.mul_smul,
            Matrix.trace_smul, Matrix.mul_assoc, smul_eq_mul]
    _ = (m : K)⁻¹ *
        Matrix.trace ((Matrix.transpose C * B) * C) := by
          rw [hintertwine]
    _ = (m : K)⁻¹ * Matrix.trace (C * (Matrix.transpose C * B)) := by
          rw [Matrix.trace_mul_comm]
    _ = (m : K)⁻¹ * Matrix.trace ((C * Matrix.transpose C) * B) := by
          rw [Matrix.mul_assoc]
    _ = (m : K)⁻¹ * Matrix.trace (((m : K) • (1 : Matrix Y Y K)) * B) := by
          rw [hCC]
    _ = (m : K)⁻¹ * ((m : K) * Matrix.trace B) := by
          simp
    _ = Matrix.trace B := by
          rw [← mul_assoc, inv_mul_cancel₀ hm, one_mul]

/-- Consequently the trace on the complementary fiber-sum-zero projection
is total trace minus base trace. -/
theorem trace_mul_complement_normalizedOwnerProjection
    {X Y K : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [Field K]
    (A : Matrix X X K) (B : Matrix Y Y K) (owner : X → Y) (m : ℕ)
    (hm : (m : K) ≠ 0)
    (hintertwine : A * Matrix.transpose
        (ownerIncidenceMatrix (K := K) owner) =
      Matrix.transpose (ownerIncidenceMatrix (K := K) owner) * B)
    (huniform : ∀ a, (ownerFiberFinset owner a).card = m) :
    Matrix.trace (A * (1 - normalizedOwnerProjection owner m)) =
      Matrix.trace A - Matrix.trace B := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub,
    trace_mul_normalizedOwnerProjection_eq_trace_base
      A B owner m hm hintertwine huniform]

/-- Graph-facing trace split for a saturated minimum-layer extension.  The
fiber-sum-zero sector of the exterior adjacency has trace equal to minus the
number of child vertices.  In the residual `(d,s)=(124,12)` case this is
`-135`. -/
theorem exists_minimumLayer_saturated_exterior_complement_trace
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (minimumLayerExteriorVertex (secondOrderDefectGraph G) c₀)]
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hspos : 0 < s) (hsd : s < d)
    (hsat : d = (s - 1) * (s - 1) + 3) :
    let D := secondOrderDefectGraph G
    let X := minimumLayerExteriorVertex D c₀
    let H := minimumLayerGraph G D c₀
    let A := (G.comap (fun z : X => z.1)).adjMatrix ℚ
    ∃ owner : X → minimumLayerVertex D c₀,
      Matrix.trace
          (A * (1 - normalizedOwnerProjection owner (d - s))) =
        -(Fintype.card (minimumLayerVertex D c₀) : ℚ) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let X := minimumLayerExteriorVertex D c₀
  let H := minimumLayerGraph G D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let A := (G.comap (fun z : X => z.1)).adjMatrix ℚ
  let B := relationMatrix (K := ℚ) (fun a b : minimumLayerVertex D c₀ =>
    ¬H.Adj a b)
  obtain ⟨owner, hownerMem, hmap, hlift⟩ :=
    exists_minimumLayer_saturated_exteriorRelationCover
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
  have hintertwine : A * Matrix.transpose
        (ownerIncidenceMatrix (K := ℚ) owner) =
      Matrix.transpose (ownerIncidenceMatrix (K := ℚ) owner) * B := by
    exact adjMatrix_mul_ownerIncidence_transpose_relation
      (G.comap (fun z : X => z.1))
      (fun a b : minimumLayerVertex D c₀ => ¬H.Adj a b)
      owner hmap hlift
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, d = t + 4 := ⟨d - 4, by omega⟩
    norm_num
    nlinarith
  have hregParent : ∀ v : V, G.degree v = d :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by omega) hmin hbelow
  have hownerUnique : ∀ (z : X) (a : minimumLayerVertex D c₀),
      z.1 ∈ E a → a = owner z := by
    intro z a hza
    obtain ⟨q, hq, hqunique⟩ :=
      minimumLayer_existsUnique_externalOwner_of_saturated
        G hfree hd heven hmin hcard c₀ hregChild hcardChild
          hspos hsd hsat z.2
    exact (hqunique a hza).trans (hqunique (owner z) (hownerMem z)).symm
  have huniform : ∀ a, (ownerFiberFinset owner a).card = d - s := by
    intro a
    calc
      (ownerFiberFinset owner a).card = (E a).card := by
        apply Finset.card_bij (fun z _ => z.1)
        · intro z hz
          have hza : owner z = a := (Finset.mem_filter.mp hz).2
          simpa [hza] using hownerMem z
        · intro z₁ _ z₂ _ heq
          exact Subtype.ext heq
        · intro y hy
          have hyOut : y ∉ minimumLayerImageFinset D c₀ :=
            (Finset.mem_sdiff.mp hy).2
          let z : X := ⟨y, hyOut⟩
          have hza : owner z = a := (hownerUnique z a hy).symm
          refine ⟨z, ?_, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hza⟩
      _ = d - s := card_minimumLayerExternalNeighborFinset
        G D c₀ hregParent hregChild a
  have hm : ((d - s : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.sub_pos_of_lt hsd |>.ne'
  have htrace := trace_mul_complement_normalizedOwnerProjection
    A B owner (d - s) hm hintertwine huniform
  have htraceA : Matrix.trace A = 0 := by
    exact adjMatrix_trace_rat_eq_zero (G.comap (fun z : X => z.1))
  have htraceB : Matrix.trace B =
      (Fintype.card (minimumLayerVertex D c₀) : ℚ) := by
    exact trace_relationMatrix_not_adj H
  refine ⟨owner, ?_⟩
  rw [htrace, htraceA, htraceB, zero_sub]

/-- Numeric form of the trace split in the sole saturated residual. -/
theorem exists_minimumLayer_saturated_124_exterior_complement_trace
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hmin : 124 ≤ G.minDegree)
    (hcard : Fintype.card V = 124 * (124 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (minimumLayerExteriorVertex (secondOrderDefectGraph G) c₀)]
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 12)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        12 * (12 - 1) + 3) :
    let D := secondOrderDefectGraph G
    let X := minimumLayerExteriorVertex D c₀
    let A := (G.comap (fun z : X => z.1)).adjMatrix ℚ
    ∃ owner : X → minimumLayerVertex D c₀,
      Matrix.trace (A * (1 - normalizedOwnerProjection owner 112)) = -135 := by
  dsimp only
  have h := exists_minimumLayer_saturated_exterior_complement_trace
    G hfree (d := 124) (s := 12) (by norm_num) (by norm_num) hmin hcard
      c₀ hregChild hcardChild (by norm_num) (by norm_num) (by norm_num)
  norm_num at hcardChild
  simpa [hcardChild] using h

end

end Erdos85
