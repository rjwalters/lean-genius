import Proofs.Erdos85OwnerFiberJointCover
import Proofs.Erdos85ExcessEigenspace
import Proofs.Erdos85MinimumLayerSaturatedExterior

/-!
# The square identity on the fiber-sum-zero exterior sector

For a saturated minimum-layer exterior, its second-order defect matrix is
the lifted parent defect plus the owner-fiber clique matrix.  The latter
acts as `-1` on the fiber-sum-zero sector, while the all-ones matrix acts as
zero.  Hence an exterior of degree `d-1` satisfies

`A² Q = ((d-1) I - P) Q`,

where `Q` is the complementary normalized owner projection.  At `d=124`
this is the required scalar-123 identity.
-/

namespace Erdos85

noncomputable section

open Matrix
open scoped Matrix

set_option maxHeartbeats 2000000

/-- Pure matrix algebra behind the hard-sector square identity. -/
theorem mul_complement_eq_of_sq_defect_fiber_split
    {X K : Type*} [Fintype X] [DecidableEq X] [Field K]
    (A P E J : Matrix X X K) (κ m : K)
    (hE : E * E = E) (hJE : J * E = J)
    (hsq : A * A = κ • (1 : Matrix X X K) + J -
      (P + (m • E - 1))) :
    (A * A) * (1 - E) =
      (((κ + 1) • (1 : Matrix X X K)) - P) * (1 - E) := by
  have hJQ : J * (1 - E) = 0 := by
    rw [mul_sub, mul_one, hJE, sub_self]
  have hEQ : E * (1 - E) = 0 := by
    rw [mul_sub, mul_one, hE, sub_self]
  have hmEQ : (m • E) * (1 - E) = 0 := by
    rw [Matrix.smul_mul, hEQ, smul_zero]
  rw [hsq, sub_mul, add_mul, sub_mul, add_mul, sub_mul,
    hJQ, hmEQ]
  simp only [Matrix.smul_mul, Matrix.one_mul, zero_add, smul_zero,
    zero_sub, sub_zero]
  rw [add_smul, one_smul]
  noncomm_ring

/-- The fiber-clique matrix is `m E - I` for the normalized owner
projection `E`. -/
theorem ownerFiberCliqueMatrix_eq_smul_normalizedOwnerProjection_sub_one
    {X Y K : Type*} [Fintype Y] [DecidableEq X] [DecidableEq Y]
    [Field K] (owner : X → Y) (m : ℕ) (hm : (m : K) ≠ 0) :
    ownerFiberCliqueMatrix (K := K) owner =
      (m : K) • normalizedOwnerProjection owner m - 1 := by
  simp only [ownerFiberCliqueMatrix, normalizedOwnerProjection, smul_smul]
  rw [mul_inv_cancel₀ hm, one_smul]

/-- Rational transport of the regular `C₄`-free square identity. -/
theorem adjMatrix_sq_eq_sub_secondOrderDefect_of_regular_rat
    {X : Type*} [Fintype X] [DecidableEq X]
    (G : SimpleGraph X) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 X G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) :
    G.adjMatrix ℚ * G.adjMatrix ℚ =
      ((d : ℚ) - 1) • (1 : Matrix X X ℚ) +
        Matrix.of (fun _ _ => (1 : ℚ)) -
          (secondOrderDefectGraph G).adjMatrix ℚ := by
  have hsqZ := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
  ext x y
  have hxy := congrArg (fun M : Matrix X X ℤ => M x y) hsqZ
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply] at hxy ⊢
  have hc := congrArg (fun z : ℤ => (z : ℚ)) hxy
  push_cast at hc
  simpa [SimpleGraph.adjMatrix_apply,
    FriendshipTheoremOQ01.onesMatrix] using hc

/-- The exterior second-order defect matrix splits into the restricted
parent defect and the owner-fiber clique matrix, for the same canonical
owner used by both locally bijective covers. -/
theorem exists_minimumLayer_saturated_exteriorDefect_matrix_split
    {V K : Type*} [Fintype V] [DecidableEq V] [Field K]
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
    let AG := G.comap (fun z : X => z.1)
    let PG := D.comap (fun z : X => z.1)
    ∃ owner : X → minimumLayerVertex D c₀,
      (∀ z, z.1 ∈ minimumLayerExternalNeighborFinset G D c₀ (owner z)) ∧
      (∀ a, (ownerFiberFinset owner a).card = d - s) ∧
      (secondOrderDefectGraph AG).adjMatrix K =
        PG.adjMatrix K + ownerFiberCliqueMatrix owner := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let X := minimumLayerExteriorVertex D c₀
  let H := minimumLayerGraph G D c₀
  let U := minimumLayerImageFinset D c₀
  let AG := G.comap (fun z : X => z.1)
  let PG := D.comap (fun z : X => z.1)
  obtain ⟨owner, hownerMem, hmapP, hliftP, hmapA, hliftA⟩ :=
    exists_minimumLayer_saturated_jointCovers
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, d = t + 4 := ⟨d - 4, by omega⟩
    norm_num
    nlinarith
  have hregParent : ∀ v : V, G.degree v = d :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by omega) hmin hbelow
  let E := minimumLayerExternalNeighborFinset G D c₀
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
  obtain ⟨ownerC, hmemC, hcommonC⟩ :=
    exists_minimumLayer_saturated_owner_commonNeighbor_iff
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
  have hownerC : ownerC = owner := by
    funext z
    exact hownerUnique z (ownerC z) (hmemC z)
  subst ownerC
  have hsplit : ∀ {z w : X}, z ≠ w →
      ((secondOrderDefectGraph AG).Adj z w ↔
        PG.Adj z w ∨ owner z = owner w) := by
    intro z w hzw
    have hext : (secondOrderDefectGraph AG).Adj z w ↔
        (secondOrderDefectGraph G).Adj z.1 w.1 ∨
          ∃ u ∈ U, G.Adj z.1 u ∧ G.Adj w.1 u := by
      exact @finsetExterior_secondOrderDefect_adj_iff V _ _ G _ _ _ U
        (inferInstance : Fintype X) (inferInstance : DecidableEq X)
        (inferInstance : DecidableRel AG.Adj)
        (inferInstance : DecidableRel (antipodalGraph AG).Adj)
        (inferInstance : DecidableRel (triangleFreeEdgeGraph AG).Adj)
        hfree z w hzw
    exact hext.trans (or_congr Iff.rfl (hcommonC z w))
  have hdisj : ∀ {z w : X}, PG.Adj z w → owner z ≠ owner w := by
    intro z w hP how
    have hDH := hmapP hP
    rw [how] at hDH
    exact hDH.ne rfl
  refine ⟨owner, hownerMem, huniform, ?_⟩
  exact adjMatrix_eq_add_ownerFiberClique_of_split
    (secondOrderDefectGraph AG) PG owner hsplit hdisj

/-- **Graph-facing scalar-123 hard-sector package.**  In the residual
`(d,s)=(124,12)` saturated layer, one canonical owner projection gives
simultaneous invariance, trace `-135`, and the projected square identity
`A²Q = (123I-P)Q`. -/
theorem exists_minimumLayer_saturated_124_hardSector_square
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
    let P := (D.comap (fun z : X => z.1)).adjMatrix ℚ
    ∃ owner : X → minimumLayerVertex D c₀,
      let E := normalizedOwnerProjection owner 112
      let Q := 1 - E
      (∀ a, (ownerFiberFinset owner a).card = 112) ∧
      A * E = E * A ∧ P * E = E * P ∧
      Matrix.trace (A * Q) = -135 ∧
      (A * A) * Q = ((123 : ℚ) • (1 : Matrix X X ℚ) - P) * Q := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let X := minimumLayerExteriorVertex D c₀
  let AG := G.comap (fun z : X => z.1)
  let PG := D.comap (fun z : X => z.1)
  let A := AG.adjMatrix ℚ
  let P := PG.adjMatrix ℚ
  obtain ⟨owner₁, hmem₁, huniform₁, hcommA, hcommP, htrace⟩ :=
    exists_minimumLayer_saturated_jointOwnerOperators
      G hfree (d := 124) (s := 12) (by norm_num) (by norm_num)
        hmin hcard c₀ hregChild hcardChild (by norm_num) (by norm_num)
          (by norm_num)
  obtain ⟨owner₂, hmem₂, huniform₂, hsplit⟩ :=
    exists_minimumLayer_saturated_exteriorDefect_matrix_split (K := ℚ)
      G hfree (d := 124) (s := 12) (by norm_num) (by norm_num)
        hmin hcard c₀ hregChild hcardChild (by norm_num) (by norm_num)
          (by norm_num)
  have howner : owner₂ = owner₁ := by
    funext z
    obtain ⟨a, ha, haUnique⟩ :=
      minimumLayer_existsUnique_externalOwner_of_saturated
        G hfree (d := 124) (s := 12) (by norm_num) (by norm_num)
          hmin hcard c₀ hregChild hcardChild (by norm_num) (by norm_num)
            (by norm_num) z.2
    exact (haUnique (owner₂ z) (hmem₂ z)).trans
      (haUnique (owner₁ z) (hmem₁ z)).symm
  subst owner₂
  let E := normalizedOwnerProjection (K := ℚ) owner₁ 112
  let Q : Matrix X X ℚ := 1 - E
  have hm : ((112 : ℕ) : ℚ) ≠ 0 := by norm_num
  have hE : E * E = E :=
    normalizedOwnerProjection_isIdempotent owner₁ 112 hm huniform₁
  let J : Matrix X X ℚ := Matrix.of fun _ _ => 1
  have hJE : J * E = J :=
    onesMatrix_mul_normalizedOwnerProjection owner₁ 112 hm huniform₁
  have hfreeAG : ¬ containsC4 X AG := by
    intro hC4
    obtain ⟨f, hf, hadj⟩ := hC4
    apply hfree
    refine ⟨Subtype.val ∘ f, Subtype.val_injective.comp hf, ?_⟩
    intro i j hij
    exact hadj i j hij
  have hregAG : ∀ z : X, AG.degree z = 123 := by
    intro z
    change (G.comap (fun z : X => z.1)).degree z = 123
    exact minimumLayer_saturated_exterior_regular
      G hfree (d := 124) (s := 12) (by norm_num) (by norm_num)
        hmin hcard c₀ hregChild hcardChild (by norm_num) (by norm_num)
          (by norm_num) z
  have hsq := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular_rat
    AG hfreeAG hregAG
  have hclique : ownerFiberCliqueMatrix (K := ℚ) owner₁ =
      (112 : ℚ) • E - 1 :=
    ownerFiberCliqueMatrix_eq_smul_normalizedOwnerProjection_sub_one
      owner₁ 112 hm
  have hsplit' : (secondOrderDefectGraph AG).adjMatrix ℚ =
      PG.adjMatrix ℚ + ownerFiberCliqueMatrix owner₁ := by
    simpa [AG, PG, D] using hsplit
  have hsqSplit : A * A = (122 : ℚ) • (1 : Matrix X X ℚ) + J -
      (P + ((112 : ℚ) • E - 1)) := by
    change AG.adjMatrix ℚ * AG.adjMatrix ℚ =
      (122 : ℚ) • (1 : Matrix X X ℚ) +
        Matrix.of (fun _ _ => (1 : ℚ)) -
          (PG.adjMatrix ℚ + ((112 : ℚ) • E - 1))
    rw [hsq, hsplit', hclique]
    norm_num
  have hprojected := mul_complement_eq_of_sq_defect_fiber_split
    A P E J (122 : ℚ) (112 : ℚ) hE hJE hsqSplit
  norm_num at hcardChild
  refine ⟨owner₁, huniform₁, hcommA, hcommP, ?_, ?_⟩
  · simpa [Q, E, hcardChild] using htrace
  · norm_num at hprojected
    simpa [Q, E, A, P, AG, PG, D] using hprojected

end

end Erdos85
