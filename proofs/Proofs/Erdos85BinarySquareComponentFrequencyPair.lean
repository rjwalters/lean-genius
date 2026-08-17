import Proofs.Erdos85BinarySquareComponentAmbientSquareSpectrum

/-!
# Explicit frequency pairs from a defect-component eigenvector

For a real vector satisfying `A²u = λu` with `λ > 0`, the vectors
`Au ± √λ u` are eigenvectors of `A` at the paired frequencies `±√λ`.
This is purely real linear algebra; it makes no Galois-exchange assertion.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The explicit real frequency-pair decomposition of a positive square
eigenvector. -/
theorem real_frequencyPair_of_sq_eigenvector
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (u : V → ℝ) (a : ℝ)
    (hsq : A.mulVec (A.mulVec u) = a • u)
    (ha : 0 < a) :
    let r := Real.sqrt a
    let p := A.mulVec u + r • u
    let n := A.mulVec u - r • u
    A.mulVec p = r • p ∧
      A.mulVec n = (-r) • n ∧
      u = (2 * r)⁻¹ • (p - n) := by
  let r := Real.sqrt a
  let p := A.mulVec u + r • u
  let n := A.mulVec u - r • u
  have hr : r ^ 2 = a := by
    dsimp only [r]
    exact Real.sq_sqrt ha.le
  have hr' : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha.le
  have hr0 : r ≠ 0 := Real.sqrt_ne_zero'.mpr ha
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mulVec_add, hsq, Matrix.mulVec_smul]
    ext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf
    rw [hr']
    ring
  · rw [Matrix.mulVec_sub, hsq, Matrix.mulVec_smul]
    ext x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring_nf
    rw [hr']
    ring
  · ext x
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
    field_simp
    ring

/-- Zero extension reflects nonzeroness. -/
theorem connectedComponentExtend_ne_zero
    {V R : Type*} [Zero R]
    (D : SimpleGraph V) [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) (v : c.supp → R) (hv : v ≠ 0) :
    connectedComponentExtend D c v ≠ 0 := by
  intro hext
  apply hv
  funext z
  have hz := congrFun hext z.1
  simpa [connectedComponentExtend, z.2] using hz

/-- **Component frequency-pair bridge.**  A nonzero component adjacency
eigenvector with positive radicand `q - 1 - μ` extends to a nonzero ambient
vector and splits explicitly into the two adjacency frequencies
`±√(q - 1 - μ)`. -/
theorem binarySquare_componentEigenvector_frequencyPair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (v : c.supp → ℝ) (μ : ℝ)
    (hv : (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℝ).mulVec v =
      μ • v) (hv0 : v ≠ 0)
    (hrad : 0 < (q : ℝ) - 1 - μ) :
    let u := connectedComponentExtend (secondOrderDefectGraph G) c v
    let r := Real.sqrt ((q : ℝ) - 1 - μ)
    let p := (G.adjMatrix ℝ).mulVec u + r • u
    let n := (G.adjMatrix ℝ).mulVec u - r • u
    u ≠ 0 ∧
      (G.adjMatrix ℝ).mulVec p = r • p ∧
      (G.adjMatrix ℝ).mulVec n = (-r) • n ∧
      u = (2 * r)⁻¹ • (p - n) := by
  let u := connectedComponentExtend (secondOrderDefectGraph G) c v
  let a := (q : ℝ) - 1 - μ
  have hμ : μ ≠ ((q - 1 : ℕ) : ℝ) := by
    intro heq
    have hcast : (((q - 1 : ℕ) : ℝ)) = (q : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q)]
      norm_num
    rw [heq] at hrad
    rw [hcast] at hrad
    linarith
  have hsq := binarySquare_ambientAdjMatrix_sq_componentEigenvector
    G hfree hq hreg hcard c v μ hv hμ
  have hu0 : u ≠ 0 := connectedComponentExtend_ne_zero
    (secondOrderDefectGraph G) c v hv0
  have hpair := real_frequencyPair_of_sq_eigenvector
    (G.adjMatrix ℝ) u a (by simpa [u, a] using hsq) (by simpa [a] using hrad)
  exact ⟨hu0, hpair⟩

end

end Erdos85
