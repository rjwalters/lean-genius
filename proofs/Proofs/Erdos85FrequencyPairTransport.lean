import Proofs.Erdos85FrequencyPairInterface
import Proofs.Erdos85FrequencyPairGraphBlocks
import Proofs.Erdos85ZeroRowDifference
import Proofs.Erdos85DiagonalAnchorParity

/-!
# Transport from equal defect cycles to the labeled frequency-pair model

Given a graph `G` on `V` together with a system of labelings
`u : C → ZMod r → V` of the cycles of a commuting two-factor `D` — the
data produced by the equal-cycle decomposition of the second-order defect
graph — this file transports the whole frequency-pair bridge to `V`:

* the transported defect matrix is literally `cycleDefectMatrix`;
* commutation, the even second-order matrix equation, symmetry, and
  translation invariance of diagonal blocks all transport to the labeled
  adjacency matrix `labeledAdjMatrix`;
* the Fourier weight of the labeled model at displacement `t` is exactly
  the diagonal-anchor multiplicity
  `anchorMultiplicity (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))`;
* consequently the graph-facing trace identity holds:
  `trace T = 2 * ∑ s, projectedMultiplicity (anchor…) s • ζ^s`,
  together with its square-branch and vanishing-branch consequences.

The inputs `hcommZ` and `hsqZ` are supplied for the extremal graph by
`adjMatrix_comm_secondOrderDefect_of_even` and
`adjMatrix_sq_eq_sub_secondOrderDefect_of_even`; the labeling data is the
equal-odd-cycle decomposition of the defect two-factor.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

section Transport

variable {K : Type*} [Field K]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {C : Type*} [Fintype C] [DecidableEq C]
variable {r : ℕ} [NeZero r]

/-- The total labeling map of an equal-cycle system. -/
def cycleLabeling (u : C → ZMod r → V) : ZMod r × C → V := fun x ↦ u x.2 x.1

/-- The adjacency matrix of `G` transported to labeled cycle
coordinates. -/
def labeledAdjMatrix (K : Type*) [Field K] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u : C → ZMod r → V) :
    Matrix (ZMod r × C) (ZMod r × C) K :=
  (G.adjMatrix K).submatrix (cycleLabeling u) (cycleLabeling u)

@[simp] theorem labeledAdjMatrix_apply (G : SimpleGraph V)
    [DecidableRel G.Adj] (u : C → ZMod r → V) (x y : ZMod r × C) :
    labeledAdjMatrix K G u x y = G.adjMatrix K (u x.2 x.1) (u y.2 y.1) :=
  rfl

theorem adjMatrix_map_intCast (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.adjMatrix ℤ).map (Int.castRingHom K) = G.adjMatrix K := by
  ext x y
  simp only [Matrix.map_apply, SimpleGraph.adjMatrix_apply,
    apply_ite (Int.castRingHom K)]
  norm_num

/-- The transported defect matrix of an equal-cycle system is the standard
labeled defect operator. -/
theorem submatrix_defect_eq_cycleDefectMatrix
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (u : C → ZMod r → V) (hr3 : 3 ≤ r)
    (hinj : Function.Injective (cycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) = {u c (x - 1), u c (x + 1)}) :
    (D.adjMatrix K).submatrix (cycleLabeling u) (cycleLabeling u) =
      cycleDefectMatrix K C r := by
  ext ⟨x, c⟩ ⟨y, e⟩
  rw [Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply,
    cycleDefectMatrix, Matrix.blockDiagonal_apply]
  simp only [cycleLabeling]
  have hadj : D.Adj (u c x) (u e y) ↔ e = c ∧ (y = x - 1 ∨ y = x + 1) := by
    rw [← SimpleGraph.mem_neighborFinset, huD c x]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · have hp : ((y, e) : ZMod r × C) = (x - 1, c) := hinj h
        exact ⟨(Prod.ext_iff.mp hp).2, Or.inl (Prod.ext_iff.mp hp).1⟩
      · have hp : ((y, e) : ZMod r × C) = (x + 1, c) := hinj h
        exact ⟨(Prod.ext_iff.mp hp).2, Or.inr (Prod.ext_iff.mp hp).1⟩
    · rintro ⟨rfl, rfl | rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
  by_cases hce : c = e
  · subst hce
    rw [if_pos rfl, Matrix.circulant_apply, defectKernel]
    have h1 : (x - y = 1) = (y = x - 1) := by
      apply propext
      exact ⟨fun h ↦ by linear_combination -h,
        fun h ↦ by linear_combination -h⟩
    have h2 : (x - y = -1) = (y = x + 1) := by
      apply propext
      exact ⟨fun h ↦ by linear_combination -h,
        fun h ↦ by linear_combination -h⟩
    have hADJ : D.Adj (u c x) (u c y) ↔ (y = x - 1 ∨ y = x + 1) := by
      simpa using hadj
    have hxor : ¬(y = x - 1 ∧ y = x + 1) := by
      rintro ⟨rfl, habs⟩
      exact zmod_sub_one_ne_add_one_of_three_le hr3 x habs
    simp only [h1, h2]
    by_cases hy1 : y = x - 1
    · rw [if_pos (hADJ.mpr (Or.inl hy1)), if_pos hy1,
        if_neg fun hy2 ↦ hxor ⟨hy1, hy2⟩, add_zero]
    · by_cases hy2 : y = x + 1
      · rw [if_pos (hADJ.mpr (Or.inr hy2)), if_neg hy1, if_pos hy2,
          zero_add]
      · rw [if_neg fun h ↦ (hADJ.mp h).elim hy1 hy2, if_neg hy1,
          if_neg hy2, add_zero]
  · rw [if_neg hce, if_neg fun h ↦ hce ((hadj.mp h).1.symm)]

/-- Commutation transports to the labeled model. -/
theorem labeledAdjMatrix_comm_cycleDefectMatrix
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : C → ZMod r → V) (hr3 : 3 ≤ r)
    (hbij : Function.Bijective (cycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) = {u c (x - 1), u c (x + 1)})
    (hcommZ : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ) :
    labeledAdjMatrix K G u * cycleDefectMatrix K C r =
      cycleDefectMatrix K C r * labeledAdjMatrix K G u := by
  have hcommK : G.adjMatrix K * D.adjMatrix K =
      D.adjMatrix K * G.adjMatrix K := by
    have h := congrArg (fun A ↦ A.map (Int.castRingHom K)) hcommZ
    simpa only [Matrix.map_mul, adjMatrix_map_intCast] using h
  rw [← submatrix_defect_eq_cycleDefectMatrix D u hr3 hbij.injective huD,
    labeledAdjMatrix, ← Equiv.coe_ofBijective _ hbij,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hcommK]

/-- The even second-order matrix equation transports to the labeled
model. -/
theorem labeledAdjMatrix_sq
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : C → ZMod r → V) (hr3 : 3 ≤ r)
    (hbij : Function.Bijective (cycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) = {u c (x - 1), u c (x + 1)})
    {d : ℕ}
    (hsqZ : G.adjMatrix ℤ * G.adjMatrix ℤ =
      ((d : ℤ) - 1) • (1 : Matrix V V ℤ) +
        FriendshipTheoremOQ01.onesMatrix V - D.adjMatrix ℤ) :
    labeledAdjMatrix K G u * labeledAdjMatrix K G u =
      ((d : K) - 1) • (1 : Matrix (ZMod r × C) (ZMod r × C) K) +
        (Matrix.of fun _ _ : ZMod r × C ↦ (1 : K)) -
          cycleDefectMatrix K C r := by
  have hsqK : G.adjMatrix K * G.adjMatrix K =
      ((d : K) - 1) • (1 : Matrix V V K) +
        (Matrix.of fun _ _ : V ↦ (1 : K)) - D.adjMatrix K := by
    have h := congrArg (fun A ↦ A.map (Int.castRingHom K)) hsqZ
    simp only [Matrix.map_mul, adjMatrix_map_intCast] at h
    rw [h]
    ext a b
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      FriendshipTheoremOQ01.onesMatrix, SimpleGraph.adjMatrix_apply,
      smul_eq_mul]
    split_ifs <;> simp only [eq_intCast] <;> push_cast <;> ring
  rw [← submatrix_defect_eq_cycleDefectMatrix D u hr3 hbij.injective huD,
    labeledAdjMatrix, ← Equiv.coe_ofBijective _ hbij,
    Matrix.submatrix_mul_equiv, hsqK]
  ext z w
  simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul,
    Equiv.coe_ofBijective]
  congr 2
  simp [hbij.injective.eq_iff]

/-- Symmetry transports to the labeled model. -/
theorem labeledAdjMatrix_isSymm (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : C → ZMod r → V) : (labeledAdjMatrix K G u).IsSymm := by
  rw [Matrix.IsSymm, labeledAdjMatrix, Matrix.transpose_submatrix,
    SimpleGraph.transpose_adjMatrix]

/-- Translation invariance of diagonal blocks transports to the labeled
model, via the orientation dichotomy and the vanishing of
reverse-oriented diagonal blocks. -/
theorem labeledAdjMatrix_diag_translationInvariant
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : C → ZMod r → V) (hr3 : 3 ≤ r) (hrOdd : Odd r)
    (hbij : Function.Bijective (cycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) = {u c (x - 1), u c (x + 1)})
    (hcommZ : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ) :
    ∀ (c : C) (x y : ZMod r),
      labeledAdjMatrix K G u (x + 1, c) (y + 1, c) =
        labeledAdjMatrix K G u (x, c) (y, c) := by
  intro c x y
  have huc : Function.Injective (u c) := by
    intro a b hab
    have h : ((a, c) : ZMod r × C) = (b, c) := hbij.injective hab
    exact (Prod.ext_iff.mp h).1
  have hiff := graph_equalOddCycle_diagBlock_adj_shift_iff hr3 hrOdd G D
    (u c) huc hcommZ (huD c) x y
  simp only [labeledAdjMatrix_apply, SimpleGraph.adjMatrix_apply, hiff]

/-- **The Fourier weight is the diagonal-anchor multiplicity.**  The
displacement-`t` weight of the labeled model is exactly the number of
cycles whose zero-row block support contains `t`. -/
theorem sum_labeledAdjMatrix_diag_eq_anchorMultiplicity
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : C → ZMod r → V)
    (t : ZMod r) :
    ∑ c : C, labeledAdjMatrix K G u (0, c) (t, c) =
      ((anchorMultiplicity
        (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c)) t : ℕ) : K) := by
  have hmem : ∀ c : C,
      G.Adj (u c 0) (u c t) ↔
        t ∈ graphCycleBlockZeroSupport G (u c) (u c) := by
    intro c
    rw [graphCycleBlockZeroSupport, mem_zeroRowSupport_iff]
    simp [SimpleGraph.adjMatrix_apply]
  simp only [labeledAdjMatrix_apply, SimpleGraph.adjMatrix_apply]
  rw [Finset.sum_boole]
  rw [anchorMultiplicity]
  congr 2
  exact Finset.filter_congr fun c _ ↦ hmem c

end Transport

/-! ## Graph-facing frequency-pair bridge -/

section GraphFacing

variable {K : Type*} [Field K]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {C : Type*} [Fintype C] [DecidableEq C]
variable {r p : ℕ} [NeZero r] [NeZero p]

/-- **Graph-facing square identity** `T² = (d - 1 - (ζ + ζ⁻¹)) • id` for
the restriction of the labeled adjacency operator to the frequency-pair
space. -/
theorem graph_defectEigenspaceRestrict_sq
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : C → ZMod r → V) (hr3 : 3 ≤ r)
    (hbij : Function.Bijective (cycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) = {u c (x - 1), u c (x + 1)})
    {d : ℕ}
    (hsqZ : G.adjMatrix ℤ * G.adjMatrix ℤ =
      ((d : ℤ) - 1) • (1 : Matrix V V ℤ) +
        FriendshipTheoremOQ01.onesMatrix V - D.adjMatrix ℤ)
    (hcomm : labeledAdjMatrix K G u * cycleDefectMatrix K C r =
      cycleDefectMatrix K C r * labeledAdjMatrix K G u)
    {ζ : K} (hζr : ζ ^ r = 1) (hζ1 : ζ ≠ 1) :
    defectEigenspaceRestrict (labeledAdjMatrix K G u) hcomm (ζ + ζ⁻¹) *
        defectEigenspaceRestrict (labeledAdjMatrix K G u) hcomm (ζ + ζ⁻¹) =
      ((d : K) - 1 - (ζ + ζ⁻¹)) • LinearMap.id :=
  defectEigenspaceRestrict_sq_ones hcomm
    (labeledAdjMatrix_sq G D u hr3 hbij huD hsqZ) hζr hζ1

/-- **Graph-facing frequency-pair trace identity**
`trace T = 2 · H(ζ)`: the trace of the restricted adjacency operator is
twice the prime Fourier transform of the projected diagonal-anchor
multiplicity. -/
theorem graph_trace_eq_two_mul_projected_anchor_fourier
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : C → ZMod r → V) (hr3 : 3 ≤ r) (hrOdd : Odd r) (hdvd : p ∣ r)
    (hbij : Function.Bijective (cycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) = {u c (x - 1), u c (x + 1)})
    (hcommZ : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    (hcomm : labeledAdjMatrix K G u * cycleDefectMatrix K C r =
      cycleDefectMatrix K C r * labeledAdjMatrix K G u)
    {ζ : K} (hζp : ζ ^ p = 1) (hζsq : ζ ^ 2 ≠ 1) (hr0 : (r : K) ≠ 0) :
    LinearMap.trace K
        (defectEigenspace (cycleDefectMatrix K C r) (ζ + ζ⁻¹))
        (defectEigenspaceRestrict (labeledAdjMatrix K G u) hcomm
          (ζ + ζ⁻¹)) =
      2 * ∑ s : ZMod p,
        ((projectedMultiplicity (ZMod.castHom hdvd (ZMod p))
          (anchorMultiplicity
            (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))) s : ℕ) :
              K) * ζ ^ s.val :=
  trace_defectEigenspaceRestrict_eq_two_mul_projected_fourier hcomm
    (labeledAdjMatrix_diag_translationInvariant G D u hr3 hrOdd hbij huD
      hcommZ)
    (labeledAdjMatrix_isSymm G u) hrOdd hdvd hζp hζsq hr0
    (anchorMultiplicity fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))
    (fun t ↦ sum_labeledAdjMatrix_diag_eq_anchorMultiplicity G u t)

/-- **Graph-facing square branch**: if `d - 1 - μ = s²` is a nonzero
square, the projected anchor Fourier transform is an integral multiple of
`s`. -/
theorem graph_projected_anchor_fourier_eq_int_mul_of_sq [CharZero K]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : C → ZMod r → V) (hr3 : 3 ≤ r) (hrOdd : Odd r) (hdvd : p ∣ r)
    (hbij : Function.Bijective (cycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) = {u c (x - 1), u c (x + 1)})
    (hcommZ : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    {d : ℕ}
    (hsqZ : G.adjMatrix ℤ * G.adjMatrix ℤ =
      ((d : ℤ) - 1) • (1 : Matrix V V ℤ) +
        FriendshipTheoremOQ01.onesMatrix V - D.adjMatrix ℤ)
    {ζ : K} (hζp : ζ ^ p = 1) (hζsq : ζ ^ 2 ≠ 1)
    {s : K} (hs : s ≠ 0) (hκ : (d : K) - 1 - (ζ + ζ⁻¹) = s * s) :
    ∃ w : ℤ,
      ∑ y : ZMod p,
        ((projectedMultiplicity (ZMod.castHom hdvd (ZMod p))
          (anchorMultiplicity
            (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))) y : ℕ) :
              K) * ζ ^ y.val = (w : K) * s :=
  projected_fourier_eq_int_mul_of_sq
    (labeledAdjMatrix_comm_cycleDefectMatrix G D u hr3 hbij huD hcommZ)
    (labeledAdjMatrix_sq G D u hr3 hbij huD hsqZ)
    (labeledAdjMatrix_diag_translationInvariant G D u hr3 hrOdd hbij huD
      hcommZ)
    (labeledAdjMatrix_isSymm G u) hrOdd hdvd hζp hζsq hs hκ
    (anchorMultiplicity fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))
    (fun t ↦ sum_labeledAdjMatrix_diag_eq_anchorMultiplicity G u t)

/-- **Graph-facing vanishing branch**: if the frequency-pair trace is
zero, the projected anchor Fourier transform vanishes — the hypothesis of
the prime Fourier uniformity terminal. -/
theorem graph_projected_anchor_fourier_eq_zero_of_trace_eq_zero
    [CharZero K]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : C → ZMod r → V) (hr3 : 3 ≤ r) (hrOdd : Odd r) (hdvd : p ∣ r)
    (hbij : Function.Bijective (cycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) = {u c (x - 1), u c (x + 1)})
    (hcommZ : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    (hcomm : labeledAdjMatrix K G u * cycleDefectMatrix K C r =
      cycleDefectMatrix K C r * labeledAdjMatrix K G u)
    {ζ : K} (hζp : ζ ^ p = 1) (hζsq : ζ ^ 2 ≠ 1)
    (htrace0 : LinearMap.trace K
      (defectEigenspace (cycleDefectMatrix K C r) (ζ + ζ⁻¹))
      (defectEigenspaceRestrict (labeledAdjMatrix K G u) hcomm
        (ζ + ζ⁻¹)) = 0) :
    ∑ y : ZMod p,
      ((projectedMultiplicity (ZMod.castHom hdvd (ZMod p))
        (anchorMultiplicity
          (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))) y : ℕ) :
            K) * ζ ^ y.val = 0 :=
  projected_fourier_eq_zero_of_trace_eq_zero hcomm
    (labeledAdjMatrix_diag_translationInvariant G D u hr3 hrOdd hbij huD
      hcommZ)
    (labeledAdjMatrix_isSymm G u) hrOdd hdvd hζp hζsq
    (anchorMultiplicity fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))
    (fun t ↦ sum_labeledAdjMatrix_diag_eq_anchorMultiplicity G u t)
    htrace0

end GraphFacing

end

end Erdos85
