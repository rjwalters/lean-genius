import Proofs.Erdos85ResidualSixthMomentStrict
import Proofs.Erdos85SymmetricCubeTraceSquares
import Proofs.Erdos85CubicDiagonalParity

/-! # Evenness and parity rounding of the service sixth trace -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- A symmetric integer matrix whose cubic diagonal is even has even sixth
trace. Off-diagonal squares pair under transposition; diagonal squares
vanish modulo two. -/
theorem even_trace_pow_six_of_cube_diag_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℤ) (hA : A.IsSymm)
    (hdiag : ∀ i, Even ((A ^ 3) i i)) :
    Even (Matrix.trace (A ^ 6)) := by
  let B := A ^ 3
  let f : V × V → ZMod 2 := fun ij ↦ ((B ij.1 ij.2) ^ 2 : ℤ)
  have hB : B.IsSymm := hA.pow 3
  have hsum : ∑ ij ∈ (Finset.univ ×ˢ Finset.univ), f ij = 0 := by
    apply Finset.sum_involution
      (fun ij _ ↦ (ij.2, ij.1))
    · intro ij hij
      have hijSym : B ij.2 ij.1 = B ij.1 ij.2 :=
        congrFun (congrFun hB.eq ij.1) ij.2
      simp only [f, hijSym]
      push_cast
      have htwo : (2 : ZMod 2) = 0 := by decide
      rw [← two_mul, htwo, zero_mul]
    · intro ij hij hf
      intro heq
      have hii : ij.1 = ij.2 := (congrArg Prod.fst heq).symm
      have heven : (2 : ℤ) ∣ B ij.1 ij.1 :=
        even_iff_two_dvd.mp (hdiag ij.1)
      have hzero : (B ij.1 ij.1 : ZMod 2) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).2 heven
      apply hf
      simp only [f]
      rw [← hii]
      push_cast
      rw [hzero]
      norm_num
    · intro ij hij
      simp
    · intro ij hij
      rfl
  rw [even_iff_two_dvd]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
  rw [trace_pow_six_eq_sum_cube_apply_sq A hA]
  push_cast
  rw [← Finset.sum_product']
  simpa [B, f] using hsum

/-- Every simple graph has even sixth adjacency trace. -/
theorem even_trace_int_adjMatrix_pow_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Even (Matrix.trace ((G.adjMatrix ℤ) ^ 6)) := by
  apply even_trace_pow_six_of_cube_diag_even
  · exact G.isSymm_adjMatrix
  · intro i
    simpa [pow_succ] using even_adjMatrix_cube_apply_self G i

/-- Strictness plus parity raises the integer service threshold to `61250`. -/
theorem trace_int_adjMatrix_pow_six_ge_61250_of_complex_strict
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hstrict : 61248 < (Matrix.trace ((G.adjMatrix ℂ) ^ 6)).re) :
    61250 ≤ Matrix.trace ((G.adjMatrix ℤ) ^ 6) := by
  have hge := trace_int_adjMatrix_pow_six_ge_61249_of_complex_strict G hstrict
  have heven := even_trace_int_adjMatrix_pow_six G
  rcases heven with ⟨k, hk⟩
  omega

end

end Erdos85

#print axioms Erdos85.even_trace_pow_six_of_cube_diag_even
#print axioms Erdos85.even_trace_int_adjMatrix_pow_six
#print axioms
  Erdos85.trace_int_adjMatrix_pow_six_ge_61250_of_complex_strict
