import Mathlib

/-! The modulo-five step for q7 mixed fifth traces. Frobenius is applied to
an actual integer matrix, avoiding assumptions about residual root arithmetic.
The graph-specific fifth-trace expansion remains an explicit premise. -/
namespace Erdos85
open Matrix Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A trace-zero integer matrix has fifth trace divisible by5. -/
theorem five_dvd_trace_fifth_of_trace_zero (A : Matrix V V ℤ)
    (htrace : Matrix.trace A = 0) : (5 : ℤ) ∣ Matrix.trace (A ^ 5) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let f := Int.castRingHom (ZMod 5)
  let B : Matrix V V (ZMod 5) := A.map f
  have hmap (n : ℕ) : ((Matrix.trace (A ^ n) : ℤ) : ZMod 5) =
      Matrix.trace (B ^ n) := by
    rw [Matrix.trace, Matrix.trace]
    push_cast
    change (∑ x, f ((A ^ n) x x)) = ∑ x, ((A.map f) ^ n) x x
    rw [← Matrix.map_pow]
    rfl
  have hf := ZMod.trace_pow_card (p := 5) B
  have hb : Matrix.trace B = 0 := by
    simpa [htrace] using (hmap 1).symm
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp
  rw [hmap 5, hf, hb]
  norm_num

/-- The established q7 fifth-trace expansion forces the mixed overlap residue.
This theorem consumes that expansion; it does not assert it for arbitrary matrices. -/
theorem mixed_defect_trace_residue_of_fifth_identity (A : Matrix V V ℤ)
    (htrace : Matrix.trace A = 0) (h T R : ℤ)
    (hidentity : Matrix.trace (A ^ 5) = 12691 + 549*h + 72*T + R) :
    Int.ModEq 5 R (3*T+h+4) := by
  obtain ⟨k, hk⟩ := five_dvd_trace_fifth_of_trace_zero A htrace
  rw [hidentity] at hk
  change R % 5 = (3*T+h+4) % 5
  omega
end Erdos85
