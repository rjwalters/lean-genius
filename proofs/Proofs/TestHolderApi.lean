-- Test Hölder inequality API availability in Docker Mathlib
import Mathlib

-- Available:
#check NNReal.young_inequality
#check ENNReal.lintegral_mul_le_Lp_mul_Lq
#check @MeasureTheory.L2.inner_def

-- Check HolderConjugate
#check Real.HolderConjugate
#check NNReal.HolderConjugate

-- Check if p=2 gives conjugate q=2
#check @Real.HolderConjugate.symm

-- ENNReal power mean
#check ENNReal.rpow_natCast
#check ENNReal.rpow_le_rpow

-- Lp spaces for general p
#check @MeasureTheory.Lp
#check @MeasureTheory.MemLp

-- eLpNorm (Lp norm for general p)
#check @MeasureTheory.eLpNorm
#check @MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm

-- Complex inner product
#check @inner_self_eq_norm_sq

-- Minkowski/triangle inequality on Lp
#check @MeasureTheory.eLpNorm_add_le

-- Check NNReal Hölder conjugate for p=q=2
example : NNReal.HolderConjugate 2 2 := by
  rw [NNReal.holderConjugate_iff]
  norm_num
