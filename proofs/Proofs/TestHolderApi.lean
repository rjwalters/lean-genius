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

-- snorm (Lp norm for general p)
#check @MeasureTheory.snorm
#check @MeasureTheory.snorm_le_snorm_mul_snorm_of_nq

-- Complex inner product
#check @inner_self_eq_norm_sq

-- Minkowski/triangle inequality on Lp
#check @MeasureTheory.snorm_add_le

-- Check NNReal Hölder conjugate for p=q=2
example : NNReal.HolderConjugate 2 2 := by
  rw [NNReal.HolderConjugate]
  norm_num
