import Mathlib

-- Test Mathlib's Schnirelmann density API availability
#check schnirelmannDensity
#check schnirelmannDensity_nonneg
#check schnirelmannDensity_le_one

-- Test Set operations we need
#check Set.image2
#check Set.range

-- Test Filter/Asymptotics
#check Filter.atTop
#check Asymptotics.IsLittleO
#check Real.log
