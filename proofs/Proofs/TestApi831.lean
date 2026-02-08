-- Test API availability for Erdos831
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Card

-- Test: Can we use Set.Finite from these imports?
#check @Set.Finite
#check EuclideanSpace ℝ (Fin 2)
#check Finset.card
#check Nat.card
#check sInf
