import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- Test Finset.Icc card
#check @Finset.card_Icc
#check @Nat.card_Icc

-- Test Set.Finite
#check @Set.Finite.subset
#check @Set.finite_Icc

-- Test a simple card_Icc usage
example : (Finset.Icc 3 7).card = 5 := by decide
