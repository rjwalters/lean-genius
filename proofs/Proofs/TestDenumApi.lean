import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Data.Rat.Denumerable
import Mathlib.Logic.Denumerable
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic

-- Search for the isomorphism theorem with various name patterns
#check @Order.iso_of_countable_dense
-- #check @Order.orderIsoOfCountableDenseLinearOrder
-- #check @OrderIso.ofCountableDenseLinearOrder

-- Check what exists in Order namespace
#check @Order.PartialIso
#check @Order.PartialIso.comm
#check @Order.exists_between_finsets
-- Check if there's an OrderIso instance derived from PartialIso
-- #check @Order.PartialIso.toOrderIso
-- #check @Order.orderIsoNatEquivRat

-- Try the Nonempty approach
example : Nonempty (ℚ ≃o ℚ) := ⟨OrderIso.refl ℚ⟩

-- The actual theorem might produce Nonempty (α ≃o β)
-- #check @nonempty_orderIso_of_countable_dense_linear_order
