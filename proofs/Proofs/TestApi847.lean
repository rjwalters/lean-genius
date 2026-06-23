-- Test API availability for Erdos847 proof
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Card

-- Check pigeonhole
#check @Finset.exists_lt_card_fiber_of_nsmul_lt_card

-- Check Finset filtering
#check Finset.filter_subset
#check Finset.card_filter_le

-- Check Finset.card_le_card
#check Finset.card_le_card

-- Check division
#check Nat.div_le_self
