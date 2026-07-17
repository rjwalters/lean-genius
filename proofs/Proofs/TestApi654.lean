import Mathlib

-- Check what APIs are available for fiber-based cardinality bounds
#check @Finset.card_le_card_of_injOn
#check @Finset.card_image_le
#check @Finset.card_eq_sum_card_fiberwise
#check @Finset.card_biUnion_le
#check @Finset.card_le_card
-- Check: does sum_card_fiberwise_eq_card exist?
-- We need: S.card = (S.image f).sum (fun t => (S.filter (fun x => f x = t)).card)

-- Check Nat.div_le
#check Nat.div_le_iff_le_mul
#check Nat.le_div_iff_mul_le
