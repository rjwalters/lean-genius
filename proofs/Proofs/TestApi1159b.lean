import Mathlib

open Configuration

-- Check HasLines fields
#check @HasLines.mkFinOrder
#print HasLines

-- Check HasPoints fields
#print HasPoints

-- Check if mkLine exists
#check @HasLines.mkLine

-- Check if there's a mkPoint
#check @HasPoints.mkPoint

-- Check for line intersection results (two lines in a projective plane meet)
#check @ProjectivePlane.mkFinOrder

-- Print the ProjectivePlane class
#print ProjectivePlane

-- Check Set.Nonempty
#check @Set.Nonempty

-- Check Finset.card_le_card
#check @Finset.card_le_card

-- Check Set.nontrivial
#check @Set.nontrivial_iff_exists_ne
