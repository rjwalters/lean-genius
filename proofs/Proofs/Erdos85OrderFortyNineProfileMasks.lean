import Proofs.Erdos85OrderFortyNineCnfSegments

/-!
# Canonical h=9 profile masks

This is the Lean counterpart of the vertex-layout code in
`sat49/certify_t34.py`: highs first, then triple supports, uncovered pairs,
singleton repetitions grouped by high point, and finally empty supports.
-/

namespace Erdos85

structure OrderFortyNineH9Triple where
  a : Nat
  b : Nat
  c : Nat
deriving DecidableEq, Repr

abbrev OrderFortyNineH9System := List OrderFortyNineH9Triple

def orderFortyNineH9Triple (a b c : Nat) : OrderFortyNineH9Triple := ⟨a, b, c⟩

def OrderFortyNineH9Triple.mask (t : OrderFortyNineH9Triple) : Nat :=
  2 ^ t.a + 2 ^ t.b + 2 ^ t.c

def OrderFortyNineH9Triple.containsPair
    (t : OrderFortyNineH9Triple) (a b : Nat) : Bool :=
  (a == t.a && b == t.b) ||
  (a == t.a && b == t.c) ||
  (a == t.b && b == t.c)

def OrderFortyNineH9Triple.contains
    (t : OrderFortyNineH9Triple) (w : Nat) : Bool :=
  w == t.a || w == t.b || w == t.c

def orderFortyNineH9PairMasks (sys : OrderFortyNineH9System) : List Nat :=
  orderFortyNineHighPairs.filterMap fun ab =>
    if sys.any fun t => t.containsPair ab.1.val ab.2.val then
      none
    else
      some (2 ^ ab.1.val + 2 ^ ab.2.val)

def orderFortyNineH9SingletonMasks (sys : OrderFortyNineH9System) : List Nat :=
  (List.finRange 9).flatMap fun w =>
    List.replicate (sys.countP fun t => t.contains w.val) (2 ^ w.val)

def orderFortyNineH9ProfileMaskList (sys : OrderFortyNineH9System) : List Nat :=
  let core := List.replicate 9 0 ++ sys.map (·.mask) ++
    orderFortyNineH9PairMasks sys ++ orderFortyNineH9SingletonMasks sys
  core ++ List.replicate (49 - core.length) 0

def orderFortyNineH9ProfileMasks (sys : OrderFortyNineH9System) : Array Nat :=
  (orderFortyNineH9ProfileMaskList sys).toArray

def orderFortyNineH9T2Systems : Array OrderFortyNineH9System := #[
  [orderFortyNineH9Triple 0 1 2, orderFortyNineH9Triple 3 4 5],
  [orderFortyNineH9Triple 0 1 2, orderFortyNineH9Triple 0 3 4]
]

def orderFortyNineH9T3Systems : Array OrderFortyNineH9System := #[
  [orderFortyNineH9Triple 0 1 2, orderFortyNineH9Triple 3 4 5,
    orderFortyNineH9Triple 3 6 7],
  [orderFortyNineH9Triple 0 1 2, orderFortyNineH9Triple 3 4 5,
    orderFortyNineH9Triple 6 7 8],
  [orderFortyNineH9Triple 0 1 2, orderFortyNineH9Triple 0 3 4,
    orderFortyNineH9Triple 0 5 6],
  [orderFortyNineH9Triple 0 1 2, orderFortyNineH9Triple 0 3 4,
    orderFortyNineH9Triple 1 3 5],
  [orderFortyNineH9Triple 0 1 2, orderFortyNineH9Triple 0 3 4,
    orderFortyNineH9Triple 1 5 6]
]

def orderFortyNineH9T4Systems : Array OrderFortyNineH9System := #[
  [orderFortyNineH9Triple 0 1 2, orderFortyNineH9Triple 3 4 5,
    orderFortyNineH9Triple 3 6 7, orderFortyNineH9Triple 4 6 8],
  [orderFortyNineH9Triple 0 1 2, orderFortyNineH9Triple 0 3 4,
    orderFortyNineH9Triple 0 5 6, orderFortyNineH9Triple 0 7 8],
  [orderFortyNineH9Triple 0 1 2, orderFortyNineH9Triple 0 3 4,
    orderFortyNineH9Triple 0 5 6, orderFortyNineH9Triple 1 3 5],
  [orderFortyNineH9Triple 0 1 2, orderFortyNineH9Triple 0 3 4,
    orderFortyNineH9Triple 0 5 6, orderFortyNineH9Triple 1 3 7],
  [orderFortyNineH9Triple 0 1 2, orderFortyNineH9Triple 0 3 4,
    orderFortyNineH9Triple 0 5 6, orderFortyNineH9Triple 1 7 8],
  [orderFortyNineH9Triple 0 1 2, orderFortyNineH9Triple 0 3 4,
    orderFortyNineH9Triple 1 3 5, orderFortyNineH9Triple 2 4 5],
  [orderFortyNineH9Triple 0 1 2, orderFortyNineH9Triple 0 3 4,
    orderFortyNineH9Triple 1 3 5, orderFortyNineH9Triple 2 4 6],
  [orderFortyNineH9Triple 0 1 2, orderFortyNineH9Triple 0 3 4,
    orderFortyNineH9Triple 1 3 5, orderFortyNineH9Triple 2 6 7],
  [orderFortyNineH9Triple 0 1 2, orderFortyNineH9Triple 0 3 4,
    orderFortyNineH9Triple 1 5 6, orderFortyNineH9Triple 2 7 8],
  [orderFortyNineH9Triple 0 1 2, orderFortyNineH9Triple 0 3 4,
    orderFortyNineH9Triple 1 5 6, orderFortyNineH9Triple 3 5 7],
  [orderFortyNineH9Triple 0 1 2, orderFortyNineH9Triple 0 3 4,
    orderFortyNineH9Triple 1 5 6, orderFortyNineH9Triple 3 7 8]
]

theorem orderFortyNineH9T4Rep0Masks_generated :
    orderFortyNineH9ProfileMasks orderFortyNineH9T4Systems[0]! =
      orderFortyNineH9T4Rep0Masks := by
  native_decide

theorem orderFortyNineH9ProfileMasks_high_zero
    (sys : OrderFortyNineH9System) :
    OrderFortyNineHighMasksZero (orderFortyNineH9ProfileMasks sys) := by
  intro a w
  fin_cases a <;>
    simp [orderFortyNineH9ProfileMasks, orderFortyNineH9ProfileMaskList,
      orderFortyNineSupportMask, orderFortyNineHighVertex]

end Erdos85
