import Proofs.Erdos85OrderFortyNineCanonicalTripleSystem

/-!
# Target-side fiber census for the canonical h=9 profile masks

For every canonical representative system (2 + 5 + 11 across t = 2, 3, 4) this
file verifies the exact multiplicity of each high support among the 49 entries
of `orderFortyNineH9ProfileMasks rep`:

* empty support: `13 − t` entries (the 9 high rows plus `4 − t` trailing pads);
* singleton `{w}`: as many entries as triples of the rep containing `w`;
* pair `{a, b}`: exactly one entry if no triple covers the pair, none otherwise;
* triple: exactly one entry if it is a rep triple, none otherwise;
* supports of size ≥ 4: none.

The census is split into kernel-checked chunks, one for each of the 18
representatives and all 512 subsets of `Fin 9`, together with a bridge to the
`Fintype.card` form consumed by
`exists_orderFortyNine_vertexLabeling_of_supportFiberCardEq`.
-/

namespace Erdos85

set_option maxRecDepth 100000

/-- Fiber size of a support among the 49 canonical mask entries. -/
def orderFortyNineMaskFiberCount (masks : Array Nat) (S : Finset (Fin 9)) :
    Nat :=
  (Finset.univ.filter fun i : Fin 49 =>
    orderFortyNineMaskSupport masks i = S).card

/-- Bit mask of a subset of `Fin 9`. -/
def orderFortyNineFinsetMask (S : Finset (Fin 9)) : Nat :=
  S.sum fun w => 2 ^ w.val

/-- Predicted fiber size of a support for a given canonical system. -/
def orderFortyNineExpectedFiber (sys : OrderFortyNineH9System)
    (S : Finset (Fin 9)) : Nat :=
  let m := orderFortyNineFinsetMask S
  if S.card == 0 then 13 - sys.length
  else if S.card == 1 then sys.countP fun tr => tr.mask &&& m == m
  else if S.card == 2 then
    if sys.any (fun tr => tr.mask &&& m == m) then 0 else 1
  else if S.card == 3 then
    if sys.any (fun tr => tr.mask == m) then 1 else 0
  else 0

/-- All 18 canonical representatives in table order. -/
def orderFortyNineAllH9Reps : List OrderFortyNineH9System :=
  orderFortyNineH9T2Systems.toList ++ orderFortyNineH9T3Systems.toList ++
    orderFortyNineH9T4Systems.toList

private theorem orderFortyNineMaskFiberCount_eq_expected_t2_rep0
    (S : Finset (Fin 9)) :
    orderFortyNineMaskFiberCount
        (orderFortyNineH9ProfileMasks orderFortyNineH9T2Systems[0]!) S =
      orderFortyNineExpectedFiber orderFortyNineH9T2Systems[0]! S := by
  decide +revert

private theorem orderFortyNineMaskFiberCount_eq_expected_t2_rep1
    (S : Finset (Fin 9)) :
    orderFortyNineMaskFiberCount
        (orderFortyNineH9ProfileMasks orderFortyNineH9T2Systems[1]!) S =
      orderFortyNineExpectedFiber orderFortyNineH9T2Systems[1]! S := by
  decide +revert

private theorem orderFortyNineMaskFiberCount_eq_expected_t3_rep0
    (S : Finset (Fin 9)) :
    orderFortyNineMaskFiberCount
        (orderFortyNineH9ProfileMasks orderFortyNineH9T3Systems[0]!) S =
      orderFortyNineExpectedFiber orderFortyNineH9T3Systems[0]! S := by
  decide +revert

private theorem orderFortyNineMaskFiberCount_eq_expected_t3_rep1
    (S : Finset (Fin 9)) :
    orderFortyNineMaskFiberCount
        (orderFortyNineH9ProfileMasks orderFortyNineH9T3Systems[1]!) S =
      orderFortyNineExpectedFiber orderFortyNineH9T3Systems[1]! S := by
  decide +revert

private theorem orderFortyNineMaskFiberCount_eq_expected_t3_rep2
    (S : Finset (Fin 9)) :
    orderFortyNineMaskFiberCount
        (orderFortyNineH9ProfileMasks orderFortyNineH9T3Systems[2]!) S =
      orderFortyNineExpectedFiber orderFortyNineH9T3Systems[2]! S := by
  decide +revert

private theorem orderFortyNineMaskFiberCount_eq_expected_t3_rep3
    (S : Finset (Fin 9)) :
    orderFortyNineMaskFiberCount
        (orderFortyNineH9ProfileMasks orderFortyNineH9T3Systems[3]!) S =
      orderFortyNineExpectedFiber orderFortyNineH9T3Systems[3]! S := by
  decide +revert

private theorem orderFortyNineMaskFiberCount_eq_expected_t3_rep4
    (S : Finset (Fin 9)) :
    orderFortyNineMaskFiberCount
        (orderFortyNineH9ProfileMasks orderFortyNineH9T3Systems[4]!) S =
      orderFortyNineExpectedFiber orderFortyNineH9T3Systems[4]! S := by
  decide +revert

private theorem orderFortyNineMaskFiberCount_eq_expected_t4_rep0
    (S : Finset (Fin 9)) :
    orderFortyNineMaskFiberCount
        (orderFortyNineH9ProfileMasks orderFortyNineH9T4Systems[0]!) S =
      orderFortyNineExpectedFiber orderFortyNineH9T4Systems[0]! S := by
  decide +revert

private theorem orderFortyNineMaskFiberCount_eq_expected_t4_rep1
    (S : Finset (Fin 9)) :
    orderFortyNineMaskFiberCount
        (orderFortyNineH9ProfileMasks orderFortyNineH9T4Systems[1]!) S =
      orderFortyNineExpectedFiber orderFortyNineH9T4Systems[1]! S := by
  decide +revert

private theorem orderFortyNineMaskFiberCount_eq_expected_t4_rep2
    (S : Finset (Fin 9)) :
    orderFortyNineMaskFiberCount
        (orderFortyNineH9ProfileMasks orderFortyNineH9T4Systems[2]!) S =
      orderFortyNineExpectedFiber orderFortyNineH9T4Systems[2]! S := by
  decide +revert

private theorem orderFortyNineMaskFiberCount_eq_expected_t4_rep3
    (S : Finset (Fin 9)) :
    orderFortyNineMaskFiberCount
        (orderFortyNineH9ProfileMasks orderFortyNineH9T4Systems[3]!) S =
      orderFortyNineExpectedFiber orderFortyNineH9T4Systems[3]! S := by
  decide +revert

private theorem orderFortyNineMaskFiberCount_eq_expected_t4_rep4
    (S : Finset (Fin 9)) :
    orderFortyNineMaskFiberCount
        (orderFortyNineH9ProfileMasks orderFortyNineH9T4Systems[4]!) S =
      orderFortyNineExpectedFiber orderFortyNineH9T4Systems[4]! S := by
  decide +revert

private theorem orderFortyNineMaskFiberCount_eq_expected_t4_rep5
    (S : Finset (Fin 9)) :
    orderFortyNineMaskFiberCount
        (orderFortyNineH9ProfileMasks orderFortyNineH9T4Systems[5]!) S =
      orderFortyNineExpectedFiber orderFortyNineH9T4Systems[5]! S := by
  decide +revert

private theorem orderFortyNineMaskFiberCount_eq_expected_t4_rep6
    (S : Finset (Fin 9)) :
    orderFortyNineMaskFiberCount
        (orderFortyNineH9ProfileMasks orderFortyNineH9T4Systems[6]!) S =
      orderFortyNineExpectedFiber orderFortyNineH9T4Systems[6]! S := by
  decide +revert

private theorem orderFortyNineMaskFiberCount_eq_expected_t4_rep7
    (S : Finset (Fin 9)) :
    orderFortyNineMaskFiberCount
        (orderFortyNineH9ProfileMasks orderFortyNineH9T4Systems[7]!) S =
      orderFortyNineExpectedFiber orderFortyNineH9T4Systems[7]! S := by
  decide +revert

private theorem orderFortyNineMaskFiberCount_eq_expected_t4_rep8
    (S : Finset (Fin 9)) :
    orderFortyNineMaskFiberCount
        (orderFortyNineH9ProfileMasks orderFortyNineH9T4Systems[8]!) S =
      orderFortyNineExpectedFiber orderFortyNineH9T4Systems[8]! S := by
  decide +revert

private theorem orderFortyNineMaskFiberCount_eq_expected_t4_rep9
    (S : Finset (Fin 9)) :
    orderFortyNineMaskFiberCount
        (orderFortyNineH9ProfileMasks orderFortyNineH9T4Systems[9]!) S =
      orderFortyNineExpectedFiber orderFortyNineH9T4Systems[9]! S := by
  decide +revert

private theorem orderFortyNineMaskFiberCount_eq_expected_t4_rep10
    (S : Finset (Fin 9)) :
    orderFortyNineMaskFiberCount
        (orderFortyNineH9ProfileMasks orderFortyNineH9T4Systems[10]!) S =
      orderFortyNineExpectedFiber orderFortyNineH9T4Systems[10]! S := by
  decide +revert

private theorem orderFortyNineAllH9Reps_cases
    (sys : OrderFortyNineH9System) (hsys : sys ∈ orderFortyNineAllH9Reps) :
    sys = orderFortyNineH9T2Systems[0]! ∨
      sys = orderFortyNineH9T2Systems[1]! ∨
      sys = orderFortyNineH9T3Systems[0]! ∨
      sys = orderFortyNineH9T3Systems[1]! ∨
      sys = orderFortyNineH9T3Systems[2]! ∨
      sys = orderFortyNineH9T3Systems[3]! ∨
      sys = orderFortyNineH9T3Systems[4]! ∨
      sys = orderFortyNineH9T4Systems[0]! ∨
      sys = orderFortyNineH9T4Systems[1]! ∨
      sys = orderFortyNineH9T4Systems[2]! ∨
      sys = orderFortyNineH9T4Systems[3]! ∨
      sys = orderFortyNineH9T4Systems[4]! ∨
      sys = orderFortyNineH9T4Systems[5]! ∨
      sys = orderFortyNineH9T4Systems[6]! ∨
      sys = orderFortyNineH9T4Systems[7]! ∨
      sys = orderFortyNineH9T4Systems[8]! ∨
      sys = orderFortyNineH9T4Systems[9]! ∨
      sys = orderFortyNineH9T4Systems[10]! := by
  decide +revert

/-- Master census: the canonical mask fibers realize the predicted counts for
every representative and every support. -/
theorem orderFortyNineMaskFiberCount_eq_expected :
    ∀ sys ∈ orderFortyNineAllH9Reps, ∀ S : Finset (Fin 9),
      orderFortyNineMaskFiberCount (orderFortyNineH9ProfileMasks sys) S =
        orderFortyNineExpectedFiber sys S := by
  intro sys hsys S
  rcases orderFortyNineAllH9Reps_cases sys hsys with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst sys
    exact orderFortyNineMaskFiberCount_eq_expected_t2_rep0 S
  · subst sys
    exact orderFortyNineMaskFiberCount_eq_expected_t2_rep1 S
  · subst sys
    exact orderFortyNineMaskFiberCount_eq_expected_t3_rep0 S
  · subst sys
    exact orderFortyNineMaskFiberCount_eq_expected_t3_rep1 S
  · subst sys
    exact orderFortyNineMaskFiberCount_eq_expected_t3_rep2 S
  · subst sys
    exact orderFortyNineMaskFiberCount_eq_expected_t3_rep3 S
  · subst sys
    exact orderFortyNineMaskFiberCount_eq_expected_t3_rep4 S
  · subst sys
    exact orderFortyNineMaskFiberCount_eq_expected_t4_rep0 S
  · subst sys
    exact orderFortyNineMaskFiberCount_eq_expected_t4_rep1 S
  · subst sys
    exact orderFortyNineMaskFiberCount_eq_expected_t4_rep2 S
  · subst sys
    exact orderFortyNineMaskFiberCount_eq_expected_t4_rep3 S
  · subst sys
    exact orderFortyNineMaskFiberCount_eq_expected_t4_rep4 S
  · subst sys
    exact orderFortyNineMaskFiberCount_eq_expected_t4_rep5 S
  · subst sys
    exact orderFortyNineMaskFiberCount_eq_expected_t4_rep6 S
  · subst sys
    exact orderFortyNineMaskFiberCount_eq_expected_t4_rep7 S
  · subst sys
    exact orderFortyNineMaskFiberCount_eq_expected_t4_rep8 S
  · subst sys
    exact orderFortyNineMaskFiberCount_eq_expected_t4_rep9 S
  · subst sys
    exact orderFortyNineMaskFiberCount_eq_expected_t4_rep10 S


/-- Bridge to the subtype-cardinality form used by the vertex-labeling
constructor. -/
theorem orderFortyNine_card_maskFiber (masks : Array Nat)
    (S : Finset (Fin 9)) :
    Fintype.card {i : Fin 49 // orderFortyNineMaskSupport masks i = S} =
      orderFortyNineMaskFiberCount masks S :=
  Fintype.card_subtype _

/-- Convenience: the census in subtype-cardinality form. -/
theorem orderFortyNine_card_maskFiber_eq_expected
    {sys : OrderFortyNineH9System} (hsys : sys ∈ orderFortyNineAllH9Reps)
    (S : Finset (Fin 9)) :
    Fintype.card
        {i : Fin 49 //
          orderFortyNineMaskSupport (orderFortyNineH9ProfileMasks sys) i = S} =
      orderFortyNineExpectedFiber sys S := by
  rw [orderFortyNine_card_maskFiber]
  exact orderFortyNineMaskFiberCount_eq_expected sys hsys S

/-- Membership of the stratum arrays in the combined list, for direct reuse. -/
theorem mem_allH9Reps_of_mem_t2 {sys : OrderFortyNineH9System}
    (h : sys ∈ orderFortyNineH9T2Systems.toList) :
    sys ∈ orderFortyNineAllH9Reps := by
  unfold orderFortyNineAllH9Reps
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h)))

theorem mem_allH9Reps_of_mem_t3 {sys : OrderFortyNineH9System}
    (h : sys ∈ orderFortyNineH9T3Systems.toList) :
    sys ∈ orderFortyNineAllH9Reps := by
  unfold orderFortyNineAllH9Reps
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))

theorem mem_allH9Reps_of_mem_t4 {sys : OrderFortyNineH9System}
    (h : sys ∈ orderFortyNineH9T4Systems.toList) :
    sys ∈ orderFortyNineAllH9Reps := by
  unfold orderFortyNineAllH9Reps
  exact List.mem_append.mpr (Or.inr h)

end Erdos85
