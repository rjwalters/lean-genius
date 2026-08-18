import Proofs.Erdos85OneHighV2Inventory

/-! # Pairing refinements of one-high miss tables

The inventory records, for each source branch, the multiset of miss labels at
the endpoints of its internal matching edges.  It does not record how those
endpoints are paired.  This file supplies the missing finite refinement: it
enumerates every canonical pairing compatible with a table row and then takes
the Cartesian product over the eight source branches.
-/

namespace Erdos85

/-- A canonical unordered pair of branch labels.  Diagonal pairs are retained:
they represent internal edges whose two endpoints have the same miss label. -/
abbrev OneHighLabelPair := Fin 8 × Fin 8

def oneHighLabelPairCode (p : OneHighLabelPair) : Nat :=
  8 * p.1.val + p.2.val

def oneHighCanonicalLabelPairs : List OneHighLabelPair :=
  (List.ofFn fun i : Fin 8 => i).flatMap fun i =>
    (List.ofFn fun j : Fin 8 => j).filterMap fun j =>
      if i ≤ j then some (i, j) else none

/-- Number of occurrences of `label` among the two endpoints represented by
one (possibly diagonal) unordered label pair. -/
def oneHighLabelPairEndpointCount
    (pair : OneHighLabelPair) (label : Fin 8) : Nat :=
  (if pair.1 = label then 1 else 0) +
    (if pair.2 = label then 1 else 0)

def oneHighPairingEndpointCount
    (pairs : List OneHighLabelPair) (label : Fin 8) : Nat :=
  (pairs.map fun pair => oneHighLabelPairEndpointCount pair label).sum

/-- The canonical lists of one or two unordered pairs appropriate to a source
branch.  The order restriction in the two-edge case removes the permutation
duplication while retaining repeated pairs. -/
def oneHighSourcePairingShapes
    (profile : Nat) (source : Fin 8) : List (List OneHighLabelPair) :=
  if oneHighFamilyInternalEdges profile source = 1 then
    oneHighCanonicalLabelPairs.map fun pair => [pair]
  else
    oneHighCanonicalLabelPairs.flatMap fun first =>
      (oneHighCanonicalLabelPairs.filter fun second =>
        decide (oneHighLabelPairCode first ≤ oneHighLabelPairCode second)).map
          fun second => [first, second]

/-- Exact compatibility with the directed miss-count row.  Checking every
label is essential: the table row fixes endpoint multiplicities, not pair
multiplicities. -/
def oneHighSourcePairingCompatible
    (table : OneHighMissTable) (source : Fin 8)
    (pairs : List OneHighLabelPair) : Bool :=
  (List.ofFn fun label : Fin 8 => label).all fun label =>
    decide (oneHighPairingEndpointCount pairs label =
      oneHighFamilyTableGet table source.val label.val)

def oneHighCompatibleSourcePairings
    (profile : Nat) (table : OneHighMissTable) (source : Fin 8) :
    List (List OneHighLabelPair) :=
  (oneHighSourcePairingShapes profile source).filter
    (oneHighSourcePairingCompatible table source)

/-- Cartesian product of a list of finite choice lists. -/
def oneHighChooseEach {A : Type*} : List (List A) → List (List A)
  | [] => [[]]
  | choices :: remaining =>
      choices.flatMap fun choice =>
        (oneHighChooseEach remaining).map fun suffix => choice :: suffix

/-- Pointwise specification of a result of `oneHighChooseEach`. -/
def OneHighChoicesCompatible {A : Type*} : List (List A) → List A → Prop
  | [], [] => True
  | options :: remaining, choice :: suffix =>
      choice ∈ options ∧ OneHighChoicesCompatible remaining suffix
  | _, _ => False

/-- Every global pairing refinement compatible with the eight table rows.
Entry `i` of a refinement is the pairing chosen for source branch `i`. -/
def oneHighPairingRefinements
    (profile : Nat) (table : OneHighMissTable) :
    List (List (List OneHighLabelPair)) :=
  oneHighChooseEach (List.ofFn fun source : Fin 8 =>
    oneHighCompatibleSourcePairings profile table source)

/-- Global multiplicity of an unordered label pair in a pairing refinement. -/
def oneHighPairingRefinementMultiplicity
    (refinement : List (List OneHighLabelPair))
    (pair : OneHighLabelPair) : Nat :=
  refinement.flatten.count pair

@[simp] theorem oneHighChooseEach_nil {A : Type*} :
    oneHighChooseEach ([] : List (List A)) = [[]] := rfl

theorem oneHighChooseEach_mem_iff {A : Type*}
    (choiceLists : List (List A)) (choices : List A) :
    choices ∈ oneHighChooseEach choiceLists ↔
      OneHighChoicesCompatible choiceLists choices := by
  induction choiceLists generalizing choices with
  | nil => cases choices <;> simp [oneHighChooseEach, OneHighChoicesCompatible]
  | cons options remaining ih =>
      cases choices with
      | nil => simp [oneHighChooseEach, OneHighChoicesCompatible]
      | cons choice suffix =>
          simp [oneHighChooseEach, OneHighChoicesCompatible, ih]

theorem oneHighChooseEach_length_of_mem {A : Type*}
    {choiceLists : List (List A)} {choices : List A}
    (h : choices ∈ oneHighChooseEach choiceLists) :
    choices.length = choiceLists.length := by
  induction choiceLists generalizing choices with
  | nil => simpa [oneHighChooseEach] using h
  | cons options rest ih =>
      simp only [oneHighChooseEach, List.mem_flatMap, List.mem_map] at h
      rcases h with ⟨choice, _, suffix, hsuffix, rfl⟩
      simp [ih hsuffix]

theorem oneHighPairingRefinement_length
    {profile : Nat} {table : OneHighMissTable}
    {refinement : List (List OneHighLabelPair)}
    (h : refinement ∈ oneHighPairingRefinements profile table) :
    refinement.length = 8 := by
  have := oneHighChooseEach_length_of_mem h
  simpa [oneHighPairingRefinements] using this

theorem oneHighPairingRefinements_mem_iff
    (profile : Nat) (table : OneHighMissTable)
    (refinement : List (List OneHighLabelPair)) :
    refinement ∈ oneHighPairingRefinements profile table ↔
      OneHighChoicesCompatible
        (List.ofFn fun source : Fin 8 =>
          oneHighCompatibleSourcePairings profile table source)
        refinement := by
  exact oneHighChooseEach_mem_iff _ _

theorem oneHighCompatibleSourcePairings_sound
    {profile : Nat} {table : OneHighMissTable} {source : Fin 8}
    {pairs : List OneHighLabelPair}
    (h : pairs ∈ oneHighCompatibleSourcePairings profile table source) :
    oneHighSourcePairingCompatible table source pairs = true := by
  exact (List.mem_filter.mp h).2

end Erdos85
