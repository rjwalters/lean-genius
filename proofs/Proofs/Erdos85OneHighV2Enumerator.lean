import Proofs.Erdos85OneHighV2Inventory

/-! # Executable constrained enumeration of labeled h=1 miss tables -/

namespace Erdos85

def oneHighTableRows (profile : Nat) : List Nat :=
  List.ofFn fun i : Fin 8 => 2 * oneHighFamilyInternalEdges profile i

def oneHighAddDegree (degrees : List Nat) (i value : Nat) : List Nat :=
  degrees.set i (degrees.getD i 0 + value)

def oneHighAddEdgeDegrees (degrees : List Nat)
    (edge : Nat × Nat) (value : Nat) : List Nat :=
  oneHighAddDegree (oneHighAddDegree degrees edge.1 value) edge.2 value

def oneHighEdgeUpper (rows degrees : List Nat)
    (edge : Nat × Nat) : Nat :=
  min (rows.getD edge.1 0 - degrees.getD edge.1 0)
    (rows.getD edge.2 0 - degrees.getD edge.2 0)

def oneHighRowDeficits (rows degrees : List Nat) : List Nat :=
  List.zipWith (· - ·) rows degrees

def oneHighFutureNeighbors (edges : List (Nat × Nat)) (i : Nat) : List Nat :=
  edges.filterMap fun edge =>
    if edge.1 = i then some edge.2
    else if edge.2 = i then some edge.1
    else none

/-- Safe pruning bound used by the authoritative Python enumerator.  Every
remaining deficit must fit through the remaining capacities of its possible
neighbors, and the total remaining degree must be even. -/
def oneHighEnumerationFeasible (rows degrees : List Nat)
    (edges : List (Nat × Nat)) : Bool :=
  let deficits := oneHighRowDeficits rows degrees
  decide (deficits.sum % 2 = 0) &&
    (List.range 8).all fun i =>
      decide (deficits.getD i 0 ≤
        ((oneHighFutureNeighbors edges i).map fun j =>
          deficits.getD j 0).sum)

/-- Depth-first counterpart of `enumerate_h1_miss_tables.py`.  At each of
the 24 relevant edges it chooses exactly the values that fit both remaining
row capacities; a completed value vector is retained iff all row sums hit
their targets. -/
def enumerateOneHighTableValuesAux (rows : List Nat) :
    List (Nat × Nat) → List Nat → List Nat → List (List Nat)
  | edges, degrees, reversedValues =>
      if oneHighEnumerationFeasible rows degrees edges then
        match edges with
        | [] => if degrees = rows then [reversedValues.reverse] else []
        | edge :: remaining =>
            (List.range (oneHighEdgeUpper rows degrees edge + 1)).flatMap fun value =>
              enumerateOneHighTableValuesAux rows remaining
                (oneHighAddEdgeDegrees degrees edge value)
                (value :: reversedValues)
      else []

def enumerateOneHighTableValues (profile : Nat) : List (List Nat) :=
  enumerateOneHighTableValuesAux (oneHighTableRows profile)
    oneHighFamilyTablePairs (List.replicate 8 0) []

def oneHighFiniteTableOfValues (values : List Nat) : OneHighFiniteMissTable :=
  fun pair =>
    let value := match (oneHighFamilyTablePairs.zip values).find?
        (fun entry => entry.1 = (pair.1.1.val, pair.1.2.val)) with
      | some entry => entry.2
      | none => 0
    ⟨value % 5, Nat.mod_lt _ (by omega)⟩

def enumerateOneHighFiniteTables
    (profile : Nat) : List OneHighFiniteMissTable :=
  (enumerateOneHighTableValues profile).map oneHighFiniteTableOfValues

theorem enumerateOneHighTableValues_length_four :
    (enumerateOneHighTableValues 4).length = 16692 := by
  native_decide

theorem enumerateOneHighTableValues_length_three :
    (enumerateOneHighTableValues 3).length = 31512 := by
  native_decide

theorem enumerateOneHighTableValues_length_two :
    (enumerateOneHighTableValues 2).length = 70070 := by
  native_decide

theorem enumerateOneHighTableValues_length_one :
    (enumerateOneHighTableValues 1).length = 169668 := by
  native_decide

theorem enumerateOneHighTableValues_length_zero :
    (enumerateOneHighTableValues 0).length = 449358 := by
  native_decide

end Erdos85
