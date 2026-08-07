import Proofs.Erdos85DegreeSixQuotientClassification

/-!
# A historical eight-vertex matching obstruction at degree six

This is a direct kernel-checked exhaustion of the relaxed local model that was
previously thought to remain after coloring the unique component quotient
`(5,8,20)`.  The earlier color congruence was arithmetically incorrect; the
correct sieve makes every component antipodal.  Consequently this closed
computation remains valid as a finite statement, but is no longer asserted as
a consequence of a degree-six second-order graph.
-/

namespace Erdos85
namespace DegreeSixResidualMatching

abbrev Edge := Nat × Nat
abbrev Matching := List Edge
abbrev Factorization := List Matching

def cycleEdge (a b : Nat) : Bool :=
  (a + 1) % 8 = b || (b + 1) % 8 = a

def complementEdge (e : Edge) : Bool :=
  e.1 < e.2 && e.2 < 8 && !cycleEdge e.1 e.2

def complementEdges : List Edge :=
  ((List.range 8).flatMap fun a =>
    (List.range 8).map fun b => (a, b)).filter complementEdge

/-- Perfect matchings of the remaining vertices using complement-of-`C8`
edges.  Fuel is the number of pairs still to choose. -/
def matchingsAux : Nat → List Nat → List Matching
  | 0, remaining => if remaining.isEmpty then [[]] else []
  | fuel + 1, [] => []
  | fuel + 1, a :: rest =>
      rest.filter (fun b => complementEdge (min a b, max a b)) |>.flatMap fun b =>
        (matchingsAux fuel (rest.erase b)).map fun m =>
          (min a b, max a b) :: m

def matchings : List Matching := matchingsAux 4 (List.range 8)

def matchingContained (m edges : List Edge) : Bool :=
  m.all fun e => e ∈ edges

/-- Factorizations of all twenty complement edges into five perfect
matchings.  Choosing a factor containing the first remaining edge makes the
enumeration canonical. -/
def factorizationsAux : Nat → List Edge → Factorization → List Factorization
  | 0, edges, chosen => if edges.isEmpty then [chosen.reverse] else []
  | fuel + 1, [], chosen => [chosen.reverse]
  | fuel + 1, edge :: edges, chosen =>
      matchings.filter (fun m => edge ∈ m && matchingContained m (edge :: edges))
        |>.flatMap fun m =>
          factorizationsAux fuel
            ((edge :: edges).filter fun e => !(e ∈ m)) (m :: chosen)

def factorizations : List Factorization :=
  factorizationsAux 5 complementEdges []

def cyclicOrders : List (List Nat) :=
  [1, 2, 3, 4].permutations.filterMap fun p =>
    if p.getD 0 0 < p.getD 3 0 then some (0 :: p) else none

def edgePairings : List (List Nat) :=
  [[1, 0, 3, 2], [2, 3, 0, 1], [3, 2, 1, 0]]

def edgeMask (e : Edge) : Nat := 2 ^ e.1 + 2 ^ e.2

def partner (m : Matching) (v : Nat) : Nat :=
  match m.find? (fun e => e.1 = v || e.2 = v) with
  | none => 0
  | some e => if e.1 = v then e.2 else e.1

def transportedMask (internal : Matching) (e : Edge) : Nat :=
  2 ^ partner internal e.1 + 2 ^ partner internal e.2

def disjointFour (p : List Nat) : Bool :=
  let a := p.getD 0 0
  let b := p.getD 1 0
  let c := p.getD 2 0
  let d := p.getD 3 0
  a &&& b = 0 && a &&& c = 0 && a &&& d = 0 &&
    b &&& c = 0 && b &&& d = 0 && c &&& d = 0 &&
    a + b + c + d = 255

def reorderFactors (f : Factorization) (order : List Nat) : Factorization :=
  order.map fun i => f.getD i []

def localEdgePossible (factors : Factorization) (internal : Matching)
    (i edgeIndex : Nat) : Bool :=
  let own := (factors.getD i []).getD edgeIndex (0, 0)
  edgePairings.any fun pairing =>
    (List.range 4).any fun upward =>
      (List.range 4).any fun downward =>
        let p := [
          transportedMask internal own,
          edgeMask ((factors.getD i []).getD (pairing.getD edgeIndex 0) (0, 0)),
          edgeMask ((factors.getD ((i + 2) % 5) []).getD upward (0, 0)),
          edgeMask ((factors.getD ((i + 3) % 5) []).getD downward (0, 0))]
        disjointFour p

def passesLocalPartitionTest (factorization : Factorization)
    (order : List Nat) (internal : Matching) : Bool :=
  let factors := reorderFactors factorization order
  (List.range 5).all fun i =>
    (List.range 4).all fun edgeIndex =>
      localEdgePossible factors internal i edgeIndex

def localModels : List (Factorization × List Nat × Matching) :=
  factorizations.flatMap fun f =>
    cyclicOrders.flatMap fun order =>
      matchings.filterMap fun internal =>
        if passesLocalPartitionTest f order internal then
          some (f, order, internal)
        else none

theorem matching_count : matchings.length = 31 := by native_decide

theorem factorization_count : factorizations.length = 38 := by native_decide

theorem cyclic_order_count : cyclicOrders.length = 12 := by native_decide

theorem checked_case_count :
    factorizations.length * cyclicOrders.length * matchings.length = 14136 := by
  native_decide

theorem no_local_models : localModels = [] := by native_decide

end DegreeSixResidualMatching
end Erdos85
