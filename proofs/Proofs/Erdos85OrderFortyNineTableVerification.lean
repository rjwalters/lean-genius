import Proofs.Erdos85OrderFortyNineProfileMasks
import Proofs.Erdos85OrderFortyNineWitnessTable

/-!
# h=9 classification: enumeration completeness (L2) and witness-table validity (L3)

L2: the witness table's system column enumerates EXACTLY the raw
prefix-normalized linear triple systems (T1 = {0,1,2}, T2 ∈ {{3,4,5},{0,3,4}},
remaining triples ascending in combination order, pairwise linear), mirroring
`sat49/iso_witnesses.py::raw_systems` loop-for-loop.

L3: every table row's witness permutation maps its system onto the canonical
representative selected by its rep index (as sets of 3-sets), with the
permutation verified to be a genuine permutation of {0..8} and the rep index
in bounds (via `Array.get?` matching `some`).

The finite checks are discharged with `native_decide` (921-row table); the
`Lean.ofReduceBool` axiom is therefore part of this file's audit, consistent
with the already-disclosed certificate-terminal axioms.
-/

namespace Erdos85
namespace OrderFortyNineWitnessTable

set_option maxRecDepth 100000

/-- All 3-subsets of {0..8} as ascending lists, in `itertools.combinations`
order (outer index smallest). -/
def allTriples : List (List Nat) :=
  (List.range 9).flatMap fun a =>
    (List.range 9).flatMap fun b =>
      (List.range 9).filterMap fun c =>
        if a < b ∧ b < c then some [a, b, c] else none

/-- Numeric encoding of an ascending triple; on digit lists this agrees with
Python tuple lexicographic order. -/
def encTriple (T : List Nat) : Nat := T.foldl (fun acc x => acc * 10 + x) 0

/-- Linearity of two triples: at most one common point. -/
def linB (S T : List Nat) : Bool :=
  Nat.ble (S.countP fun x => T.contains x) 1

/-- The two normalized second triples. -/
def secondTriples : List (List Nat) := [[3, 4, 5], [0, 3, 4]]

/-- Raw prefix-normalized systems with 2 triples. -/
def rawT2 : List (List (List Nat)) :=
  secondTriples.map fun T2 => [[0, 1, 2], T2]

/-- Raw prefix-normalized systems with 3 triples (mirrors
`raw_systems(3)`: skip `T3 <= T2`, then both linearity checks). -/
def rawT3 : List (List (List Nat)) :=
  secondTriples.flatMap fun T2 =>
    allTriples.filterMap fun T3 =>
      if Nat.ble (encTriple T3) (encTriple T2) then none
      else if linB T3 [0, 1, 2] && linB T3 T2 then some [[0, 1, 2], T2, T3]
      else none

/-- Raw prefix-normalized systems with 4 triples (mirrors `raw_systems(4)`). -/
def rawT4 : List (List (List Nat)) :=
  secondTriples.flatMap fun T2 =>
    allTriples.flatMap fun T3 =>
      if Nat.ble (encTriple T3) (encTriple T2) then []
      else if !(linB T3 [0, 1, 2] && linB T3 T2) then []
      else
        allTriples.filterMap fun T4 =>
          if Nat.ble (encTriple T4) (encTriple T3) then none
          else if linB T4 [0, 1, 2] && linB T4 T2 && linB T4 T3 then
            some [[0, 1, 2], T2, T3, T4]
          else none

/-- L2 (t = 2). -/
theorem rawT2_eq_table : rawT2 = tableT2.map (·.1) := by native_decide

/-- L2 (t = 3). -/
theorem rawT3_eq_table : rawT3 = tableT3.map (·.1) := by native_decide

/-- L2 (t = 4). -/
theorem rawT4_eq_table : rawT4 = tableT4.map (·.1) := by native_decide

/-- Apply a witness permutation (given as its image list) to one triple. -/
def applyPermTriple (p : List Nat) (T : List Nat) : List Nat :=
  T.map fun x => p.getD x 0

/-- Equality of triples as sets. -/
def tripleSetEqB (S T : List Nat) : Bool :=
  S.length == T.length && S.all (fun x => T.contains x) &&
    T.all (fun x => S.contains x)

/-- Equality of systems as sets of 3-sets. -/
def systemSetEqB (A B : List (List Nat)) : Bool :=
  A.length == B.length && A.all (fun S => B.any (tripleSetEqB S)) &&
    B.all (fun S => A.any (tripleSetEqB S))

/-- Triples of a mask-layer system as ascending-constructor lists. -/
def h9SystemTriples (s : OrderFortyNineH9System) : List (List Nat) :=
  s.map fun t => [t.a, t.b, t.c]

/-- Full validity of one table row against a canonical rep array: rep index in
bounds, witness a genuine permutation of {0..8}, and the permuted system equal
to the selected canonical system as sets of 3-sets. -/
def rowValid (reps : Array OrderFortyNineH9System) (row : Row) : Bool :=
  match reps[row.2.1]? with
  | some rep =>
      row.2.2.length == 9 &&
        (List.range 9).all (fun i => row.2.2.contains i) &&
        systemSetEqB (row.1.map (applyPermTriple row.2.2)) (h9SystemTriples rep)
  | none => false

/-- L3 (t = 2). -/
theorem tableT2_valid :
    tableT2.all (rowValid orderFortyNineH9T2Systems) = true := by native_decide

/-- L3 (t = 3). -/
theorem tableT3_valid :
    tableT3.all (rowValid orderFortyNineH9T3Systems) = true := by native_decide

/-- L3 (t = 4). -/
theorem tableT4_valid :
    tableT4.all (rowValid orderFortyNineH9T4Systems) = true := by native_decide

/-- Per-row extraction of validity from the table-level checks. -/
theorem rowValid_of_mem_tableT2 {row : Row} (h : row ∈ tableT2) :
    rowValid orderFortyNineH9T2Systems row = true :=
  List.all_eq_true.mp tableT2_valid row h

theorem rowValid_of_mem_tableT3 {row : Row} (h : row ∈ tableT3) :
    rowValid orderFortyNineH9T3Systems row = true :=
  List.all_eq_true.mp tableT3_valid row h

theorem rowValid_of_mem_tableT4 {row : Row} (h : row ∈ tableT4) :
    rowValid orderFortyNineH9T4Systems row = true :=
  List.all_eq_true.mp tableT4_valid row h

end OrderFortyNineWitnessTable
end Erdos85
