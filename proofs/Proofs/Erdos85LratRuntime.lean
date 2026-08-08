import Std.Data.HashMap
import Proofs.Erdos85DimacsSatBridge
import Proofs.Erdos85OrderFortyNineProfileMasks

/-!
# Runtime DIMACS/LRAT replay for the Erdős 85 certificates

The order-49 instances are tens of megabytes, so they are loaded at runtime
rather than embedded as kernel terms.  `LRAT.check_sound` remains the logical
trust boundary; this module supplies only a byte-oriented DIMACS parser and a
small replay executable.
-/

namespace Erdos85

open Std Sat
open Std.Tactic.BVDecide

namespace DimacsRuntime

@[inline] def isSpace (b : UInt8) : Bool :=
  b == 9 || b == 10 || b == 13 || b == 32

partial def skipSpace (data : ByteArray) (start : Nat) : Nat :=
  if h : start < data.size then
    if isSpace data[start] then skipSpace data (start + 1) else start
  else
    start

partial def skipLine (data : ByteArray) (start : Nat) : Nat :=
  if h : start < data.size then
    if data[start] == 10 then start + 1 else skipLine data (start + 1)
  else
    start

partial def parseDigits (data : ByteArray) (start acc : Nat) : Nat × Nat :=
  if h : start < data.size then
    let b := data[start]
    if 48 ≤ b.toNat && b.toNat ≤ 57 then
      parseDigits data (start + 1) (acc * 10 + (b.toNat - 48))
    else
      (acc, start)
  else
    (acc, start)

def parseIntToken (data : ByteArray) (start : Nat) : Except String (Int × Nat) := do
  if h : start < data.size then
    let negative := data[start] == 45
    let digitStart := if negative then start + 1 else start
    if hd : digitStart < data.size then
      let b := data[digitStart]
      if !(48 ≤ b.toNat && b.toNat ≤ 57) then
        throw s!"expected DIMACS integer at byte {start}"
      let (magnitude, next) := parseDigits data digitStart 0
      return (if negative then -(magnitude : Int) else (magnitude : Int), next)
    else
      throw "truncated DIMACS integer"
  else
    throw "unexpected end of DIMACS input"

partial def parseClauses (data : ByteArray) (start : Nat)
    (clauses : Array (CNF.Clause Nat)) (currentRev : CNF.Clause Nat) :
    Except String (CNF Nat) := do
  let i := skipSpace data start
  if h : i < data.size then
    let b := data[i]
    if b == 99 || b == 112 then
      -- `c` comments and the unique `p cnf ...` header both occupy a line.
      parseClauses data (skipLine data i) clauses currentRev
    else
      let (lit, next) ← parseIntToken data i
      if lit == 0 then
        parseClauses data next (clauses.push currentRev.reverse) []
      else
        let id := lit.natAbs
        if id == 0 then
          throw s!"illegal zero DIMACS identifier at byte {i}"
        let literal : Nat × Bool := (id - 1, 0 < lit)
        parseClauses data next clauses (literal :: currentRev)
  else
    if currentRev.isEmpty then
      return { clauses := clauses }
    else
      throw "unterminated final DIMACS clause"

def parse (data : ByteArray) : Except String (CNF Nat) :=
  parseClauses data 0 #[] []

def load (path : System.FilePath) : IO (CNF Nat) := do
  let data ← IO.FS.readBinFile path
  match parse data with
  | .ok cnf => return cnf
  | .error message => throw <| .userError message

end DimacsRuntime

namespace LratRenumber

open LRAT

def mapId (firstDerived : Nat) (mapping : Std.HashMap Nat Nat)
    (id : Nat) : Except String Nat :=
  if id < firstDerived then
    return id
  else
    match mapping[id]? with
    | some mapped => return mapped
    | none => throw s!"LRAT hint references unmapped derived clause {id}"

def mapIds (firstDerived : Nat) (mapping : Std.HashMap Nat Nat)
    (ids : Array Nat) : Except String (Array Nat) :=
  ids.mapM (mapId firstDerived mapping)

partial def go (firstDerived : Nat) (proof : Array IntAction) (idx next : Nat)
    (mapping : Std.HashMap Nat Nat) (out : Array IntAction) :
    Except String (Array IntAction) := do
  if h : idx < proof.size then
    match proof[idx] with
    | .addEmpty oldId hints =>
        let hints ← mapIds firstDerived mapping hints
        go firstDerived proof (idx + 1) (next + 1)
          (mapping.insert oldId next) (out.push (.addEmpty next hints))
    | .addRup oldId clause hints =>
        let hints ← mapIds firstDerived mapping hints
        go firstDerived proof (idx + 1) (next + 1)
          (mapping.insert oldId next) (out.push (.addRup next clause hints))
    | .addRat oldId clause pivot rupHints ratHints =>
        let rupHints ← mapIds firstDerived mapping rupHints
        let ratHints ← ratHints.mapM fun pair => do
          let clauseId ← mapId firstDerived mapping pair.1
          let hints ← mapIds firstDerived mapping pair.2
          return (clauseId, hints)
        go firstDerived proof (idx + 1) (next + 1)
          (mapping.insert oldId next)
          (out.push (.addRat next clause pivot rupHints ratHints))
    | .del ids =>
        let ids ← mapIds firstDerived mapping ids
        go firstDerived proof (idx + 1) next mapping (out.push (.del ids))
  else
    return out

def renumber (numOriginalClauses : Nat) (proof : Array IntAction) :
    Except String (Array IntAction) :=
  let firstDerived := numOriginalClauses + 1
  go firstDerived proof 0 firstDerived {} #[]

end LratRenumber

def replayLrat (cnfPath lratPath : System.FilePath) : IO Bool := do
  let cnf ← DimacsRuntime.load cnfPath
  let rawProof ← LRAT.loadLRATProof lratPath
  let proof ← IO.ofExcept (LratRenumber.renumber cnf.clauses.size rawProof)
  return LRAT.check proof cnf

partial def cnfSegmentEq (cnf : Sat.CNF Nat) (offset : Nat)
    (segment : Array DimacsClause) (idx : Nat := 0) : Bool :=
  if h : idx < segment.size then
    cnf.clauses[offset + idx]? ==
      some (dimacsClauseToSatClause segment[idx]) &&
      cnfSegmentEq cnf offset segment (idx + 1)
  else
    true

def c4CnfSegmentEq (cnf : Sat.CNF Nat) (offset : Nat) : Bool × Nat := Id.run do
  let mut idx := 0
  let mut ok := true
  for ij in orderFortyNineStrictPairs (List.finRange 49) do
    let away := orderFortyNineVerticesAway ij.1 ij.2
    for ww in orderFortyNineStrictPairs away do
      let clause := dimacsClauseToSatClause
        (orderFortyNineC4Clause (ij, ww))
      ok := ok && cnf.clauses[offset + idx]? == some clause
      idx := idx + 1
  return (ok, idx)

def h9System? (tag : String) (idx : Nat) : Option OrderFortyNineH9System :=
  match tag with
  | "t2" => orderFortyNineH9T2Systems[idx]?
  | "t3" => orderFortyNineH9T3Systems[idx]?
  | "t4" => orderFortyNineH9T4Systems[idx]?
  | _ => none

def checkProfileCnf (tag : String) (idx : Nat) (cnfPath : System.FilePath) :
    IO Bool := do
  let some sys := h9System? tag idx
    | throw <| .userError s!"unknown profile {tag}[{idx}]"
  let cnf ← DimacsRuntime.load cnfPath
  let masks := orderFortyNineH9ProfileMasks sys
  let fixed := orderFortyNineFixedClauses masks
  let degree := (orderFortyNineDegreeBlocks 9).clauses
  let partition := orderFortyNinePartitionClauses masks
  let fixedOffset := 0
  let c4Offset := fixedOffset + fixed.size
  let c4Result := c4CnfSegmentEq cnf c4Offset
  let degreeOffset := c4Offset + c4Result.2
  let partitionOffset := degreeOffset + degree.size
  let expectedSize := partitionOffset + partition.size
  IO.println s!"segment sizes: fixed={fixed.size}, c4={c4Result.2}, degree={degree.size}, partition={partition.size}"
  if cnf.clauses.size != expectedSize then
    IO.println s!"clause-count mismatch: parsed={cnf.clauses.size}, generated={expectedSize}"
    return false
  let fixedOk := cnfSegmentEq cnf fixedOffset fixed
  IO.println s!"fixed segment: {fixedOk}"
  let c4Ok := c4Result.1
  IO.println s!"C4 segment: {c4Ok}"
  let degreeOk := cnfSegmentEq cnf degreeOffset degree
  IO.println s!"degree segment: {degreeOk}"
  let partitionOk := cnfSegmentEq cnf partitionOffset partition
  IO.println s!"partition segment: {partitionOk}"
  return fixedOk && c4Ok && degreeOk && partitionOk

def replayGeneratedProfileLrat
    (tag : String) (idx : Nat) (lratPath : System.FilePath) : IO Bool := do
  let some sys := h9System? tag idx
    | throw <| .userError s!"unknown profile {tag}[{idx}]"
  let masks := orderFortyNineH9ProfileMasks sys
  let cnf := orderFortyNineGeneratedSatCnf masks
  let rawProof ← Std.Tactic.BVDecide.LRAT.loadLRATProof lratPath
  let proof ← IO.ofExcept (LratRenumber.renumber cnf.clauses.size rawProof)
  IO.println s!"generated CNF clauses: {cnf.clauses.size}; LRAT actions: {proof.size}"
  return Std.Tactic.BVDecide.LRAT.check proof cnf

end Erdos85

def main (args : List String) : IO UInt32 := do
  match args with
  | ["generated", tag, idxText, lratPath] =>
      let some idx := idxText.toNat?
        | throw <| .userError s!"invalid profile index {idxText}"
      let accepted ← Erdos85.replayGeneratedProfileLrat tag idx lratPath
      IO.println s!"generated-profile LRAT accepted: {accepted}"
      return if accepted then 0 else 1
  | ["profile", tag, idxText, cnfPath] =>
      let some idx := idxText.toNat?
        | throw <| .userError s!"invalid profile index {idxText}"
      let matched ← Erdos85.checkProfileCnf tag idx cnfPath
      IO.println s!"profile CNF matched: {matched}"
      return if matched then 0 else 1
  | [cnfPath, lratPath] =>
      let cnf ← Erdos85.DimacsRuntime.load cnfPath
      let rawProof ← Std.Tactic.BVDecide.LRAT.loadLRATProof lratPath
      let proof ← IO.ofExcept
        (Erdos85.LratRenumber.renumber cnf.clauses.size rawProof)
      IO.println s!"CNF clauses: {cnf.clauses.size}; LRAT actions: {proof.size}"
      let accepted := Std.Tactic.BVDecide.LRAT.check proof cnf
      IO.println s!"LRAT accepted: {accepted}"
      return if accepted then 0 else 1
  | _ =>
      IO.eprintln "usage: Erdos85LratRuntime <instance.cnf> <proof.lrat>"
      return 2
