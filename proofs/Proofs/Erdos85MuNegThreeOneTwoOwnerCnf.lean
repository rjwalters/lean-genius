import Proofs.Erdos85DimacsSatBridge

/-!
# Fixed-phase owner-grid CNFs for the μ=-3 self cell (k,r) = (1,2)

Node: outline F.3 (μ=-3 lane; embedding assigned in squad msg 13661).

One parameterized generator covering the eight σ=0 orientation/phase
sub-cases of the `(−3,1,2)` owner grid (squad msgs 13639/13658): the
same-sign cross half is fixed to the oriented matching `j = c + i`
(forward) or `j = c − i` (reverse) with even phase `c`; the
opposite-sign cross half (degree one per row and column, entrywise
intertwining) and the 48-owner hit graph remain variable, under the
owner-tiling service law and the intersecting-zero / disjoint-≤1
exterior C4 constraints.  Variables: `D(i,j) = i*8+j+1` for the 64
cross cells, hit variables from 65 in admissible-pair order.  The
clause stream mirrors the verified generator
`muneg3_onetwo_fixed_owner_cnf.py` exactly.
-/

namespace Erdos85

open Std Sat

def muNegThreeCellRow (a : Nat) : Nat := a / 8
def muNegThreeCellCol (a : Nat) : Nat := a % 8

def muNegThreeDVar (a : Nat) : Nat := a + 1

def muNegThreeSameSign (a : Nat) : Bool :=
  muNegThreeCellRow a % 2 == muNegThreeCellCol a % 2

def muNegThreeOffsetOne (x y : Nat) : Bool :=
  (y + 8 - x) % 8 == 1 || (y + 8 - x) % 8 == 7

def muNegThreeAdm (a b : Nat) : Bool :=
  a != b &&
    !muNegThreeOffsetOne (muNegThreeCellRow a) (muNegThreeCellRow b) &&
    !muNegThreeOffsetOne (muNegThreeCellCol a) (muNegThreeCellCol b)

def muNegThreeHitPairs : List (Nat × Nat) :=
  (List.range 64).flatMap fun a =>
    ((List.range 64).filter fun b => a < b && muNegThreeAdm a b).map
      fun b => (a, b)

def muNegThreeXVar? (a b : Nat) : Option Nat :=
  let p := if a < b then (a, b) else (b, a)
  (muNegThreeHitPairs.idxOf? p).map (· + 65)

def muNegThreeXLit? (a b : Nat) : Option Int :=
  (muNegThreeXVar? a b).map Int.ofNat

def muNegThreePhi (fwd : Bool) (c i : Nat) : Nat :=
  if fwd then (c + i) % 8 else (c + 8 - i % 8) % 8

/-- Phase 1: unit clauses fixing the same-sign half to the matching. -/
def muNegThreeFixClauses (fwd : Bool) (c : Nat) : List DimacsClause :=
  (List.range 8).flatMap fun i =>
    ((List.range 8).filter fun j => i % 2 == j % 2).map fun j =>
      if j == muNegThreePhi fwd c i then
        [Int.ofNat (muNegThreeDVar (i * 8 + j))]
      else
        [-Int.ofNat (muNegThreeDVar (i * 8 + j))]

def muNegThreeExactlyOne (lits : List Int) : List DimacsClause :=
  [lits] ++ lits.flatMap fun x =>
    (lits.filter fun y => x < y).map fun y => [-x, -y]

/-- Phase 2/3: the opposite-sign half has exactly one entry per row and
per column. -/
def muNegThreeOppRowClauses : List DimacsClause :=
  (List.range 8).flatMap fun i =>
    muNegThreeExactlyOne (((List.range 8).filter
      fun j => !(i % 2 == j % 2)).map
        fun j => Int.ofNat (muNegThreeDVar (i * 8 + j)))

def muNegThreeOppColClauses : List DimacsClause :=
  (List.range 8).flatMap fun j =>
    muNegThreeExactlyOne (((List.range 8).filter
      fun i => !(i % 2 == j % 2)).map
        fun i => Int.ofNat (muNegThreeDVar (i * 8 + j)))

def muNegThreeSumEq (a b c d : Int) : List DimacsClause :=
  [[-a, c, d], [-b, c, d], [-c, a, b], [-d, a, b],
   [-a, -b, c], [-a, -b, d], [-c, -d, a], [-c, -d, b]]

/-- Phase 4: entrywise C8 intertwining of the cross block. -/
def muNegThreeIntertwineClauses : List DimacsClause :=
  (List.range 8).flatMap fun i =>
    (List.range 8).flatMap fun j =>
      muNegThreeSumEq
        (Int.ofNat (muNegThreeDVar (((i + 7) % 8) * 8 + j)))
        (Int.ofNat (muNegThreeDVar (((i + 1) % 8) * 8 + j)))
        (Int.ofNat (muNegThreeDVar (i * 8 + (j + 1) % 8)))
        (Int.ofNat (muNegThreeDVar (i * 8 + (j + 7) % 8)))

/-- Phase 5: hits require both endpoint cells active (non-defect). -/
def muNegThreeHitActivityClauses : List DimacsClause :=
  muNegThreeHitPairs.flatMap fun p =>
    match muNegThreeXVar? p.1 p.2 with
    | some x =>
        [[-Int.ofNat x, -Int.ofNat (muNegThreeDVar p.1)],
         [-Int.ofNat x, -Int.ofNat (muNegThreeDVar p.2)]]
    | none => []

def muNegThreeServiceLits (a : Nat) (onRow : Bool) (t : Nat) : List Int :=
  (List.range 64).filterMap fun b =>
    if b != a &&
        (if onRow then muNegThreeCellRow b == t
          else muNegThreeCellCol b == t) then
      muNegThreeXLit? a b
    else none

def muNegThreeGuarded (g : Int) (lits : List Int) : List DimacsClause :=
  [g :: lits] ++ lits.flatMap fun x =>
    (lits.filter fun y => x < y).map fun y => [g, -x, -y]

/-- Phase 6: owner-tiling service, guarded by cell activity. -/
def muNegThreeServiceClauses : List DimacsClause :=
  (List.range 64).flatMap fun a =>
    let i := muNegThreeCellRow a
    let j := muNegThreeCellCol a
    let g : Int := Int.ofNat (muNegThreeDVar a)
    ((List.range 8).flatMap fun m =>
      if muNegThreeOffsetOne i m then []
      else muNegThreeGuarded g (muNegThreeServiceLits a true m)) ++
    ((List.range 8).flatMap fun n =>
      if muNegThreeOffsetOne j n then []
      else muNegThreeGuarded g (muNegThreeServiceLits a false n))

def muNegThreeCommons (a b : Nat) : List Nat :=
  (List.range 64).filter fun g => g != a && g != b &&
    (muNegThreeXVar? a g).isSome && (muNegThreeXVar? b g).isSome

/-- Phase 7: exterior C4 — intersecting owner cells share no common
hit; disjoint cells share at most one. -/
def muNegThreeC4Clauses : List DimacsClause :=
  (List.range 64).flatMap fun a =>
    ((List.range 64).filter fun b => a < b).flatMap fun b =>
      let ks := muNegThreeCommons a b
      if muNegThreeCellRow a == muNegThreeCellRow b ||
          muNegThreeCellCol a == muNegThreeCellCol b then
        ks.filterMap fun g => do
          let x ← muNegThreeXLit? a g
          let y ← muNegThreeXLit? b g
          return [-x, -y]
      else
        ks.flatMap fun g => (ks.filter fun h => g < h).filterMap fun h => do
          let xag ← muNegThreeXLit? a g
          let xbg ← muNegThreeXLit? b g
          let xah ← muNegThreeXLit? a h
          let xbh ← muNegThreeXLit? b h
          return [-xag, -xbg, -xah, -xbh]

def muNegThreeOneTwoOwnerDimacsClauses (fwd : Bool) (c : Nat) :
    Array DimacsClause :=
  (muNegThreeFixClauses fwd c ++ muNegThreeOppRowClauses ++
    muNegThreeOppColClauses ++ muNegThreeIntertwineClauses ++
    muNegThreeHitActivityClauses ++ muNegThreeServiceClauses ++
    muNegThreeC4Clauses).toArray

def muNegThreeOneTwoOwnerSatCnf (fwd : Bool) (c : Nat) : CNF Nat where
  clauses := dimacsFormulaToSatClauses (muNegThreeOneTwoOwnerDimacsClauses fwd c)

set_option maxHeartbeats 0 in
theorem muNegThreeHitPairs_size : muNegThreeHitPairs.length = 1120 := by
  native_decide

set_option maxHeartbeats 0 in
theorem muNegThreeOneTwoOwnerDimacsClauses_size_fwd_c0 :
    (muNegThreeOneTwoOwnerDimacsClauses true 0).size = 252848 := by
  native_decide

end Erdos85
