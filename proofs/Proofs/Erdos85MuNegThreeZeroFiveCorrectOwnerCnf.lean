import Proofs.Erdos85MuNegThreeZeroFiveOwnerCnf

/-!
# Honest 88-owner CNFs for the μ=-3 `(0,5)` endpoint

Unlike the old h114-derived owner list, each h305 shore contains its four
antipodal exterior-pair edges in addition to the eight mode-dependent edges.
Thus the fixed shore block has 24 owners and the guarded cross block has 64.
-/

namespace Erdos85

open Std Sat

/-- The twelve exterior-pair owners on one h305 shore. -/
def muNegThreeZeroFiveShoreOwners (base : Nat) (tri : Bool) :
    List (Nat × Nat) :=
  ((List.range 8).map fun i =>
    let j := (i + if tri then 1 else 3) % 8
    (min (base + i) (base + j), max (base + i) (base + j))) ++
  ((List.range 4).map fun i => (base + i, base + i + 4))

/-- The honest h305 owner universe: twelve owners on each shore followed by
all 64 potential cross owners. -/
def muNegThreeZeroFiveCorrectOwners (uTri vTri : Bool) :
    List (Nat × Nat) :=
  muNegThreeZeroFiveShoreOwners 0 uTri ++
  muNegThreeZeroFiveShoreOwners 8 vTri ++
  ((List.range 8).flatMap fun i =>
    (List.range 8).map fun j => (i, 8 + j))

def muNegThreeZeroFiveCorrectHitPairs (uTri vTri : Bool) :
    List (Nat × Nat) :=
  let os := muNegThreeZeroFiveCorrectOwners uTri vTri
  (List.range os.length).flatMap fun a =>
    ((List.range os.length).filter fun b =>
      a < b && muNegOneAdm (os[a]!) (os[b]!)).map fun b => (a, b)

def muNegThreeZeroFiveCorrectXVar? (pairs : List (Nat × Nat))
    (a b : Nat) : Option Nat :=
  let p := if a < b then (a, b) else (b, a)
  (pairs.idxOf? p).map (· + 65)

def muNegThreeZeroFiveCorrectXLit? (pairs : List (Nat × Nat))
    (a b : Nat) : Option Int :=
  (muNegThreeZeroFiveCorrectXVar? pairs a b).map Int.ofNat

/-- Cross owners are recognized from their endpoints, so the shift from 16
to 24 fixed owners cannot silently mis-guard an owner. -/
def muNegThreeZeroFiveCorrectGuard? (os : List (Nat × Nat))
    (a : Nat) : Option Nat :=
  let p := os[a]!
  if p.1 < 8 && 8 ≤ p.2 then some (muNegOneDVar p.1 (p.2 - 8)) else none

def muNegThreeZeroFiveCorrectHitActivityClauses
    (os pairs : List (Nat × Nat)) : List DimacsClause :=
  pairs.flatMap fun pr =>
    match muNegThreeZeroFiveCorrectXVar? pairs pr.1 pr.2 with
    | some x =>
        (match muNegThreeZeroFiveCorrectGuard? os pr.1 with
          | some g => [[-Int.ofNat x, -Int.ofNat g]]
          | none => []) ++
        (match muNegThreeZeroFiveCorrectGuard? os pr.2 with
          | some g => [[-Int.ofNat x, -Int.ofNat g]]
          | none => [])
    | none => []

def muNegThreeZeroFiveCorrectServiceClauses
    (os pairs : List (Nat × Nat)) : List DimacsClause :=
  (List.range os.length).flatMap fun a =>
    let pre : List Int :=
      match muNegThreeZeroFiveCorrectGuard? os a with
      | some g => [Int.ofNat g]
      | none => []
    (muNegOneTwelve (os[a]!)).flatMap fun w =>
      let lits := (List.range os.length).filterMap fun b =>
        if b != a && muNegOnePairMem (os[b]!) w then
          muNegThreeZeroFiveCorrectXLit? pairs a b
        else none
      [pre ++ lits] ++ muNegOnePairsOf lits pre

def muNegThreeZeroFiveCorrectC4Clauses
    (os pairs : List (Nat × Nat)) : List DimacsClause :=
  (List.range os.length).flatMap fun a =>
    ((List.range os.length).filter fun b => a < b).flatMap fun b =>
      let ks := (List.range os.length).filter fun g =>
        g != a && g != b &&
          (muNegThreeZeroFiveCorrectXVar? pairs a g).isSome &&
          (muNegThreeZeroFiveCorrectXVar? pairs b g).isSome
      if muNegOneShare (os[a]!) (os[b]!) then
        ks.filterMap fun g => do
          let x ← muNegThreeZeroFiveCorrectXLit? pairs a g
          let y ← muNegThreeZeroFiveCorrectXLit? pairs b g
          return [-x, -y]
      else
        (List.range ks.length).flatMap fun gi =>
          ((List.range ks.length).filter fun hi => gi < hi).filterMap
            fun hi => do
              let xag ← muNegThreeZeroFiveCorrectXLit? pairs a (ks[gi]!)
              let xbg ← muNegThreeZeroFiveCorrectXLit? pairs b (ks[gi]!)
              let xah ← muNegThreeZeroFiveCorrectXLit? pairs a (ks[hi]!)
              let xbh ← muNegThreeZeroFiveCorrectXLit? pairs b (ks[hi]!)
              return [-xag, -xbg, -xah, -xbh]

/-- The corrected generator whose byte ordering is mirrored by
`generate_h305_owner_cnf.py`. -/
def muNegThreeZeroFiveCorrectOwnerDimacsClauses
    (uTri vTri σ : Bool) : Array DimacsClause :=
  let os := muNegThreeZeroFiveCorrectOwners uTri vTri
  let pairs := muNegThreeZeroFiveCorrectHitPairs uTri vTri
  (muNegThreeZeroFiveCrossRowClauses σ ++
    muNegThreeZeroFiveCrossColClauses σ ++
    muNegOneIntertwineClauses ++
    muNegThreeZeroFiveCorrectHitActivityClauses os pairs ++
    muNegThreeZeroFiveCorrectServiceClauses os pairs ++
    muNegThreeZeroFiveCorrectC4Clauses os pairs).toArray

def muNegThreeZeroFiveCorrectOwnerSatCnf (uTri vTri σ : Bool) : CNF Nat where
  clauses := dimacsFormulaToSatClauses
    (muNegThreeZeroFiveCorrectOwnerDimacsClauses uTri vTri σ)

end Erdos85
