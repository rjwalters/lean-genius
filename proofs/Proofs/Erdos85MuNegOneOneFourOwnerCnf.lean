import Proofs.Erdos85DimacsSatBridge

/-!
# Variable-cross owner CNFs for the μ=-1 self cell (k,r) = (1,4)

Node: outline F.3 (μ=-1 lane; embedding per squad msgs 13868/13925).

One parameterized generator covering the six sector/sign sub-cases of
the `(−1,1,4)` owner grid: shores u (vertices 0..7) and v (8..15) each
carry a sector flag (`false` = all-TF with within-shore owner offset 3,
`true` = all-triangle with offset 1); the sign phase `σ` relates the two
alternating shores.  The 64 cross cells carry defect variables
`D(i,j) = i*8+j+1` with row/column degree 4 split same-sign 2 /
opposite-sign 2 and entrywise C8 intertwining.  Owners are the 16 fixed
within-shore pairs plus the 32 active (non-defect) cross cells; hit
variables from 65 in admissible-pair order.  Service follows the
owner-tiling law (G-adjacent within-tri owners exclude their endpoints,
all other owners include them), with the intersecting-zero /
disjoint-≤1 exterior C4 constraints.  The clause stream mirrors the
verified generator `muneg1_onefour_owner_cnf.py` exactly.
-/

namespace Erdos85

open Std Sat

def muNegOneShoreOf (x : Nat) : Bool := 8 ≤ x
def muNegOneCoord (x : Nat) : Nat := x % 8

def muNegOneGAdj (x y : Nat) : Bool :=
  (muNegOneShoreOf x == muNegOneShoreOf y) &&
    ((muNegOneCoord x + 8 - muNegOneCoord y) % 8 == 1 ||
      (muNegOneCoord x + 8 - muNegOneCoord y) % 8 == 7)

def muNegOneNbrs (x : Nat) : List Nat :=
  (List.range 16).filter fun y => muNegOneGAdj x y

def muNegOneSign (σ : Bool) (x : Nat) : Bool :=
  if x < 8 then x % 2 == 1
  else ((x % 8) + (if σ then 1 else 0)) % 2 == 1

/-- Owners: 8 within-u pairs, 8 within-v pairs, 64 cross cells (in that
order, matching the Python generator). -/
def muNegOneOwners (uTri vTri : Bool) : List (Nat × Nat) :=
  ((List.range 8).map fun i =>
    let j := (i + if uTri then 1 else 3) % 8
    (min i j, max i j)) ++
  ((List.range 8).map fun i =>
    let j := (i + if vTri then 1 else 3) % 8
    (min (8 + i) (8 + j), max (8 + i) (8 + j))) ++
  ((List.range 8).flatMap fun i => (List.range 8).map fun j => (i, 8 + j))

def muNegOnePairMem (p : Nat × Nat) (w : Nat) : Bool :=
  p.1 == w || p.2 == w

def muNegOneAdjacentPair (p : Nat × Nat) : Bool :=
  muNegOneGAdj p.1 p.2

def muNegOneServed (p : Nat × Nat) : List Nat :=
  (List.range 16).filter fun w =>
    muNegOneGAdj p.1 w || muNegOneGAdj p.2 w ||
      (muNegOneAdjacentPair p && muNegOnePairMem p w)

def muNegOneTwelve (p : Nat × Nat) : List Nat :=
  (List.range 16).filter fun w =>
    !(muNegOneServed p).contains w &&
      !(muNegOneAdjacentPair p && muNegOnePairMem p w)

def muNegOneAdm (p q : Nat × Nat) : Bool :=
  p != q &&
    (muNegOneTwelve p).contains q.1 && (muNegOneTwelve p).contains q.2 &&
    (muNegOneTwelve q).contains p.1 && (muNegOneTwelve q).contains p.2

def muNegOneDVar (i j : Nat) : Nat := i * 8 + j + 1

def muNegOneHitPairs (uTri vTri : Bool) : List (Nat × Nat) :=
  let os := muNegOneOwners uTri vTri
  (List.range os.length).flatMap fun a =>
    ((List.range os.length).filter fun b =>
      a < b && muNegOneAdm (os[a]!) (os[b]!)).map fun b => (a, b)

def muNegOneXVar? (pairs : List (Nat × Nat)) (a b : Nat) : Option Nat :=
  let p := if a < b then (a, b) else (b, a)
  (pairs.idxOf? p).map (· + 65)

def muNegOneXLit? (pairs : List (Nat × Nat)) (a b : Nat) : Option Int :=
  (muNegOneXVar? pairs a b).map Int.ofNat

/-- Python-order exactly-two: all (n−1)-subsets as ALO clauses in element
order, then negated triples in combination order. -/
def muNegOneExactlyTwo (lits : List Int) : List DimacsClause :=
  (lits.map fun x => lits.filter fun l => l != x) ++
  ((List.range lits.length).flatMap fun i =>
    ((List.range lits.length).filter fun j => i < j).flatMap fun j =>
      ((List.range lits.length).filter fun k => j < k).map fun k =>
        [-lits[i]!, -lits[j]!, -lits[k]!])

def muNegOneCrossRowClauses (σ : Bool) : List DimacsClause :=
  (List.range 8).flatMap fun i =>
    muNegOneExactlyTwo (((List.range 8).filter fun j =>
      muNegOneSign σ i == muNegOneSign σ (8 + j)).map fun j =>
        Int.ofNat (muNegOneDVar i j)) ++
    muNegOneExactlyTwo (((List.range 8).filter fun j =>
      !(muNegOneSign σ i == muNegOneSign σ (8 + j))).map fun j =>
        Int.ofNat (muNegOneDVar i j))

def muNegOneCrossColClauses (σ : Bool) : List DimacsClause :=
  (List.range 8).flatMap fun j =>
    muNegOneExactlyTwo (((List.range 8).filter fun i =>
      muNegOneSign σ i == muNegOneSign σ (8 + j)).map fun i =>
        Int.ofNat (muNegOneDVar i j)) ++
    muNegOneExactlyTwo (((List.range 8).filter fun i =>
      !(muNegOneSign σ i == muNegOneSign σ (8 + j))).map fun i =>
        Int.ofNat (muNegOneDVar i j))

def muNegOneSumEq (a b c d : Int) : List DimacsClause :=
  [[-a, c, d], [-b, c, d], [-c, a, b], [-d, a, b],
   [-a, -b, c], [-a, -b, d], [-c, -d, a], [-c, -d, b]]

def muNegOneIntertwineClauses : List DimacsClause :=
  (List.range 8).flatMap fun i =>
    (List.range 8).flatMap fun j =>
      muNegOneSumEq
        (Int.ofNat (muNegOneDVar ((i + 7) % 8) j))
        (Int.ofNat (muNegOneDVar ((i + 1) % 8) j))
        (Int.ofNat (muNegOneDVar i ((j + 1) % 8)))
        (Int.ofNat (muNegOneDVar i ((j + 7) % 8)))

/-- Cross owner guard variable, none for within-shore owners. -/
def muNegOneGuard? (uTri vTri : Bool) (a : Nat) : Option Nat :=
  if a < 16 then none
  else
    let p := (muNegOneOwners uTri vTri)[a]!
    some (muNegOneDVar p.1 (p.2 - 8))

def muNegOneHitActivityClauses (uTri vTri : Bool)
    (pairs : List (Nat × Nat)) : List DimacsClause :=
  pairs.flatMap fun pr =>
    match muNegOneXVar? pairs pr.1 pr.2 with
    | some x =>
        (match muNegOneGuard? uTri vTri pr.1 with
          | some g => [[-Int.ofNat x, -Int.ofNat g]]
          | none => []) ++
        (match muNegOneGuard? uTri vTri pr.2 with
          | some g => [[-Int.ofNat x, -Int.ofNat g]]
          | none => [])
    | none => []

def muNegOnePairsOf (lits : List Int) (prefixLits : List Int) :
    List DimacsClause :=
  (List.range lits.length).flatMap fun i =>
    ((List.range lits.length).filter fun j => i < j).map fun j =>
      prefixLits ++ [-lits[i]!, -lits[j]!]

def muNegOneServiceClauses (uTri vTri : Bool)
    (pairs : List (Nat × Nat)) : List DimacsClause :=
  let os := muNegOneOwners uTri vTri
  (List.range os.length).flatMap fun a =>
    let pre : List Int :=
      match muNegOneGuard? uTri vTri a with
      | some g => [Int.ofNat g]
      | none => []
    (muNegOneTwelve (os[a]!)).flatMap fun w =>
      let lits := (List.range os.length).filterMap fun b =>
        if b != a && muNegOnePairMem (os[b]!) w then
          muNegOneXLit? pairs a b
        else none
      [pre ++ lits] ++ muNegOnePairsOf lits pre

def muNegOneShare (p q : Nat × Nat) : Bool :=
  muNegOnePairMem q p.1 || muNegOnePairMem q p.2

def muNegOneC4Clauses (uTri vTri : Bool)
    (pairs : List (Nat × Nat)) : List DimacsClause :=
  let os := muNegOneOwners uTri vTri
  (List.range os.length).flatMap fun a =>
    ((List.range os.length).filter fun b => a < b).flatMap fun b =>
      let ks := (List.range os.length).filter fun g =>
        g != a && g != b && (muNegOneXVar? pairs a g).isSome &&
          (muNegOneXVar? pairs b g).isSome
      if muNegOneShare (os[a]!) (os[b]!) then
        ks.filterMap fun g => do
          let x ← muNegOneXLit? pairs a g
          let y ← muNegOneXLit? pairs b g
          return [-x, -y]
      else
        (List.range ks.length).flatMap fun gi =>
          ((List.range ks.length).filter fun hi => gi < hi).filterMap
            fun hi => do
              let xag ← muNegOneXLit? pairs a (ks[gi]!)
              let xbg ← muNegOneXLit? pairs b (ks[gi]!)
              let xah ← muNegOneXLit? pairs a (ks[hi]!)
              let xbh ← muNegOneXLit? pairs b (ks[hi]!)
              return [-xag, -xbg, -xah, -xbh]

def muNegOneOneFourOwnerDimacsClauses (uTri vTri σ : Bool) :
    Array DimacsClause :=
  let pairs := muNegOneHitPairs uTri vTri
  (muNegOneCrossRowClauses σ ++ muNegOneCrossColClauses σ ++
    muNegOneIntertwineClauses ++
    muNegOneHitActivityClauses uTri vTri pairs ++
    muNegOneServiceClauses uTri vTri pairs ++
    muNegOneC4Clauses uTri vTri pairs).toArray

def muNegOneOneFourOwnerSatCnf (uTri vTri σ : Bool) : CNF Nat where
  clauses :=
    dimacsFormulaToSatClauses (muNegOneOneFourOwnerDimacsClauses uTri vTri σ)

set_option maxHeartbeats 0 in
theorem muNegOneOneFourOwnerDimacsClauses_size_TFTF :
    (muNegOneOneFourOwnerDimacsClauses false false false).size = 550016 := by
  native_decide

set_option maxHeartbeats 0 in
theorem muNegOneOneFourOwnerDimacsClauses_size_tritri :
    (muNegOneOneFourOwnerDimacsClauses true true false).size = 558336 := by
  native_decide

end Erdos85
