import Std

/-!
# Executable core of the three-high triple completion engine

The declarations are moved verbatim from the soundness engine, initial-state
bridge and hash split. Keeping this module independent of Mathlib allows its
generated C to be precompiled without precompiling the proof dependency tree.
The Engine, Bridge and Split modules retain the soundness proofs.
-/

namespace Erdos85
namespace H3TripleCompletion

abbrev V := Fin 49

/-- High-support mask of the canonical `t = 1` labelling. -/
def maskOf (v : V) : Nat :=
  if v.val < 3 then 0 else if v.val = 3 then 7 else if v.val < 11 then 1
  else if v.val < 18 then 2 else if v.val < 25 then 4 else 0

def col (v : V) (w : Fin 3) : Bool := (maskOf v).testBit w.val

def capOf (v : V) : Nat := if v.val < 3 then 8 else 7

def fiber0 : List V := [3, 4, 5, 6, 7, 8, 9, 10]

def fiber1 : List V := [3, 11, 12, 13, 14, 15, 16, 17]

def fiber2 : List V := [3, 18, 19, 20, 21, 22, 23, 24]

def fiberList (w : Fin 3) : List V :=
  match w with
  | 0 => fiber0
  | 1 => fiber1
  | 2 => fiber2

def fiberMask (w : Fin 3) : Nat :=
  match w with
  | 0 => 2040
  | 1 => 260104
  | 2 => 33292296

def highVerts : List V := [0, 1, 2]

def coreVerts : List V :=
  [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]

def emptyVerts : List V :=
  [25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41,
    42, 43, 44, 45, 46, 47, 48]

def coreClauses : List (V × Fin 3) :=
  coreVerts.flatMap fun u => [(u, 0), (u, 1), (u, 2)]

def M49 : Nat := 2 ^ 49 - 1

/-- A partial graph: a bit row and a neighbour list for each vertex. -/
structure St where
  rows : Vector Nat 49
  nbr : Vector (List V) 49

def St.adj (s : St) (a b : V) : Bool := (s.rows[a.val]).testBit b.val

def St.addEdge (s : St) (u x : V) : St where
  rows := (s.rows.set u.val (s.rows[u.val] ||| 2 ^ x.val)).set x.val
    (s.rows[x.val] ||| 2 ^ u.val)
  nbr := (s.nbr.set u.val (x :: s.nbr[u.val])).set x.val (u :: s.nbr[x.val])

def St.allowed (s : St) (u x : V) : Bool :=
  decide ((s.nbr[x.val]).length < capOf x) &&
    decide ((s.nbr[u.val]).length < capOf u) &&
    (s.nbr[u.val]).all fun y => ((s.rows[y.val] &&& s.rows[x.val]) &&& M49) == 0

def St.tryAdd (s : St) (u x : V) : Option St :=
  if u = x then none
  else if s.adj u x then some s
  else if s.allowed u x then some (s.addEdge u x) else none

def clauseOpen (s : St) (u : V) (w : Fin 3) : Bool :=
  ((s.rows[u.val] &&& fiberMask w) &&& M49) == 0

def twinSkip (s : St) (u : V) (w : Fin 3) (x : V) : Bool :=
  (fiberList w).any fun y =>
    decide (y.val < x.val) && decide (y ≠ u) &&
      decide (s.rows[y.val] = s.rows[x.val]) && decide (maskOf y = maskOf x)

def findClause (s : St) : Option (V × Fin 3) :=
  coreClauses.find? fun p => clauseOpen s p.1 p.2

def dfs1 (leaf : St → Bool) : Nat → St → Bool
  | 0, _ => false
  | fuel + 1, s =>
    match findClause s with
    | none => leaf s
    | some (u, w) =>
      decide (3 ≤ u.val) && clauseOpen s u w &&
        (fiberList w).all fun x =>
          decide (x = u) || twinSkip s u w x ||
            match s.tryAdd u x with
            | none => true
            | some s' => dfs1 leaf fuel s'

abbrev Tri := V × V × V

def allTriples : List Tri :=
  fiber0.flatMap fun a => fiber1.flatMap fun b => fiber2.map fun c => (a, b, c)

def containsV (v : V) (t : Tri) : Bool :=
  (!col v 0 || decide (t.1 = v)) && (!col v 1 || decide (t.2.1 = v)) &&
    (!col v 2 || decide (t.2.2 = v))

def pairOK (s : St) (a b : V) : Bool :=
  decide (a = b) || (((s.rows[a.val] &&& s.rows[b.val]) &&& M49) == 0)

def insertable (s : St) (t : Tri) : Bool :=
  decide ((s.nbr[t.1.val]).length < capOf t.1) &&
    decide ((s.nbr[t.2.1.val]).length < capOf t.2.1) &&
    decide ((s.nbr[t.2.2.val]).length < capOf t.2.2) &&
    pairOK s t.1 t.2.1 && pairOK s t.1 t.2.2 && pairOK s t.2.1 t.2.2

def hasCol (s : St) (a : V) (w : Fin 3) : Bool :=
  !(((s.rows[a.val] &&& fiberMask w) &&& M49) == 0)

def hasAllCols (s : St) (a : V) : Bool := hasCol s a 0 && hasCol s a 1 && hasCol s a 2

/-- Runtime closure check used by phase 2: highs are full, nonempty low
vertices have all colour neighbours, and each empty vertex is either
untouched or has all colour neighbours. -/
def stateOK (s : St) : Bool :=
  (highVerts.all fun h => decide ((s.nbr[h.val]).length = capOf h)) &&
    (coreVerts.all fun a => hasAllCols s a) &&
    (emptyVerts.all fun e => (s.rows[e.val] == 0) || hasAllCols s e)

/-- The fibre masks already have no bits above 48. Cache the row and avoid
three redundant intersections with M49. -/
@[inline] def hasAllColsFast (s : St) (a : V) : Bool :=
  let row := s.rows[a.val]
  !((row &&& 2040) == 0) && !((row &&& 260104) == 0) &&
    !((row &&& 33292296) == 0)

def stateOKFast (s : St) : Bool :=
  (highVerts.all fun h => decide ((s.nbr[h.val]).length = capOf h)) &&
    (coreVerts.all fun a => hasAllColsFast s a) &&
    (emptyVerts.all fun e => (s.rows[e.val] == 0) || hasAllColsFast s e)

/-- Occurrence counts of the vertices in a list of triples (heuristic only). -/
def triCounts (avail : List Tri) : Array Nat :=
  avail.foldl (fun cnt t =>
    let cnt := cnt.modify t.1.val (· + 1)
    let cnt := if t.2.1 = t.1 then cnt else cnt.modify t.2.1.val (· + 1)
    if t.2.2 = t.1 ∨ t.2.2 = t.2.1 then cnt else cnt.modify t.2.2.val (· + 1))
    (Array.replicate 49 0)

/-- Choose the deficient nonempty vertex minimizing candidate count divided by
remaining degree. Cross multiplication avoids division and preserves the first
vertex on ties. `dfs2` soundness is independent of this ordering. -/
def pickCore (s : St) (avail : List Tri) : Option V :=
  let cnt := triCounts avail
  (coreVerts.foldl (fun (best : Option (Nat × Nat × V)) v =>
    let need := 7 - (s.nbr[v.val]).length
    if 0 < need then
      let c := cnt[v.val]!
      match best with
      | none => some (c, need, v)
      | some (c', need', _) =>
        if c * need' < c' * need then some (c, need, v) else best
    else best) none).map fun p => p.2.2

def findFresh (s : St) : Option V :=
  emptyVerts.find? fun e => s.rows[e.val] == 0

def addTri (s : St) (n : V) (t : Tri) : Option St :=
  match s.tryAdd n t.1 with
  | none => none
  | some s1 =>
    match s1.tryAdd n t.2.1 with
    | none => none
    | some s2 => s2.tryAdd n t.2.2

def patLoop (f : Tri → List Tri → Bool) (pre : List Tri) : List Tri → Bool
  | [] => true
  | c :: rest => f c (pre ++ c :: rest) && patLoop f pre rest

def containsM (m : Nat) (v : V) (t : Tri) : Bool :=
  (!m.testBit 0 || decide (t.1 = v)) && (!m.testBit 1 || decide (t.2.1 = v)) &&
    (!m.testBit 2 || decide (t.2.2 = v))

/-- `patLoop` on the available triples split by whether they contain `v`. -/
def patLoopSplit (f : Tri → List Tri → Bool) (v : V) (avail : List Tri) : Bool :=
  let m := maskOf v
  patLoop f (avail.filter fun t => !containsM m v t) (avail.filter fun t => containsM m v t)

/-- One phase-2 node, with the recursive call abstracted. -/
def step2 (leaf : St → Bool) (rec : St → List Tri → Bool) (s : St)
    (avail : List Tri) : Bool :=
  match pickCore s avail with
  | none => leaf s
  | some v =>
    decide (3 ≤ v.val) && decide (v.val < 25) &&
      decide ((s.nbr[v.val]).length < 7) &&
      match findFresh s with
      | none => true
      | some n =>
        decide (25 ≤ n.val) && (s.rows[n.val] == 0) &&
          patLoopSplit
            (fun c av =>
              match addTri s n c with
              | none => true
              | some s' => rec s' av)
            v avail

def dfs2 (leaf : St → Bool) : Nat → St → List Tri → Bool
  | 0, _, _ => false
  | fuel + 1, s, avail0 =>
    stateOKFast s && step2 leaf (dfs2 leaf fuel) s (avail0.filter (insertable s))

/-- Initial bit row: a high vertex sees its colour fibre, a low vertex sees
the high vertices in its mask. -/
def initRow (a : V) : Nat :=
  if h : a.val < 3 then fiberMask ⟨a.val, h⟩ else maskOf a

/-- The initial partial graph: exactly the high–low edges. -/
def s0 : St where
  rows := Vector.ofFn initRow
  nbr := Vector.ofFn fun a => (List.finRange 49).filter fun b => (initRow a).testBit b.val

/-- A cheap key of a partial graph, used only to distribute phase-1 leaves. -/
def stKey (s : St) : Nat :=
  s.rows.toArray.foldl (fun acc r => (acc * 31 + r) % 1000003) 0

/-! ## Phase-three candidate and insertion helpers -/

def cands3 (s : St) (u : V) : List V :=
  (List.finRange 49).filter fun x => decide (x ≠ u) && !s.adj u x && s.allowed u x

def gate3 (s : St) : Bool :=
  emptyVerts.any fun u =>
    decide ((s.nbr[u.val]).length < 7) &&
      decide ((s.nbr[u.val]).length + (cands3 s u).length < 7)

def pick3 (s : St) : Option V :=
  (emptyVerts.foldl (fun (best : Option (Nat × V)) u =>
    if (s.nbr[u.val]).length < 7 then
      let cnt := (cands3 s u).length
      match best with
      | none => some (cnt, u)
      | some (c, _) => if cnt < c then some (cnt, u) else best
    else best) none).map fun p => p.2

def addMany (s : St) (u : V) : List V → Option St
  | [] => some s
  | x :: xs =>
    match s.tryAdd u x with
    | none => none
    | some s' => addMany s' u xs

end H3TripleCompletion
end Erdos85
