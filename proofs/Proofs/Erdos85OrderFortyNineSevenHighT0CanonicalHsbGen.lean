import Std.Data.HashMap

/-!
# High-side symmetry-breaking clauses (`hsb`) for the H7/T0 cubes: generator

Core-only (no Mathlib) transcription of `hsb_clauses` in
`research/problems/erdos-85-wip-01/h7_structural_pilot_20261008/gen_pilot.py`.

Vertices use the canonical numbering: empties `7..13`, singleton lows
`14..27` (`14 + 2 * label + copy`), pair lows `28..48` (lexicographic label
pairs).  A *row* is the sorted list of outside (`14..48`) neighbours of one
empty vertex.  A clause forbids one row of empty `7 + k` given exact rows of
empties `7 .. 7 + k - 1`.

Soundness does **not** depend on the search below being right.  Every emitted
clause carries a witness `(sig, flips)` of the high-side group
`S₇ ⋉ (ℤ/2)⁷`; `check` re-validates the witness with the small pure functions
`vmap` / `key`, and `clauses` keeps only entries that pass `check`.  The
soundness theorem (`...HsbSound`) is about `check`, so a bug in the search can
only drop clauses (which the byte-identity test against the Python generator
would reveal), never produce an unsound one.
-/

namespace Erdos85.SevenHighT0Hsb

/-- Label pair of pair-support vertex `28 + index`. -/
def pairOf (index : Nat) : Nat × Nat :=
  if index < 6 then (0, index + 1)
  else if index < 11 then (1, index - 4)
  else if index < 15 then (2, index - 8)
  else if index < 18 then (3, index - 11)
  else if index < 20 then (4, index - 13)
  else (5, 6)

/-- Index of the label pair `a < b` in lexicographic order. -/
def pairIdx (a b : Nat) : Nat := a * (13 - a) / 2 + (b - a - 1)

/-- Action of the group element `(sig, flips)` on an outside vertex
(`vmap` of the Python generator). -/
def vmap (sig : Nat → Nat) (flips : Nat) (v : Nat) : Nat :=
  if v < 28 then
    14 + 2 * sig ((v - 14) / 2) +
      (if flips.testBit ((v - 14) / 2) then 1 - (v - 14) % 2
        else (v - 14) % 2)
  else
    28 + pairIdx
      (min (sig (pairOf (v - 28)).1) (sig (pairOf (v - 28)).2))
      (max (sig (pairOf (v - 28)).1) (sig (pairOf (v - 28)).2))

/-- Weight of an outside vertex: smaller key = lexicographically smaller row
in DIMACS edge order (`row_key` of the Python generator). -/
def weight (v : Nat) : Nat := 2 ^ (48 - v)

def key (row : List Nat) : Nat := (row.map weight).sum

/-- Adjacency of two empty labels in a 21-bit empty-sector mask. -/
def maskAdj (mask left right : Nat) : Bool :=
  left != right && mask.testBit (pairIdx (min left right) (max left right))

/-- Number of empty neighbours of empty label `e`. -/
def maskDeg (mask e : Nat) : Nat :=
  (if maskAdj mask e 0 then 1 else 0) + (if maskAdj mask e 1 then 1 else 0) +
  (if maskAdj mask e 2 then 1 else 0) + (if maskAdj mask e 3 then 1 else 0) +
  (if maskAdj mask e 4 then 1 else 0) + (if maskAdj mask e 5 then 1 else 0) +
  (if maskAdj mask e 6 then 1 else 0)

/-- Zero-based SAT variable of the low edge `(7 + j, v)`, `j < 7 ≤ 14 ≤ v`. -/
def edgeVar (j v : Nat) : Nat := j * (83 - j) / 2 + (v - 7 - j - 1)

/-- The clause "not all of these rows": negative literals of the edges
`(7 + j, v)`, `v ∈ rows[j]`.  Also the blocking clause of a leaf. -/
def clause (rows : List (List Nat)) : List (Nat × Bool) :=
  (List.range rows.length).flatMap fun j =>
    (rows.getD j []).map fun v => (edgeVar j v, false)

def sigOf (sig : List Nat) (i : Nat) : Nat := sig.getD i 0

/-- `sig` restricted to `0..6` is an injection into `0..6`. -/
def sigOk (sig : List Nat) : Bool :=
  (List.range 7).all fun i =>
    decide (sigOf sig i < 7) &&
      (List.range 7).all fun j => i == j || sigOf sig i != sigOf sig j

/-- A plausible exact row of empty `7 + j`: outside vertices, no repeats, and
as many as the low-degree equation leaves for outside neighbours. -/
def rowOk (mask j : Nat) (row : List Nat) : Bool :=
  row.all (fun v => decide (14 ≤ v) && decide (v < 49)) &&
    decide row.Nodup && decide (row.length + maskDeg mask j = 7)

/-- Witness check for one clause: the group element fixes (the key of) every
prefix row and strictly lowers the key of the last row. -/
def check (mask : Nat) (rows : List (List Nat)) (sig : List Nat)
    (flips : Nat) : Bool :=
  decide (0 < rows.length) && decide (rows.length ≤ 7) && sigOk sig &&
    (List.range rows.length).all fun j =>
      rowOk mask j (rows.getD j []) &&
        (if j + 1 = rows.length then
          decide (key ((rows.getD j []).map (vmap (sigOf sig) flips)) <
            key (rows.getD j []))
        else
          decide (key ((rows.getD j []).map (vmap (sigOf sig) flips)) =
            key (rows.getD j [])))

structure Entry where
  rows : List (List Nat)
  sig : List Nat
  flips : Nat

def Entry.ok (mask : Nat) (e : Entry) : Bool :=
  check mask e.rows e.sig e.flips

/-! ## Search (mirrors the Python generator; not trusted) -/

structure Elt where
  sig : List Nat
  flips : Nat
  /-- `wtab[v] = weight (vmap v)` for `14 ≤ v < 49`. -/
  wtab : Array Nat

def mkElt (sig : List Nat) (flips : Nat) : Elt :=
  { sig := sig, flips := flips,
    wtab := (Array.range 49).map fun v =>
      if v < 14 then 0 else weight (vmap (sigOf sig) flips v) }

def insertAll (x : Nat) : List Nat → List (List Nat)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertAll x ys).map (y :: ·)

def perms : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => (perms xs).flatMap (insertAll x)

def group (_ : Unit) : Array Elt :=
  ((perms (List.range 7)).flatMap fun sig =>
    (List.range 128).map fun flips => mkElt sig flips).toArray

def mappedKey (g : Elt) (row : List Nat) : Nat :=
  row.foldl (fun acc v => acc + g.wtab[v]!) 0

def invSig (sig : List Nat) : List Nat :=
  (List.range 7).map fun u => sig.idxOf u

def invFlips (sig : List Nat) (flips : Nat) : Nat :=
  (List.range 7).foldl (fun acc w =>
    if flips.testBit w then acc ||| (1 <<< sigOf sig w) else acc) 0

def labelMask (v : Nat) : Nat :=
  if v < 28 then 1 <<< ((v - 14) / 2)
  else (1 <<< (pairOf (v - 28)).1) ||| (1 <<< (pairOf (v - 28)).2)

def outside : List Nat := (List.range 35).map (· + 14)

/-- Rows of the given size with pairwise disjoint high labels, in
lexicographic order (`candidate_rows`). -/
def candRows : Nat → List Nat → Nat → List (List Nat)
  | 0, _, _ => [[]]
  | _ + 1, [], _ => []
  | n + 1, v :: rest, used =>
      (if labelMask v &&& used = 0 then
        (candRows n rest (used ||| labelMask v)).map (v :: ·)
      else []) ++ candRows (n + 1) rest used

def commonEmpty (mask e f : Nat) : Nat :=
  ((List.range 7).filter fun g => maskAdj mask e g && maskAdj mask f g).length

def compatible (mask k : Nat) (row : List Nat) (pre : List (List Nat)) :
    Bool :=
  (List.range pre.length).all fun f =>
    decide (((pre.getD f []).filter (row.contains ·)).length +
      commonEmpty mask k f ≤ 1)

inductive Item where
  | forbid (e : Entry)
  | leaf (rows : List (List Nat))

/-- One node of the stabilizer-chain recursion: forbidden rows of this node
in candidate order, then the subtrees of the canonical rows in key order. -/
def level (mask : Nat) :
    Nat → Nat → List (List Nat) → Array Elt → List Item
  | 0, _, pre, _ => [Item.leaf pre]
  | fuel + 1, k, pre, stab =>
      let cands := (candRows (7 - maskDeg mask k) outside 0).filter
        fun r => compatible mask k r pre
      let st := cands.reverse.foldl
        (fun (st : Std.HashMap Nat (Option Elt) × List (List Nat)) r =>
          if st.1.contains (key r) then st
          else
            (stab.foldl (fun (m : Std.HashMap Nat (Option Elt)) g =>
                let kk := mappedKey g r
                if m.contains kk then m else m.insert kk (some g))
              (st.1.insert (key r) none),
             r :: st.2))
        (({} : Std.HashMap Nat (Option Elt)), ([] : List (List Nat)))
      let forb := cands.filterMap fun r =>
        match st.1.get? (key r) with
        | some (some g) =>
            some (Item.forbid
              { rows := pre ++ [r], sig := invSig g.sig,
                flips := invFlips g.sig g.flips })
        | _ => none
      forb ++ st.2.reverse.flatMap fun r =>
        level mask fuel (k + 1) (pre ++ [r])
          (stab.filter fun g => mappedKey g r == key r)

def items (depth mask : Nat) : List Item :=
  level mask depth 0 [] (group ())

def entries (depth mask : Nat) : List Entry :=
  (items depth mask).filterMap fun
    | .forbid e => some e
    | .leaf _ => none

def leaves (depth mask : Nat) : List (List (List Nat)) :=
  (items depth mask).filterMap fun
    | .forbid _ => none
    | .leaf rows => some rows

/-- Clause list of entries whose witness passes `check`. -/
def clausesOfEntries (mask : Nat) (es : List Entry) :
    List (List (Nat × Bool)) :=
  (es.filter (Entry.ok mask)).map fun e => clause e.rows

/-- The `hsb<depth>` clause list of a mask, as a Lean term. -/
def clauses (depth mask : Nat) : List (List (Nat × Bool)) :=
  clausesOfEntries mask (entries depth mask)

/-- Blocking clauses of the leaves (the cover CNF's extra clauses). -/
def coverClauses (depth mask : Nat) : List (List (Nat × Bool)) :=
  (leaves depth mask).map clause

end Erdos85.SevenHighT0Hsb
