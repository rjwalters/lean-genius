import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalHsbGen

/-!
DIMACS emitter for the Lean `hsb` clause list, for byte-identity checks
against `gen_pilot.py` (see `check_hsb_lean_identity.py` next to it).

    h7hsb hsb   <depth> <mask>   -- SevenHighT0Hsb.clauses depth mask
    h7hsb cover <depth> <mask>   -- SevenHighT0Hsb.coverClauses depth mask

One clause per line, no header.  `stderr` reports how many search entries
were produced and how many survived the witness check (they must agree).
-/

namespace Erdos85.SevenHighT0HsbEmit

open Erdos85.SevenHighT0Hsb

def clauseLine (c : List (Nat × Bool)) : String :=
  String.intercalate " "
    (c.map fun l => (if l.2 then "" else "-") ++ toString (l.1 + 1)) ++ " 0\n"

def emitClauses (cs : List (List (Nat × Bool))) : IO Unit := do
  let out ← IO.getStdout
  let mut chunk := ""
  let mut n := 0
  for c in cs do
    chunk := chunk ++ clauseLine c
    n := n + 1
    if n % 4096 = 0 then
      out.putStr chunk
      chunk := ""
  out.putStr chunk
  out.flush

end Erdos85.SevenHighT0HsbEmit

open Erdos85.SevenHighT0Hsb Erdos85.SevenHighT0HsbEmit in
def main (args : List String) : IO UInt32 := do
  match args with
  | [mode, depthS, maskS] =>
      let depth := depthS.toNat!
      let mask := maskS.toNat!
      if mode == "hsb" then
        let es := entries depth mask
        let cs := clausesOfEntries mask es
        emitClauses cs
        IO.eprintln s!"entries={es.length} checked={cs.length}"
        pure (if es.length == cs.length then 0 else 3)
      else if mode == "cover" then
        let cs := coverClauses depth mask
        emitClauses cs
        IO.eprintln s!"leaves={cs.length}"
        pure 0
      else
        IO.eprintln "mode must be hsb or cover"
        pure 2
  | _ =>
      IO.eprintln "usage: h7hsb (hsb|cover) <depth> <mask>"
      pure 2
