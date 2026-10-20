/-! Reproducer: build a large DIMACS-like String by repeated `++` and print it once. -/

def clauseLine (clause : List Int) : String :=
  String.intercalate " " (clause.map toString) ++ " 0"

/-- Deterministic pseudo-clauses: lengths 1..4, literals in ±[1, top]. -/
def mkClauses (n top : Nat) : Array (List Int) := Id.run do
  let mut out : Array (List Int) := Array.mkEmpty n
  let mut s : Nat := 12345
  for _ in [0:n] do
    s := (s * 1103515245 + 12345) % 2147483648
    let len := s % 4 + 1
    let mut c : List Int := []
    for _ in [0:len] do
      s := (s * 1103515245 + 12345) % 2147483648
      let v : Int := Int.ofNat (s % top + 1)
      c := (if s % 2 = 0 then v else -v) :: c
    out := out.push c
  return out

def renderDimacs (top : Nat) (cls : Array (List Int)) : String := Id.run do
  let mut out := s!"p cnf {top} {cls.size}\n"
  for clause in cls do
    out := out ++ clauseLine clause ++ "\n"
  return out

def emitChunked (top : Nat) (cls : Array (List Int)) : IO Unit := do
  IO.print s!"p cnf {top} {cls.size}\n"
  let mut chunk := ""
  for i in [0:cls.size] do
    chunk := chunk ++ clauseLine cls[i]! ++ "\n"
    if i % 4096 = 4095 then
      IO.print chunk
      chunk := ""
  if !chunk.isEmpty then
    IO.print chunk

def main (args : List String) : IO UInt32 := do
  match args with
  | [mode, nStr] =>
    let n := nStr.toNat!
    let cls := mkClauses n 42184
    match mode with
    | "whole" => IO.print (renderDimacs 42184 cls); return 0
    | "chunk" => emitChunked 42184 cls; return 0
    | "size"  =>
        let s := renderDimacs 42184 cls
        IO.eprintln s!"utf8ByteSize={s.utf8ByteSize} length={s.length}"
        return 0
    | "stdouth" =>
        -- print via raw handle putStr, bypassing Stream
        let h ← IO.getStdout
        h.putStr (renderDimacs 42184 cls); h.flush; return 0
    | _ => return 2
  | [mode, nStr, dStr] =>
    let n := nStr.toNat!
    let d := dStr.toNat!
    let cls := mkClauses n 42184
    match mode with
    | "late" =>
        -- mimic `lean --run`: 340 bytes of elaboration warnings land in the
        -- (fully buffered) stdout first, then the run takes a while.
        IO.print (String.ofList (List.replicate 339 'w') ++ "\n")
        IO.sleep d.toUInt32
        IO.print (renderDimacs 42184 cls); return 0
    | "delay" =>
        let s := renderDimacs 42184 cls
        IO.sleep d.toUInt32
        IO.print s; return 0
    | _ => return 2
  | _ => IO.eprintln "usage: emitbug whole|chunk|size N"; return 2
