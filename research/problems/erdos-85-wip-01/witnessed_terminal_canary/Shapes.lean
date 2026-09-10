import Proofs.Erdos85ThreeHighCanonicalTripleShapes
open Erdos85
def main : IO Unit := do
  for k in List.finRange 3 do
    IO.println s!"{(threeHighCanonicalTripleShapes k).map (fun S => ((List.finRange 24).filter (fun i => i ∈ S)).map Fin.val)}"
