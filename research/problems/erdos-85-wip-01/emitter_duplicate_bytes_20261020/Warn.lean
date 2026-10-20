def f (s : String) : List Char := s.data
def main (args : List String) : IO UInt32 := do
  IO.eprintln s!"args={args}"; return 2
