import Proofs.Erdos85H3TripleCompletionSplit

/- Instrumentation only. This mirrors dfs1 with a constant-true leaf and
records the real stKey distribution. It asserts no exclusion theorem. -/
set_option maxRecDepth 100000

namespace Erdos85.H3TripleCompletion

structure Profile where
  nodes : Nat := 0
  leaves : Nat := 0
  exhausted : Nat := 0
  invalid : Nat := 0
  buckets : Array Nat := Array.replicate 384 0

def profilePhaseOne : Nat → St → StateM Profile Unit
  | 0, _ => modify fun p => { p with exhausted := p.exhausted + 1 }
  | fuel + 1, s => do
    modify fun p => { p with nodes := p.nodes + 1 }
    match findClause s with
    | none =>
      let bucket := stKey s % 384
      modify fun p => { p with leaves := p.leaves + 1,
        buckets := p.buckets.modify bucket (· + 1) }
    | some (u, w) =>
      if decide (3 ≤ u.val) && clauseOpen s u w then
        for x in fiberList w do
          if !(decide (x = u) || twinSkip s u w x) then
            match s.tryAdd u x with
            | none => pure ()
            | some s' => profilePhaseOne fuel s'
      else
        modify fun p => { p with invalid := p.invalid + 1 }

#eval do
  let (_, p) := (profilePhaseOne 70 s0).run {}
  IO.println s!"nodes={p.nodes} leaves={p.leaves} exhausted={p.exhausted} invalid={p.invalid}"
  IO.println s!"buckets={p.buckets.toList}"

end Erdos85.H3TripleCompletion
