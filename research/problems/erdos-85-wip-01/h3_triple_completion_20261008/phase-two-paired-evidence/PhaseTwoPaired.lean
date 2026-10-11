import Proofs.Erdos85H3TripleCompletionSplit

/- Bounded instrumentation only. No equivalence or exclusion theorem is claimed.
Collect the exact bucket-zero phase-one states, then count phase-two nodes with
the same filtering, choice, insertion and pattern-ban order as the engine. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Erdos85.H3TripleCompletion

structure TwoProfile where
  nodes : Nat := 0
  leaves : Nat := 0
  exhausted : Nat := 0
  invalid : Nat := 0
  noFresh : Nat := 0
  rejected : Nat := 0
  available : Nat := 0
  capped : Bool := false

def collectZero : Nat → St → StateM (Array St) Unit
  | 0, _ => pure ()
  | fuel + 1, s => do
    match findClause s with
    | none =>
      if stKey s % 384 = 0 then modify (·.push s)
    | some (u, w) =>
      if decide (3 ≤ u.val) && clauseOpen s u w then
        for x in fiberList w do
          if !(decide (x = u) || twinSkip s u w x) then
            match s.tryAdd u x with
            | none => pure ()
            | some s' => collectZero fuel s'

def profilePatterns (limit : Nat) (f : Tri → List Tri → StateM TwoProfile Unit)
    (pre : List Tri) : List Tri → StateM TwoProfile Unit
  | [] => pure ()
  | c :: rest => do
    if (← get).nodes ≥ limit then
      modify fun p => { p with capped := true }
      return
    f c (pre ++ c :: rest)
    profilePatterns limit f pre rest

def profileTwo (fast : Bool) (limit : Nat) : Nat → St → List Tri → StateM TwoProfile Unit
  | 0, _, _ => modify fun p => { p with exhausted := p.exhausted + 1 }
  | fuel + 1, s, avail0 => do
    if (← get).nodes ≥ limit then
      modify fun p => { p with capped := true }
      return
    modify fun p => { p with nodes := p.nodes + 1 }
    if !(if fast then stateOKFast s else stateOK s) then
      modify fun p => { p with invalid := p.invalid + 1 }
      return
    let avail := avail0.filter (insertable s)
    modify fun p => { p with available := p.available + avail.length }
    match pickCore s avail with
    | none => modify fun p => { p with leaves := p.leaves + 1 }
    | some v =>
      if !(decide (3 ≤ v.val) && decide (v.val < 25) &&
          decide ((s.nbr[v.val]).length < 7)) then
        modify fun p => { p with invalid := p.invalid + 1 }
        return
      match findFresh s with
      | none => modify fun p => { p with noFresh := p.noFresh + 1 }
      | some n =>
        if !(decide (25 ≤ n.val) && (s.rows[n.val] == 0)) then
          modify fun p => { p with invalid := p.invalid + 1 }
          return
        let m := maskOf v
        profilePatterns limit (fun c av => do
          match addTri s n c with
          | none => modify fun p => { p with rejected := p.rejected + 1 }
          | some s' => profileTwo fast limit fuel s' av)
          (avail.filter fun t => !containsM m v t)
          (avail.filter fun t => containsM m v t)

def runTwoProfile : IO Unit := do
  let (_, states) := (collectZero 70 s0).run #[]
  IO.println s!"STATES count={states.size}"
  for fast in [false, true] do
    let mut i := 0
    for s in states do
      i := i + 1
      let cell ← IO.mkRef ({} : TwoProfile)
      let begin ← IO.monoMsNow
      let (_, p) := (profileTwo fast 10000 30 s allTriples).run {}
      cell.set p
      let finish ← IO.monoMsNow
      let p ← cell.get
      IO.println s!"PROFILE fast={fast} leaf={i} key={stKey s} nodes={p.nodes} leaves={p.leaves} exhausted={p.exhausted} invalid={p.invalid} no_fresh={p.noFresh} rejected={p.rejected} available={p.available} capped={p.capped} elapsed_ms={finish-begin}"

#eval runTwoProfile

end Erdos85.H3TripleCompletion
