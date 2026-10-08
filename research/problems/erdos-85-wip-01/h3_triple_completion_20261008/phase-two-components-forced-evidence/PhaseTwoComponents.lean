import Proofs.Erdos85H3TripleCompletionSplit

/- Bounded instrumentation only. No equivalence or exclusion theorem is claimed.
Collect at most 1,000 phase-two node inputs per bucket-zero state, then replay
individual components. Timings include each replay loop and are not additive
production runtime measurements. Insert replays all candidates, including those
not reached before the collection cap. Checksums keep results observable. -/
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
  samples : Array (St × List Tri) := #[]

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

def profileTwo (limit : Nat) : Nat → St → List Tri → StateM TwoProfile Unit
  | 0, _, _ => modify fun p => { p with exhausted := p.exhausted + 1 }
  | fuel + 1, s, avail0 => do
    if (← get).nodes ≥ limit then
      modify fun p => { p with capped := true }
      return
    modify fun p => { p with
      nodes := p.nodes + 1
      samples := p.samples.push (s, avail0) }
    if !stateOK s then
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
          | some s' => profileTwo limit fuel s' av)
          (avail.filter fun t => !containsM m v t)
          (avail.filter fun t => containsM m v t)

structure NodeSample where
  state : St
  input : List Tri
  filtered : List Tri
  picked : Option V
  fresh : Option V

def enrichSample (s : St) (input : List Tri) : NodeSample :=
  let filtered := input.filter (insertable s)
  ⟨s, input, filtered, pickCore s filtered, findFresh s⟩

/-- Force the computed checksum into an IO reference before stopping the clock. -/
@[noinline] def timeComponent (leaf : Nat) (name : String) (f : Unit → Nat) : IO Unit := do
  let cell ← IO.mkRef 0
  let begin ← IO.monoMsNow
  cell.set (f ())
  let finish ← IO.monoMsNow
  let checksum ← cell.get
  IO.println s!"COMPONENT leaf={leaf} name={name} elapsed_ms={finish-begin} checksum={checksum}"

def appendChecksum (pre : List Tri) : List Tri → Nat
  | [] => 0
  | c :: rest => (pre ++ c :: rest).length + appendChecksum pre rest

def runComponents : IO Unit := do
  let (_, states) := (collectZero 70 s0).run #[]
  IO.println s!"STATES count={states.size}"
  let mut i := 0
  for s in states do
    i := i + 1
    let (_, p) := (profileTwo 1000 30 s allTriples).run {}
    IO.println s!"SAMPLE leaf={i} key={stKey s} nodes={p.nodes} leaves={p.leaves} exhausted={p.exhausted} invalid={p.invalid} capped={p.capped}"
    let samples := p.samples.map fun (s, av) => enrichSample s av
    timeComponent i "state" fun _ => samples.foldl (fun acc x =>
      acc + if stateOK x.state then 1 else 0) 0
    timeComponent i "filter" fun _ => samples.foldl (fun acc x =>
      acc + (x.input.filter (insertable x.state)).length) 0
    timeComponent i "pick" fun _ => samples.foldl (fun acc x =>
      acc + ((pickCore x.state x.filtered).map (fun v => v.val+1)).getD 0) 0
    timeComponent i "fresh" fun _ => samples.foldl (fun acc x =>
      acc + ((findFresh x.state).map (fun v => v.val+1)).getD 0) 0
    timeComponent i "partition" fun _ => samples.foldl (fun acc x =>
      match x.picked with
      | none => acc
      | some v =>
        let m := maskOf v
        acc + (x.filtered.filter fun t => !containsM m v t).length +
          (x.filtered.filter fun t => containsM m v t).length) 0
    timeComponent i "append" fun _ => samples.foldl (fun acc x =>
      match x.picked with
      | none => acc
      | some v =>
        let m := maskOf v
        acc + appendChecksum (x.filtered.filter fun t => !containsM m v t)
          (x.filtered.filter fun t => containsM m v t)) 0
    timeComponent i "insert" fun _ => samples.foldl (fun acc x =>
      match x.picked, x.fresh with
      | some v, some n =>
        (x.filtered.filter (containsM (maskOf v) v)).foldl (fun acc t =>
          match addTri x.state n t with
          | none => acc
          | some child => acc + (child.nbr[n.val]).length + 1) acc
      | _, _ => acc) 0

#eval runComponents

end Erdos85.H3TripleCompletion
