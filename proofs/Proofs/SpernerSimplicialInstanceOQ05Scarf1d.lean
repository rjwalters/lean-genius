/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: researcher-1
-/
import Proofs.SpernerSimplicialInstance
import Mathlib.Data.Fin.Basic

/-
# Constructive Scarf Walk on the 1-d Interval Triangulation

This file provides the 1-d specialisation of the Scarf walk: a
fully computable algorithm that, given a non-panchromatic starting
cell of the interval triangulation `intervalTriangulation m hm`,
walks along the pseudomanifold adjacency to find a panchromatic
cell whose existence is guaranteed by Sperner's lemma.

This is **Candidate C2-1d** of the research problem
`sperner-simplicial-instance-oq-05`. The matrix-level result
`intervalTriangulation` (in `SpernerSimplicialInstance.lean`) is the
parent; this file adds:

* `IsPanchromatic1d` — a 1-d cell is panchromatic iff its two
  vertex colours differ.
* `Scarf1d.step` — one step of the Scarf walk via the public
  `T.adj` of the parent triangulation.
* `scarfWalkAux` / `scarfWalk` — the walk itself, bounded by `m`
  fuel.
* `scarfWalk_isPanchromatic` — soundness (the walk returns a
  panchromatic cell); proof currently a `sorry` (S6+ discharge
  plan in `research/problems/sperner-simplicial-instance-oq-05/
  sessions/2026-05-30-s6-act-c2-1d.md`).
* `exists_panchromatic_constructive` — the constructive Sperner
  1-d witness extracted from the walk + soundness.

The companion smoke test verifies the walk on the `m = 3`,
"0, 0, 1" colouring at kernel level via `decide`.
-/

namespace SpernerSimplicialInstanceOQ05Scarf1d

open Triangulation

variable {m : ℕ} (c : ℕ → Fin 2)

/-- A cell `i : Fin m` of `intervalTriangulation m hm` is
**panchromatic** under colouring `c` iff its two vertices receive
different colours. The 1-d simplex has vertices `(i, i+1)`, so
`IsPanchromatic1d c i ↔ c i ≠ c (i+1)`. -/
def IsPanchromatic1d (i : Fin m) : Prop :=
  c i.val ≠ c (i.val + 1)

instance (i : Fin m) : Decidable (IsPanchromatic1d c i) := by
  unfold IsPanchromatic1d
  infer_instance

/-- One step of the **1-d Scarf walk**. From cell `i` entered
through face `k`, leave through the opposite face `k'`. If that
face is a boundary (`adj = none`), we are stuck at `i`; otherwise
the adjacent cell `i'` is either panchromatic (we are done; return
`.inl i'`) or non-panchromatic (continue; return `.inr (i', k'')`,
where `k''` is the face through which `i'` was entered, per the
pseudomanifold adjacency record). -/
def step (hm : 0 < m) (i : Fin m) (k : Fin 2)
    (_h_in : ¬ IsPanchromatic1d c i) :
    Fin m ⊕ (Fin m × Fin 2) :=
  let k' : Fin 2 := if k.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  match (Triangulation.intervalTriangulation m hm).adj i k' with
  | none           => .inl i
  | some (i', k'') =>
      if IsPanchromatic1d c i' then .inl i'
      else .inr (i', k'')

/-- The Scarf walk, recursive on a `ℕ` fuel parameter. If the
current cell is already panchromatic, return it; otherwise take a
`step`, accept the panchromatic cell if the step succeeded, else
recurse on the non-panchromatic neighbour with the remaining fuel.
Bounding `m` fuel exhausts the cell set (Pigeonhole on `Fin m`),
so the walk always terminates within `m` steps in the soundness
discharge. -/
def scarfWalkAux (hm : 0 < m) :
    Fin m → Fin 2 → ℕ → Fin m
  | start, _, 0     => start  -- fuel out (impossible in the discharge proof)
  | start, k, n + 1 =>
      if h : IsPanchromatic1d c start then start
      else
        match step c hm start k h with
        | .inl winner       => winner
        | .inr (next, k')   => scarfWalkAux hm next k' n

/-- The **1-d Scarf walk** entry point. Starts at `start` with
entry face `k`; runs for at most `m` fuel steps. -/
def scarfWalk (hm : 0 < m) (start : Fin m) (k : Fin 2)
    (_h_start : ¬ IsPanchromatic1d c start) : Fin m :=
  scarfWalkAux c hm start k m

/-- **Soundness** of the 1-d Scarf walk: the returned cell is
panchromatic.

(Discharge plan in S6 session memo §4: monotone-walk invariant +
no-revisit corollary + fuel-exhaustion impossibility.) -/
theorem scarfWalk_isPanchromatic (hm : 0 < m) (start : Fin m) (k : Fin 2)
    (h_start : ¬ IsPanchromatic1d c start) :
    IsPanchromatic1d c (scarfWalk c hm start k h_start) := by
  sorry

/-- **Constructive Sperner 1-d**: from a boundary door at
`(boundary_door.1, boundary_door.2)` (i.e. an `adj = none` site)
with a non-panchromatic source cell, the Scarf walk produces a
panchromatic cell of `intervalTriangulation m hm`. -/
theorem exists_panchromatic_constructive (hm : 0 < m)
    (boundary_door : Fin m × Fin 2)
    (h_door : ¬ IsPanchromatic1d c boundary_door.1) :
    ∃ i : Fin m, IsPanchromatic1d c i :=
  ⟨scarfWalk c hm boundary_door.1 boundary_door.2 h_door,
   scarfWalk_isPanchromatic c hm _ _ _⟩

end SpernerSimplicialInstanceOQ05Scarf1d
