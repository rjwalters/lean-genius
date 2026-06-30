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
* `scarfWalk_isPanchromatic` — soundness (the rightward walk
  returns a panchromatic cell), proved from the start-relative
  reachability hypothesis `c start ≠ c m`. See the soundness note
  below for why the unconditional / endpoint-only statements are
  false for a general start.
* `exists_panchromatic_constructive` — the constructive Sperner
  1-d witness extracted from the walk + soundness, under the
  endpoint-parity hypothesis `c 0 ≠ c m`.

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

/-! ## Soundness

The soundness theorem `scarfWalk_isPanchromatic` and the
constructive existence corollary `exists_panchromatic_constructive`
are proved further down (after the structural reduction lemmas they
depend on).

**S8 correction (this session, researcher-2).** Two earlier sessions
established that the *unconditional* soundness statement (over an
arbitrary entry face `k`) is false:

* S7 (researcher-1, 2026-06-01) found the **constant-colouring**
  counterexample (`m = 3`, `c ≡ 0`): no cell is panchromatic, so the
  walk can only terminate on a non-panchromatic cell.
* S8 PREP (researcher-1, 2026-06-04) proposed repairing this with the
  endpoint-parity hypothesis `c 0 ≠ c m`.

That proposal is **still insufficient for a general start/direction**:
take `m = 5`, `c = (1, 0, 0, 0, 0, 0)`, `start = 2`, entry face `1`
(rightward). Then `c 0 = 1 ≠ 0 = c 5`, so the parity hypothesis holds,
yet the only colour switch is the edge `[0,1]` — which lies *behind*
the rightward walk. The walk runs `2 → 3 → 4` and stops at the
non-panchromatic right boundary cell `4`. Soundness fails.

The walk is monotone in the cell index with direction fixed by the
entry face, so the correct hypothesis is **start-relative**: a
rightward walk (entry face `1`) from cell `start` lands on a
panchromatic cell iff a colour switch lies in `{start, …, m}`, for
which `c start ≠ c m` is sufficient. That is the hypothesis used
below. The boundary-door existence corollary then instantiates it at
`start = 0`, where `c 0 ≠ c m` is exactly the classical 1-d Sperner
endpoint condition. -/

/-! ## S7 ACT — Structural Reduction Lemmas

Three reduction-by-definition lemmas that the S8 discharge of
`scarfWalk_isPanchromatic` (now complete) relied on. Plus a
kernel-level `decide` verification on a concrete 3-cell instance.

Each is a syntactic fact about `scarfWalk` / `scarfWalkAux` that the
discharge unfolds over. Recording them as named lemmas avoids
re-proving the same `rfl` / `split_ifs` micro-steps inside the larger
discharge. -/

/-- Unfolding lemma: `scarfWalk` is `scarfWalkAux` at fuel `m`. -/
theorem scarfWalk_eq_scarfWalkAux (hm : 0 < m) (start : Fin m) (k : Fin 2)
    (h_start : ¬ IsPanchromatic1d c start) :
    scarfWalk c hm start k h_start = scarfWalkAux c hm start k m := rfl

/-- Fuel base case: `scarfWalkAux` at zero fuel returns `start`
unchanged (regardless of the entry face `k`). -/
theorem scarfWalkAux_zero_fuel (hm : 0 < m) (start : Fin m) (k : Fin 2) :
    scarfWalkAux c hm start k 0 = start := rfl

/-- Panchromatic-start short-circuit: if `start` is already
panchromatic, `scarfWalkAux` at positive fuel returns it immediately
without consulting `step`.

This lemma is what lets the discharge ignore the panchromatic
branch of `scarfWalkAux` after the initial entry: the walk only
makes a real `step` call when `start` is non-panchromatic. -/
theorem scarfWalkAux_of_panchromatic_start (hm : 0 < m) (start : Fin m)
    (k : Fin 2) (n : ℕ) (h : IsPanchromatic1d c start) :
    scarfWalkAux c hm start k (n + 1) = start := by
  unfold scarfWalkAux
  simp [h]

/-- Non-panchromatic unfolding: at positive fuel and a
non-panchromatic current cell, `scarfWalkAux` reduces to a `step`
followed by the recursive call on the remaining fuel. -/
theorem scarfWalkAux_step (hm : 0 < m) (s : Fin m) (k : Fin 2) (n : ℕ)
    (h : ¬ IsPanchromatic1d c s) :
    scarfWalkAux c hm s k (n + 1)
      = match step c hm s k h with
        | Sum.inl w => w
        | Sum.inr (next, k') => scarfWalkAux c hm next k' n := by
  conv_lhs => unfold scarfWalkAux
  rw [dif_neg h]

/-- One **rightward** step (entry face `1`) of the Scarf walk. From a
non-panchromatic cell `s` with `s + 1 < m`, the walk moves to cell
`s + 1` (again entered through face `1`): it returns `s + 1` if that
cell is panchromatic, otherwise it recurses there. -/
theorem scarfWalkAux_right_succ (hm : 0 < m) (s : Fin m) (n : ℕ)
    (hps : ¬ IsPanchromatic1d c s) (hlt : s.val + 1 < m) :
    scarfWalkAux c hm s 1 (n + 1)
      = if IsPanchromatic1d c (⟨s.val + 1, hlt⟩ : Fin m)
        then (⟨s.val + 1, hlt⟩ : Fin m)
        else scarfWalkAux c hm (⟨s.val + 1, hlt⟩ : Fin m) 1 n := by
  rw [scarfWalkAux_step c hm s 1 n hps]
  have hst : step c hm s 1 hps
      = if IsPanchromatic1d c (⟨s.val + 1, hlt⟩ : Fin m)
        then Sum.inl (⟨s.val + 1, hlt⟩ : Fin m)
        else Sum.inr ((⟨s.val + 1, hlt⟩ : Fin m), (⟨1, by omega⟩ : Fin 2)) := by
    show (match (intervalTriangulation m hm).adj s ⟨0, by omega⟩ with
          | none => Sum.inl s
          | some (i', k'') =>
              if IsPanchromatic1d c i' then Sum.inl i' else Sum.inr (i', k''))
        = _
    rw [intervalTriangulation_adj_zero hm s hlt]
  rw [hst]
  by_cases hp1 : IsPanchromatic1d c (⟨s.val + 1, hlt⟩ : Fin m)
  · rw [if_pos hp1, if_pos hp1]
  · rw [if_neg hp1, if_neg hp1]; rfl

/-- Soundness, by induction on the fuel: a rightward walk (entry
face `1`) from any cell `s` whose left-vertex colour differs from the
right-endpoint colour `c m` lands on a panchromatic cell, provided
the fuel `n` is at least the remaining distance `m - s`. -/
theorem scarfWalkAux_right_isPanchromatic (hm : 0 < m) :
    ∀ (n : ℕ) (s : Fin m), m - s.val ≤ n → c s.val ≠ c m →
      IsPanchromatic1d c (scarfWalkAux c hm s 1 n) := by
  intro n
  induction n with
  | zero =>
      intro s hle _
      exact absurd hle (by have := s.isLt; omega)
  | succ n ih =>
      intro s hle hreach
      by_cases hps : IsPanchromatic1d c s
      · rw [scarfWalkAux_of_panchromatic_start c hm s 1 n hps]; exact hps
      · have hcs : c s.val = c (s.val + 1) := by
          unfold IsPanchromatic1d at hps; exact not_not.mp hps
        have hlt : s.val + 1 < m := by
          rcases Nat.lt_or_ge (s.val + 1) m with h | h
          · exact h
          · have heq : s.val + 1 = m := by have := s.isLt; omega
            exact absurd (hcs.trans (congrArg c heq)) hreach
        rw [scarfWalkAux_right_succ c hm s n hps hlt]
        by_cases hp1 : IsPanchromatic1d c (⟨s.val + 1, hlt⟩ : Fin m)
        · rw [if_pos hp1]; exact hp1
        · rw [if_neg hp1]
          refine ih ⟨s.val + 1, hlt⟩ ?_ ?_
          · show m - (s.val + 1) ≤ n; omega
          · show c (s.val + 1) ≠ c m; rw [← hcs]; exact hreach

/-- **Soundness** of the rightward 1-d Scarf walk (entry face `1`):
the returned cell is panchromatic, given the start-relative
reachability hypothesis `c start ≠ c m` (a colour switch lies weakly
to the right of `start`). See the module note above for why the
unconditional and endpoint-only (`c 0 ≠ c m`) statements are false
for a general start. -/
theorem scarfWalk_isPanchromatic (hm : 0 < m) (start : Fin m)
    (h_reach : c start.val ≠ c m)
    (h_start : ¬ IsPanchromatic1d c start) :
    IsPanchromatic1d c (scarfWalk c hm start 1 h_start) := by
  rw [scarfWalk_eq_scarfWalkAux]
  exact scarfWalkAux_right_isPanchromatic c hm m start
    (by have := start.isLt; omega) h_reach

/-- **Discrete intermediate-value theorem** (classical 1-d Sperner):
if the two endpoint colours of `{0, …, m}` differ, some cell of
`intervalTriangulation m hm` is panchromatic. Pure colour-combinatorics,
independent of the walk. -/
theorem discrete_ivt_panchromatic_cell (_hm : 0 < m) (h_parity : c 0 ≠ c m) :
    ∃ i : Fin m, IsPanchromatic1d c i := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ j, j ≤ m → c 0 = c j := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ihj =>
        intro hj
        have hjm : j < m := by omega
        have hpan := hcon ⟨j, hjm⟩
        simp only [IsPanchromatic1d, not_not] at hpan
        rw [ihj (by omega)]; exact hpan
  exact h_parity (key m le_rfl)

/-- **Constructive Sperner 1-d**: under the endpoint-parity
hypothesis `c 0 ≠ c m`, the rightward Scarf walk started at the left
boundary cell `0` produces a panchromatic cell of
`intervalTriangulation m hm`. -/
theorem exists_panchromatic_constructive (hm : 0 < m) (h_parity : c 0 ≠ c m) :
    ∃ i : Fin m, IsPanchromatic1d c i := by
  by_cases h0 : IsPanchromatic1d c (⟨0, hm⟩ : Fin m)
  · exact ⟨_, h0⟩
  · exact ⟨scarfWalk c hm ⟨0, hm⟩ 1 h0,
      scarfWalk_isPanchromatic c hm ⟨0, hm⟩ (by simpa using h_parity) h0⟩

/-- **Smoke test (m = 3 / colouring 0,0,1,1)**: starting at the
left boundary door `(0, 1)` of `intervalTriangulation 3` with the
colouring `c(n) = if n ≤ 1 then 0 else 1`, the Scarf walk lands
on a panchromatic cell. Kernel-level proof by `decide`.

This is the strongest possible *concrete* soundness statement: a
kernel-checked equation that `scarfWalk` returns a panchromatic
cell on this specific instance. Sister to the `findPanchromaticBrute`
demo in `SpernerSimplicialInstanceOQ05.lean` (the C1 brute-force
finder). -/
example :
    let c : ℕ → Fin 2 := fun n => if n ≤ 1 then 0 else 1
    let start : Fin 3 := ⟨0, by decide⟩
    let k : Fin 2 := ⟨1, by decide⟩
    have h_start : ¬ IsPanchromatic1d c start := by decide
    IsPanchromatic1d c (scarfWalk c (by decide : 0 < 3) start k h_start) := by
  decide

end SpernerSimplicialInstanceOQ05Scarf1d
