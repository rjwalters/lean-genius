/-
# Interior source isolation from a flow-balanced boundary (abstract directed engine)

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam
from abstract door-counting").

## Where this sits — one honest step past `exists_source_of_more_boundary_out`

`SpernerTuckerDirectedIncidenceFlow.lean` builds the abstract *directed* door
engine and proves the master flow-conservation law

  `#sources − #sinks = #boundary-out − #boundary-in`

together with its existence corollary `exists_source_of_more_boundary_out`: an
out-heavy directed boundary (the odd `dirCount_odd` seed) forces a **source** cell,
a directed path start.  Its stated limitation — repeated verbatim in every prior
session's frontier note — is that the forced source lands among *all* cells; the
classical Tucker argument needs it isolated in the **interior**, and that "still
needs the boundary-cell accounting (the asymmetric Tucker labelling)."

This file supplies exactly that accounting as an abstract lemma, factoring the
remaining geometric obligation into one precise, checkable hypothesis.  Equip the
cells with a decidable **boundary predicate** `bdry : Cell → Prop` (the cells that
touch the region boundary).  Split each side of the master identity over `bdry`:

  `(#sourcesᴵ + #sources∂) − (#sinksᴵ + #sink∂) = #boundary-out − #boundary-in`.

If the **boundary cells are flow-balanced** — `#sources∂ = #sinks∂`, i.e. the
antipodal labelling routes as many directed-path starts as ends through the
boundary — the two boundary source/sink counts cancel and the interior inherits the
whole imbalance:

  `#sourcesᴵ − #sinksᴵ = #boundary-out − #boundary-in > 0`,

so an **interior** source is forced.  This is `exists_interior_source_of_balanced_boundary`.

## Why this is progress, not a restatement

`exists_source_of_more_boundary_out` reduces "n ≥ 2 Tucker" to producing an odd
directed boundary seed *and then locating the source geometrically by hand*.  This
file replaces the hand step with a single algebraic hypothesis — **boundary flow
balance** `#sources∂ = #sinks∂` — that the eventual concrete disc labelling can
discharge by a direct finite count (the boundary ring is a 1-dimensional directed
path graph whose starts and ends match).  The remaining frontier is now a *named,
local* obligation on the boundary ring rather than an unstructured "isolate the
source", and the interior-existence conclusion is delivered by pure double counting
(0 sorries, 0 `axiom` declarations, no `decide`/`native_decide`).

The companion `card_interior_source_ge_of_balanced_boundary` records the sharper
counting statement (`#sourcesᴵ ≥ 1 + #sinksᴵ`) the path-following can consume to
track *how many* interior path roots the seed guarantees.

Self-contained over arbitrary finite `Cell`, `Door` with a decidable boundary
predicate; imports the flow engine (hence Mathlib only).  `propext` /
`Classical.choice` / `Quot.sound` only — no `sorryAx`, no `Lean.ofReduceBool`,
no `decide`.
-/
import Proofs.SpernerTuckerDirectedIncidenceFlow

namespace SpernerTuckerDirectedInteriorSource

open Finset
open SpernerTuckerDirectedIncidenceFlow

variable {Cell Door : Type*} [Fintype Cell] [Fintype Door]
variable (tail head : Cell → Door → Bool)
variable (bdry : Cell → Prop) [DecidablePred bdry]

/-! ## Splitting the source and sink counts over the boundary predicate -/

/-- **Source split.**  Every source is a boundary source or an interior source,
exclusively, so the source count splits accordingly. -/
theorem card_source_split :
    (univ.filter (IsSource tail head)).card
      = (univ.filter (fun c => IsSource tail head c ∧ bdry c)).card
        + (univ.filter (fun c => IsSource tail head c ∧ ¬ bdry c)).card := by
  have e1 : (univ.filter (IsSource tail head)).filter bdry
      = univ.filter (fun c => IsSource tail head c ∧ bdry c) := by
    rw [Finset.filter_filter]
  have e2 : (univ.filter (IsSource tail head)).filter (fun c => ¬ bdry c)
      = univ.filter (fun c => IsSource tail head c ∧ ¬ bdry c) := by
    rw [Finset.filter_filter]
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := univ.filter (IsSource tail head)) (p := bdry)
  rw [e1, e2] at h
  omega

/-- **Sink split.**  The dual statement for sinks. -/
theorem card_sink_split :
    (univ.filter (IsSink tail head)).card
      = (univ.filter (fun c => IsSink tail head c ∧ bdry c)).card
        + (univ.filter (fun c => IsSink tail head c ∧ ¬ bdry c)).card := by
  have e1 : (univ.filter (IsSink tail head)).filter bdry
      = univ.filter (fun c => IsSink tail head c ∧ bdry c) := by
    rw [Finset.filter_filter]
  have e2 : (univ.filter (IsSink tail head)).filter (fun c => ¬ bdry c)
      = univ.filter (fun c => IsSink tail head c ∧ ¬ bdry c) := by
    rw [Finset.filter_filter]
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := univ.filter (IsSink tail head)) (p := bdry)
  rw [e1, e2] at h
  omega

/-! ## The interior source count from a balanced boundary -/

/-- **Interior source excess.**  In a well-formed directed door complex whose cells
have out- and in-degree `≤ 1`, if the boundary cells are flow-balanced
(`#sources∂ = #sinks∂`) then the interior source/sink imbalance equals the whole
boundary door imbalance:

  `#sourcesᴵ − #sinksᴵ = #boundary-out − #boundary-in`. -/
theorem interior_source_sub_sink_eq_boundary
    (hdeg : ∀ c, outCount tail c ≤ 1 ∧ inCount head c ≤ 1)
    (hwf : ∀ d, IsInteriorDoor tail head d ∨ IsBoundaryOut tail head d
      ∨ IsBoundaryIn tail head d)
    (hbal : (univ.filter (fun c => IsSource tail head c ∧ bdry c)).card
      = (univ.filter (fun c => IsSink tail head c ∧ bdry c)).card) :
    ((univ.filter (fun c => IsSource tail head c ∧ ¬ bdry c)).card : ℤ)
        - (univ.filter (fun c => IsSink tail head c ∧ ¬ bdry c)).card
      = (univ.filter (IsBoundaryOut tail head)).card
        - (univ.filter (IsBoundaryIn tail head)).card := by
  have hmaster := sources_sub_sinks_eq_boundary tail head hdeg hwf
  have hsrc := card_source_split tail head bdry
  have hsink := card_sink_split tail head bdry
  have hbalZ : ((univ.filter (fun c => IsSource tail head c ∧ bdry c)).card : ℤ)
      = (univ.filter (fun c => IsSink tail head c ∧ bdry c)).card := by
    exact_mod_cast hbal
  have hsrcZ : ((univ.filter (IsSource tail head)).card : ℤ)
      = (univ.filter (fun c => IsSource tail head c ∧ bdry c)).card
        + (univ.filter (fun c => IsSource tail head c ∧ ¬ bdry c)).card := by
    exact_mod_cast hsrc
  have hsinkZ : ((univ.filter (IsSink tail head)).card : ℤ)
      = (univ.filter (fun c => IsSink tail head c ∧ bdry c)).card
        + (univ.filter (fun c => IsSink tail head c ∧ ¬ bdry c)).card := by
    exact_mod_cast hsink
  rw [hsrcZ, hsinkZ] at hmaster
  linarith [hmaster, hbalZ]

/-- **Sharp interior source count.**  Under the same hypotheses plus an out-heavy
boundary (`#boundary-in < #boundary-out` — the odd `dirCount_odd` seed), the number
of interior sources strictly exceeds the number of interior sinks; in particular it
is at least `1`. -/
theorem card_interior_source_ge_of_balanced_boundary
    (hdeg : ∀ c, outCount tail c ≤ 1 ∧ inCount head c ≤ 1)
    (hwf : ∀ d, IsInteriorDoor tail head d ∨ IsBoundaryOut tail head d
      ∨ IsBoundaryIn tail head d)
    (hbal : (univ.filter (fun c => IsSource tail head c ∧ bdry c)).card
      = (univ.filter (fun c => IsSink tail head c ∧ bdry c)).card)
    (himb : (univ.filter (IsBoundaryIn tail head)).card
      < (univ.filter (IsBoundaryOut tail head)).card) :
    (univ.filter (fun c => IsSink tail head c ∧ ¬ bdry c)).card
      < (univ.filter (fun c => IsSource tail head c ∧ ¬ bdry c)).card := by
  have heq := interior_source_sub_sink_eq_boundary tail head bdry hdeg hwf hbal
  have hbpos : (0 : ℤ) < (univ.filter (IsBoundaryOut tail head)).card
      - (univ.filter (IsBoundaryIn tail head)).card :=
    sub_pos.mpr (by exact_mod_cast himb)
  rw [← heq] at hbpos
  exact_mod_cast sub_pos.mp hbpos

/-- **An out-heavy boundary with balanced boundary cells forces an INTERIOR source.**
The Tucker payoff of the abstract directed engine: with the boundary cells
flow-balanced (`#sources∂ = #sink∂`) and the directed boundary out-heavy (the odd
seed), some **interior** cell (`¬ bdry`) is a source — a directed path root in the
region interior, exactly the object the classical Tucker/Borsuk–Ulam pivot produces.

This replaces the informal "isolate the source in the interior" step with the single
algebraic obligation `hbal`, which the concrete disc labelling can discharge by a
direct count on the 1-dimensional boundary ring. -/
theorem exists_interior_source_of_balanced_boundary
    (hdeg : ∀ c, outCount tail c ≤ 1 ∧ inCount head c ≤ 1)
    (hwf : ∀ d, IsInteriorDoor tail head d ∨ IsBoundaryOut tail head d
      ∨ IsBoundaryIn tail head d)
    (hbal : (univ.filter (fun c => IsSource tail head c ∧ bdry c)).card
      = (univ.filter (fun c => IsSink tail head c ∧ bdry c)).card)
    (himb : (univ.filter (IsBoundaryIn tail head)).card
      < (univ.filter (IsBoundaryOut tail head)).card) :
    ∃ c, IsSource tail head c ∧ ¬ bdry c := by
  have hlt := card_interior_source_ge_of_balanced_boundary tail head bdry hdeg hwf hbal himb
  have hpos : 0 < (univ.filter (fun c => IsSource tail head c ∧ ¬ bdry c)).card :=
    lt_of_le_of_lt (Nat.zero_le _) hlt
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
  exact ⟨c, (Finset.mem_filter.mp hc).2⟩

#check @interior_source_sub_sink_eq_boundary
#check @exists_interior_source_of_balanced_boundary

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`, no `decide` / `native_decide`.
#print axioms card_source_split
#print axioms interior_source_sub_sink_eq_boundary
#print axioms card_interior_source_ge_of_balanced_boundary
#print axioms exists_interior_source_of_balanced_boundary

end SpernerTuckerDirectedInteriorSource
