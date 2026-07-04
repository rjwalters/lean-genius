/-
# Antipodal symmetry balances the boundary flow (abstract directed engine)

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam
from abstract door-counting").

## Where this sits — discharging the one named obligation of the directed engine

`SpernerTuckerDirectedInteriorSource.lean` factored "n ≥ 2 Tucker" down to a single
*named, local* algebraic hypothesis on the abstract directed door engine:
**boundary flow balance**

  `hbal : #{c | source c ∧ bdry c} = #{c | sink c ∧ bdry c}`,

after which `exists_interior_source_of_balanced_boundary` delivers an interior source
(a directed path root in the region interior — the classical Tucker/Borsuk–Ulam pivot)
from an out-heavy directed boundary seed by pure double counting.  Its docstring
justified `hbal` only *informally*: "the antipodal labelling routes as many
directed-path starts as ends through the boundary."

This file turns that English sentence into a machine-checked lemma.  The mechanism is
antipodal symmetry: an involution `σ : Cell → Cell` that **reverses directed flow** on
cells — `source c ↔ sink (σ c)` — and **preserves the boundary** — `bdry (σ c) ↔
bdry c` — restricts to a bijection between the boundary sources and the boundary
sinks, so the two counts coincide on the nose.  This is the directed, source/sink
analogue of `SpernerTuckerAntipodalParity.even_card_of_free_involution` (a free
involution forces *even* cardinality): there an involution pairs a set with *itself*;
here a flow-reversing involution pairs the *sources* with the *sinks*.

## Why this is progress, not a restatement

`exists_interior_source_of_balanced_boundary` takes `hbal` as a bare arithmetic
hypothesis.  Here we discharge it from a *structural* one — antipodal flow reversal —
that the concrete antipodally symmetric disc labelling supplies transparently (the
antipodal map on cells reverses every door's orientation and fixes no cell, hence
swaps sources with sinks and preserves the boundary).  The capstone
`exists_interior_source_of_antipodal_boundary` chains the two: from a flow-reversing
boundary-preserving involution and an out-heavy directed boundary seed it produces an
**interior** source directly, with the boundary-balance obligation now internalised as
a symmetry rather than a count.

Note the asymmetry is not lost: the involution reverses flow on *cells* (source ↔
sink), which is compatible with an out-heavy directed boundary on *doors* (the odd
`dirCount_odd` seed) — the two live on different sides of the incidence and the
hypotheses never force `#boundary-out = #boundary-in`.

## Honest status

Abstract directed infrastructure, **not** a proof of n ≥ 2 Tucker.  It converts the
lone remaining algebraic obligation of the directed interior-source engine into a
transparent antipodal-symmetry hypothesis, matching the informal justification every
prior session recorded.  The concrete construction of an antipodally symmetric door
complex on `∂◊^{n}` whose directed boundary carries the odd seed remains the open
geometric frontier.

Self-contained over arbitrary finite `Cell`, `Door` with a decidable boundary
predicate; imports the interior-source engine (hence Mathlib only).  0 sorries,
0 `axiom` declarations (`propext` / `Classical.choice` / `Quot.sound` only — no
`sorryAx`, no `Lean.ofReduceBool`, no `decide` / `native_decide`).
-/
import Proofs.SpernerTuckerDirectedInteriorSource

namespace SpernerTuckerDirectedBoundarySymmetry

open Finset
open SpernerTuckerDirectedIncidenceFlow
open SpernerTuckerDirectedInteriorSource

variable {Cell Door : Type*} [Fintype Cell] [Fintype Door]
variable (tail head : Cell → Door → Bool)
variable (bdry : Cell → Prop) [DecidablePred bdry]

/-! ## Antipodal flow reversal balances the boundary source/sink counts -/

/-- **Antipodal symmetry balances the boundary flow.**  If an involution
`σ : Cell → Cell` **reverses directed flow** on cells (`source c ↔ sink (σ c)`) and
**preserves the boundary predicate** (`bdry (σ c) ↔ bdry c`), then it restricts to a
bijection between the boundary source cells and the boundary sink cells, so the two
counts are equal:

  `#{c | source c ∧ bdry c} = #{c | sink c ∧ bdry c}`.

This discharges the `hbal` hypothesis of
`SpernerTuckerDirectedInteriorSource.exists_interior_source_of_balanced_boundary`
from a structural symmetry.  Directed source/sink analogue of
`SpernerTuckerAntipodalParity.even_card_of_free_involution`. -/
theorem card_boundary_source_eq_sink_of_antipodal
    (σ : Cell → Cell) (hinv : Function.Involutive σ)
    (hswap : ∀ c, IsSource tail head c ↔ IsSink tail head (σ c))
    (hbdry : ∀ c, bdry (σ c) ↔ bdry c) :
    (univ.filter (fun c => IsSource tail head c ∧ bdry c)).card
      = (univ.filter (fun c => IsSink tail head c ∧ bdry c)).card := by
  -- `σ` is its own inverse bijection between boundary sources and boundary sinks.
  apply Finset.card_nbij' σ σ
  · -- σ maps boundary sources to boundary sinks
    intro c hc
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact ⟨(hswap c).mp hc.1, (hbdry c).mpr hc.2⟩
  · -- σ maps boundary sinks to boundary sources
    intro c hc
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    refine ⟨?_, (hbdry c).mpr hc.2⟩
    rw [hswap (σ c), hinv c]; exact hc.1
  · intro c _; exact hinv c
  · intro c _; exact hinv c

/-! ## The capstone: an antipodal boundary forces an interior source -/

/-- **An antipodally symmetric, out-heavy directed boundary forces an INTERIOR
source.**  Combine the boundary-balance symmetry above with the interior-source engine:
given

* the Freund–Todd non-degeneracy `hdeg` (out/in-degree `≤ 1`),
* well-formedness `hwf` (every door interior / boundary-out / boundary-in),
* a flow-reversing, boundary-preserving involution `σ` (antipodal symmetry), and
* an out-heavy directed boundary `himb` (the odd `dirCount_odd` seed),

some **interior** cell (`¬ bdry`) is a source — a directed path root in the region
interior, exactly the object the classical Tucker/Borsuk–Ulam pivot produces.  This is
`exists_interior_source_of_balanced_boundary` with its algebraic balance obligation
replaced by the antipodal symmetry that the concrete disc labelling supplies. -/
theorem exists_interior_source_of_antipodal_boundary
    (σ : Cell → Cell) (hinv : Function.Involutive σ)
    (hswap : ∀ c, IsSource tail head c ↔ IsSink tail head (σ c))
    (hbdry : ∀ c, bdry (σ c) ↔ bdry c)
    (hdeg : ∀ c, outCount tail c ≤ 1 ∧ inCount head c ≤ 1)
    (hwf : ∀ d, IsInteriorDoor tail head d ∨ IsBoundaryOut tail head d
      ∨ IsBoundaryIn tail head d)
    (himb : (univ.filter (IsBoundaryIn tail head)).card
      < (univ.filter (IsBoundaryOut tail head)).card) :
    ∃ c, IsSource tail head c ∧ ¬ bdry c :=
  exists_interior_source_of_balanced_boundary tail head bdry hdeg hwf
    (card_boundary_source_eq_sink_of_antipodal tail head bdry σ hinv hswap hbdry) himb

#check @card_boundary_source_eq_sink_of_antipodal
#check @exists_interior_source_of_antipodal_boundary

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`, no `decide` / `native_decide`.
#print axioms card_boundary_source_eq_sink_of_antipodal
#print axioms exists_interior_source_of_antipodal_boundary

end SpernerTuckerDirectedBoundarySymmetry
