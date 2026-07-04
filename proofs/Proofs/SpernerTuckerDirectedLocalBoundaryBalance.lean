/-
# Boundary-LOCAL antipodal balance: flow reversal only where the labelling is antipodal

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam
from abstract door-counting").

## Where this sits — repairing an unsatisfiable hypothesis of the antipodal capstone

`SpernerTuckerDirectedBoundarySymmetry.lean` discharged the `hbal` obligation of the
directed interior-source engine
(`SpernerTuckerDirectedInteriorSource.exists_interior_source_of_balanced_boundary`)
from a *structural* antipodal symmetry: an involution `σ : Cell → Cell` that

* **reverses directed flow on cells** — `hswap : ∀ c, source c ↔ sink (σ c)`, and
* **preserves the boundary** — `hbdry : ∀ c, bdry (σ c) ↔ bdry c`,

restricts to a bijection between the boundary sources and the boundary sinks, so
`#{source ∧ bdry} = #{sink ∧ bdry}`, and then the capstone
`exists_interior_source_of_antipodal_boundary` produces an interior source from an
out-heavy directed boundary seed.

**But its `hswap` is stated for *every* cell — and that is exactly the fully antipodal
labelling every prior session flagged as a no-go.** A flow-reversing involution on
*all* cells corresponds to a labelling with `λ(-x) = -λ(x)` at every vertex, interior
included; iteration 13 (`SpernerTuckerAntipodalSymmetry.symmetric_graph_not_tucker_level`)
proved a fully antipodally-symmetric door graph can *never* carry the odd interior seed
— the oddness appears only once the interior symmetry is **broken**. Tucker's own
hypothesis makes only the **boundary** antipodal (`λ(-v) = -λ(v)` for `v ∈ ∂Bⁿ`); the
interior labelling is free and generically asymmetric. So the *geometric antipode* on a
real disc reverses directed flow **only on the boundary cells**, and the global `hswap`
of the existing capstone is *unsatisfiable* on any genuine Tucker instance: the existing
capstone can never fire concretely.

## What this file does

It weakens `hswap` to its **boundary-local** form — the reversal is required only where
the labelling is actually antipodal:

  `hswapB : ∀ c, bdry c → (source c ↔ sink (σ c))`.

The boundary-source ↔ boundary-sink bijection needs the reversal *only on boundary
cells* (both the well-definedness and the surjectivity witnesses stay inside the
boundary, since `σ` preserves it), so this weaker hypothesis already delivers the same
balance `#{source ∧ bdry} = #{sink ∧ bdry}`, and hence the same interior source.

This is exactly the hypothesis a concrete antipodally-symmetric disc supplies:
`σ` = the geometric antipode (an involution preserving `∂Bⁿ`), flow-reversing on the
antipodally-labelled boundary but making no demand on the free interior labels. The
existing global lemmas of `SpernerTuckerDirectedBoundarySymmetry` are recovered as
one-line corollaries (`card_boundary_source_eq_sink_of_antipodal`,
`exists_interior_source_of_antipodal_boundary`), so this file *strictly generalises*
that capstone.

## Honest status

Abstract directed infrastructure, **not** a proof of n ≥ 2 Tucker. It corrects the sole
antipodal-symmetry hypothesis of the directed interior-source pipeline from a globally
symmetric (hence Tucker-vacuous) form to the boundary-local one that a real disc
actually realises. The concrete construction of an antipodally symmetric door complex on
`∂◊ⁿ` whose directed boundary carries the odd seed — with the geometric antipode
discharging `hswapB`/`hbdry` and a fine enough triangulation carrying genuine interior
rooms — remains the open geometric frontier.

Self-contained over arbitrary finite `Cell`, `Door` with a decidable boundary
predicate; imports the boundary-symmetry capstone (hence Mathlib only). 0 sorries,
0 `axiom` declarations (`propext` / `Classical.choice` / `Quot.sound` only — no
`sorryAx`, no `Lean.ofReduceBool`, no `decide` / `native_decide`).
-/
import Proofs.SpernerTuckerDirectedBoundarySymmetry

namespace SpernerTuckerDirectedLocalBoundaryBalance

open Finset
open SpernerTuckerDirectedIncidenceFlow
open SpernerTuckerDirectedInteriorSource

variable {Cell Door : Type*} [Fintype Cell] [Fintype Door]
variable (tail head : Cell → Door → Bool)
variable (bdry : Cell → Prop) [DecidablePred bdry]

/-! ## Boundary-local antipodal balance -/

/-- **Boundary-local antipodal symmetry balances the boundary flow.**  If an involution
`σ : Cell → Cell` **preserves the boundary predicate** (`bdry (σ c) ↔ bdry c`) and
**reverses directed flow on the boundary cells** — `bdry c → (source c ↔ sink (σ c))` —
then it restricts to a bijection between the boundary source cells and the boundary sink
cells, so the two counts are equal:

  `#{c | source c ∧ bdry c} = #{c | sink c ∧ bdry c}`.

The reversal is demanded **only where the labelling is antipodal** (the boundary),
matching Tucker's actual hypothesis; the free interior labelling is untouched.  Both the
well-definedness and the surjectivity witnesses of the `σ`-bijection stay inside the
boundary because `σ` preserves it, so the guarded `hswapB` suffices.  This strictly
weakens `SpernerTuckerDirectedBoundarySymmetry.card_boundary_source_eq_sink_of_antipodal`,
whose global flow reversal is unsatisfiable on a genuine (boundary-only-antipodal)
Tucker instance. -/
theorem card_boundary_source_eq_sink_of_boundary_local
    (σ : Cell → Cell) (hinv : Function.Involutive σ)
    (hbdry : ∀ c, bdry (σ c) ↔ bdry c)
    (hswapB : ∀ c, bdry c → (IsSource tail head c ↔ IsSink tail head (σ c))) :
    (univ.filter (fun c => IsSource tail head c ∧ bdry c)).card
      = (univ.filter (fun c => IsSink tail head c ∧ bdry c)).card := by
  -- `σ` is its own inverse bijection between boundary sources and boundary sinks.
  apply Finset.card_nbij' σ σ
  · -- σ maps boundary sources to boundary sinks (uses `hswapB` at `c`, `bdry c` in hand)
    intro c hc
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact ⟨(hswapB c hc.2).mp hc.1, (hbdry c).mpr hc.2⟩
  · -- σ maps boundary sinks to boundary sources (uses `hswapB` at `σ c`, whose `bdry`
    -- is supplied by `hbdry`, then `hinv` to fold `σ (σ c) = c`)
    intro c hc
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    refine ⟨?_, (hbdry c).mpr hc.2⟩
    rw [hswapB (σ c) ((hbdry c).mpr hc.2), hinv c]; exact hc.1
  · intro c _; exact hinv c
  · intro c _; exact hinv c

/-! ## The capstone with the boundary-local hypothesis -/

/-- **A boundary-locally antipodal, out-heavy directed boundary forces an INTERIOR
source.**  The boundary-local refinement of
`SpernerTuckerDirectedBoundarySymmetry.exists_interior_source_of_antipodal_boundary`:
given

* the Freund–Todd non-degeneracy `hdeg` (out/in-degree `≤ 1`),
* well-formedness `hwf` (every door interior / boundary-out / boundary-in),
* a boundary-preserving involution `σ` reversing flow **only on the boundary**
  (`hswapB` — Tucker's antipodal boundary, interior labelling free), and
* an out-heavy directed boundary `himb` (the odd `dirCount_odd` seed),

some **interior** cell (`¬ bdry`) is a source.  Unlike the global capstone, the
hypotheses here are jointly satisfiable on a real disc: `σ` is the geometric antipode,
antipodal on `∂Bⁿ` while making no demand on the asymmetric interior that carries the
odd seed. -/
theorem exists_interior_source_of_boundary_local
    (σ : Cell → Cell) (hinv : Function.Involutive σ)
    (hbdry : ∀ c, bdry (σ c) ↔ bdry c)
    (hswapB : ∀ c, bdry c → (IsSource tail head c ↔ IsSink tail head (σ c)))
    (hdeg : ∀ c, outCount tail c ≤ 1 ∧ inCount head c ≤ 1)
    (hwf : ∀ d, IsInteriorDoor tail head d ∨ IsBoundaryOut tail head d
      ∨ IsBoundaryIn tail head d)
    (himb : (univ.filter (IsBoundaryIn tail head)).card
      < (univ.filter (IsBoundaryOut tail head)).card) :
    ∃ c, IsSource tail head c ∧ ¬ bdry c :=
  exists_interior_source_of_balanced_boundary tail head bdry hdeg hwf
    (card_boundary_source_eq_sink_of_boundary_local tail head bdry σ hinv hbdry hswapB)
    himb

/-! ## The global lemmas are one-line corollaries (strict generalisation check) -/

/-- The existing global balance lemma
`SpernerTuckerDirectedBoundarySymmetry.card_boundary_source_eq_sink_of_antipodal`
falls out by dropping the `bdry c →` guard, confirming this file strictly generalises
it. -/
theorem card_boundary_source_eq_sink_of_antipodal
    (σ : Cell → Cell) (hinv : Function.Involutive σ)
    (hswap : ∀ c, IsSource tail head c ↔ IsSink tail head (σ c))
    (hbdry : ∀ c, bdry (σ c) ↔ bdry c) :
    (univ.filter (fun c => IsSource tail head c ∧ bdry c)).card
      = (univ.filter (fun c => IsSink tail head c ∧ bdry c)).card :=
  card_boundary_source_eq_sink_of_boundary_local tail head bdry σ hinv hbdry
    (fun c _ => hswap c)

/-- The global capstone
`SpernerTuckerDirectedBoundarySymmetry.exists_interior_source_of_antipodal_boundary`
as a corollary of the boundary-local one. -/
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
  exists_interior_source_of_boundary_local tail head bdry σ hinv hbdry
    (fun c _ => hswap c) hdeg hwf himb

#check @card_boundary_source_eq_sink_of_boundary_local
#check @exists_interior_source_of_boundary_local

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`, no `decide` / `native_decide`.
#print axioms card_boundary_source_eq_sink_of_boundary_local
#print axioms exists_interior_source_of_boundary_local
#print axioms card_boundary_source_eq_sink_of_antipodal
#print axioms exists_interior_source_of_antipodal_boundary

end SpernerTuckerDirectedLocalBoundaryBalance
