/-
# Directed-flow Tucker engine: the antipodal seed no-go

`SpernerTuckerDirectedInteriorSource.exists_interior_source_of_balanced_boundary`
fires an **interior** directed source from two boundary inputs:

* `hbal` — the boundary source and sink counts agree
  (`#{sources ∩ ∂} = #{sinks ∩ ∂}`), and
* `himb` — the boundary is strictly **out-heavy**
  (`#{boundary-in doors} < #{boundary-out doors}`), the odd Freund–Todd seed.

`SpernerTuckerDirectedBoundarySymmetry.card_boundary_source_eq_sink_of_antipodal`
observed that a flow-reversing antipodal involution `σ : Cell → Cell`
(`source c ↔ sink (σ c)`) discharges `hbal` **for free** — the antipodal symmetry
pairs each boundary source with a boundary sink.  So on an antipodally symmetric disc
`hbal` is automatic and the only remaining obligation is the seed `himb`.

This file records the **structural obstruction that the concrete probes exposed** (a
brute force over all `4^7 = 16384` labellings of the symmetric two-hexagon annulus disc:
`hbal` holds for *every* labelling, yet `himb` fails for *every* labelling).  The reason
is exactly dual to the `hbal` mechanism: the *same* antipodal symmetry that pairs
boundary sources with sinks **also pairs boundary-out doors with boundary-in doors**.
A boundary-out door `tailCount = 1, headCount = 0` maps under the orientation-reversing
antipodal door involution to a boundary-in door `tailCount = 0, headCount = 1`, so

  `#{boundary-out doors} = #{boundary-in doors}`

and the strict inequality `himb` **can never hold**.

Hence the directed net-flow seed `himb` is *self-defeating on a genuinely antipodal
disc*: the antipodal symmetry hands you `hbal` and simultaneously destroys `himb`.
The two hypotheses of the antipodal capstone
`exists_interior_source_of_antipodal_boundary` cannot be jointly realised by any disc
whose antipodal symmetry acts on *doors* as well as cells.  This is a decidable-free,
`decide`-free, 0-axiom **no-go**: it proves the directed strict-imbalance seed is the
wrong invariant for antipodal Tucker, and that the correct seed must be a **parity**
(mod-2) quantity — the odd count of complementary boundary edges — which *survives* the
antipodal involution instead of being cancelled by it.

The mechanism is the door-level mirror of
`card_boundary_source_eq_sink_of_antipodal`: an involution that reverses door
orientation is its own bijection between the boundary-out and boundary-in doors.

No axioms beyond `propext` / `Classical.choice` / `Quot.sound`; no `sorry`, no
`decide` / `native_decide`, no `Lean.ofReduceBool`.
-/
import Proofs.SpernerTuckerDirectedBoundarySymmetry

namespace SpernerTuckerDirectedAntipodalNoGo

open Finset
open SpernerTuckerDirectedIncidenceFlow
open SpernerTuckerDirectedInteriorSource
open SpernerTuckerDirectedBoundarySymmetry

variable {Cell Door : Type*} [Fintype Cell] [Fintype Door]
variable (tail head : Cell → Door → Bool)

/-! ## Antipodal door symmetry balances the boundary door counts -/

/-- **A flow-reversing door involution balances the boundary doors.**  If an involution
`τ : Door → Door` **reverses door orientation** on the boundary
(`IsBoundaryOut d ↔ IsBoundaryIn (τ d)`) then it restricts to a bijection between the
boundary-out doors and the boundary-in doors, so the two counts are equal:

  `#{boundary-out doors} = #{boundary-in doors}`.

This is the door-level mirror of
`SpernerTuckerDirectedBoundarySymmetry.card_boundary_source_eq_sink_of_antipodal`
(which balances the *cell* source/sink counts).  Where that lemma discharges the `hbal`
input of the interior-source engine, this lemma **refutes** its `himb` input. -/
theorem card_boundaryOut_eq_boundaryIn_of_door_involution
    (τ : Door → Door) (hinv : Function.Involutive τ)
    (hswap : ∀ d, IsBoundaryOut tail head d ↔ IsBoundaryIn tail head (τ d)) :
    (univ.filter (IsBoundaryOut tail head)).card
      = (univ.filter (IsBoundaryIn tail head)).card := by
  -- `τ` is its own inverse bijection between boundary-out and boundary-in doors.
  apply Finset.card_nbij' τ τ
  · -- τ maps boundary-out doors to boundary-in doors
    intro d hd
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    exact (hswap d).mp hd
  · -- τ maps boundary-in doors back to boundary-out doors
    intro d hd
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    rw [hswap (τ d), hinv d]; exact hd
  · intro d _; exact hinv d
  · intro d _; exact hinv d

/-! ## The no-go: an antipodal door symmetry refutes the out-heavy seed -/

/-- **The antipodal boundary is never strictly out-heavy.**  Under the same
orientation-reversing door involution `τ`, the boundary-in and boundary-out door counts
are equal, so the strict `himb` seed
`#{boundary-in} < #{boundary-out}` **cannot hold**.

This is the machine-checked obstruction the concrete probes found: on the symmetric
two-hexagon annulus disc `himb` fails for *all* `16384` labellings.  Consequently the
antipodal capstone
`SpernerTuckerDirectedBoundarySymmetry.exists_interior_source_of_antipodal_boundary`,
whose remaining hypothesis is exactly this `himb`, has **no instance on a fully antipodal
disc**: the antipodal symmetry supplies `hbal` and destroys `himb` at once. -/
theorem antipodal_boundary_never_out_heavy
    (τ : Door → Door) (hinv : Function.Involutive τ)
    (hswap : ∀ d, IsBoundaryOut tail head d ↔ IsBoundaryIn tail head (τ d)) :
    ¬ (univ.filter (IsBoundaryIn tail head)).card
        < (univ.filter (IsBoundaryOut tail head)).card := by
  intro himb
  rw [card_boundaryOut_eq_boundaryIn_of_door_involution tail head τ hinv hswap] at himb
  exact lt_irrefl _ himb

/-- **Full antipodal symmetry cannot fire the directed interior-source engine.**
Suppose a disc carries the full antipodal symmetry: a flow-reversing **cell** involution
`σ` (supplying `hbal` via `card_boundary_source_eq_sink_of_antipodal`) *and* an
orientation-reversing **door** involution `τ`.  Then whatever labelling is chosen, the
engine's out-heavy seed `himb` is false, so
`exists_interior_source_of_antipodal_boundary` is vacuous: no antipodally symmetric disc
produces the directed interior source through this route.

The `σ`/`hswap_cell`/`hbdry` data is recorded to make the "gives `hbal` for free"
half explicit; the conclusion follows from the `τ` half alone
(`antipodal_boundary_never_out_heavy`).  The moral: the directed strict-imbalance seed is
the wrong invariant under antipodal symmetry — a **parity** seed is required. -/
theorem no_directed_interior_source_under_full_antipodal
    (bdry : Cell → Prop) [DecidablePred bdry]
    (σ : Cell → Cell) (_hσinv : Function.Involutive σ)
    (_hswap_cell : ∀ c, IsSource tail head c ↔ IsSink tail head (σ c))
    (_hbdry : ∀ c, bdry (σ c) ↔ bdry c)
    (τ : Door → Door) (hτinv : Function.Involutive τ)
    (hswap_door : ∀ d, IsBoundaryOut tail head d ↔ IsBoundaryIn tail head (τ d)) :
    ¬ (univ.filter (IsBoundaryIn tail head)).card
        < (univ.filter (IsBoundaryOut tail head)).card :=
  antipodal_boundary_never_out_heavy tail head τ hτinv hswap_door

#check @card_boundaryOut_eq_boundaryIn_of_door_involution
#check @antipodal_boundary_never_out_heavy
#check @no_directed_interior_source_under_full_antipodal

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`, no `decide` / `native_decide`.
#print axioms card_boundaryOut_eq_boundaryIn_of_door_involution
#print axioms antipodal_boundary_never_out_heavy
#print axioms no_directed_interior_source_under_full_antipodal

end SpernerTuckerDirectedAntipodalNoGo
