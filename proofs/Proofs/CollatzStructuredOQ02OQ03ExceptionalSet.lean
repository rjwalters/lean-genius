import Mathlib
import Proofs.CollatzStructuredOQ02OQ03ConstBound

/-!
# Collatz OQ-02-03 — Part XIV: the exceptional (non-dropping) set is explicitly finite

Part XIII (`Proofs.CollatzStructuredOQ02OQ03ConstBound`) proved the uniform *eventual*-drop
theorem `affValid_attainsBelow_of_large`: for a non-empty valid certificate `v` of the class
`c·m + d` whose leading coefficient satisfies `A < c`, every member with

    `3 ^ (#odd steps) · (d + 1) ≤ (c − A) · m`

attains a value below itself.  The hypothesis is a *division* threshold on `m`.

This file packages that into the clean, division-free form and — the new content —
**bounds the exceptional set explicitly**.  Writing `B = 3 ^ (#odd steps) · (d + 1)` for the
constant-term bound of the window:

* `affValid_attainsBelow_of_ge` — the division-free threshold: since `A < c` forces `c − A ≥ 1`,
  every `m ≥ B` already satisfies `B ≤ (c − A)·m`, so *every* `m ≥ B` drops.  No division, no
  `D < r` boundary caveat.
* `affValid_not_attainsBelow_lt` — the contrapositive: if a member `c·m + d` does **not** drop
  within this window (`¬ AttainsBelow`), then `m < B`.  The non-dropping members are confined to
  the initial segment `m ∈ [0, B)`.
* `affValid_exceptional_subset_range` — the exceptional set, intersected with any initial segment
  `Finset.range N`, is contained in `Finset.range B`; hence
* `affValid_exceptional_card_le` — **at most `B = 3 ^ (#odd) · (d + 1)` members of the class fail
  to drop within the window**, for every `N`.  An explicit, `N`-uniform finite bound on the
  exceptional set — the honest "cofinitely many members drop, and here is how many can fail"
  reading of the determined-drop criterion `A < c`.

This directly answers the standing next-step "pin the exact finite set of non-dropping members per
determined-drop class": the set is a subset of `[0, 3^a·(d+1))`, of size at most `3^a·(d+1)`.

Self-contained on top of Part XIII: imports only `Mathlib` and
`Proofs.CollatzStructuredOQ02OQ03ConstBound` (a light companion that builds green, unlike the
mother module which sits at the Lean kernel-memory ceiling).  Axiom-free; no `decide`.
-/

namespace CollatzStructuredOQ02OQ03ConstBound

open Finset
open scoped Classical

/-- **Division-free eventual-drop threshold.**  Because `A < c` forces `c − A ≥ 1`, the Part XIII
threshold `B ≤ (c − A)·m` is implied by the simpler `m ≥ B` with `B = 3 ^ (#odd) · (d + 1)`.  So
for a non-empty valid certificate with `A < c`, *every* class member `c·m + d` with
`m ≥ 3 ^ (v.count true) · (d + 1)` attains a value below itself. -/
theorem affValid_attainsBelow_of_ge {v : List Bool} {c d : ℕ}
    (hv : AffValid v c d) (hlen : 0 < v.length)
    (hlt : (affOrbit v (c, d)).1 < c)
    {m : ℕ} (hm : 3 ^ v.count true * (d + 1) ≤ m) :
    AttainsBelow (c * m + d) := by
  refine affValid_attainsBelow_of_large hv hlen hlt ?_
  -- `c - A ≥ 1`, so `(c - A) * m ≥ m ≥ B`.
  have hge : m ≤ (c - (affOrbit v (c, d)).1) * m := by
    have h1 : 1 ≤ c - (affOrbit v (c, d)).1 := by omega
    calc m = 1 * m := (one_mul m).symm
      _ ≤ (c - (affOrbit v (c, d)).1) * m := by gcongr
  exact le_trans hm hge

/-- **The non-dropping members lie below the threshold.**  Contrapositive of
`affValid_attainsBelow_of_ge`: if the class member `c·m + d` does not attain a value below itself
within this window, then `m < 3 ^ (v.count true) · (d + 1)`.  The exceptional (non-dropping)
members are confined to the initial segment `m ∈ [0, B)`. -/
theorem affValid_not_attainsBelow_lt {v : List Bool} {c d : ℕ}
    (hv : AffValid v c d) (hlen : 0 < v.length)
    (hlt : (affOrbit v (c, d)).1 < c)
    {m : ℕ} (hm : ¬ AttainsBelow (c * m + d)) :
    m < 3 ^ v.count true * (d + 1) := by
  by_contra hle
  push_neg at hle
  exact hm (affValid_attainsBelow_of_ge hv hlen hlt hle)

/-- **The exceptional set is confined to `range B`.**  For any initial segment `range N`, the set
of `m < N` whose class member does not drop within the window is a subset of
`range (3 ^ (v.count true) · (d + 1))`.  A `Finset` form of `affValid_not_attainsBelow_lt`. -/
theorem affValid_exceptional_subset_range {v : List Bool} {c d : ℕ}
    (hv : AffValid v c d) (hlen : 0 < v.length)
    (hlt : (affOrbit v (c, d)).1 < c) (N : ℕ) :
    ((range N).filter (fun m => ¬ AttainsBelow (c * m + d)))
      ⊆ range (3 ^ v.count true * (d + 1)) := by
  intro m hm
  rw [mem_filter] at hm
  rw [mem_range]
  exact affValid_not_attainsBelow_lt hv hlen hlt hm.2

/-- **Explicit finite bound on the exceptional set.**  For every `N`, at most
`3 ^ (v.count true) · (d + 1)` members `c·m + d` with `m < N` fail to drop within the window.
The bound is uniform in `N` — the exceptional set never exceeds `B = 3^a·(d+1)` however far out one
looks.  The quantitative form of "the determined-drop criterion `A < c` forces the drop for
cofinitely many members of the class". -/
theorem affValid_exceptional_card_le {v : List Bool} {c d : ℕ}
    (hv : AffValid v c d) (hlen : 0 < v.length)
    (hlt : (affOrbit v (c, d)).1 < c) (N : ℕ) :
    ((range N).filter (fun m => ¬ AttainsBelow (c * m + d))).card
      ≤ 3 ^ v.count true * (d + 1) := by
  calc ((range N).filter (fun m => ¬ AttainsBelow (c * m + d))).card
      ≤ (range (3 ^ v.count true * (d + 1))).card :=
        card_le_card (affValid_exceptional_subset_range hv hlen hlt N)
    _ = 3 ^ v.count true * (d + 1) := card_range _

end CollatzStructuredOQ02OQ03ConstBound
