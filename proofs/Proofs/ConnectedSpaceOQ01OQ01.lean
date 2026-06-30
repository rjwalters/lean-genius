import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Tactic

/-!
# Connected space OQ-01-OQ-01: closure behaviour of path-connectedness

The parent entry (`ConnectedSpaceOQ01`) shows that **connectedness is stable under closure**:
the closure of a (pre)connected set is again (pre)connected, and a *dense connected* subset
makes the whole space connected. Its first open question asks for the analogous study of
**path-connectedness and local connectedness**, "where closure behaves differently".

This file answers that question. The phenomenon splits cleanly into a negative half and a
positive half.

## The negative half — only connectedness survives

Closure is **not** stable for path-connectedness: the topologist's sine curve
`{(x, sin (1/x)) : x > 0}` is path-connected, but its closure (which adds the segment
`{0} × [-1,1]`) is connected yet *not* path-connected. So the parent's three theorems all
weaken by exactly one notch when the hypothesis is upgraded from "connected" to
"path-connected": the conclusion stays merely *connected*.

* `isConnected_closure_of_isPathConnected` — the closure of a path-connected set is connected.
* `isConnected_of_isPathConnected_subset_closure` — the "bark and tree" salvage: any set
  wedged between a path-connected set and its closure is connected.
* `connectedSpace_of_dense_isPathConnected` — a dense path-connected subset makes the space
  connected (note: `ConnectedSpace`, **not** `PathConnectedSpace`).

## The positive half — local path-connectedness restores rigidity

In a `LocPathConnectedSpace`, path components are **clopen** (Mathlib:
`IsClopen.pathComponent`). Closedness is exactly the missing ingredient: it forces a path
component to equal its own closure, so on path components closure *does* preserve
path-connectedness. We also record the open-set criterion and identify the closure of a path
component with the connected component.

* `closure_pathComponent` — in a locally path-connected space `closure (pathComponent x) =
  pathComponent x`.
* `isPathConnected_closure_pathComponent` — hence that closure is path-connected.
* `closure_pathComponent_eq_connectedComponent` — and it equals the connected component.
* `isPathConnected_of_isConnected_of_isOpen` — a connected open set is path-connected.
* `pathConnectedSpace_of_connected` — a connected, locally path-connected space is
  path-connected.

All results are 0 axioms, no `sorry`, no `native_decide`. The Mathlib-level facts used are
`IsPathConnected.isConnected`, `IsConnected.closure`/`IsConnected.subset_closure`,
`IsClosed.pathComponent`, `pathComponent_eq_connectedComponent`, and
`IsOpen.isConnected_iff_isPathConnected`; the gallery contribution is assembling the precise
negative/positive dichotomy that the parent's open question asks for.
-/

namespace ConnectedSpaceOQ01OQ01

open Set Topology

variable {α : Type*} [TopologicalSpace α]

/-! ## The negative half: closure of a path-connected set is only connected -/

/-- **The closure of a path-connected set is connected** (but, in general, not
    path-connected — see the topologist's sine curve discussed in the module docstring).
    Path-connectedness implies connectedness, and connectedness *is* closure-stable. -/
theorem isConnected_closure_of_isPathConnected {s : Set α} (h : IsPathConnected s) :
    IsConnected (closure s) :=
  h.isConnected.closure

/-- **"Bark and tree", path version.** Any set `t` sandwiched between a path-connected set
    `s` and its closure is connected. This is the honest path-connected analogue of the
    parent's `connected_of_subset_closure`: the conclusion is connectedness, since
    path-connectedness genuinely fails to survive (the closure may add points reachable only
    through limits, not through paths). -/
theorem isConnected_of_isPathConnected_subset_closure {s t : Set α} (h : IsPathConnected s)
    (hst : s ⊆ t) (hts : t ⊆ closure s) : IsConnected t :=
  h.isConnected.subset_closure hst hts

/-- **A dense path-connected subset makes the whole space connected.** The path analogue of
    the parent's `connectedSpace_of_dense_connected`. Crucially the conclusion is
    `ConnectedSpace`, **not** `PathConnectedSpace`: density plus path-connectedness of a
    subset is not enough to path-connect the ambient space (again the sine curve sitting
    densely inside its closure). -/
theorem connectedSpace_of_dense_isPathConnected {s : Set α} (hc : IsPathConnected s)
    (hd : Dense s) : ConnectedSpace α := by
  rw [connectedSpace_iff_univ, ← hd.closure_eq]
  exact hc.isConnected.closure

/-! ## The positive half: local path-connectedness restores closure-stability -/

variable [LocPathConnectedSpace α]

/-- **In a locally path-connected space, each path component equals its own closure.**
    Path components are clopen here (`IsClopen.pathComponent`); being closed, a path component
    is its own closure. This is exactly the situation in which closure preserves
    path-connectedness. -/
theorem closure_pathComponent (x : α) : closure (pathComponent x) = pathComponent x :=
  (IsClosed.pathComponent x).closure_eq

/-- **The closure of a path component is path-connected**, because it *is* the path component
    (locally path-connected setting). Contrast with the general failure recorded above. -/
theorem isPathConnected_closure_pathComponent (x : α) :
    IsPathConnected (closure (pathComponent x)) := by
  rw [closure_pathComponent]
  exact isPathConnected_pathComponent

/-- In a locally path-connected space the closure of a path component is the connected
    component: closure leaves the (clopen) path component fixed, and path components coincide
    with connected components. -/
theorem closure_pathComponent_eq_connectedComponent (x : α) :
    closure (pathComponent x) = connectedComponent x := by
  rw [closure_pathComponent, pathComponent_eq_connectedComponent]

/-- **A connected open set in a locally path-connected space is path-connected.** Restricting
    to open sets is the standard way to recover path-connectedness from connectedness; the
    closure of such a set need not stay open, which is why this does not contradict the
    negative half. (Mathlib: `IsOpen.isConnected_iff_isPathConnected`.) -/
theorem isPathConnected_of_isConnected_of_isOpen {U : Set α} (hU : IsOpen U)
    (hc : IsConnected U) : IsPathConnected U :=
  (hU.isConnected_iff_isPathConnected).mp hc

/-- **A connected, locally path-connected space is path-connected.** The global form of the
    recovery: with local path-connectedness, connectedness and path-connectedness agree.
    (Mathlib: `PathConnectedSpace.of_locPathConnectedSpace`.) -/
theorem pathConnectedSpace_of_connected [ConnectedSpace α] : PathConnectedSpace α :=
  PathConnectedSpace.of_locPathConnectedSpace

end ConnectedSpaceOQ01OQ01
