import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic

/-!
# Connected space OQ-01: the closure of a (pre)connected set is (pre)connected

This entry formalizes the topological fact

> *The closure of a preconnected set is preconnected* (and likewise for connected sets),

together with its sharper "bark and tree" generalization and a useful corollary. The core
results are available in Mathlib (`IsPreconnected.closure`, `IsConnected.closure`,
`IsPreconnected.subset_closure`); we package them in gallery form and derive the corollary
that a **dense connected** subset forces the whole space to be connected.

Intuitively, preconnectedness cannot be destroyed by adding limit points: any open separation
of the closure would already separate the dense original set. The "bark and tree" theorem
says more — *any* set wedged between a preconnected set and its closure is preconnected.

## Main results

* `preconnected_closure` : the closure of a preconnected set is preconnected.
* `connected_closure` : the closure of a connected set is connected.
* `preconnected_of_subset_closure` : a set between `s` and `closure s` is preconnected
  ("bark and tree").
* `connectedSpace_of_dense_connected` : a dense connected subset makes the space connected.
-/

namespace ConnectedSpaceOQ01

open Set Topology

variable {α : Type*} [TopologicalSpace α]

/-- **The closure of a preconnected set is preconnected.** Adding limit points cannot break
    preconnectedness: any open cover separating `closure s` would separate the dense subset
    `s` itself. (Mathlib: `IsPreconnected.closure`.) -/
theorem preconnected_closure {s : Set α} (h : IsPreconnected s) :
    IsPreconnected (closure s) :=
  h.closure

/-- **The closure of a connected set is connected.** Same as above, retaining nonemptiness.
    (Mathlib: `IsConnected.closure`.) -/
theorem connected_closure {s : Set α} (h : IsConnected s) :
    IsConnected (closure s) :=
  h.closure

/-- **"Bark and tree".** Any set `t` sandwiched between a preconnected set `s` and its
    closure (`s ⊆ t ⊆ closure s`) is itself preconnected — a strictly stronger statement than
    closing up `s` all the way. (Mathlib: `IsPreconnected.subset_closure`.) -/
theorem preconnected_of_subset_closure {s t : Set α} (h : IsPreconnected s)
    (hst : s ⊆ t) (hts : t ⊆ closure s) : IsPreconnected t :=
  h.subset_closure hst hts

/-- The connected analogue of "bark and tree": a set between a connected set and its closure
    is connected. -/
theorem connected_of_subset_closure {s t : Set α} (h : IsConnected s)
    (hst : s ⊆ t) (hts : t ⊆ closure s) : IsConnected t :=
  h.subset_closure hst hts

/-- **A dense connected subset makes the whole space connected.** If `s` is connected and
    dense, then `α` is a `ConnectedSpace`: its closure is all of `α`, and the closure of a
    connected set is connected. -/
theorem connectedSpace_of_dense_connected {s : Set α} (hc : IsConnected s) (hd : Dense s) :
    ConnectedSpace α := by
  rw [connectedSpace_iff_univ, ← hd.closure_eq]
  exact hc.closure

/-- **A dense preconnected subset makes the whole space preconnected.** -/
theorem preconnectedSpace_of_dense_preconnected {s : Set α} (hc : IsPreconnected s)
    (hd : Dense s) : PreconnectedSpace α := by
  rw [preconnectedSpace_iff_univ, ← hd.closure_eq]
  exact hc.closure

end ConnectedSpaceOQ01
