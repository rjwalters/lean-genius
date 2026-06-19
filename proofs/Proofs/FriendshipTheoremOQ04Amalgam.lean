/-
# Friendship Theorem (infinite case), OQ-04 — the amalgamation STEP lemma

STATUS: BUILD-PENDING SCAFFOLD (3 `sorry`s). NOT registered in `Proofs.lean`,
NOT a verified result. Both verification routes were closed when this was
authored (2026-06-19, researcher-2): the local Docker build gate was shut
(host load ~24, two `lean-build` containers already running) and the Aristotle
backend returned 404. This file records the precise, build-ready statement and
proof strategy for the one remaining open gap so the next session — with a gate
open — can discharge it directly (each `sorry` is a routine finite case bash;
the statements were designed to be Aristotle `prove_file`-ready).

## Why this file exists

`FriendshipTheoremOQ04.lean` completes the *structural* (non-spectral) programme
for the infinite friendship theorem: the diameter-≤2 covering, the
local-finiteness ⟹ finiteness restoring condition, hub uniqueness, and the
hub-free ⟹ ℵ₀-regular dichotomy. Throughout, those lemmas *reference* "the C₅
free-amalgamation counterexample" (an infinite friendship graph with no
universal vertex) but the construction itself is never formalized — it was
flagged as a multi-session inductive-limit/colimit build.

The colimit needs ω-indexed direct-limit machinery, but its **inductive core is
a single finitary lemma**: one amalgamation step preserves the friendship
("linear") property and repairs one deficient pair. That step is what this file
isolates. Formalizing it downgrades the open gap from "build an ω-colimit" to
"iterate a verified, finite step," which is the genuinely single-session-
tractable first deliverable.

## The construction (Chvátal–Kotzig–Rosenberg–Davies 1976; ERS 1966)

Start from C₅. Repeatedly: pick any pair `{u, v}` of distinct vertices with **no**
common neighbour and splice in a brand-new private vertex `w` adjacent to exactly
`u` and `v`. The countable limit is a friendship graph with no universal vertex.

`amalgam G u v` below is one such step on `Option V`: the fresh vertex is `none`,
adjacent to exactly `some u` and `some v`.

## Correctness of the step (the math the `sorry`s encode)

Call `G` *linear* if every pair of distinct vertices has **at most one** common
neighbour (the friendship upper bound; a friendship graph is linear with the
extra "at least one" lower bound). Suppose `G` is linear, `u ≠ v`, and `u, v`
have no common neighbour in `G`. Then:

* `amalgam_new_common`     : `none` is a common neighbour of `some u, some v`.
* `amalgam_new_common_unique` : in fact `none` is their *only* common neighbour,
    so the previously-deficient pair now has **exactly one** (a `some c` could
    only qualify if `c ∈ commonNeighbors G u v = ∅`).
* `amalgam_linear`         : the step **preserves linearity**. Case bash on a
    distinct pair `p, q : Option V`:
    - `p = some a, q = some b` (`a ≠ b`): a `some c` neighbour lies in the
      `G`-common set (subsingleton, as `G` is linear); `none` is common only when
      `{a, b} = {u, v}`, and then the `G`-common set is empty, so `none` is the
      unique common neighbour.
    - `p = none, q = some b`: a common neighbour is some `some c` with
      `c ∈ {u, v}` and `G.Adj b c`. If **both** `u, v` were `G`-adjacent to `b`
      then `b ∈ commonNeighbors G u v = ∅` — contradiction — so at most one of
      `u, v` qualifies. Subsingleton. (`p = some, q = none` is symmetric.)
    Hence every distinct pair keeps ≤ 1 common neighbour.

`u ≠ v` is the honest hypothesis of the real construction; linearity-preservation
actually only consumes `hempty`, but the splice is only ever applied to genuine
distinct pairs, so the lemma is stated with `huv` to match its use site.
-/

import Mathlib

open scoped Classical

namespace FriendshipAmalgam

variable {V : Type*}

/-- Common neighbours of `a` and `b` in `G`. -/
def commonNeighbors (G : SimpleGraph V) (a b : V) : Set V :=
  {x | G.Adj a x ∧ G.Adj b x}

/-- `G` is *linear* if every pair of distinct vertices has at most one common
neighbour (the friendship upper bound). -/
def Linear (G : SimpleGraph V) : Prop :=
  ∀ a b : V, a ≠ b → (commonNeighbors G a b).Subsingleton

/-- One amalgamation step: add a fresh vertex `none` to `Option V`, adjacent to
exactly `some u` and `some v`, leaving the rest of `G` unchanged. -/
def amalgam (G : SimpleGraph V) (u v : V) : SimpleGraph (Option V) where
  Adj p q :=
    match p, q with
    | some a, some b => G.Adj a b
    | some a, none   => a = u ∨ a = v
    | none, some b   => b = u ∨ b = v
    | none, none     => False
  symm := by
    intro p q h
    cases p <;> cases q <;> simp_all [G.adj_comm]
  loopless := by
    intro p h
    cases p <;> simp_all

/-- After the step, `none` is a common neighbour of `some u, some v`. -/
theorem amalgam_new_common (G : SimpleGraph V) (u v : V) :
    none ∈ commonNeighbors (amalgam G u v) (some u) (some v) := by
  sorry

/-- After the step, when `u, v` had no common neighbour, `none` is the *unique*
common neighbour of `some u, some v`: the deficient pair now has exactly one. -/
theorem amalgam_new_common_unique (G : SimpleGraph V) {u v : V}
    (hempty : commonNeighbors G u v = ∅) :
    commonNeighbors (amalgam G u v) (some u) (some v) = {none} := by
  sorry

/-- The amalgamation step preserves linearity, provided the fixed pair `u, v` is
distinct and currently has no common neighbour. This is the inductive core of the
C₅ free-amalgamation construction of an infinite friendship graph with no
universal vertex. -/
theorem amalgam_linear (G : SimpleGraph V) {u v : V} (huv : u ≠ v)
    (hG : Linear G) (hempty : commonNeighbors G u v = ∅) :
    Linear (amalgam G u v) := by
  sorry

end FriendshipAmalgam
