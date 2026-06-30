/-
# Friendship Theorem (infinite case), OQ-04 — the amalgamation STEP lemma

STATUS: discharged — all three `sorry`s of the original scaffold (PR #26211) are
now closed with hand proofs (0 `sorry`, 0 `axiom`). The three obligations were
exactly the routine finite case bashes the scaffold predicted:
`amalgam_new_common` (trivial membership), `amalgam_new_common_unique` (a `some c`
witness would land in the empty `G`-common set), and `amalgam_linear` (a full
`Option V × Option V` case split, every branch closing by the empty-common-set
`key` fact or `G`'s own linearity). Authored 2026-06-19 by researcher-2.

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
  simp [commonNeighbors, amalgam]

/-- After the step, when `u, v` had no common neighbour, `none` is the *unique*
common neighbour of `some u, some v`: the deficient pair now has exactly one. -/
theorem amalgam_new_common_unique (G : SimpleGraph V) {u v : V}
    (hempty : commonNeighbors G u v = ∅) :
    commonNeighbors (amalgam G u v) (some u) (some v) = {none} := by
  ext x
  cases x with
  | none => simp [commonNeighbors, amalgam]
  | some c =>
    simp only [commonNeighbors, Set.mem_setOf_eq, amalgam, Set.mem_singleton_iff,
      reduceCtorEq, iff_false]
    rintro ⟨h1, h2⟩
    have hmem : c ∈ commonNeighbors G u v := ⟨h1, h2⟩
    rw [hempty] at hmem
    exact hmem

/-- The amalgamation step preserves linearity, provided the fixed pair `u, v` is
distinct and currently has no common neighbour. This is the inductive core of the
C₅ free-amalgamation construction of an infinite friendship graph with no
universal vertex. -/
theorem amalgam_linear (G : SimpleGraph V) {u v : V} (huv : u ≠ v)
    (hG : Linear G) (hempty : commonNeighbors G u v = ∅) :
    Linear (amalgam G u v) := by
  -- No vertex is adjacent to both `u` and `v` (else it lies in the empty common set).
  have key : ∀ b : V, ¬ (G.Adj u b ∧ G.Adj v b) := by
    intro b hb
    have hmem : b ∈ commonNeighbors G u v := hb
    rw [hempty] at hmem
    exact hmem
  intro p q hpq x hx y hy
  obtain ⟨hxp, hxq⟩ := hx
  obtain ⟨hyp, hyq⟩ := hy
  cases p with
  | none =>
    cases q with
    | none => exact absurd rfl hpq
    | some b =>
      -- `none` has no `none`-neighbour, so both common neighbours are `some _`.
      cases x with
      | none => simp [amalgam] at hxp
      | some c =>
        cases y with
        | none => simp [amalgam] at hyp
        | some d =>
          simp only [amalgam] at hxp hxq hyp hyq
          rcases hxp with rfl | rfl <;> rcases hyp with rfl | rfl
          · rfl
          · exact absurd ⟨hxq.symm, hyq.symm⟩ (key b)
          · exact absurd ⟨hyq.symm, hxq.symm⟩ (key b)
          · rfl
  | some a =>
    cases q with
    | none =>
      cases x with
      | none => simp [amalgam] at hxq
      | some c =>
        cases y with
        | none => simp [amalgam] at hyq
        | some d =>
          simp only [amalgam] at hxp hxq hyp hyq
          rcases hxq with rfl | rfl <;> rcases hyq with rfl | rfl
          · rfl
          · exact absurd ⟨hxp.symm, hyp.symm⟩ (key a)
          · exact absurd ⟨hyp.symm, hxp.symm⟩ (key a)
          · rfl
    | some b =>
      have hab : a ≠ b := fun h => hpq (by rw [h])
      cases x with
      | none =>
        cases y with
        | none => rfl
        | some d =>
          simp only [amalgam] at hxp hxq hyp hyq
          exfalso
          rcases hxp with rfl | rfl <;> rcases hxq with rfl | rfl
          · exact hab rfl
          · exact key d ⟨hyp, hyq⟩
          · exact key d ⟨hyq, hyp⟩
          · exact hab rfl
      | some c =>
        cases y with
        | none =>
          simp only [amalgam] at hxp hxq hyp hyq
          exfalso
          rcases hyp with rfl | rfl <;> rcases hyq with rfl | rfl
          · exact hab rfl
          · exact key c ⟨hxp, hxq⟩
          · exact key c ⟨hxq, hxp⟩
          · exact hab rfl
        | some d =>
          simp only [amalgam] at hxp hxq hyp hyq
          have hc : c ∈ commonNeighbors G a b := ⟨hxp, hxq⟩
          have hd : d ∈ commonNeighbors G a b := ⟨hyp, hyq⟩
          exact congrArg some (hG a b hab hc hd)

end FriendshipAmalgam
