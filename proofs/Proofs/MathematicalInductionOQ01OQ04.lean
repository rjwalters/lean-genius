import Mathlib

/-
# Ordinal Induction and the Von Neumann Cumulative Hierarchy

## The Question (OQ-01-OQ-04)
The parent entry (`mathematical-induction-oq-01`) shows that Lean's
well-founded recursion *is* transfinite induction over ordinals, packaged by
Mathlib as `Ordinal.induction`.  This child asks the natural follow-up:

> How does `Ordinal.induction` (well-founded recursion on the ordinals)
> relate to the von Neumann cumulative hierarchy `V_ α = ⋃_{β<α} 𝒫(V_ β)`,
> and to the foundational fact that set membership `(· ∈ ·)` is well-founded
> (the Axiom of Foundation / Regularity)?

The cumulative hierarchy stratifies the set-theoretic universe: every set sits
at some level `V_ α`.  Mathlib (in `Mathlib/SetTheory/ZFC/VonNeumann.lean`)
defines `vonNeumann` and proves the structural facts — the level equations
`V_ 0 = ∅`, `V_ (succ o) = 𝒫(V_ o)`, exhaustion `⋃ o, V_ o = univ`, and the
rank characterisation `x ∈ V_ o ↔ rank x < o`.  What it does **not** package is
the *bridge* between `Ordinal.induction` and the hierarchy:

  * that the von Neumann rank turns `(· ∈ ·)` into the pullback of `(· < ·)` on
    ordinals, so **Foundation is a consequence of ordinal well-foundedness**;
  * the resulting **rank-stratified strong induction** and **∈-induction**
    principles, exhibited as instances of `Ordinal.induction` (Mathlib derives
    `ZFSet.inductionOn` independently from `PSet.mem_wf`, not via rank);
  * a **uniqueness / fixed-point characterisation** of the hierarchy: `V_` is
    the *unique* ordinal-indexed family satisfying the cumulative recursion
    `F o = ⋃_{a<o} 𝒫(F a)`, proved by `Ordinal.induction`.  This is exactly the
    statement that `vonNeumann` is the `WellFounded.fix` solution of the
    cumulative functional.

## What We Prove
- `mem_imp_rank_lt`        : `y ∈ x → rank y < rank x` (the rank drop).
- `mem_subrelation_rank`   : `(· ∈ ·)` is a subrelation of `rank`-pullback of `<`.
- `mem_wf_via_rank`        : `WellFounded (· ∈ ·)` **from** ordinal well-foundedness.
- `rank_strong_induction`  : strong induction on rank, **via `Ordinal.induction`**.
- `mem_induction`          : ∈-induction (Foundation), **via `Ordinal.induction`**.
- `vonNeumann_level_induction` : prove `P` everywhere by climbing the levels `V_ o`.
- `vonNeumann_unique`      : `V_` is the unique solution of the cumulative
                             recursion (the `WellFounded.fix` fixed point).
- `vonNeumann_mem_iff_unique` : the membership-characterisation uniqueness.

Everything is fully verified: 0 sorries, 0 axioms, no `native_decide`.
-/

open Ordinal
open scoped ZFSet

namespace MathematicalInductionOQ01OQ04

variable {x y : ZFSet.{u}} {o a : Ordinal.{u}}

/-! ### Part I — The rank drop and Foundation from ordinal well-foundedness

The von Neumann `rank : ZFSet → Ordinal` strictly decreases along membership.
This single fact is the entire content of the Axiom of Foundation: it embeds
the membership relation into the (well-founded) order on ordinals. -/

/-- **Rank drop.**  A member has strictly smaller rank than the containing set.
This is `ZFSet.rank_lt_of_mem`, re-exported as the bridge lemma. -/
theorem mem_imp_rank_lt (h : y ∈ x) : ZFSet.rank y < ZFSet.rank x :=
  ZFSet.rank_lt_of_mem h

/-- **Membership is a subrelation of the rank-pullback of `<`.**  Equivalently,
`rank : ZFSet → Ordinal` is an order-embedding of the membership relation into
the well-founded order on ordinals. -/
theorem mem_subrelation_rank :
    Subrelation (α := ZFSet.{u}) (· ∈ ·) (InvImage (· < ·) ZFSet.rank) :=
  fun h => mem_imp_rank_lt h

/-- **Foundation from ordinal well-foundedness.**  Because the ordinals are
well-founded under `<` and `rank` strictly drops along `∈`, the membership
relation on `ZFSet` is well-founded.  This re-proves the Axiom of Foundation
(Mathlib's `ZFSet.mem_wf`) through the cumulative hierarchy rank rather than
through `PSet`. -/
theorem mem_wf_via_rank : WellFounded ((· ∈ ·) : ZFSet.{u} → ZFSet.{u} → Prop) :=
  mem_subrelation_rank.wf (InvImage.wf ZFSet.rank wellFounded_lt)

/-! ### Part II — Induction principles as instances of `Ordinal.induction`

`Ordinal.induction` is well-founded recursion on the ordinals.  Transporting it
along `rank` yields strong induction on sets ordered by rank, and specialising
the rank drop recovers ∈-induction. -/

/-- **Rank-stratified strong induction.**  To prove `P` for every set it suffices
to prove `P x` assuming `P y` for every set `y` of strictly smaller rank.  The
proof is a direct application of `Ordinal.induction` to the rank. -/
theorem rank_strong_induction {P : ZFSet.{u} → Prop}
    (H : ∀ x, (∀ y, ZFSet.rank y < ZFSet.rank x → P y) → P x) : ∀ x, P x := by
  -- Prove `P` level by level: by ordinal induction, `P` holds on every set of
  -- rank `o`, assuming it holds on all sets of smaller rank.
  have key : ∀ o : Ordinal.{u}, ∀ x : ZFSet.{u}, ZFSet.rank x = o → P x := by
    intro o
    induction o using Ordinal.induction with
    | h o IH =>
      intro x hx
      refine H x (fun y hy => ?_)
      exact IH (ZFSet.rank y) (hx ▸ hy) y rfl
  exact fun x => key (ZFSet.rank x) x rfl

/-- **∈-induction (Foundation), via `Ordinal.induction`.**  The usual
membership-induction principle on sets, here obtained as a specialisation of
rank-stratified strong induction through the rank drop `mem_imp_rank_lt`.
(Mathlib's `ZFSet.inductionOn` proves the same statement, but from
`PSet.mem_wf`; this derivation routes through the cumulative hierarchy.) -/
theorem mem_induction {P : ZFSet.{u} → Prop}
    (H : ∀ x, (∀ y ∈ x, P y) → P x) : ∀ x, P x :=
  rank_strong_induction fun x IH => H x fun _ hy => IH _ (mem_imp_rank_lt hy)

/-! ### Part III — Climbing the cumulative hierarchy

The membership characterisation `x ∈ V_ o ↔ rank x < o` lets us recast strong
induction as "climbing the levels": to prove `P` everywhere it suffices, at each
level `o`, to extend `P` from the whole of `V_ o` to the sets of rank exactly
`o`. -/

/-- **Level induction up the cumulative hierarchy.**  Reading `∀ x ∈ V_ o, P x`
as "`P` holds below level `o`" (since `x ∈ V_ o ↔ rank x < o`), this is the
hierarchy form of strong induction, again powered by `Ordinal.induction`. -/
theorem vonNeumann_level_induction {P : ZFSet.{u} → Prop}
    (H : ∀ o : Ordinal.{u}, (∀ x ∈ ZFSet.vonNeumann o, P x) →
      ∀ x, ZFSet.rank x = o → P x) : ∀ x, P x := by
  apply rank_strong_induction
  intro x IH
  refine H (ZFSet.rank x) (fun y hy => ?_) x rfl
  -- `y ∈ V_ (rank x)` unfolds to `rank y < rank x`, which is exactly `IH`.
  exact IH y (ZFSet.mem_vonNeumann.mp hy)

/-! ### Part IV — Uniqueness of the hierarchy (the `WellFounded.fix` fixed point)

`vonNeumann` is defined by the cumulative recursion `V_ o = ⋃_{a<o} 𝒫(V_ a)`
(Mathlib uses `termination_by`, i.e. `WellFounded.fix`).  We show this recursion
has a *unique* solution: any `F` satisfying the same equation equals `vonNeumann`.
The proof is `Ordinal.induction` — the very principle that justifies the
recursive definition. -/

/-- **Uniqueness of the cumulative recursion.**  If `F : Ordinal → ZFSet`
satisfies the von Neumann recurrence `F o = ⋃_{a < o} 𝒫(F a)`, then `F = V_`.
Equivalently: `vonNeumann` is the unique fixed point of the cumulative
functional, i.e. its `WellFounded.fix` solution is determined. -/
theorem vonNeumann_unique (F : Ordinal.{u} → ZFSet.{u})
    (hF : ∀ o, F o = ⋃ a : Set.Iio o, ZFSet.powerset (F a)) :
    F = ZFSet.vonNeumann := by
  funext o
  induction o using Ordinal.induction with
  | h o IH =>
    apply ZFSet.ext
    intro x
    rw [hF o, ZFSet.mem_iUnion, ZFSet.mem_vonNeumann']
    constructor
    · rintro ⟨⟨a, ha⟩, hx⟩
      rw [ZFSet.mem_powerset] at hx
      exact ⟨a, ha, by rwa [IH a ha] at hx⟩
    · rintro ⟨a, ha, hx⟩
      exact ⟨⟨a, ha⟩, by rw [ZFSet.mem_powerset, IH a ha]; exact hx⟩

/-- **Membership-characterisation uniqueness.**  The hierarchy is also pinned
down level-by-level by its members: `V_ o` is the set of all sets of rank `< o`.
Any family with that membership property is `vonNeumann`. -/
theorem vonNeumann_mem_iff_unique (F : Ordinal.{u} → ZFSet.{u})
    (hF : ∀ o x, x ∈ F o ↔ ZFSet.rank x < o) : F = ZFSet.vonNeumann := by
  funext o
  apply ZFSet.ext
  intro x
  rw [hF o x, ZFSet.mem_vonNeumann]

end MathematicalInductionOQ01OQ04
