/-
# Non-Crossing Partitions as Finpartitions: a Decidable, Countable Model
## (ballot-problem-oq-04-oq-02)

**Open question** (from `ballot-problem-oq-04`, openQuestion[2]): the parent entry
introduced non-crossing partitions of `Fin n` as a predicate `IsNonCrossing` on the
*setoid* (same-block equivalence relation) and developed their structural theory, but the
setoid model has a defect for *counting*: an arbitrary `Setoid (Fin n)` (a `Prop`-valued
relation) is not a `Fintype`, so one cannot form `Fintype.card {s // IsNonCrossing s}`.

This file repairs that defect by porting non-crossing partitions to Mathlib's
`Finpartition (univ : Finset (Fin n))`, which **is** a `Fintype`, and proving the two
formulations agree. Concretely:

* **Finpartition model** (`IsNonCrossingFp`): the non-crossing predicate phrased on a
  `Finpartition` via its "same part" relation `b ∈ P.part a`, mirroring the parent's
  setoid condition verbatim, together with a `Decidable` instance (all four quantifiers
  range over the `Fintype` `Fin n` and `b ∈ P.part a` is decidable).

* **Agreement** (`isNonCrossingFp_ofSetoid_iff`): for a setoid `s` with decidable relation,
  `IsNonCrossingFp (Finpartition.ofSetoid s) ↔ IsNonCrossing s`. The two models describe
  the same combinatorial objects; this is immediate from Mathlib's
  `Finpartition.mem_part_ofSetoid_iff_rel`, which identifies `b ∈ (ofSetoid s).part a` with
  `s a b`.

* **Countability** (`nonCrossingCount`): with the `Decidable` instance,
  `{P : Finpartition univ // IsNonCrossingFp P}` is a `Fintype`, so the non-crossing
  partitions of `Fin n` have a well-defined cardinality `nonCrossingCount n`.

* **The discriminator at `n = 4`.** For `n ≤ 3` *every* partition is non-crossing
  (`isNonCrossingFp_of_n_le_three`), so `nonCrossingCount n = Fintype.card (Finpartition univ)`
  there — non-crossing partitions and all partitions agree. At `n = 4` they first diverge:
  the partition `{{0,2},{1,3}}` (the kernel of `· % 2` on `Fin 4`) **crosses**
  (`crossing4_not_isNonCrossing`), giving a strict drop
  `nonCrossingCount 4 < Fintype.card (Finpartition univ)` (`nonCrossingCount_four_lt`).
  This is exactly the `catalan 4 = 14 < 15 = Bell 4` phenomenon, now a theorem about the
  Finpartition model rather than a hand computation.

The exact value `nonCrossingCount n = catalan n` is the content of the explicit
Dyck-word ↔ non-crossing-partition bijection (sibling `ballot-problem-oq-04-oq-01`); this
entry supplies the *countable model* and the *first point of divergence* that make that
counting statement well-typed.

**Sorry count**: 0. **Axiom count**: 0 (only foundational `propext`/`Classical.choice`/
`Quot.sound`; the `n=4` witness uses *kernel* `decide`, so no `Lean.ofReduceBool`).
-/

import Mathlib
import Proofs.BallotProblemOQ04

open Finset

namespace BallotProblemOQ04OQ02

open BallotProblemOQ04 (IsNonCrossing)

/-! ## Section I: The Finpartition model of non-crossing partitions

A `Finpartition (univ : Finset (Fin n))` is a genuine `Fintype`, unlike a bare
`Setoid (Fin n)`. We phrase the non-crossing predicate on it through the "same part"
relation `b ∈ P.part a`, mirroring the parent's setoid condition `s a c → s b d → s a b`. -/

/-- **Non-crossing, Finpartition form.** A finite partition `P` of `Fin n` is *non-crossing*
if no two distinct parts interleave: whenever `a < b < c < d` with `a, c` in one part
(`c ∈ P.part a`) and `b, d` in another (`d ∈ P.part b`), the indices `a, b` already share a
part. This is the parent's `IsNonCrossing` condition with `s x y` replaced by `y ∈ P.part x`. -/
def IsNonCrossingFp {n : ℕ} (P : Finpartition (univ : Finset (Fin n))) : Prop :=
  ∀ a b c d : Fin n, a < b → b < c → c < d → c ∈ P.part a → d ∈ P.part b → b ∈ P.part a

/-- The non-crossing predicate is decidable: all quantifiers range over the finite type
`Fin n`, and `c ∈ P.part a` is decidable membership in a `Finset`. -/
instance instDecidableIsNonCrossingFp {n : ℕ} (P : Finpartition (univ : Finset (Fin n))) :
    Decidable (IsNonCrossingFp P) := by
  unfold IsNonCrossingFp; infer_instance

/-! ## Section II: Agreement of the setoid and Finpartition models

`Finpartition.ofSetoid` turns a (decidable) setoid into the finpartition of its
equivalence classes, and `mem_part_ofSetoid_iff_rel` says `b ∈ (ofSetoid s).part a ↔ s a b`.
So the two non-crossing predicates are literally the same condition. -/

/-- **Agreement.** The Finpartition non-crossing predicate on `Finpartition.ofSetoid s`
coincides with the parent's setoid non-crossing predicate on `s`. The two formalizations of
"non-crossing partition" describe the same objects. -/
theorem isNonCrossingFp_ofSetoid_iff {n : ℕ} (s : Setoid (Fin n)) [DecidableRel s.r] :
    IsNonCrossingFp (Finpartition.ofSetoid s) ↔ IsNonCrossing s := by
  unfold IsNonCrossingFp IsNonCrossing
  simp only [Finpartition.mem_part_ofSetoid_iff_rel]

/-! ## Section III: For `n ≤ 3` every partition is non-crossing -/

/-- **No crossings below four points.** Every finite partition of `Fin n` with `n ≤ 3` is
non-crossing — a crossing needs four strictly increasing indices, which do not fit. (Direct
analogue of the parent's `isNonCrossing_of_n_le_three`.) -/
theorem isNonCrossingFp_of_n_le_three {n : ℕ} (hn : n ≤ 3)
    (P : Finpartition (univ : Finset (Fin n))) : IsNonCrossingFp P := by
  intro a b c d hab hbc hcd _ _
  exfalso
  rw [Fin.lt_def] at hab hbc hcd
  have hd : d.val < n := d.isLt
  omega

/-! ## Section IV: Counting, and the discriminator at `n = 4` -/

/-- The number of non-crossing partitions of `Fin n`, now well-defined because the
Finpartition model is a `Fintype`. -/
def nonCrossingCount (n : ℕ) : ℕ :=
  Fintype.card {P : Finpartition (univ : Finset (Fin n)) // IsNonCrossingFp P}

/-- For `n ≤ 3`, non-crossing partitions and *all* partitions coincide, so the non-crossing
count equals the total partition count (the Bell number). -/
theorem nonCrossingCount_eq_card_of_n_le_three {n : ℕ} (hn : n ≤ 3) :
    nonCrossingCount n = Fintype.card (Finpartition (univ : Finset (Fin n))) := by
  unfold nonCrossingCount
  exact Fintype.card_congr (Equiv.subtypeUnivEquiv (isNonCrossingFp_of_n_le_three hn))

/-- The crossing setoid on `Fin 4`: two indices are related iff they have the same parity,
i.e. the partition into `{0, 2}` (even) and `{1, 3}` (odd) — the smallest crossing partition. -/
def crossing4 : Setoid (Fin 4) := Setoid.ker (fun a : Fin 4 => a.val % 2)

instance : DecidableRel (crossing4).r := fun a b => by
  unfold crossing4 Setoid.ker Function.onFun; exact inferInstanceAs (Decidable (_ = _))

/-- The parity partition `{{0,2},{1,3}}` of `Fin 4` **crosses**: `0 < 1 < 2 < 3` with
`0 ~ 2` and `1 ~ 3` but `¬ 0 ~ 1`. Hence it violates the (setoid) non-crossing condition. -/
theorem crossing4_not_isNonCrossing : ¬ IsNonCrossing crossing4 := by
  intro h
  -- `h 0 1 2 3` would force `0 ~ 1`, i.e. `0 % 2 = 1 % 2`.
  have h01 : crossing4.r 0 1 := h 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [crossing4, Setoid.ker, Function.onFun] at h01
  exact absurd h01 (by decide)

/-- The Finpartition realising the crossing partition `{{0,2},{1,3}}` on `Fin 4`. It is a
witness that *not* every partition of `Fin 4` is non-crossing. -/
def crossing4Fp : Finpartition (univ : Finset (Fin 4)) := Finpartition.ofSetoid crossing4

theorem crossing4Fp_not_isNonCrossingFp : ¬ IsNonCrossingFp crossing4Fp :=
  fun h => crossing4_not_isNonCrossing ((isNonCrossingFp_ofSetoid_iff crossing4).mp h)

/-- **The discriminator at `n = 4`.** Non-crossing partitions are a *strict* subfamily of
all partitions of `Fin 4`: the parity partition `{{0,2},{1,3}}` crosses. This is the
first `n` at which the non-crossing count drops below the total (Bell) count — the
`catalan 4 = 14 < 15 = Bell 4` phenomenon, as a theorem about the Finpartition model. -/
theorem nonCrossingCount_four_lt :
    nonCrossingCount 4 < Fintype.card (Finpartition (univ : Finset (Fin 4))) :=
  Fintype.card_subtype_lt (x := crossing4Fp) crossing4Fp_not_isNonCrossingFp

#check @isNonCrossingFp_ofSetoid_iff
#check @nonCrossingCount_eq_card_of_n_le_three
#check @nonCrossingCount_four_lt

end BallotProblemOQ04OQ02
