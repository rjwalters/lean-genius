import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

/-
# Hexagrammum Mysticum — the S₆ cycle-type census (OQ-03 incomplete-01)

## Parent lineage

`pascals-hexagon` (Pascal's Hexagon Theorem, Wiedijk #28)
→ `pascals-hexagon-oq-03` (the 60-Pascal-line scaffold, `HexagonLabeling := Sym(6) ⧸ D₆`)
→ **this file** (`pascals-hexagon-oq-03-incomplete-01`).

The `oq-03` scaffold establishes the **60** count (distinct Pascal lines
= `|Sym(6) / D₆| = 720 / 12 = 60`) and states the Steiner / Kirkman *point*
counts (20, 60) as `sorry`-guarded geometric targets over an abstract
`Fintype` instance — those require the full projective concurrence machinery
(Cayley–Bacharach) and remain open.

## What this file proves (sorry-free)

The remaining Hexagrammum Mysticum incidence counts are governed by a purely
**combinatorial** backbone: the census of `Sym(6) = Equiv.Perm (Fin 6)` by
cycle type. Conway & Ryba, *The Pascal Mysticum Demystified*
(Math. Intelligencer 34 (2012) 4–8), index the whole 95-point / 95-line
configuration by conjugacy classes of `S₆`:

* **6-cycles** index the **Pascal lines (60)** and **Kirkman points (60)**;
* **products of two 3-cycles** index the **Steiner points (20)** and
  **Cayley–Salmon lines (20)**;
* **products of three 2-cycles** index the **Plücker lines (15)** and
  **Salmon points (15)**.

The point/line pairs at each cycle type are exchanged by the **outer
automorphism of `S₆`**, so each cycle-type class of size `2k` splits into
`k` "point" objects and `k` "line" objects (the class of size `15` is
self-paired: 15 lines and 15 points share the single 15-element class).

This file verifies the three governing class sizes exactly, over the honest
concrete group `Equiv.Perm (Fin 6)`, characterising each class by an
elementary power / fixed-point predicate (no `cycleType` API needed):

| class          | predicate                                   | size |
|----------------|---------------------------------------------|------|
| identity total | `Fintype.card (Perm (Fin 6))`               | 720  |
| 6-cycles       | fixed-point-free, `σ⁶=1`, `σ²≠1`, `σ³≠1`     | 120  |
| (3,3)          | fixed-point-free, `σ³=1`                     | 40   |
| (2,2,2)        | fixed-point-free involution                 | 15   |

From these, the Hexagrammum object counts follow by the Conway–Ryba pairing:
`120/2 = 60`, `40/2 = 20`, and `15` (self-paired).

## Honest scope

This is the *combinatorial* half of the Hexagrammum Mysticum: it fixes the
exact sizes of the indexing conjugacy classes and records the Conway–Ryba
correspondence. It does **not** formalize the projective *bijection* between
these classes and the geometric points/lines — that is the content of the
still-open `steiner_count_eq_20` / `kirkman_count_eq_60` targets in `oq-03`.
The class-size theorems are discharged by `native_decide` (hence the file
depends on `Lean.ofReduceBool`; it is not axiom-free).
-/

namespace PascalsHexagonOQ03Incomplete01

open Equiv

/-- `σ : Sym(6)` is **fixed-point-free** (its support is all of `Fin 6`). -/
def FixedPointFree (σ : Equiv.Perm (Fin 6)) : Prop := ∀ i, σ i ≠ i

instance (σ : Equiv.Perm (Fin 6)) : Decidable (FixedPointFree σ) :=
  inferInstanceAs (Decidable (∀ i, σ i ≠ i))

/-- A fixed-point-free `σ` with `σ⁶ = 1` but `σ² ≠ 1` and `σ³ ≠ 1` is exactly
    a **6-cycle** of `Sym(6)`. (Fixed-point-free forces cycle type among
    `(6), (4,2), (3,3), (2,2,2)`; `σ² ≠ 1` kills `(2,2,2)`, `σ³ ≠ 1` kills
    `(3,3)`, and `σ⁶ = 1` kills `(4,2)` since a `(4,2)` element has `σ⁶ = σ²
    ≠ 1`.) These index the Pascal lines and Kirkman points. -/
def IsSixCycle (σ : Equiv.Perm (Fin 6)) : Prop :=
  FixedPointFree σ ∧ σ ^ 6 = 1 ∧ σ ^ 2 ≠ 1 ∧ σ ^ 3 ≠ 1

instance (σ : Equiv.Perm (Fin 6)) : Decidable (IsSixCycle σ) :=
  inferInstanceAs (Decidable (FixedPointFree σ ∧ σ ^ 6 = 1 ∧ σ ^ 2 ≠ 1 ∧ σ ^ 3 ≠ 1))

/-- A fixed-point-free `σ` with `σ³ = 1` is exactly a **product of two
    3-cycles** (cycle type `(3,3)`): no fixed points and order dividing 3
    forces every cycle to have length 3, and `3 + 3 = 6`. These index the
    Steiner points and Cayley–Salmon lines. -/
def IsDoubleThreeCycle (σ : Equiv.Perm (Fin 6)) : Prop :=
  FixedPointFree σ ∧ σ ^ 3 = 1

instance (σ : Equiv.Perm (Fin 6)) : Decidable (IsDoubleThreeCycle σ) :=
  inferInstanceAs (Decidable (FixedPointFree σ ∧ σ ^ 3 = 1))

/-- A fixed-point-free involution of `Sym(6)` is exactly a **product of three
    2-cycles** (cycle type `(2,2,2)`): no fixed points and `σ² = 1` forces
    every cycle to have length 2, and `2 + 2 + 2 = 6`. These index the
    Plücker lines and Salmon points. -/
def IsTripleTransposition (σ : Equiv.Perm (Fin 6)) : Prop :=
  FixedPointFree σ ∧ σ ^ 2 = 1

instance (σ : Equiv.Perm (Fin 6)) : Decidable (IsTripleTransposition σ) :=
  inferInstanceAs (Decidable (FixedPointFree σ ∧ σ ^ 2 = 1))

/-- Anchor: `Sym(6)` has order `720`. -/
theorem card_sym6 : Fintype.card (Equiv.Perm (Fin 6)) = 720 := by
  native_decide

/-- **Pascal / Kirkman census.** There are exactly `120 = 2 · 60` six-cycles
    in `Sym(6)`; the outer automorphism splits them into the 60 Pascal lines
    and the 60 Kirkman points. -/
theorem card_sixCycles :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => IsSixCycle σ)).card = 120 := by
  native_decide

/-- **Steiner / Cayley census.** There are exactly `40 = 2 · 20` products of
    two 3-cycles in `Sym(6)`; the outer automorphism splits them into the 20
    Steiner points and the 20 Cayley (Cayley–Salmon) lines. -/
theorem card_doubleThreeCycles :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => IsDoubleThreeCycle σ)).card = 40 := by
  native_decide

/-- **Plücker / Salmon census.** There are exactly `15` products of three
    2-cycles in `Sym(6)`; this class is self-paired under the outer
    automorphism (15 Plücker lines and 15 Salmon points). -/
theorem card_tripleTranspositions :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => IsTripleTransposition σ)).card = 15 := by
  native_decide

/-!
## Completeness of the fixed-point-free census

The three classes above are the Hexagrammum-indexing cycle types, but they do not
by themselves account for *all* fixed-point-free permutations of `Sym(6)`. The
partitions of `6` into parts `≥ 2` are `(6), (4,2), (3,3), (2,2,2)`; the one
missing type is `(4,2)`, which indexes **no** geometric object. Adding it closes
the census: the four classes exhaust the derangements of `Fin 6` (`D₆ = 265`).
-/

/-- A fixed-point-free `σ` with `σ⁴ = 1` but `σ² ≠ 1` is exactly a permutation of
    cycle type `(4,2)`: fixed-point-freeness forces the cycle type among
    `(6),(4,2),(3,3),(2,2,2)`; `σ⁴ = 1` (order dividing 4) kills `(6)` and `(3,3)`,
    and `σ² ≠ 1` kills `(2,2,2)`, leaving `(4,2)`. Unlike the other three classes
    this cycle type indexes **no** Hexagrammum object; it is recorded only to
    complete the fixed-point-free census (`fixedPointFree_iff_census`). -/
def IsFourTwoCycle (σ : Equiv.Perm (Fin 6)) : Prop :=
  FixedPointFree σ ∧ σ ^ 4 = 1 ∧ σ ^ 2 ≠ 1

instance (σ : Equiv.Perm (Fin 6)) : Decidable (IsFourTwoCycle σ) :=
  inferInstanceAs (Decidable (FixedPointFree σ ∧ σ ^ 4 = 1 ∧ σ ^ 2 ≠ 1))

/-- There are exactly `90 = C(6,4)·3!` permutations of cycle type `(4,2)` in
    `Sym(6)`. These index no Hexagrammum object; they are the fixed-point-free
    class the geometric configuration ignores. -/
theorem card_fourTwoCycles :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => IsFourTwoCycle σ)).card = 90 := by
  native_decide

/-- **The fixed-point-free classification.** A permutation of `Sym(6)` is
    fixed-point-free iff its cycle type is one of the four with all parts `≥ 2`:
    a 6-cycle, a `(4,2)`, a double 3-cycle, or a triple transposition. This proves
    the three Hexagrammum classes together with the geometrically-inert `(4,2)`
    class **exhaust** the fixed-point-free permutations, so the census below is
    complete (no cycle type is missed). -/
theorem fixedPointFree_iff_census :
    ∀ σ : Equiv.Perm (Fin 6), FixedPointFree σ ↔
      (IsSixCycle σ ∨ IsFourTwoCycle σ ∨ IsDoubleThreeCycle σ ∨ IsTripleTransposition σ) := by
  native_decide

/-- The fixed-point-free permutations of `Sym(6)` number `265` — the sixth
    derangement number `D₆`. (`FixedPointFree σ` is exactly `∀ i, σ i ≠ i`, i.e.
    membership in `derangements (Fin 6)`.) -/
theorem card_fixedPointFree :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => FixedPointFree σ)).card = 265 := by
  native_decide

/-- **Census closure.** The four fixed-point-free class sizes sum to `D₆ = 265`:
    `120 + 90 + 40 + 15 = 265`. Together with `fixedPointFree_iff_census` (the
    classes cover every derangement) and `card_fixedPointFree` (there are exactly
    `265` derangements), the exact match forces the four classes to be pairwise
    disjoint and exhaustive. Only the `120 / 40 / 15` classes carry geometric
    meaning; the `90` `(4,2)`-permutations are inert. -/
theorem fixedPointFree_census_sum : 120 + 90 + 40 + 15 = 265 := by norm_num

/-!
## Hexagrammum Mysticum object counts (Conway–Ryba pairing)

The geometric object counts follow from the census by the 2:1 outer-automorphism
pairing (self-paired at the `(2,2,2)` class).
-/

/-- **60 Pascal lines** (half the 120 six-cycles). -/
theorem pascal_lines_eq_60 : 120 / 2 = 60 := by norm_num

/-- **60 Kirkman points** (the other half of the 120 six-cycles). -/
theorem kirkman_points_eq_60 : 120 / 2 = 60 := by norm_num

/-- **20 Steiner points** (half the 40 double-3-cycles). -/
theorem steiner_points_eq_20 : 40 / 2 = 20 := by norm_num

/-- **20 Cayley–Salmon lines** (the other half of the 40 double-3-cycles). -/
theorem cayley_lines_eq_20 : 40 / 2 = 20 := by norm_num

/-- **15 Plücker lines / 15 Salmon points** (the self-paired `(2,2,2)` class). -/
theorem plucker_and_salmon_eq_15 : (15 : ℕ) = 15 := rfl

/-- **Configuration totals.** The Hexagrammum Mysticum is a `(95₃, 95₃)`
    configuration: `60 + 20 + 15 = 95` points and `60 + 20 + 15 = 95` lines. -/
theorem hexagrammum_points_eq_95 : 60 + 20 + 15 = 95 := by norm_num

theorem hexagrammum_lines_eq_95 : 60 + 20 + 15 = 95 := by norm_num

end PascalsHexagonOQ03Incomplete01
