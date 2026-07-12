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

/-! ### Census exactness at the level of the proven cardinalities

`fixedPointFree_census_sum` records the bare numeral identity `120 + 90 + 40 + 15 = 265`.
The following capstone upgrades it to reference the *proven* filter cardinalities: the four
class sizes, as machine-checked `Finset.card`s, sum to exactly the derangement count
`card_fixedPointFree`. Together with `fixedPointFree_iff_census` (the four classes cover
every derangement), this exact equality forces the classes to be pairwise disjoint — no
derangement is double-counted — closing the census both ways (cover *and* exactness). -/

/-- **Census exactness.** The four fixed-point-free class sizes, taken as the *proven*
    filter cardinalities (`card_sixCycles`, `card_fourTwoCycles`, `card_doubleThreeCycles`,
    `card_tripleTranspositions`), sum to exactly `card_fixedPointFree = 265`. With the
    exhaustive cover `fixedPointFree_iff_census`, the exact count forces pairwise
    disjointness of the four classes. -/
theorem census_cards_sum_eq_fixedPointFree :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => IsSixCycle σ)).card
      + (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => IsFourTwoCycle σ)).card
      + (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => IsDoubleThreeCycle σ)).card
      + (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => IsTripleTransposition σ)).card
      = (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => FixedPointFree σ)).card := by
  simp only [card_sixCycles, card_fourTwoCycles, card_doubleThreeCycles,
    card_tripleTranspositions, card_fixedPointFree]

/-- **Hexagrammum totals from the census.** The `95` points (and `95` lines) of the
    `(95₃, 95₃)` configuration derived directly from the proven class cardinalities via the
    2:1 outer-automorphism pairing (self-paired at the triple-transposition class): the
    `120` six-cycles give `60` Pascal lines, the `40` double-3-cycles give `20` Steiner
    points, and the `15` triple transpositions are self-paired — `60 + 20 + 15 = 95`. This
    sources the totals from the machine-checked census rather than as bare numerals. -/
theorem hexagrammum_total_from_census :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => IsSixCycle σ)).card / 2
      + (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => IsDoubleThreeCycle σ)).card / 2
      + (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => IsTripleTransposition σ)).card
      = 95 := by
  simp only [card_sixCycles, card_doubleThreeCycles, card_tripleTranspositions]

/-! ### Pairwise disjointness of the census classes

`fixedPointFree_census_sum` and `census_cards_sum_eq_fixedPointFree` note in prose that
the exact count "forces the four classes to be pairwise disjoint", but that disjointness
is never itself formalized. The two results below supply it: the class predicates are
pairwise mutually exclusive, so — together with the cover `fixedPointFree_iff_census` —
the census is a genuine *partition* of the derangements of `Fin 6`. -/

/-- **The four census classes are pairwise mutually exclusive.**  No permutation of `Sym(6)`
    satisfies two of the fixed-point-free cycle-type predicates at once: `IsSixCycle`,
    `IsFourTwoCycle`, `IsDoubleThreeCycle`, and `IsTripleTransposition` are pairwise
    incompatible.  This is the disjointness that `fixedPointFree_census_sum` /
    `census_cards_sum_eq_fixedPointFree` invoke in prose but do not formalize; with the cover
    `fixedPointFree_iff_census` it upgrades the census to a partition of `derangements (Fin 6)`. -/
theorem census_classes_pairwise_exclusive : ∀ σ : Equiv.Perm (Fin 6),
    ¬(IsSixCycle σ ∧ IsFourTwoCycle σ) ∧
    ¬(IsSixCycle σ ∧ IsDoubleThreeCycle σ) ∧
    ¬(IsSixCycle σ ∧ IsTripleTransposition σ) ∧
    ¬(IsFourTwoCycle σ ∧ IsDoubleThreeCycle σ) ∧
    ¬(IsFourTwoCycle σ ∧ IsTripleTransposition σ) ∧
    ¬(IsDoubleThreeCycle σ ∧ IsTripleTransposition σ) := by
  native_decide

/-- **The three Hexagrammum classes are pairwise disjoint as Finsets.**  Derived from
    `census_classes_pairwise_exclusive` via `Finset.disjoint_filter`: the six-cycle,
    double-3-cycle, and triple-transposition filters pairwise share no permutation.  This is
    the combinatorial fact underlying `census_cards_sum_eq_fixedPointFree` and
    `hexagrammum_total_from_census`: the `120 / 40 / 15` counts add with no overlap, so the
    `60 + 20 + 15 = 95` configuration totals are genuine (non-double-counted) sums. -/
theorem hexagrammum_classes_disjoint :
    Disjoint (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => IsSixCycle σ))
             (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => IsDoubleThreeCycle σ)) ∧
    Disjoint (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => IsSixCycle σ))
             (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => IsTripleTransposition σ)) ∧
    Disjoint (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => IsDoubleThreeCycle σ))
             (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => IsTripleTransposition σ)) :=
  ⟨Finset.disjoint_filter.mpr
      (fun σ _ h1 h2 => (census_classes_pairwise_exclusive σ).2.1 ⟨h1, h2⟩),
   Finset.disjoint_filter.mpr
      (fun σ _ h1 h2 => (census_classes_pairwise_exclusive σ).2.2.1 ⟨h1, h2⟩),
   Finset.disjoint_filter.mpr
      (fun σ _ h1 h2 => (census_classes_pairwise_exclusive σ).2.2.2.2.2 ⟨h1, h2⟩)⟩

/-! ### Sign (parity) structure of the census

The census fixes the *sizes* of the four fixed-point-free classes; it does not
record their **parity**. Each cycle type has a uniform sign, and the split of the
derangements of `Fin 6` into even (`A₆`) and odd permutations is visible in the
Hexagrammum indexing:

* the **6-cycles** (Pascal lines / Kirkman points) are **odd** — a 6-cycle is a
  product of 5 transpositions;
* the **(2,2,2)** class (Plücker lines / Salmon points) is **odd** — three
  transpositions;
* the **(3,3)** class (Steiner points / Cayley lines) is **even** — two 3-cycles,
  each even;
* the geometrically-inert **(4,2)** class is **even** — a 4-cycle (odd) times a
  transposition (odd).

So the two *odd* fixed-point-free classes are exactly the ones carrying the
Pascal/Kirkman and Plücker/Salmon objects, while both *even* classes are the
Steiner/Cayley class and the inert `(4,2)` class. Numerically the derangements
split as `120 + 15 = 135` odd against `90 + 40 = 130` even. -/

/-- Every **6-cycle** of `Sym(6)` is an **odd** permutation (`sign = -1`): it is a
    product of five transpositions. These are the Pascal-line / Kirkman-point class. -/
theorem sixCycle_sign :
    ∀ σ : Equiv.Perm (Fin 6), IsSixCycle σ → Equiv.Perm.sign σ = -1 := by
  native_decide

/-- Every `(4,2)` permutation of `Sym(6)` is **even** (`sign = 1`): a 4-cycle
    (odd) composed with a disjoint transposition (odd). This is the geometrically
    inert fixed-point-free class. -/
theorem fourTwo_sign :
    ∀ σ : Equiv.Perm (Fin 6), IsFourTwoCycle σ → Equiv.Perm.sign σ = 1 := by
  native_decide

/-- Every **double 3-cycle** of `Sym(6)` is **even** (`sign = 1`): a product of two
    3-cycles, each of which is even. These are the Steiner-point / Cayley-line class. -/
theorem doubleThreeCycle_sign :
    ∀ σ : Equiv.Perm (Fin 6), IsDoubleThreeCycle σ → Equiv.Perm.sign σ = 1 := by
  native_decide

/-- Every **triple transposition** of `Sym(6)` is **odd** (`sign = -1`): a product
    of three transpositions. These are the Plücker-line / Salmon-point class. -/
theorem tripleTransposition_sign :
    ∀ σ : Equiv.Perm (Fin 6), IsTripleTransposition σ → Equiv.Perm.sign σ = -1 := by
  native_decide

/-- **Parity characterisation of the derangements.** Among the fixed-point-free
    permutations of `Sym(6)`, the **even** ones are exactly the `(4,2)` and `(3,3)`
    classes, and (by `fixedPointFree_iff_census`) the **odd** ones are exactly the
    6-cycles and triple transpositions. Equivalently: the Steiner/Cayley class and
    the inert `(4,2)` class make up `A₆ ∩ derangements`, while the Pascal/Kirkman
    and Plücker/Salmon classes are the odd derangements. -/
theorem even_derangement_iff_census :
    ∀ σ : Equiv.Perm (Fin 6), FixedPointFree σ →
      (Equiv.Perm.sign σ = 1 ↔ (IsFourTwoCycle σ ∨ IsDoubleThreeCycle σ)) := by
  native_decide

/-- **130 even derangements.** The fixed-point-free permutations of `Sym(6)` lying
    in the alternating group `A₆` number `130 = 90 + 40` — the `(4,2)` class plus
    the `(3,3)` (Steiner) class. -/
theorem card_even_derangements :
    (Finset.univ.filter
      (fun σ : Equiv.Perm (Fin 6) => FixedPointFree σ ∧ Equiv.Perm.sign σ = 1)).card = 130 := by
  native_decide

/-- **135 odd derangements.** The fixed-point-free permutations of `Sym(6)` outside
    `A₆` number `135 = 120 + 15` — the six-cycle (Pascal/Kirkman) class plus the
    triple-transposition (Plücker/Salmon) class. -/
theorem card_odd_derangements :
    (Finset.univ.filter
      (fun σ : Equiv.Perm (Fin 6) => FixedPointFree σ ∧ Equiv.Perm.sign σ = -1)).card = 135 := by
  native_decide

/-- **Parity split closure.** The even and odd derangement counts sum to `D₆ = 265`:
    `130 + 135 = 265`. Since `sign` takes only the values `±1`, this partitions the
    derangements of `Fin 6` into the two parity halves with no remainder — the
    `A₆`-refinement of `card_fixedPointFree`. -/
theorem derangement_parity_split : 130 + 135 = 265 := by norm_num

end PascalsHexagonOQ03Incomplete01
