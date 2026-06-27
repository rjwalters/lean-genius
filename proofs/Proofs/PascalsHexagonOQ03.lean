import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

import Proofs.PascalsHexagon

/-!
# Hexagrammum Mysticum — The 60-Pascal-Line Configuration (S1 Scaffold)

## Open question

Parent: `pascals-hexagon` (Pascal's Hexagon Theorem, Wiedijk #28).
`conclusion.openQuestions[2]`:

> Can the 60-Pascal-line configuration be formalized, including Steiner
> and Kirkman point counts?

## Resolution claim (S1)

**YES** — the combinatorial backbone of the Hexagrammum Mysticum is
formalizable. Six points on a conic admit `|Sym(6) / D_6| = 60` distinct
hexagonal labelings, each yielding a Pascal line via the parent theorem.
The Steiner and Kirkman point counts (20 and 60) follow from finite
enumeration plus a concurrence proof on representative triples.

## Mathematical statement

Let `A, B, C, D, E, F` be six points on a non-degenerate conic.

* The symmetric group `Sym(6)` of order 720 acts on the orderings of
  these six points.
* Two orderings produce the same Pascal line iff they differ by a
  cyclic rotation (6 elements) or a reversal (factor of 2) — i.e.,
  by an element of the dihedral subgroup `D_6` of order 12.
* Hence the number of distinct Pascal lines is

  `|Sym(6) / D_6| = 720 / 12 = 60`.

The 60 Pascal lines exhibit a rich incidence structure (Hexagrammum
Mysticum):

* **60 Pascal lines** (one per hexagonal labeling).
* **20 Steiner points** (concurrent intersection of 3 Pascal lines each).
* **60 Kirkman points** (also triples of Pascal lines, combinatorially
  distinct from Steiner triples).
* **15 Plücker lines** (4 Kirkman points each).
* **15 Salmon points** (concurrences of Plücker lines).

## S1 deliverable

* `hexRot`, `hexRev` — concrete cyclic rotation and reversal on `Fin 6`.
* `hexagonalGroup := Subgroup.closure {hexRot, hexRev}` — the dihedral
  subgroup of `Sym(6)`.
* `HexagonLabeling := Sym(6) ⧸ hexagonalGroup` — the type of hexagonal
  labelings.
* `card_sym6 = 720` — proved by `native_decide`.
* `card_hexagonalGroup = 12` — **OQ-03-OQ-01** (S3d, proved via the
  dihedral homomorphism `dihedralHomToSym6`).
* `card_hexagon_labelings = 60` — follows from the previous two by
  Lagrange (proved).
* `pascalLine` — Pascal-line map from labelings, **OQ-03-OQ-02**: total,
  defined via the canonical coset representative `lbl.out'` (the
  representative-independence / full well-definedness remains future work).
* `SteinerPoint`, `KirkmanPoint` — structures encoding the
  concurrence-triple data.
* `steiner_count_eq_20`, `kirkman_count_eq_60` — main count statements
  for **OQ-03-OQ-03** and **OQ-03-OQ-04** (sorry).

## Sub-OQ decomposition

* **OQ-03-OQ-01** (**PROVED — S3d**): `card_hexagonalGroup = 12`.
  Constructed the homomorphism
  `dihedralHomToSym6 : DihedralGroup 6 →* Equiv.Perm (Fin 6)` sending
  `r i ↦ hexRot ^ i.val` and `sr i ↦ hexRev * hexRot ^ i.val`, proved
  injectivity (via `orderOf_hexRot = 6` and `hexRev_ne_hexRot_pow_of_lt`),
  proved the range equals `hexagonalGroup`, and concluded
  `Nat.card hexagonalGroup = Nat.card (DihedralGroup 6) = 12` via
  `MonoidHom.ofInjective` + `Nat.card_congr` + `DihedralGroup.nat_card`.
  The dependent claim `card_hexagon_labelings = 60` follows by Lagrange
  (`Subgroup.card_eq_card_quotient_mul_card_subgroup`).

* **OQ-03-OQ-02** (~100 lines): `pascalLine` definition and
  well-definedness on the quotient. Given `lbl : HexagonLabeling`,
  pick a representative `π : Equiv.Perm (Fin 6)`, define the permuted
  hexagon `π · hex`, and apply `pascal_hexagon_theorem` to obtain the
  Pascal line. Well-definedness: two `D_6`-equivalent permutations
  yield the same Pascal line (a cyclic rotation permutes
  `(pascalP, pascalQ, pascalR)` cyclically; a reversal swaps two).

* **OQ-03-OQ-03** (~400 lines): `steiner_count_eq_20`. Strategy:
  enumerate the 20 Steiner triples explicitly as a `Finset` of
  3-subsets of `HexagonLabeling`. Prove concurrence for one
  representative triple via either the Cayley-Bacharach axiom or a
  symbolic coordinate computation (`ring`/`polyrith`); the rest
  follow by an `S_6`-symmetry argument.

* **OQ-03-OQ-04** (~400 lines): `kirkman_count_eq_60`. Analogous to
  OQ-03-OQ-03 but with the Kirkman triple combinatorics (each Kirkman
  point lies on a different family of triples). The combinatorial
  pattern is documented in Conway & Ryba 2012, "The Pascal Mysticum
  Demystified", which uses the outer automorphism of `S_6`.

* **OQ-03-OQ-05** (optional, ~200 lines): Cayley lines (4 lines of 5
  Steiner points each), Plücker lines, and Salmon points.

## References

* Pascal (1639); Steiner (1827); Kirkman (1849); Cayley (1849).
* Salmon, *Conic Sections* (1879).
* Conway & Ryba, *The Pascal Mysticum Demystified* (2012).
* Wiedijk #28.
-/

namespace PascalsHexagonOQ03

set_option linter.unusedVariables false

-- ============================================================
-- PART 1: Cyclic Rotation and Reversal on Fin 6
-- ============================================================

/-- Cyclic rotation of `Fin 6` by one position: `i ↦ i + 1 mod 6`.
    This is Mathlib's `finRotate 6`. -/
def hexRot : Equiv.Perm (Fin 6) := finRotate 6

/-- Reversal of `Fin 6`: `i ↦ 5 - i`. Uses Mathlib's `Fin.rev` whose
    involutivity is `Fin.rev_rev`. -/
def hexRev : Equiv.Perm (Fin 6) where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := Fin.rev_rev
  right_inv := Fin.rev_rev

-- ============================================================
-- PART 2: The Dihedral Subgroup of Sym(6)
-- ============================================================

/-- The dihedral subgroup of `Sym(6)` generated by cyclic rotation
    and reversal of `Fin 6`. It is isomorphic to `DihedralGroup 6`,
    hence has order 12.

    (Cardinality proved in `card_hexagonalGroup`, deferred to
    **OQ-03-OQ-01**.) -/
def hexagonalGroup : Subgroup (Equiv.Perm (Fin 6)) :=
  Subgroup.closure {hexRot, hexRev}

/-- The cyclic-rotation generator lies in `hexagonalGroup`. -/
theorem hexRot_mem_hexagonalGroup : hexRot ∈ hexagonalGroup := by
  unfold hexagonalGroup
  exact Subgroup.subset_closure (Set.mem_insert _ _)

/-- The reversal generator lies in `hexagonalGroup`. -/
theorem hexRev_mem_hexagonalGroup : hexRev ∈ hexagonalGroup := by
  unfold hexagonalGroup
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

-- ============================================================
-- PART 2b: Dihedral Relations on `hexRot` and `hexRev` (S2)
-- ============================================================
-- The three relations below are the defining relations of `DihedralGroup 6`:
--   r^6 = 1,    s^2 = 1,    s r s = r⁻¹.
-- They are proved by concrete computation on `Equiv.Perm (Fin 6)`. The
-- S3 plan uses them to construct an injective monoid homomorphism
-- `DihedralGroup 6 →* Equiv.Perm (Fin 6)` whose image equals
-- `hexagonalGroup`, yielding `Nat.card hexagonalGroup = 12`.

/-- **Dihedral relation 1**: `hexRot` has order dividing 6. -/
theorem hexRot_pow_six : hexRot ^ 6 = 1 := by
  ext i
  fin_cases i <;> decide

/-- **Dihedral relation 2**: `hexRev` has order dividing 2 (is an involution).

    Note: in `Equiv.Perm (Fin 6)`, `x ^ 2 = x * x` definitionally, so this
    form is equivalent to `hexRev ^ 2 = 1`. -/
theorem hexRev_mul_self : hexRev * hexRev = 1 := by
  ext i
  fin_cases i <;> decide

/-- **Dihedral relation 3** (rotation conjugates to its inverse under reversal):
    `hexRev * hexRot * hexRev = hexRot⁻¹`. -/
theorem hexRev_hexRot_hexRev : hexRev * hexRot * hexRev = hexRot⁻¹ := by
  ext i
  fin_cases i <;> decide

-- ============================================================
-- PART 2c: Order of `hexRot` and `hexRev` (S3a)
-- ============================================================
-- Sharpens `hexRot_pow_six` and `hexRev_mul_self` to exact orders.
-- These two facts plus `hexRev_hexRot_hexRev` give the standard injectivity
-- argument for the dihedral homomorphism `DihedralGroup 6 →* Sym(6)` (S3b).
-- (Reason: `orderOf hexRot = 6` and `orderOf hexRev = 2` together with the
-- conjugation relation force the 12 elements `{hexRot^i, hexRev * hexRot^i :
-- i ∈ Fin 6}` to be pairwise distinct.)

/-- The non-trivial powers of `hexRot` below the 6th are not the identity.
    Combined with `hexRot_pow_six`, this pins `orderOf hexRot` to exactly 6.

    Argument order matches `Mathlib.GroupTheory.OrderOfElement.orderOf_eq_iff`:
    `m < n` first, then `0 < m`. -/
theorem hexRot_pow_lt_six_ne_one :
    ∀ m, m < 6 → 0 < m → hexRot ^ m ≠ 1 := by
  intro m hlt hm h
  interval_cases m
  all_goals
    exact absurd (congrArg (fun (e : Equiv.Perm (Fin 6)) => e 0) h)
      (by native_decide)

/-- **`orderOf hexRot = 6`** — the rotation has order exactly 6.
    Direct upgrade of `hexRot_pow_six` using `hexRot_pow_lt_six_ne_one`. -/
theorem orderOf_hexRot : orderOf hexRot = 6 := by
  apply (orderOf_eq_iff (by norm_num)).mpr
  exact ⟨hexRot_pow_six, hexRot_pow_lt_six_ne_one⟩

/-- **`orderOf hexRev = 2`** — the reversal is an involution distinct from 1.
    Uses `hexRev_mul_self` (from `pow_two`) and `hexRev_ne_one`. -/
theorem orderOf_hexRev : orderOf hexRev = 2 := by
  apply (orderOf_eq_iff (by norm_num)).mpr
  refine ⟨?_, ?_⟩
  · rw [pow_two]; exact hexRev_mul_self
  · intro m hlt hm
    interval_cases m
    rw [pow_one]
    exact hexRev_ne_one

-- ============================================================
-- PART 2d: Semiconjugacy and Power-Inversion (S3b-prep)
-- ============================================================
-- The S2 dihedral relation `hexRev * hexRot * hexRev = hexRot⁻¹` extends
-- to all powers via `SemiconjBy`. The four lemmas below give the form
-- needed for the four cases of `map_mul'` in the S3c homomorphism
-- `DihedralGroup 6 →* Equiv.Perm (Fin 6)` (built from `hexRot, hexRev`):
--   • `r i * sr j` requires pushing `hexRot ^ i.val` past `hexRev`.
--   • `sr i * r j` and `sr i * sr j` similarly need the powered form.
-- All four are pure group-theory consequences of S2 + S3a; no new
-- computation on `Equiv.Perm (Fin 6)` is required.

/-- `hexRev` is self-inverse: `hexRev⁻¹ = hexRev`.
    Immediate from `hexRev_mul_self : hexRev * hexRev = 1`. -/
theorem hexRev_inv : hexRev⁻¹ = hexRev :=
  inv_eq_of_mul_eq_one_right hexRev_mul_self

/-- **Semiconjugacy form of the S2 relation**: `hexRev * hexRot = hexRot⁻¹ * hexRev`.
    Equivalent to `hexRev_hexRot_hexRev` after right-multiplying by `hexRev`
    and using `hexRev_mul_self`. Phrased via Mathlib's `SemiconjBy` so the
    powered form follows by `SemiconjBy.pow_right`. -/
theorem hexRev_semiconj_hexRot : SemiconjBy hexRev hexRot hexRot⁻¹ := by
  unfold SemiconjBy
  calc hexRev * hexRot
      = hexRev * hexRot * 1 := by rw [mul_one]
    _ = hexRev * hexRot * (hexRev * hexRev) := by rw [← hexRev_mul_self]
    _ = (hexRev * hexRot * hexRev) * hexRev := by rw [← mul_assoc]
    _ = hexRot⁻¹ * hexRev := by rw [hexRev_hexRot_hexRev]

/-- **Powered semiconjugacy**: `hexRev * hexRot ^ n = (hexRot ^ n)⁻¹ * hexRev`.
    Push form of the dihedral conjugation relation; obtained from
    `hexRev_semiconj_hexRot` via `SemiconjBy.pow_right` plus `inv_pow`. -/
theorem hexRev_semiconj_hexRot_pow (n : ℕ) :
    hexRev * hexRot ^ n = (hexRot ^ n)⁻¹ * hexRev := by
  have h : SemiconjBy hexRev (hexRot ^ n) (hexRot⁻¹ ^ n) :=
    hexRev_semiconj_hexRot.pow_right n
  -- `SemiconjBy.eq` extracts the equation `a * x = y * a`; rewrite `hexRot⁻¹ ^ n` to `(hexRot^n)⁻¹`.
  rw [inv_pow] at h
  exact h.eq

/-- **Conjugation-by-`hexRev` powered form**:
    `hexRev * hexRot ^ n * hexRev = (hexRot ^ n)⁻¹`.
    Combines `hexRev_semiconj_hexRot_pow` with `hexRev_mul_self` to cancel
    the trailing pair. This is the workhorse for the `sr * sr` and `r * sr`
    cases of the S3c homomorphism's `map_mul'`. -/
theorem hexRev_hexRot_pow_hexRev (n : ℕ) :
    hexRev * hexRot ^ n * hexRev = (hexRot ^ n)⁻¹ := by
  rw [hexRev_semiconj_hexRot_pow n, mul_assoc, hexRev_mul_self, mul_one]

-- ============================================================
-- PART 2e: ZMod-Indexed Power Helpers (S3c-prep-2)
-- ============================================================
-- The S3c homomorphism `φ : DihedralGroup 6 →* Equiv.Perm (Fin 6)`
-- will map `r i ↦ hexRot ^ i.val` and
-- `sr i ↦ hexRev * hexRot ^ i.val`. Its four `map_mul'` cases each
-- reduce to a single rewrite of the form `hexRot ^ (i ± j).val = …`
-- where the `±` and `.val` interact via the `ZMod 6` modular
-- wraparound (`hexRot ^ 6 = 1` plus `(i + j).val ≡ i.val + j.val [MOD 6]`).
-- The three lemmas below package the additive, negation, and
-- subtractive forms once, so that S3d can discharge each
-- `map_mul'` case in a single `rw` chain.
--
-- Mechanism: combine `ZMod.val_add` (which gives
-- `(i + j).val = (i.val + j.val) % 6` at `n = 6`) with
-- `pow_mod_orderOf hexRot _` (which collapses `hexRot ^ (k % 6) = hexRot ^ k`
-- using `orderOf_hexRot = 6`, S3a).
--
-- No new Mathlib dependencies beyond what S2/S3a/S3b-prep already
-- pull in: `pow_add`, `pow_zero`, `pow_mod_orderOf`
-- (`Mathlib/GroupTheory/OrderOfElement.lean:252` at pinned rev
-- `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`), `ZMod.val_add`,
-- `ZMod.val_zero`, `add_neg_cancel`, and `eq_inv_of_mul_eq_one_left`.

/-- **Additive form**: the `ZMod 6` sum of exponents commutes with
    `hexRot ^ _.val`. Equivalent to saying that the map
    `ZMod 6 → Equiv.Perm (Fin 6)`, `i ↦ hexRot ^ i.val`, respects
    addition; this is the `r i * r j = r (i + j)` reduction in the
    S3c homomorphism. -/
private lemma hexRot_pow_zmod_val_add (i j : ZMod 6) :
    hexRot ^ (i + j).val = hexRot ^ i.val * hexRot ^ j.val := by
  rw [← pow_add]
  -- `ZMod.val_add` gives `(i + j).val = (i.val + j.val) % 6`; then
  -- `pow_mod_orderOf` with `orderOf_hexRot = 6` collapses the `% 6`.
  rw [ZMod.val_add i j, ← orderOf_hexRot, pow_mod_orderOf]

/-- **Negation form**: `(hexRot ^ i.val)⁻¹ = hexRot ^ (-i).val`.
    Equivalent to saying that the map `i ↦ hexRot ^ i.val` respects
    additive inversion. Derived from `hexRot_pow_zmod_val_add` at
    `j = -i` via `add_neg_cancel` + `ZMod.val_zero` + `pow_zero`. -/
private lemma hexRot_pow_zmod_val_neg (i : ZMod 6) :
    (hexRot ^ i.val)⁻¹ = hexRot ^ (-i).val := by
  have h := hexRot_pow_zmod_val_add i (-i)
  rw [add_neg_cancel, ZMod.val_zero, pow_zero] at h
  -- `h : 1 = hexRot ^ i.val * hexRot ^ (-i).val`
  exact (eq_inv_of_mul_eq_one_left h.symm).symm

/-- **Subtractive form**:
    `(hexRot ^ i.val)⁻¹ * hexRot ^ j.val = hexRot ^ (j - i).val`.
    Combines `hexRot_pow_zmod_val_neg` (replace the inverse with a
    negated `.val`) with `hexRot_pow_zmod_val_add` (collapse the
    additive form) and `neg_add_eq_sub` (rewrite `(-i) + j` as
    `j - i`). This is the rewrite that lets the `sr i * sr j` case
    of the S3c homomorphism's `map_mul'` collapse after applying
    `hexRev_hexRot_pow_hexRev` to the central
    `hexRev * hexRot ^ i.val * hexRev` triple. -/
private lemma hexRot_pow_zmod_val_sub (j i : ZMod 6) :
    (hexRot ^ i.val)⁻¹ * hexRot ^ j.val = hexRot ^ (j - i).val := by
  rw [hexRot_pow_zmod_val_neg]
  rw [← hexRot_pow_zmod_val_add (-i) j, neg_add_eq_sub]

-- ============================================================
-- PART 2f: Anti-Push of `hexRev` Past `hexRot ^ n` (S3d-prep)
-- ============================================================
-- The S3b-prep `hexRev_semiconj_hexRot_pow` gives the "push-from-left"
-- form `hexRev * hexRot^n = (hexRot^n)⁻¹ * hexRev`. The S3d `map_mul'`
-- case `r i * sr j ↦ sr (j - i)` also needs the "push-from-right" form
-- `hexRot^n * hexRev = hexRev * (hexRot^n)⁻¹`, derived below in three
-- rewrites from `hexRev_hexRot_pow_hexRev` (S3b-prep) and
-- `hexRev_mul_self` (S2).

/-- **Anti-push form**: `hexRot ^ n * hexRev = hexRev * (hexRot ^ n)⁻¹`.
    Companion to `hexRev_semiconj_hexRot_pow` for the `r * sr`
    `map_mul'` case of the S3d homomorphism. Proved by left-multiplying
    `hexRev_hexRot_pow_hexRev` by `hexRev` and collapsing
    `hexRev * hexRev` via `hexRev_mul_self`. -/
private theorem hexRot_pow_mul_hexRev (n : ℕ) :
    hexRot ^ n * hexRev = hexRev * (hexRot ^ n)⁻¹ := by
  rw [← hexRev_hexRot_pow_hexRev n, ← mul_assoc, ← mul_assoc, hexRev_mul_self, one_mul]

-- ============================================================
-- PART 2g: `hexRev` Is Not a Power of `hexRot` (S3d-prep)
-- ============================================================
-- For injectivity of the S3d homomorphism, the only non-trivial case
-- is `sr i ↦ 1`: this would force `hexRev = (hexRot ^ i.val)⁻¹`, which
-- via `hexRot_pow_zmod_val_neg` equals `hexRot ^ (-i).val` — a power
-- of `hexRot` with exponent in `[0, 6)`. The lemma below rules out
-- this case by explicit enumeration over the six possible exponents.

/-- **Disjointness of rotations and reflections**: `hexRev` is not equal
    to any of the six powers `hexRot ^ 0, …, hexRot ^ 5`.
    Verified by `native_decide` on each explicit exponent. -/
private lemma hexRev_ne_hexRot_pow_of_lt (k : ℕ) (hk : k < 6) :
    hexRev ≠ hexRot ^ k := by
  intro h
  interval_cases k <;> exact absurd h (by native_decide)

-- ============================================================
-- PART 2h: The Dihedral Homomorphism (S3d)
-- ============================================================
-- Build `dihedralHomToSym6 : DihedralGroup 6 →* Equiv.Perm (Fin 6)`
-- sending `r i ↦ hexRot ^ i.val` and `sr i ↦ hexRev * hexRot ^ i.val`.
-- All four `map_mul'` cases close mechanically using the S2/S3a/S3b-prep/
-- S3c-prep-2 + S3d-prep lemmas (no new computation on `Equiv.Perm`):
--   • `r * r`:  `hexRot_pow_zmod_val_add`
--   • `r * sr`: `hexRot_pow_mul_hexRev` + `hexRot_pow_zmod_val_sub`
--   • `sr * r`: `hexRot_pow_zmod_val_add` (after a single `mul_assoc`)
--   • `sr * sr`: `hexRev_hexRot_pow_hexRev` + `hexRot_pow_zmod_val_sub`

/-- The monoid homomorphism `DihedralGroup 6 →* Equiv.Perm (Fin 6)`
    realising `hexagonalGroup` as the image of the abstract dihedral
    group of order 12. Rotations `r i` map to powers of `hexRot`;
    reflections `sr i` map to `hexRev` composed with a power of `hexRot`. -/
def dihedralHomToSym6 : DihedralGroup 6 →* Equiv.Perm (Fin 6) where
  toFun
    | DihedralGroup.r i => hexRot ^ i.val
    | DihedralGroup.sr i => hexRev * hexRot ^ i.val
  map_one' := by
    show hexRot ^ (0 : ZMod 6).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' := by
    intro x y
    cases x with
    | r i =>
      cases y with
      | r j =>
        show hexRot ^ (i + j).val = hexRot ^ i.val * hexRot ^ j.val
        exact hexRot_pow_zmod_val_add i j
      | sr j =>
        show hexRev * hexRot ^ (j - i).val = hexRot ^ i.val * (hexRev * hexRot ^ j.val)
        rw [← mul_assoc, hexRot_pow_mul_hexRev, mul_assoc, hexRot_pow_zmod_val_sub]
    | sr i =>
      cases y with
      | r j =>
        show hexRev * hexRot ^ (i + j).val = hexRev * hexRot ^ i.val * hexRot ^ j.val
        rw [mul_assoc, ← hexRot_pow_zmod_val_add]
      | sr j =>
        show hexRot ^ (j - i).val = hexRev * hexRot ^ i.val * (hexRev * hexRot ^ j.val)
        rw [← mul_assoc, hexRev_hexRot_pow_hexRev, hexRot_pow_zmod_val_sub]

@[simp] private lemma dihedralHomToSym6_r (i : ZMod 6) :
    dihedralHomToSym6 (DihedralGroup.r i) = hexRot ^ i.val := rfl

@[simp] private lemma dihedralHomToSym6_sr (i : ZMod 6) :
    dihedralHomToSym6 (DihedralGroup.sr i) = hexRev * hexRot ^ i.val := rfl

/-- **Injectivity of `dihedralHomToSym6`**.

    * `r i ↦ 1`: forces `hexRot ^ i.val = 1`; by `orderOf_hexRot = 6`
      and `i.val < 6`, conclude `i.val = 0`, hence `i = 0` and
      `r i = r 0 = 1`.
    * `sr i ↦ 1`: forces `hexRev = (hexRot ^ i.val)⁻¹`; the inverse
      rewrites via `hexRot_pow_zmod_val_neg` to a power of `hexRot`
      with exponent `< 6`, contradicting
      `hexRev_ne_hexRot_pow_of_lt`. -/
theorem dihedralHomToSym6_injective :
    Function.Injective dihedralHomToSym6 := by
  rw [injective_iff_map_eq_one]
  intro g hg
  cases g with
  | r i =>
    -- `hg : hexRot ^ i.val = 1`; conclude `i = 0`.
    have hi_lt : i.val < 6 := ZMod.val_lt i
    have hi_dvd : orderOf hexRot ∣ i.val := orderOf_dvd_of_pow_eq_one hg
    rw [orderOf_hexRot] at hi_dvd
    have hi_val_zero : i.val = 0 := Nat.eq_zero_of_dvd_of_lt hi_dvd hi_lt
    have : i = 0 := (ZMod.val_eq_zero i).mp hi_val_zero
    rw [this]; rfl
  | sr i =>
    -- `hg : hexRev * hexRot ^ i.val = 1` ⇒ contradiction.
    exfalso
    have h1 : hexRev = (hexRot ^ i.val)⁻¹ :=
      eq_inv_of_mul_eq_one_right hg
    rw [hexRot_pow_zmod_val_neg] at h1
    exact hexRev_ne_hexRot_pow_of_lt (-i).val (ZMod.val_lt _) h1

/-- **Range equals `hexagonalGroup`**.

    `≤`: both `hexRot ^ i.val` and `hexRev * hexRot ^ i.val` lie in
    `hexagonalGroup` (a subgroup containing the two generators).

    `≥`: `hexagonalGroup = closure {hexRot, hexRev}` and both
    generators are images: `hexRot = dihedralHomToSym6 (r 1)` (via
    `(1 : ZMod 6).val = 1`) and `hexRev = dihedralHomToSym6 (sr 0)`
    (via `(0 : ZMod 6).val = 0`). -/
theorem dihedralHomToSym6_range :
    dihedralHomToSym6.range = hexagonalGroup := by
  apply le_antisymm
  · -- `≤`: every image lies in `hexagonalGroup`.
    rintro _ ⟨g, rfl⟩
    cases g with
    | r i =>
      show hexRot ^ i.val ∈ hexagonalGroup
      exact pow_mem hexRot_mem_hexagonalGroup _
    | sr i =>
      show hexRev * hexRot ^ i.val ∈ hexagonalGroup
      exact mul_mem hexRev_mem_hexagonalGroup
              (pow_mem hexRot_mem_hexagonalGroup _)
  · -- `≥`: closure of two generators contained in range.
    show hexagonalGroup ≤ dihedralHomToSym6.range
    unfold hexagonalGroup
    rw [Subgroup.closure_le]
    intro x hx
    rcases (Set.mem_insert_iff.mp hx) with rfl | hx'
    · refine ⟨DihedralGroup.r 1, ?_⟩
      show hexRot ^ (1 : ZMod 6).val = hexRot
      have : (1 : ZMod 6).val = 1 := by decide
      rw [this, pow_one]
    · -- `x ∈ {hexRev}` ⇒ `x = hexRev`.
      rw [Set.mem_singleton_iff] at hx'
      subst hx'
      refine ⟨DihedralGroup.sr 0, ?_⟩
      show hexRev * hexRot ^ (0 : ZMod 6).val = hexRev
      rw [ZMod.val_zero, pow_zero, mul_one]

-- ============================================================
-- PART 3: Hexagon Labelings as Sym(6) ⧸ D_6
-- ============================================================

/-- A *hexagon labeling*: an equivalence class of permutations of the
    six hexagon vertices under cyclic rotation and reversal. Equivalently,
    a coset of `hexagonalGroup` in `Sym(6)`. -/
abbrev HexagonLabeling : Type :=
  Equiv.Perm (Fin 6) ⧸ hexagonalGroup

-- ============================================================
-- PART 4: Cardinality Facts
-- ============================================================

/-- `|Sym(6)| = 720`. -/
theorem card_sym6 : Fintype.card (Equiv.Perm (Fin 6)) = 720 := by
  native_decide

/-- **OQ-03-OQ-01**: the dihedral subgroup `hexagonalGroup` has order 12.

    Progress so far (S2 + S3a + S3b-prep, this PR adds the third):

    * S2 — dihedral defining relations on `(hexRot, hexRev)`:
      `hexRot_pow_six`, `hexRev_mul_self`, `hexRev_hexRot_hexRev`.
    * S3a — exact orders: `orderOf_hexRot` (= 6), `orderOf_hexRev` (= 2).
    * S3b-prep — powered semiconjugacy (this PR):
      `hexRev_inv`, `hexRev_semiconj_hexRot`, `hexRev_semiconj_hexRot_pow`,
      `hexRev_hexRot_pow_hexRev`. These extend the S2 conjugation
      relation from `n = 1` to all natural exponents.

    Together S2 + S3a + S3b-prep give the standard dihedral toolkit:
    the twelve elements `{hexRot ^ i, hexRev * hexRot ^ i : i ∈ Fin 6}`
    are pairwise distinct and the four `map_mul'` cases of the
    DihedralGroup-into-Sym(6) hom rewrite mechanically using these
    lemmas.

    **S3d completes** the program: `dihedralHomToSym6` (PART 2h) is the
    homomorphism, `dihedralHomToSym6_injective` gives injectivity, and
    `dihedralHomToSym6_range` shows the image equals `hexagonalGroup`.
    Together with `DihedralGroup.nat_card`, this yields
    `Nat.card hexagonalGroup = 2 * 6 = 12`. -/
theorem card_hexagonalGroup : Nat.card hexagonalGroup = 12 := by
  rw [← dihedralHomToSym6_range]
  rw [← Nat.card_congr (MonoidHom.ofInjective dihedralHomToSym6_injective).toEquiv]
  exact DihedralGroup.nat_card

/-- **Hexagrammum Mysticum count**: six points on a conic determine
    exactly 60 distinct hexagonal labelings, hence at most 60 Pascal lines.

    By Lagrange: `|Sym(6) ⧸ D_6| · |D_6| = |Sym(6)|`, so
    `|Sym(6) ⧸ D_6| = 720 / 12 = 60`.

    Follows from `card_sym6`, `card_hexagonalGroup`, and
    `Subgroup.card_eq_card_quotient_mul_card_subgroup`. -/
theorem card_hexagon_labelings : Nat.card HexagonLabeling = 60 := by
  have h_total :
      Nat.card (Equiv.Perm (Fin 6)) =
        Nat.card HexagonLabeling * Nat.card hexagonalGroup :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup hexagonalGroup
  rw [card_hexagonalGroup] at h_total
  have h_sym : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card]; exact card_sym6
  rw [h_sym] at h_total
  omega

-- ============================================================
-- PART 4b: Hexagon Relabeling Action (S4b ACT — toolkit for OQ-02)
-- ============================================================

/-- Index the six vertices of an inscribed hexagon as a function `Fin 6 → ProjPoint`.
    Sets up the relabeling action of `Sym(6)` on inscribed hexagons. -/
def hexVertex {C : Conic} (hex : InscribedHexagon C) : Fin 6 → ProjPoint
  | ⟨0, _⟩ => hex.A
  | ⟨1, _⟩ => hex.B
  | ⟨2, _⟩ => hex.C'
  | ⟨3, _⟩ => hex.D
  | ⟨4, _⟩ => hex.E
  | ⟨5, _⟩ => hex.F

/-- Conic-membership proof bundled with each vertex. -/
def hexVertex_onConic {C : Conic} (hex : InscribedHexagon C) :
    ∀ i : Fin 6, pointOnConic (hexVertex hex i) C
  | ⟨0, _⟩ => hex.hA
  | ⟨1, _⟩ => hex.hB
  | ⟨2, _⟩ => hex.hC
  | ⟨3, _⟩ => hex.hD
  | ⟨4, _⟩ => hex.hE
  | ⟨5, _⟩ => hex.hF

/-- Projective validity proof bundled with each vertex. -/
def hexVertex_valid {C : Conic} (hex : InscribedHexagon C) :
    ∀ i : Fin 6, ProjPoint.valid (hexVertex hex i)
  | ⟨0, _⟩ => hex.hAvalid
  | ⟨1, _⟩ => hex.hBvalid
  | ⟨2, _⟩ => hex.hCvalid
  | ⟨3, _⟩ => hex.hDvalid
  | ⟨4, _⟩ => hex.hEvalid
  | ⟨5, _⟩ => hex.hFvalid

/-- Relabel the vertices of an inscribed hexagon by a permutation `π : Sym(6)`.
    The conic-membership and projective-validity proofs transport along with the
    vertex permutation, so the result is again an `InscribedHexagon C`. This is
    the workhorse for **OQ-03-OQ-02**: the Pascal line of a hexagon labeling
    will be the Pascal line of the hexagon permuted by a representative of the
    labeling. -/
def permuteHexagon {C : Conic} (hex : InscribedHexagon C)
    (π : Equiv.Perm (Fin 6)) : InscribedHexagon C where
  A := hexVertex hex (π 0)
  B := hexVertex hex (π 1)
  C' := hexVertex hex (π 2)
  D := hexVertex hex (π 3)
  E := hexVertex hex (π 4)
  F := hexVertex hex (π 5)
  hA := hexVertex_onConic hex (π 0)
  hB := hexVertex_onConic hex (π 1)
  hC := hexVertex_onConic hex (π 2)
  hD := hexVertex_onConic hex (π 3)
  hE := hexVertex_onConic hex (π 4)
  hF := hexVertex_onConic hex (π 5)
  hAvalid := hexVertex_valid hex (π 0)
  hBvalid := hexVertex_valid hex (π 1)
  hCvalid := hexVertex_valid hex (π 2)
  hDvalid := hexVertex_valid hex (π 3)
  hEvalid := hexVertex_valid hex (π 4)
  hFvalid := hexVertex_valid hex (π 5)

-- ============================================================
-- PART 4c: Action of the Dihedral Generators on the Pascal Triple
--          (OQ-03-OQ-02 well-definedness backbone)
-- ============================================================

/- The well-definedness of `pascalLine` rests on how the two dihedral
   generators permute the three Pascal points `(P, Q, R)`.  Working in
   homogeneous coordinates (`lineThrough = lineIntersection = crossProduct`),
   antisymmetry of the cross product (`cross_anticomm`) gives the exact signs:

     hexRot : (P, Q, R) ↦ (Q,  R, -P)
     hexRev : (P, Q, R) ↦ (-Q, -P, R)

   Each generator therefore permutes the set `{[P], [Q], [R]}` of *projective*
   Pascal points (signs are invisible projectively).  Since `P, Q, R` are
   collinear (`pascal_hexagon_theorem`), they span a single projective Pascal
   line, which is consequently fixed by `hexRot`, `hexRev`, and hence by all of
   `hexagonalGroup = ⟨hexRot, hexRev⟩ ≅ D₆`.  This is the geometric backbone of
   the descent claim **OQ-03-OQ-02**.  (Promoting set-invariance of the three
   *projective* points to literal equality of the spanned `ProjLine` value
   additionally needs a notion of line-equality up to nonzero scalar together
   with a nondegeneracy hypothesis, and is deferred — see the `pascalLine`
   docstring below.) -/

/-- `hexRot` sends the first Pascal point to the second: `P' = Q`. -/
theorem pascalP_permuteHexagon_hexRot {C : Conic} (hex : InscribedHexagon C) :
    pascalP (permuteHexagon hex hexRot) = pascalQ hex := by
  show lineIntersection (lineThrough (hexVertex hex (hexRot 0)) (hexVertex hex (hexRot 1)))
        (lineThrough (hexVertex hex (hexRot 3)) (hexVertex hex (hexRot 4)))
      = lineIntersection (lineThrough hex.B hex.C') (lineThrough hex.E hex.F)
  rw [show hexRot 0 = 1 from by decide, show hexRot 1 = 2 from by decide,
      show hexRot 3 = 4 from by decide, show hexRot 4 = 5 from by decide]
  rfl

/-- `hexRot` sends the second Pascal point to the third: `Q' = R`. -/
theorem pascalQ_permuteHexagon_hexRot {C : Conic} (hex : InscribedHexagon C) :
    pascalQ (permuteHexagon hex hexRot) = pascalR hex := by
  show lineIntersection (lineThrough (hexVertex hex (hexRot 1)) (hexVertex hex (hexRot 2)))
        (lineThrough (hexVertex hex (hexRot 4)) (hexVertex hex (hexRot 5)))
      = lineIntersection (lineThrough hex.C' hex.D) (lineThrough hex.F hex.A)
  rw [show hexRot 1 = 2 from by decide, show hexRot 2 = 3 from by decide,
      show hexRot 4 = 5 from by decide, show hexRot 5 = 0 from by decide]
  rfl

/-- `hexRot` sends the third Pascal point to the negated first: `R' = -P`.
    The lone sign comes from one `cross_anticomm`. -/
theorem pascalR_permuteHexagon_hexRot {C : Conic} (hex : InscribedHexagon C) :
    pascalR (permuteHexagon hex hexRot) = -(pascalP hex) := by
  show lineIntersection (lineThrough (hexVertex hex (hexRot 2)) (hexVertex hex (hexRot 3)))
        (lineThrough (hexVertex hex (hexRot 5)) (hexVertex hex (hexRot 0)))
      = -(lineIntersection (lineThrough hex.A hex.B) (lineThrough hex.D hex.E))
  rw [show hexRot 2 = 3 from by decide, show hexRot 3 = 4 from by decide,
      show hexRot 5 = 0 from by decide, show hexRot 0 = 1 from by decide]
  show lineIntersection (lineThrough hex.D hex.E) (lineThrough hex.A hex.B)
      = -(lineIntersection (lineThrough hex.A hex.B) (lineThrough hex.D hex.E))
  exact (cross_anticomm (lineThrough hex.A hex.B) (lineThrough hex.D hex.E)).symm

/-- `hexRev` sends the first Pascal point to the negated second: `P' = -Q`.
    Both inner factors flip sign (cancelling under bilinearity) and one outer
    `cross_anticomm` remains; proved by coordinate expansion. -/
theorem pascalP_permuteHexagon_hexRev {C : Conic} (hex : InscribedHexagon C) :
    pascalP (permuteHexagon hex hexRev) = -(pascalQ hex) := by
  show lineIntersection (lineThrough (hexVertex hex (hexRev 0)) (hexVertex hex (hexRev 1)))
        (lineThrough (hexVertex hex (hexRev 3)) (hexVertex hex (hexRev 4)))
      = -(lineIntersection (lineThrough hex.B hex.C') (lineThrough hex.E hex.F))
  rw [show hexRev 0 = 5 from by decide, show hexRev 1 = 4 from by decide,
      show hexRev 3 = 2 from by decide, show hexRev 4 = 1 from by decide]
  show lineIntersection (lineThrough hex.F hex.E) (lineThrough hex.C' hex.B)
      = -(lineIntersection (lineThrough hex.B hex.C') (lineThrough hex.E hex.F))
  ext i
  fin_cases i <;>
    simp only [lineIntersection, lineThrough, cross_apply, Pi.neg_apply,
               Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue] <;>
    ring

/-- `hexRev` sends the second Pascal point to the negated first: `Q' = -P`. -/
theorem pascalQ_permuteHexagon_hexRev {C : Conic} (hex : InscribedHexagon C) :
    pascalQ (permuteHexagon hex hexRev) = -(pascalP hex) := by
  show lineIntersection (lineThrough (hexVertex hex (hexRev 1)) (hexVertex hex (hexRev 2)))
        (lineThrough (hexVertex hex (hexRev 4)) (hexVertex hex (hexRev 5)))
      = -(lineIntersection (lineThrough hex.A hex.B) (lineThrough hex.D hex.E))
  rw [show hexRev 1 = 4 from by decide, show hexRev 2 = 3 from by decide,
      show hexRev 4 = 1 from by decide, show hexRev 5 = 0 from by decide]
  show lineIntersection (lineThrough hex.E hex.D) (lineThrough hex.B hex.A)
      = -(lineIntersection (lineThrough hex.A hex.B) (lineThrough hex.D hex.E))
  ext i
  fin_cases i <;>
    simp only [lineIntersection, lineThrough, cross_apply, Pi.neg_apply,
               Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue] <;>
    ring

/-- `hexRev` fixes the third Pascal point: `R' = R`.  The two inner sign flips
    cancel and no outer flip is incurred. -/
theorem pascalR_permuteHexagon_hexRev {C : Conic} (hex : InscribedHexagon C) :
    pascalR (permuteHexagon hex hexRev) = pascalR hex := by
  show lineIntersection (lineThrough (hexVertex hex (hexRev 2)) (hexVertex hex (hexRev 3)))
        (lineThrough (hexVertex hex (hexRev 5)) (hexVertex hex (hexRev 0)))
      = lineIntersection (lineThrough hex.C' hex.D) (lineThrough hex.F hex.A)
  rw [show hexRev 2 = 3 from by decide, show hexRev 3 = 2 from by decide,
      show hexRev 5 = 0 from by decide, show hexRev 0 = 5 from by decide]
  show lineIntersection (lineThrough hex.D hex.C') (lineThrough hex.A hex.F)
      = lineIntersection (lineThrough hex.C' hex.D) (lineThrough hex.F hex.A)
  ext i
  fin_cases i <;>
    simp only [lineIntersection, lineThrough, cross_apply, Pi.neg_apply,
               Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue] <;>
    ring

-- ============================================================
-- PART 4d: Projective Line Equality of the Pascal Line under the Generators
--          (OQ-03-OQ-02: promoting set-invariance to ProjLine equality)
-- ============================================================

/- PART 4c established that `hexRot` / `hexRev` permute the *set*
   `{[P], [Q], [R]}` of projective Pascal points (the signs are invisible
   projectively).  Here we upgrade that to the literal statement that the
   spanned projective *line* is unchanged.  The right notion of "same
   projective line" for homogeneous line-vectors is parallelism, i.e. a
   vanishing cross product (for nonzero vectors this is equivalence up to a
   nonzero scalar):

     sameProjLine l m  :⟺  l ×₃ m = 0.

   The crux is the rotation case `P ×₃ Q ∥ Q ×₃ R`, which holds exactly
   because `P, Q, R` are collinear; the algebraic engine is the `BAC–CAB`
   identity `(P ×₃ Q) ×₃ (Q ×₃ R) = det(P, Q, R) • Q`. -/

/-- Two homogeneous line-vectors represent the **same projective line** exactly
    when they are parallel — their cross product vanishes.  For nonzero vectors
    this is equality of the underlying projective line (proportionality up to a
    nonzero scalar). -/
def sameProjLine (l m : ProjLine) : Prop := crossProduct l m = 0

/-- `sameProjLine` is reflexive: every line is parallel to itself. -/
theorem sameProjLine_refl (l : ProjLine) : sameProjLine l l := by
  unfold sameProjLine
  funext i
  fin_cases i <;>
    simp only [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Pi.zero_apply, Fin.isValue] <;>
    ring

/-- Negating a line-vector preserves the projective line: `l ∥ -l`. -/
theorem sameProjLine_neg_right (l : ProjLine) : sameProjLine l (-l) := by
  unfold sameProjLine
  funext i
  fin_cases i <;>
    simp only [cross_apply, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
               Matrix.head_cons, Pi.zero_apply, Fin.isValue] <;>
    ring

/-- Scaling a line-vector by any scalar preserves the projective line:
    `l ∥ c • l`.  (For `c ≠ 0` this is the full "up to nonzero scalar"
    equivalence; the cross-product characterisation makes even the degenerate
    `c = 0` case hold.) -/
theorem sameProjLine_smul_right (c : ℝ) (l : ProjLine) : sameProjLine l (c • l) := by
  unfold sameProjLine
  funext i
  fin_cases i <;>
    simp only [cross_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
               Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply, Fin.isValue] <;>
    ring

/-- **BAC–CAB specialisation.** For any three vectors in `ℝ³`,
    `(P ×₃ Q) ×₃ (Q ×₃ R) = det(P, Q, R) • Q`.  This is the vector identity
    `(a ×₃ b) ×₃ (c ×₃ d) = [a,b,d] c − [a,b,c] d` with `a = P, b = Q,
    c = Q, d = R`, where the companion term `[P,Q,Q] • R` vanishes.  A pure
    polynomial identity in the nine coordinates, closed by `ring`. -/
theorem cross_cross_eq_det_smul (P Q R : ProjPoint) :
    crossProduct (crossProduct P Q) (crossProduct Q R)
      = (threeVectorMatrix P Q R).det • Q := by
  funext i
  fin_cases i <;>
    simp only [cross_apply, threeVectorMatrix, Matrix.det_fin_three, Matrix.of_apply,
               Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
               Matrix.head_cons, Fin.isValue, Nat.reduceAdd, Fin.reduceFinMk] <;>
    ring

/-- **Rotation crux.** When `P, Q, R` are collinear the two candidate Pascal
    lines `P ×₃ Q` and `Q ×₃ R` are parallel — they are the *same* projective
    line.  This is the literal line-equality behind the `hexRot`
    set-invariance of PART 4c: collinearity forces `det(P,Q,R) = 0`, so the
    `BAC–CAB` identity collapses the cross of the two lines to zero. -/
theorem sameProjLine_of_collinear (P Q R : ProjPoint) (h : collinear P Q R) :
    sameProjLine (crossProduct P Q) (crossProduct Q R) := by
  unfold sameProjLine
  rw [cross_cross_eq_det_smul]
  rw [collinear] at h
  rw [h, zero_smul]

/-- **`hexRot` fixes the Pascal line projectively.**  The Pascal line of the
    rotated hexagon — spanned by `pascalP' = Q` and `pascalQ' = R` (PART 4c) —
    is the same projective line as the Pascal line of `hex` (spanned by
    `P, Q`).  Reduces to the rotation crux via `pascal_hexagon_theorem`. -/
theorem pascalLine_hexRot_sameProjLine {C : Conic} (hex : InscribedHexagon C) :
    sameProjLine
      (lineThrough (pascalP hex) (pascalQ hex))
      (lineThrough (pascalP (permuteHexagon hex hexRot))
                   (pascalQ (permuteHexagon hex hexRot))) := by
  rw [pascalP_permuteHexagon_hexRot, pascalQ_permuteHexagon_hexRot]
  unfold lineThrough
  exact sameProjLine_of_collinear _ _ _ (pascal_hexagon_theorem C hex)

/-- **`hexRev` fixes the Pascal line projectively.**  The reflected Pascal line
    is spanned by `pascalP' = -Q` and `pascalQ' = -P` (PART 4c), i.e. it equals
    `(-Q) ×₃ (-P) = -(P ×₃ Q)` up to the cross-product signs, hence the same
    projective line.  Proved directly by coordinate expansion. -/
theorem pascalLine_hexRev_sameProjLine {C : Conic} (hex : InscribedHexagon C) :
    sameProjLine
      (lineThrough (pascalP hex) (pascalQ hex))
      (lineThrough (pascalP (permuteHexagon hex hexRev))
                   (pascalQ (permuteHexagon hex hexRev))) := by
  rw [pascalP_permuteHexagon_hexRev, pascalQ_permuteHexagon_hexRev]
  unfold sameProjLine lineThrough
  funext i
  fin_cases i <;>
    simp only [cross_apply, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
               Matrix.head_cons, Pi.zero_apply, Fin.isValue] <;>
    ring

/-- **OQ-03-OQ-02 (projective level).**  Both dihedral generators send the
    Pascal line of `hex` to the *same projective line*.  This is the geometric
    heart of the descent claim: combined with `card_hexagon_labelings`
    (`|HexagonLabeling| = 60`) it says each of the 60 cosets has a
    well-defined Pascal line at the generator level.  The remaining gap to a
    fully quotient-level `pascalLine` (descent through `Quotient.out'`) is the
    closure induction propagating this generator-invariance to all of
    `hexagonalGroup = ⟨hexRot, hexRev⟩`. -/
theorem pascalLine_generators_sameProjLine {C : Conic} (hex : InscribedHexagon C) :
    sameProjLine (lineThrough (pascalP hex) (pascalQ hex))
        (lineThrough (pascalP (permuteHexagon hex hexRot))
                     (pascalQ (permuteHexagon hex hexRot)))
      ∧ sameProjLine (lineThrough (pascalP hex) (pascalQ hex))
        (lineThrough (pascalP (permuteHexagon hex hexRev))
                     (pascalQ (permuteHexagon hex hexRev))) :=
  ⟨pascalLine_hexRot_sameProjLine hex, pascalLine_hexRev_sameProjLine hex⟩

-- ============================================================
-- PART 4e: `sameProjLine` is a Partial Equivalence Relation
--          (the algebraic engine for the quotient descent)
-- ============================================================

/- PART 4d showed each *generator* of the dihedral group fixes the Pascal
   projective line.  To promote this to invariance under the whole group
   `⟨hexRot, hexRev⟩` by closure induction, `sameProjLine` must be an
   equivalence relation along the orbit.  It is reflexive (PART 4d) and we
   now add the two remaining pieces:

     * **symmetry** — `l ∥ m ⟹ m ∥ l` (the cross product is anti-symmetric);
     * **transitivity** — `l ∥ m ⟹ m ∥ n ⟹ l ∥ n`, *provided the middle
       vector `m ≠ 0`*.

   The `m ≠ 0` hypothesis is genuinely necessary: the zero vector is parallel
   to everything (`0 ×₃ v = 0`), so without it `0 ∥ a` and `0 ∥ b` would force
   `a ∥ b`.  On the Pascal orbit the middle line is the cross product of two
   distinct projective points of a non-degenerate conic, hence nonzero, so the
   hypothesis is satisfied wherever the descent uses it.

   Together these make `sameProjLine` a *partial equivalence relation* (PER):
   an equivalence relation on the set of nonzero homogeneous line-vectors,
   exactly the structure a `Quotient`/`Setoid` descent of `pascalLine`
   requires. -/

/-- **Symmetry of `sameProjLine`.**  `l ∥ m ⟹ m ∥ l`.  The cross product is
    anti-symmetric (`m ×₃ l = -(l ×₃ m)`), so a vanishing cross product is a
    symmetric relation.  Proved coordinate-wise to reuse the file's
    `cross_apply` simp set. -/
theorem sameProjLine_symm {l m : ProjLine} (h : sameProjLine l m) :
    sameProjLine m l := by
  unfold sameProjLine at h ⊢
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Pi.zero_apply, Fin.isValue] at h0 h1 h2
  funext i
  fin_cases i
  · simp only [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Pi.zero_apply, Fin.isValue]
    linear_combination -h0
  · simp only [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Pi.zero_apply, Fin.isValue]
    linear_combination -h1
  · simp only [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Pi.zero_apply, Fin.isValue]
    linear_combination -h2

/-- **Transitivity of `sameProjLine` along a nonzero middle vector.**
    If `l ∥ m` and `m ∥ n` with `m ≠ 0`, then `l ∥ n`.

    *Proof engine.*  For every coordinate `k`, the scaled vector
    `m k • (l ×₃ n)` vanishes identically: each of its three components is a
    fixed `ℝ`-linear combination of the (vanishing) components of `l ×₃ m` and
    `m ×₃ n` (a `linear_combination` certificate, one per coordinate pair).
    Hence `m k • (l ×₃ n) = 0` for all `k`.  Since `m ≠ 0`, some coordinate
    `m k ≠ 0`, and `smul_eq_zero` forces `l ×₃ n = 0`.

    This is the projective statement "two lines both proportional to a common
    nonzero line are proportional to each other", proved without dividing. -/
theorem sameProjLine_trans {l m n : ProjLine} (hm : m ≠ 0)
    (h1 : sameProjLine l m) (h2 : sameProjLine m n) :
    sameProjLine l n := by
  unfold sameProjLine at h1 h2 ⊢
  -- Component equations of `l ×₃ m = 0` and `m ×₃ n = 0`.
  have a0 : l 1 * m 2 - l 2 * m 1 = 0 := by
    have := congrFun h1 0
    simpa only [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
                Pi.zero_apply, Fin.isValue] using this
  have a1 : l 2 * m 0 - l 0 * m 2 = 0 := by
    have := congrFun h1 1
    simpa only [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
                Pi.zero_apply, Fin.isValue] using this
  have a2 : l 0 * m 1 - l 1 * m 0 = 0 := by
    have := congrFun h1 2
    simpa only [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
                Pi.zero_apply, Fin.isValue] using this
  have b0 : m 1 * n 2 - m 2 * n 1 = 0 := by
    have := congrFun h2 0
    simpa only [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
                Pi.zero_apply, Fin.isValue] using this
  have b1 : m 2 * n 0 - m 0 * n 2 = 0 := by
    have := congrFun h2 1
    simpa only [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
                Pi.zero_apply, Fin.isValue] using this
  have b2 : m 0 * n 1 - m 1 * n 0 = 0 := by
    have := congrFun h2 2
    simpa only [cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
                Pi.zero_apply, Fin.isValue] using this
  -- Each coordinate of `m` annihilates `l ×₃ n`.
  have key0 : m 0 • crossProduct l n = 0 := by
    funext i
    fin_cases i
    · simp only [cross_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
                 Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply, Fin.isValue]
      linear_combination (l 0) * b0 - (n 2) * a2 - (n 1) * a1
    · simp only [cross_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
                 Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply, Fin.isValue]
      linear_combination (l 0) * b1 + (n 0) * a1
    · simp only [cross_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
                 Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply, Fin.isValue]
      linear_combination (l 0) * b2 + (n 0) * a2
  have key1 : m 1 • crossProduct l n = 0 := by
    funext i
    fin_cases i
    · simp only [cross_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
                 Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply, Fin.isValue]
      linear_combination (l 1) * b0 + (n 1) * a0
    · simp only [cross_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
                 Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply, Fin.isValue]
      linear_combination (l 1) * b1 - (n 0) * a0 - (n 2) * a2
    · simp only [cross_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
                 Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply, Fin.isValue]
      linear_combination (l 1) * b2 + (n 1) * a2
  have key2 : m 2 • crossProduct l n = 0 := by
    funext i
    fin_cases i
    · simp only [cross_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
                 Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply, Fin.isValue]
      linear_combination (l 2) * b0 + (n 2) * a0
    · simp only [cross_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
                 Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply, Fin.isValue]
      linear_combination (l 2) * b1 + (n 2) * a1
    · simp only [cross_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
                 Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply, Fin.isValue]
      linear_combination (l 2) * b2 - (n 1) * a1 - (n 0) * a0
  -- `m ≠ 0` ⟹ some coordinate is nonzero ⟹ `l ×₃ n = 0`.
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hm
  simp only [Pi.zero_apply] at hk
  fin_cases k
  · rcases smul_eq_zero.mp key0 with h | h
    · exact absurd h hk
    · exact h
  · rcases smul_eq_zero.mp key1 with h | h
    · exact absurd h hk
    · exact h
  · rcases smul_eq_zero.mp key2 with h | h
    · exact absurd h hk
    · exact h

/-- **`sameProjLine` is a PER on nonzero line-vectors.**  Bundles reflexivity,
    symmetry, and (nonzero-middle) transitivity — the equivalence-relation
    structure the quotient descent of `pascalLine` consumes.  Stated as a
    conjunction rather than a `Setoid` instance because transitivity is only
    available along nonzero representatives (which is all the descent needs:
    the Pascal line of a non-degenerate inscribed hexagon is nonzero). -/
theorem sameProjLine_isPER :
    (∀ l : ProjLine, sameProjLine l l)
      ∧ (∀ {l m : ProjLine}, sameProjLine l m → sameProjLine m l)
      ∧ (∀ {l m n : ProjLine}, m ≠ 0 → sameProjLine l m → sameProjLine m n →
          sameProjLine l n) :=
  ⟨sameProjLine_refl, sameProjLine_symm, fun hm => sameProjLine_trans hm⟩

/-- **Both generators agree on a *single* common projective line.**  An
    immediate consequence of symmetry + transitivity applied to
    `pascalLine_generators_sameProjLine`: the rotated and reflected Pascal
    lines are the same projective line as each other (not merely each equal to
    the original), provided the original line `lineThrough (pascalP hex)
    (pascalQ hex)` is nonzero.  This is the first nontrivial use of the PER
    structure and the shape every closure-induction step takes. -/
theorem pascalLine_hexRot_hexRev_sameProjLine {C : Conic} (hex : InscribedHexagon C)
    (hne : lineThrough (pascalP hex) (pascalQ hex) ≠ 0) :
    sameProjLine
      (lineThrough (pascalP (permuteHexagon hex hexRot))
                   (pascalQ (permuteHexagon hex hexRot)))
      (lineThrough (pascalP (permuteHexagon hex hexRev))
                   (pascalQ (permuteHexagon hex hexRev))) :=
  sameProjLine_trans hne
    (sameProjLine_symm (pascalLine_hexRot_sameProjLine hex))
    (pascalLine_hexRev_sameProjLine hex)

-- ============================================================
-- PART 5: Pascal-Line Map
-- ============================================================

/-- The Pascal line associated with a hexagon labeling. Given an inscribed
    hexagon `(A, B, C, D, E, F)` and a labeling `lbl ∈ HexagonLabeling`,
    a representative permutation `π : Fin 6 → Fin 6` rearranges the six
    vertices into a new cyclic ordering, whose opposite-side intersections
    `P, Q, R` are collinear (by Pascal's theorem). The Pascal line is the
    line through two of those three Pascal points.

    The map is made *total* by evaluating it at the canonical coset
    representative `lbl.out' : Equiv.Perm (Fin 6)` (`Quotient.out'`). The
    `D_6`-invariance of the resulting projective line — i.e. that the value
    is independent of the choice of representative — is the genuine
    "well-definedness" content of **OQ-03-OQ-02**; its geometric backbone is
    the generator-action of `hexRot`/`hexRev` on `{±P, ±Q, ±R}` (see the
    `OQ-03-OQ-02` knowledge notes). Establishing that as a *projective* line
    equality additionally needs equality of lines up to a nonzero scalar plus
    a nondegeneracy hypothesis, and is deferred. -/
noncomputable def pascalLine
    (C : Conic) (hex : InscribedHexagon C) (lbl : HexagonLabeling) : ProjLine :=
  lineThrough (pascalP (permuteHexagon hex lbl.out'))
              (pascalQ (permuteHexagon hex lbl.out'))

/-- **Hexagrammum Mysticum (existence statement)**: the assignment
    `HexagonLabeling → ProjLine` from a hexagon labeling to its Pascal
    line is total. Six points on a conic determine 60 Pascal lines
    indexed by `HexagonLabeling`.

    The full geometric content (the 60 lines are distinct in general
    position, the incidence structure with Steiner and Kirkman points)
    is captured by the subsequent definitions and theorems. -/
theorem hexagrammum_mysticum_pascal_lines
    (C : Conic) (hex : InscribedHexagon C) :
    ∃ (lines : HexagonLabeling → ProjLine), lines = pascalLine C hex :=
  ⟨pascalLine C hex, rfl⟩

-- ============================================================
-- PART 6: Steiner Points
-- ============================================================

/-- A *Steiner point* of an inscribed hexagon: the concurrent intersection
    of 3 Pascal lines forming a Steiner triple of hexagonal labelings.
    Each Steiner point lies on exactly 3 of the 60 Pascal lines.

    The 20 Steiner triples are explicitly characterized via the outer
    automorphism of `S_6` (Conway-Ryba 2012). -/
structure SteinerPoint (C : Conic) (hex : InscribedHexagon C) where
  /-- The concurrency point in projective space. -/
  point : ProjPoint
  /-- The three hexagon labelings whose Pascal lines pass through `point`. -/
  triple : Finset HexagonLabeling
  /-- Exactly 3 Pascal lines through each Steiner point. -/
  card_triple : triple.card = 3
  /-- Each labeling in the triple has its Pascal line through `point`. -/
  on_lines : ∀ lbl ∈ triple, pointOnLine point (pascalLine C hex lbl)

/-- **Steiner's count theorem (OQ-03-OQ-03 statement)**: six points on a
    non-degenerate conic determine exactly 20 Steiner points. -/
theorem steiner_count_eq_20
    (C : Conic) (hex : InscribedHexagon C)
    [Fintype (SteinerPoint C hex)] :
    Fintype.card (SteinerPoint C hex) = 20 := by
  sorry

-- ============================================================
-- PART 7: Kirkman Points
-- ============================================================

/-- A *Kirkman point* of an inscribed hexagon: the concurrent intersection
    of 3 Pascal lines forming a Kirkman triple, combinatorially distinct
    from the Steiner triples. -/
structure KirkmanPoint (C : Conic) (hex : InscribedHexagon C) where
  /-- The concurrency point in projective space. -/
  point : ProjPoint
  /-- The three hexagon labelings whose Pascal lines pass through `point`. -/
  triple : Finset HexagonLabeling
  /-- Exactly 3 Pascal lines through each Kirkman point. -/
  card_triple : triple.card = 3
  /-- Each labeling in the triple has its Pascal line through `point`. -/
  on_lines : ∀ lbl ∈ triple, pointOnLine point (pascalLine C hex lbl)

/-- **Kirkman's count theorem (OQ-03-OQ-04 statement)**: six points on a
    non-degenerate conic determine exactly 60 Kirkman points. -/
theorem kirkman_count_eq_60
    (C : Conic) (hex : InscribedHexagon C)
    [Fintype (KirkmanPoint C hex)] :
    Fintype.card (KirkmanPoint C hex) = 60 := by
  sorry

-- ============================================================
-- PART 8: Sanity Lemmas (Unconditional)
-- ============================================================

/-- `hexRot` is not the identity. (Sanity check: cyclic rotation by 1
    moves `0 ↦ 1`.) -/
theorem hexRot_ne_one : hexRot ≠ 1 := by
  intro h
  have : hexRot 0 = (1 : Equiv.Perm (Fin 6)) 0 := by rw [h]
  simp [hexRot, finRotate] at this

/-- `hexRev` is not the identity. (Sanity check: reversal swaps `0` and `5`.) -/
theorem hexRev_ne_one : hexRev ≠ 1 := by
  intro h
  have : hexRev 0 = (1 : Equiv.Perm (Fin 6)) 0 := by rw [h]
  simp [hexRev, Fin.rev] at this

end PascalsHexagonOQ03
