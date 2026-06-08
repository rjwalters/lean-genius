/-
# ℓ-Rank Adapter for `ClassGroup` Torsion — Erdős #90 Sub-Issue (a)

## Purpose

This file provides the **ℓ-rank adapter** identified by item 2 of the audit
`research/MATHLIB-PREREQS-UNIT-DISTANCE.md` as the smallest concrete
prerequisite for the OpenAI 2026 unit-distance construction (parent tracker
#20576). It is a sub-issue (a) of that tracker; sub-issue (b) (axiomatized
Golod–Shafarevich, #22606) and sub-issue (c) (axiomatized class field tower
infrastructure, #22607) landed earlier and are imported only conceptually
(this file is self-contained Lean-wise).

The audit classifies this as a **"verified adapter"**: Mathlib v4.26.0
already has `ClassGroup K`, `Fintype (ClassGroup (𝓞 K))` for number fields,
and standard torsion-subgroup API. All this file does is expose the
ℓ-torsion subgroup with a definitional name suitable for downstream use in
the Golod–Shafarevich bound, and provide a small library of API lemmas
plus one worked example.

## Status

`status: "verified"` — **0 sorries, 0 `axiom` declarations, 0
structure-encoded assumptions**. Every definition and lemma is a thin
wrapper or a direct consequence of existing Mathlib infrastructure.

## Mathematical content

For a prime `ℓ` and a number field `K`, the ℓ-torsion subgroup of the
class group `Cl(K) = ClassGroup (𝓞 K)` is
```
Cl(K)[ℓ] = { x ∈ Cl(K) | x ^ ℓ = 1 }
```
Since `Cl(K)` is finite (Mathlib's `RingOfIntegers.instFintypeClassGroup`),
`Cl(K)[ℓ]` is finite. As an elementary abelian ℓ-group it is automatically
a `(ZMod ℓ)`-vector space, and its ℓ-rank `d_ℓ(Cl K)` is the dimension of
this vector space — equivalently, the unique integer `r` with
`Nat.card Cl(K)[ℓ] = ℓ ^ r`.

This is the quantity that enters the Golod–Shafarevich number-theoretic
inequality `d_ℓ > 2 + 2·√(r₁ + r₂ + 1) ⇒ infinite ℓ-class field tower`,
stated as the axiom `golodShafarevich_number_field` in
`Proofs/Erdos90/GolodShafarevich.lean` (sub-issue (b)).

## API exposed

* `classGroupLTorsion K ℓ` — the ℓ-torsion subgroup of `ClassGroup (𝓞 K)`.
* `Fintype` and `Finite` instances for `classGroupLTorsion K ℓ`.
* `classGroupLRank K ℓ` — the ℓ-rank, defined as `Nat.log ℓ` of the
  cardinality of `classGroupLTorsion K ℓ`. For an elementary abelian
  ℓ-group of order `ℓ ^ r`, this returns exactly `r`.
* `classGroupLTorsion_le_torsion` — every ℓ-torsion element is a torsion
  element of `ClassGroup (𝓞 K)`.
* `classGroupLRank_rat` — worked example: `classGroupLRank ℚ ℓ = 0` for
  every prime ℓ (since `Cl(ℚ) ≅ 1`).

## References

- Parent: #20576. Sub-issues: this file = #22604; #22606 (GolodShafarevich);
  #22607 (ClassFieldTower).
- Audit: `research/MATHLIB-PREREQS-UNIT-DISTANCE.md` (item 2, "partial,
  needs adapter").
- Mathlib paths: `Mathlib/RingTheory/ClassGroup.lean`,
  `Mathlib/NumberTheory/NumberField/ClassNumber.lean`,
  `Mathlib/GroupTheory/Torsion.lean`.
- Mathlib `v4.26.0` rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
-/

import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.ClassGroup
import Mathlib.GroupTheory.Torsion
import Mathlib.Tactic

namespace Erdos90.ClassGroupLRank

open NumberField

/-! ## The ℓ-torsion subgroup of the class group

`classGroupLTorsion K ℓ` is the subgroup of `ClassGroup (𝓞 K)` consisting
of elements `x` with `x ^ ℓ = 1`. This is the standard definition of the
ℓ-torsion subgroup of a commutative group and is a thin wrapper over
`Subgroup.mk` constraining elements by `· ^ ℓ = 1`.

Mathlib has `CommGroup.torsion` (all torsion elements) and primary
components `primaryComponent`. We do **not** reuse either of these because:

* `CommGroup.torsion` collects elements of *any* finite order, whereas we
  need exactly the ℓ-torsion.
* `primaryComponent p` collects elements whose order is *some* power of
  `p`, which strictly contains the ℓ-torsion (the ℓ²-torsion is in the
  primary component but not in the ℓ-torsion when `ℓ ∣ order`). For the
  Golod–Shafarevich application we need the *exact* ℓ-torsion, which is
  the kernel of the ℓ-th power map and forms an elementary abelian
  ℓ-group. -/

/-- The ℓ-torsion subgroup of `ClassGroup (𝓞 K)`: elements `x` with
    `x ^ ℓ = 1`. Defined directly as a `Subgroup` of `ClassGroup (𝓞 K)`. -/
def classGroupLTorsion (K : Type*) [Field K] [NumberField K] (ℓ : ℕ) :
    Subgroup (ClassGroup (𝓞 K)) where
  carrier := { x | x ^ ℓ = 1 }
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [mul_pow, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [inv_pow, ha, inv_one]

/-- Membership characterization. -/
@[simp]
theorem mem_classGroupLTorsion {K : Type*} [Field K] [NumberField K] {ℓ : ℕ}
    (x : ClassGroup (𝓞 K)) :
    x ∈ classGroupLTorsion K ℓ ↔ x ^ ℓ = 1 := Iff.rfl

/-- `classGroupLTorsion` is finite because the ambient `ClassGroup (𝓞 K)`
    is finite (Mathlib's `RingOfIntegers.instFintypeClassGroup`). -/
noncomputable instance fintypeClassGroupLTorsion
    (K : Type*) [Field K] [NumberField K] (ℓ : ℕ) :
    Fintype (classGroupLTorsion K ℓ) :=
  Fintype.ofFinite _

/-- Convenience `Finite` instance (often easier to use than `Fintype`). -/
instance finiteClassGroupLTorsion
    (K : Type*) [Field K] [NumberField K] (ℓ : ℕ) :
    Finite (classGroupLTorsion K ℓ) :=
  Subtype.finite

/-! ## The ℓ-rank

For an elementary abelian ℓ-group of order `ℓ ^ r`, the ℓ-rank is `r`,
which equals `Nat.log ℓ` of the cardinality. For a prime ℓ, the ℓ-torsion
subgroup of a finite commutative group *is* an elementary abelian ℓ-group,
so this is the correct value.

We give the definition unconditionally on `ℓ` (no `Fact ℓ.Prime`); when
`ℓ = 0` or `ℓ = 1`, the resulting "rank" is either `0` (since `Nat.log 0`
and `Nat.log 1` both return `0`) or describes a trivial situation. The
intended invocations always supply a prime `ℓ`. -/

/-- The ℓ-rank of the class group: the unique integer `r` such that
    `Nat.card (classGroupLTorsion K ℓ) = ℓ ^ r`, computed as
    `Nat.log ℓ (Nat.card ...)`.

    For a prime `ℓ`, the ℓ-torsion subgroup is an elementary abelian
    ℓ-group of order `ℓ ^ r`, and this definition returns `r`. -/
noncomputable def classGroupLRank
    (K : Type*) [Field K] [NumberField K] (ℓ : ℕ) : ℕ :=
  Nat.log ℓ (Nat.card (classGroupLTorsion K ℓ))

/-! ## Basic API

These are the lemmas downstream files will consume when bridging the
opaque marker `HasClassGroupLRank` (declared in
`Proofs/Erdos90/GolodShafarevich.lean`) to the concrete definition above.
-/

/-- An ℓ-torsion element of `ClassGroup (𝓞 K)` has finite order (it
    divides `ℓ`). Hence the ℓ-torsion subgroup is contained in the full
    torsion subgroup `CommGroup.torsion`.

    *Note:* the proof uses `ℓ ≠ 0` because `x ^ 0 = 1` for every `x` and
    would force every element into the "0-torsion", which is not finite-
    order in general. -/
theorem classGroupLTorsion_le_torsion
    (K : Type*) [Field K] [NumberField K] (ℓ : ℕ) (hℓ : ℓ ≠ 0) :
    classGroupLTorsion K ℓ ≤ CommGroup.torsion (ClassGroup (𝓞 K)) := by
  intro x hx
  rw [mem_classGroupLTorsion] at hx
  rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  exact ⟨ℓ, Nat.pos_of_ne_zero hℓ, hx⟩

/-- The ℓ-torsion subgroup is the whole class group whenever `ℓ` is a
    multiple of the exponent of `Cl(K)`. In particular, for any `K` and
    `ℓ = Nat.card (ClassGroup (𝓞 K))`, the ℓ-torsion is everything (by
    Lagrange's theorem applied to a finite commutative group). -/
theorem classGroupLTorsion_eq_top_of_classNumber_dvd
    (K : Type*) [Field K] [NumberField K] (ℓ : ℕ)
    (h : Nat.card (ClassGroup (𝓞 K)) ∣ ℓ) :
    classGroupLTorsion K ℓ = ⊤ := by
  ext x
  refine ⟨fun _ => Subgroup.mem_top _, fun _ => ?_⟩
  rw [mem_classGroupLTorsion]
  obtain ⟨k, hk⟩ := h
  rw [hk, pow_mul]
  -- `x ^ Nat.card G = 1` for any element of a finite commutative group `G`.
  have hcard : x ^ Nat.card (ClassGroup (𝓞 K)) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact pow_card_eq_one
  rw [hcard, one_pow]

/-- The ℓ-rank is bounded by `Nat.log ℓ (Nat.card (ClassGroup (𝓞 K)))`:
    the ℓ-torsion subgroup has cardinality at most the cardinality of
    the whole class group. -/
theorem classGroupLRank_le_log_classNumber
    (K : Type*) [Field K] [NumberField K] (ℓ : ℕ) :
    classGroupLRank K ℓ ≤ Nat.log ℓ (Nat.card (ClassGroup (𝓞 K))) := by
  unfold classGroupLRank
  apply Nat.log_mono_right
  exact Nat.card_le_card_of_injective _ Subtype.val_injective

/-! ## Worked example: K = ℚ

`Cl(ℚ) ≅ 1`, so every ℓ-torsion subgroup is trivial and `d_ℓ(Cl(ℚ)) = 0`
for every prime ℓ. This is the smallest possible example; it verifies
that the definitional pipeline (subgroup → finiteness → cardinality →
log) compiles and computes correctly. -/

/-- The class group of `ℚ` has cardinality 1 (since `ℤ` is a PID). This
    is a restatement of Mathlib's `Rat.classNumber_eq`. -/
theorem natCard_classGroup_rat : Nat.card (ClassGroup (𝓞 ℚ)) = 1 := by
  rw [Nat.card_eq_fintype_card]
  exact Rat.classNumber_eq

/-- For `K = ℚ`, the ℓ-torsion subgroup of `Cl(ℚ)` is trivial. -/
theorem classGroupLTorsion_rat (ℓ : ℕ) :
    classGroupLTorsion ℚ ℓ = ⊥ := by
  have hcard : Nat.card (ClassGroup (𝓞 ℚ)) = 1 := natCard_classGroup_rat
  -- ClassGroup (𝓞 ℚ) is a singleton, so every subgroup is trivial.
  have : Subsingleton (ClassGroup (𝓞 ℚ)) :=
    Nat.card_eq_one_iff_unique.mp hcard |>.1
  exact Subgroup.eq_bot_of_subsingleton _

/-- **Worked example.** For `K = ℚ` and any `ℓ`, the ℓ-rank is `0`. -/
theorem classGroupLRank_rat (ℓ : ℕ) : classGroupLRank ℚ ℓ = 0 := by
  unfold classGroupLRank
  have h := classGroupLTorsion_rat ℓ
  -- card of the trivial subgroup is 1.
  have hcard : Nat.card (classGroupLTorsion ℚ ℓ) = 1 := by
    rw [h]
    simp [Nat.card_eq_fintype_card]
  rw [hcard]
  exact Nat.log_one_right ℓ

/-! ## Axiom Enumeration

Per `CLAUDE.md` axiom integrity policy, we explicitly enumerate the
assumptions in this file:

* `axiom` declarations: **0**.
* Sorries: **0**.
* Assumption-carrying structure fields: **0** (no `structure` is declared
  in this file; the only `Subgroup.mk`-style construction is a verified
  closure under `1`, `mul`, and `inv`, with all three proofs supplied).

Total: **0** new assumptions. This file is a pure adapter over existing
Mathlib content; integrating it into `src/data/proofs/erdos-90/meta.json`
does **not** change `axiomCount` (remains at 16: 13 from
`ClassFieldTower.lean` + 3 from `GolodShafarevich.lean`).
-/

end Erdos90.ClassGroupLRank
