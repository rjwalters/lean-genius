import Mathlib

/-
# Unifying EuclideanDomain GCD with GCDMonoid Normalization

## Research Problem
gcd-algorithm-oq-04

## What This Proves

In Lean 4/Mathlib, GCDs arise from two typeclass hierarchies:
- `EuclideanDomain` provides `EuclideanDomain.gcd` via the Euclidean algorithm
- `GCDMonoid` provides `GCDMonoid.gcd` with normalization guarantees

### Key Structural Fact

`EuclideanDomain.gcdMonoid` is a **`def`** (not an `instance`) in Mathlib. It creates
a `GCDMonoid R` structure where `gcd = EuclideanDomain.gcd`, but it is NOT
automatically synthesized by typeclass resolution. To use it, you must write:
  `letI := EuclideanDomain.gcdMonoid R`

### Coherence with `EuclideanDomain.gcdMonoid`

When `EuclideanDomain.gcdMonoid` is used, `GCDMonoid.gcd = EuclideanDomain.gcd`
by definitional equality (`rfl`). This justifies the coherence.

### Concrete types (ℤ, Polynomial F)

For specific types, Lean uses DIFFERENT `GCDMonoid` instances (not from
`EuclideanDomain.gcdMonoid`):
- **ℤ**: `GCDMonoid ℤ` uses `↑(Int.gcd a b)` (always ≥ 0), distinct from
  `EuclideanDomain.gcd` (which can give negative results)
- **Polynomial F**: `GCDMonoid (Polynomial F)` comes from UFD theory, not
  directly `EuclideanDomain.gcdMonoid`

For ℤ specifically, `(EuclideanDomain.gcd a b).natAbs = Int.gcd a b`
(from `Int.natAbs_euclideanDomain_gcd` in Mathlib), so they are **associated**.

## Key Mathlib Facts

- `EuclideanDomain.gcdMonoid (R)` — def creating GCDMonoid where gcd = EuclideanDomain.gcd
- `Int.natAbs_euclideanDomain_gcd` — `natAbs` of `EuclideanDomain.gcd` equals `Int.gcd`
- `Int.coe_gcd : ↑(Int.gcd i j) = GCDMonoid.gcd i j` — the ℤ GCDMonoid uses Int.gcd
- `Int.associated_iff_natAbs` — association in ℤ iff same natAbs

## Axiom Count
0 axioms, 0 sorries.
-/

namespace GcdAlgorithmOQ04

open EuclideanDomain

/-! ## Part I: GCDMonoid Divisibility Axioms for EuclideanDomain.gcd

These hold in any EuclideanDomain, without any GCDMonoid instance.
-/

section EuclideanGCDAxioms

variable {R : Type*} [EuclideanDomain R] [DecidableEq R]

/-- `EuclideanDomain.gcd` divides the left argument. -/
theorem euclidean_gcd_dvd_left (a b : R) : EuclideanDomain.gcd a b ∣ a :=
  gcd_dvd_left a b

/-- `EuclideanDomain.gcd` divides the right argument. -/
theorem euclidean_gcd_dvd_right (a b : R) : EuclideanDomain.gcd a b ∣ b :=
  gcd_dvd_right a b

/-- Any common divisor divides `EuclideanDomain.gcd` (universal property). -/
theorem euclidean_dvd_gcd {a b d : R} (ha : d ∣ a) (hb : d ∣ b) :
    d ∣ EuclideanDomain.gcd a b :=
  dvd_gcd ha hb

/-- The universal divisibility property characterizes the GCD. -/
theorem euclidean_dvd_gcd_iff (a b d : R) :
    d ∣ EuclideanDomain.gcd a b ↔ d ∣ a ∧ d ∣ b :=
  ⟨fun h => ⟨dvd_trans h (gcd_dvd_left a b), dvd_trans h (gcd_dvd_right a b)⟩,
   fun ⟨ha, hb⟩ => dvd_gcd ha hb⟩

/-- `EuclideanDomain.gcd` satisfies all three GCDMonoid axioms. -/
theorem euclidean_gcd_satisfies_gcdMonoid_axioms (a b : R) :
    EuclideanDomain.gcd a b ∣ a ∧
    EuclideanDomain.gcd a b ∣ b ∧
    (∀ d : R, d ∣ a → d ∣ b → d ∣ EuclideanDomain.gcd a b) :=
  ⟨gcd_dvd_left a b, gcd_dvd_right a b, fun _ ha hb => dvd_gcd ha hb⟩

end EuclideanGCDAxioms

/-! ## Part II: GCDMonoid Instance from EuclideanDomain

`EuclideanDomain.gcdMonoid` is a `def` (not an `instance`) that creates a
`GCDMonoid R` structure where `GCDMonoid.gcd = EuclideanDomain.gcd`.
-/

section GCDMonoidInstance

variable {R : Type*} [EuclideanDomain R] [DecidableEq R]

/-- **Coherence**: When using `EuclideanDomain.gcdMonoid`, the GCDs are equal. -/
theorem euclidean_gcd_eq_gcdMonoid_gcd_via_def (a b : R) :
    letI : GCDMonoid R := EuclideanDomain.gcdMonoid R
    EuclideanDomain.gcd a b = GCDMonoid.gcd a b :=
  rfl

/-- With `EuclideanDomain.gcdMonoid`, the GCDs satisfy the universal property. -/
theorem gcdMonoid_via_def_dvd_gcd_iff (a b d : R) :
    letI : GCDMonoid R := EuclideanDomain.gcdMonoid R
    d ∣ GCDMonoid.gcd a b ↔ d ∣ a ∧ d ∣ b := by
  letI : GCDMonoid R := EuclideanDomain.gcdMonoid R
  -- GCDMonoid.gcd is definitionally EuclideanDomain.gcd under letI
  exact euclidean_dvd_gcd_iff a b d

end GCDMonoidInstance

/-! ## Part III: Integer Normalization

For ℤ, the `GCDMonoid ℤ` instance uses `↑(Int.gcd a b)` (always ≥ 0), while
`EuclideanDomain.gcd` can give negative results. The key coherence theorem is:
  `(EuclideanDomain.gcd a b).natAbs = Int.gcd a b`
-/

section IntegerNormalization

/-- `Int.gcd` and `GCDMonoid.gcd` for ℤ — both computable and always ≥ 0. -/
example : Int.gcd (6 : ℤ) (-3) = 3 := by native_decide
example : GCDMonoid.gcd (6 : ℤ) (-3) = 3 := by native_decide
example : Int.gcd (12 : ℤ) 8 = 4 := by native_decide
example : GCDMonoid.gcd (12 : ℤ) 8 = 4 := by native_decide

/-- **natAbs Coherence** (Mathlib: `Int.natAbs_euclideanDomain_gcd`):
    The natAbs of `EuclideanDomain.gcd` equals `Int.gcd`. -/
theorem int_euclidean_gcd_natAbs (a b : ℤ) :
    (EuclideanDomain.gcd a b).natAbs = Int.gcd a b :=
  Int.natAbs_euclideanDomain_gcd a b

/-- **Association**: `EuclideanDomain.gcd` and `↑(Int.gcd)` are associated in ℤ. -/
theorem int_euclidean_gcd_associated_cast (a b : ℤ) :
    Associated (EuclideanDomain.gcd a b) (↑(Int.gcd a b) : ℤ) := by
  rw [Int.associated_iff_natAbs]
  simp [int_euclidean_gcd_natAbs]

/-- **Association with GCDMonoid.gcd**: For ℤ, `EuclideanDomain.gcd` and
    `GCDMonoid.gcd` are associated (since `GCDMonoid.gcd a b = ↑(Int.gcd a b)`). -/
theorem int_euclidean_gcd_associated_gcdMonoid (a b : ℤ) :
    Associated (EuclideanDomain.gcd a b) (GCDMonoid.gcd a b) := by
  rw [← Int.coe_gcd]
  exact int_euclidean_gcd_associated_cast a b

end IntegerNormalization

/-! ## Part IV: Type Hierarchy Summary

The instance chain for any EuclideanDomain R (with DecidableEq R):
  EuclideanDomain R
    ↓ (EuclideanDomain.gcdMonoid — explicit def, not auto-instance)
  GCDMonoid R (with gcd = EuclideanDomain.gcd)
    ↓ (automatic from GCDMonoid)
  UniqueFactorizationMonoid R
  IsBezout R

For concrete types, Lean may use a DIFFERENT GCDMonoid instance (like Int's
normalized one), so the two GCDs can differ by an associated unit.
-/

section TypeHierarchy

variable {R : Type*} [EuclideanDomain R] [DecidableEq R]

/-- The GCDMonoid created by `EuclideanDomain.gcdMonoid` is a valid instance. -/
example : GCDMonoid R := EuclideanDomain.gcdMonoid R

/-- Using `EuclideanDomain.gcdMonoid`, we get a UniqueFactorizationMonoid. -/
example : UniqueFactorizationMonoid R :=
  letI := EuclideanDomain.gcdMonoid R
  inferInstance

/-- Using `EuclideanDomain.gcdMonoid`, we get a Bézout domain. -/
example : IsBezout R :=
  letI := EuclideanDomain.gcdMonoid R
  inferInstance

end TypeHierarchy

end GcdAlgorithmOQ04
