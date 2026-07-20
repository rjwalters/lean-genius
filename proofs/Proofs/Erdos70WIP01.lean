import Mathlib
import Proofs.Erdos70Problem

/-
# Erdős #70 — closure of the countable-ordinal class and conjecture specializations
# (erdos-70-wip-01)

## The Problem

**Erdős Problem #70** (OPEN). Does the continuum satisfy the partition relation
`𝔠 → (β, n)₂³` for *every* countable ordinal `β` and every `2 ≤ n < ω`?
`Erdos70Problem.lean` sets up `PartitionArrow`, `IsCountableOrdinal`, the
conjecture `erdos_70_conjecture` and the special cases `conjecture_omega` /
`conjecture_omega_squared`, and proves a handful of specific countability facts
(`omega0_countable`, `omega0_plus_n_countable`, `omega0_squared_countable`) plus
the two monotonicity directions of the arrow.

This file supplies the **general structural lemmas** those specific facts are
instances of: the countable ordinals are downward-closed and closed under `+`
and `*`; and it wires the open conjecture to its published special cases.

## Results (all in `namespace Erdos70`)

1. `IsCountableOrdinal.of_le` — countability is *downward closed*: `α ≤ β` and
   `β` countable ⟹ `α` countable. (`omega0_plus_n_countable` etc. become
   corollaries of this + closure below.)

2. `isCountableOrdinal_add` / `isCountableOrdinal_mul` — the countable ordinals
   are closed under ordinal addition and multiplication.

3. `erdos_70_conjecture_imp_omega` / `_imp_omega_squared` — the open conjecture
   specializes to its two flagship cases `𝔠 → (ω, n)` and `𝔠 → (ω², n)`, using
   the parent's countability witnesses.

## Summary: 0 sorries, 0 axioms, no `native_decide`. Built over the gallery defs.
-/

namespace Erdos70

/-- **Downward closure.** A sub-ordinal of a countable ordinal is countable. -/
theorem IsCountableOrdinal.of_le {α β : Ordinal} (hαβ : α ≤ β)
    (h : IsCountableOrdinal β) : IsCountableOrdinal α :=
  (Ordinal.card_le_card hαβ).trans h

/-- The countable ordinals are closed under ordinal addition. -/
theorem isCountableOrdinal_add {α β : Ordinal}
    (hα : IsCountableOrdinal α) (hβ : IsCountableOrdinal β) :
    IsCountableOrdinal (α + β) := by
  unfold IsCountableOrdinal at *
  rw [Ordinal.card_add]
  exact Cardinal.add_le_aleph0.mpr ⟨hα, hβ⟩

/-- The countable ordinals are closed under ordinal multiplication. -/
theorem isCountableOrdinal_mul {α β : Ordinal}
    (hα : IsCountableOrdinal α) (hβ : IsCountableOrdinal β) :
    IsCountableOrdinal (α * β) := by
  unfold IsCountableOrdinal at *
  rw [Ordinal.card_mul]
  calc α.card * β.card ≤ Cardinal.aleph0 * Cardinal.aleph0 :=
        mul_le_mul' hα hβ
    _ = Cardinal.aleph0 := Cardinal.aleph0_mul_aleph0

/-- **Closure under natural-number exponentiation.**  If `α` is a countable
ordinal then so is `α ^ n` for every `n : ℕ`.  Proof by induction on `n`:
`α ^ 0 = 1` is countable, and `α ^ (n+1) = α ^ n * α` is countable by
`IsCountableOrdinal.mul`.  This generalises the parent's `omega0_squared_countable`
(`ω * ω = ω ^ 2`) to all finite powers. -/
theorem isCountableOrdinal_opow_nat {α : Ordinal} (hα : IsCountableOrdinal α) :
    ∀ n : ℕ, IsCountableOrdinal (α ^ (n : Ordinal))
  | 0 => by simpa using one_countable
  | (n + 1) => by
      have hstep : α ^ ((n + 1 : ℕ) : Ordinal) = α ^ (n : Ordinal) * α := by
        rw [Nat.cast_add, Nat.cast_one, Ordinal.opow_add, Ordinal.opow_one]
      rw [hstep]
      exact (isCountableOrdinal_opow_nat hα n).mul hα

/-- Every finite power of `ω` is a countable ordinal: `ω ^ n` is countable for all
`n : ℕ`.  (`ω ^ 2 = ω · ω` recovers the parent's `omega0_squared_countable`.) -/
theorem omega0_opow_nat_countable (n : ℕ) :
    IsCountableOrdinal (Ordinal.omega0 ^ (n : Ordinal)) :=
  isCountableOrdinal_opow_nat omega0_countable n

/-- The open conjecture specializes to the flagship case `𝔠 → (ω, n)₂³`. -/
theorem erdos_70_conjecture_imp_omega (h : erdos_70_conjecture) (n : ℕ)
    (hn : 2 ≤ n) : conjecture_omega n :=
  h Ordinal.omega0 n omega0_countable hn

/-- The open conjecture specializes to `𝔠 → (ω², n)₂³`. -/
theorem erdos_70_conjecture_imp_omega_squared (h : erdos_70_conjecture) (n : ℕ)
    (hn : 2 ≤ n) : conjecture_omega_squared n :=
  h (Ordinal.omega0 * Ordinal.omega0) n omega0_squared_countable hn

end Erdos70
