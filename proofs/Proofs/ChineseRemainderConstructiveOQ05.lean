/-
# Axiom-free CRT worked examples — removing the parent's `native_decide` (OQ-05)

The parent gallery entry **chinese-remainder-constructive** proves the structural
Chinese Remainder Theorem (existence, uniqueness, the Bézout construction)
symbolically and axiom-free, but its advertised *worked examples* — the classic
Sunzi problem (`x = 23` mod `105`) and the four-moduli example (`x = 53` mod
`210`) — are discharged by `native_decide`. That tactic trusts the compiler's
kernel reduction and so pulls in the `Lean.ofReduceBool` axiom: the entry is
`axiomatized`, its sole assumption being exactly these computational checks.

This file removes that assumption. Each worked example is re-established
**without `native_decide`**, by a short Chinese-Remainder argument: the residue
conditions say `x ≡ N` modulo each (pairwise coprime) modulus, so by
`Nat.modEq_and_modEq_iff_modEq_mul` they combine to `x ≡ N` modulo the product,
and the range bound then forces `x = N`. The residue checks themselves use kernel
`decide`/`omega`, which depend only on the ordinary foundational axioms — not
`Lean.ofReduceBool`.

The results are stated as *iff*s `(residues) ↔ x = N` over the appropriate range,
so each simultaneously certifies existence (the witness `N` works) and uniqueness
(nothing else in range does). `#print axioms` on every theorem below lists only
`propext`, `Classical.choice`, `Quot.sound`.
-/
import Mathlib

namespace ChineseRemainderConstructiveOQ05

/- ## The Sunzi problem: x ≡ 2 (mod 3), 3 (mod 5), 2 (mod 7) -/

/-- **Sunzi's problem, axiom-free.** Over `0 ≤ x < 105 = 3·5·7`, the three
congruences hold *iff* `x = 23`. Existence (23 is a solution) and uniqueness
(it is the only one in range) in a single statement, with no `native_decide`. -/
theorem sunzi_crt (x : ℕ) (hx : x < 105) :
    (x % 3 = 2 ∧ x % 5 = 3 ∧ x % 7 = 2) ↔ x = 23 := by
  constructor
  · rintro ⟨h3, h5, h7⟩
    have e3 : x ≡ 23 [MOD 3] := by unfold Nat.ModEq; omega
    have e5 : x ≡ 23 [MOD 5] := by unfold Nat.ModEq; omega
    have e7 : x ≡ 23 [MOD 7] := by unfold Nat.ModEq; omega
    have e15 : x ≡ 23 [MOD 3 * 5] :=
      (Nat.modEq_and_modEq_iff_modEq_mul (by decide)).mp ⟨e3, e5⟩
    have e105 : x ≡ 23 [MOD 3 * 5 * 7] :=
      (Nat.modEq_and_modEq_iff_modEq_mul (by decide)).mp ⟨e15, e7⟩
    have : x % 105 = 23 % 105 := e105
    omega
  · rintro rfl
    refine ⟨by decide, by decide, by decide⟩

/-- The smallest positive Sunzi solution is `23`. -/
theorem sunzi_value : (23 : ℕ) % 3 = 2 ∧ (23 : ℕ) % 5 = 3 ∧ (23 : ℕ) % 7 = 2 := by
  refine ⟨by decide, by decide, by decide⟩

/-- Uniqueness is only *modulo 105*: the next solution `23 + 105 = 128` satisfies
the same congruences but lies outside the range — illustrating why the range
bound in `sunzi_crt` is essential. -/
theorem sunzi_shift : (128 : ℕ) % 3 = 2 ∧ (128 : ℕ) % 5 = 3 ∧ (128 : ℕ) % 7 = 2 := by
  refine ⟨by decide, by decide, by decide⟩

/- ## The four-moduli example: x ≡ 1,2,3,4 (mod 2,3,5,7) -/

/-- **Four pairwise-coprime moduli, axiom-free.** Over `0 ≤ x < 210 = 2·3·5·7`,
the four congruences hold *iff* `x = 53`. Same Chinese-Remainder argument, no
`native_decide`. -/
theorem four_moduli_crt (x : ℕ) (hx : x < 210) :
    (x % 2 = 1 ∧ x % 3 = 2 ∧ x % 5 = 3 ∧ x % 7 = 4) ↔ x = 53 := by
  constructor
  · rintro ⟨h2, h3, h5, h7⟩
    have e2 : x ≡ 53 [MOD 2] := by unfold Nat.ModEq; omega
    have e3 : x ≡ 53 [MOD 3] := by unfold Nat.ModEq; omega
    have e5 : x ≡ 53 [MOD 5] := by unfold Nat.ModEq; omega
    have e7 : x ≡ 53 [MOD 7] := by unfold Nat.ModEq; omega
    have e6 : x ≡ 53 [MOD 2 * 3] :=
      (Nat.modEq_and_modEq_iff_modEq_mul (by decide)).mp ⟨e2, e3⟩
    have e30 : x ≡ 53 [MOD 2 * 3 * 5] :=
      (Nat.modEq_and_modEq_iff_modEq_mul (by decide)).mp ⟨e6, e5⟩
    have e210 : x ≡ 53 [MOD 2 * 3 * 5 * 7] :=
      (Nat.modEq_and_modEq_iff_modEq_mul (by decide)).mp ⟨e30, e7⟩
    have : x % 210 = 53 % 210 := e210
    omega
  · rintro rfl
    refine ⟨by decide, by decide, by decide, by decide⟩

/-- The four-moduli solution value `53`. -/
theorem four_moduli_value :
    (53 : ℕ) % 2 = 1 ∧ (53 : ℕ) % 3 = 2 ∧ (53 : ℕ) % 5 = 3 ∧ (53 : ℕ) % 7 = 4 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/- ## A reusable axiom-free two-modulus certificate -/

/-- A general, axiom-free CRT certificate for two coprime moduli: if the witness
`N` satisfies both congruences and is in range, then over `0 ≤ x < m*n` the pair
of congruences holds *iff* `x = N`. This is the structural fact the numeric
examples above instantiate — established without `native_decide`. -/
theorem crt_pair_iff {m n N : ℕ} (hmn : Nat.Coprime m n) (hN : N < m * n)
    {a b : ℕ} (ha : N % m = a) (hb : N % n = b) (x : ℕ) (hx : x < m * n) :
    (x % m = a ∧ x % n = b) ↔ x = N := by
  constructor
  · rintro ⟨hxa, hxb⟩
    have em : x ≡ N [MOD m] := by unfold Nat.ModEq; omega
    have en : x ≡ N [MOD n] := by unfold Nat.ModEq; omega
    have emn : x ≡ N [MOD m * n] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hmn).mp ⟨em, en⟩
    have hxmod : x % (m * n) = N % (m * n) := emn
    rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hN] at hxmod
    exact hxmod
  · rintro rfl
    exact ⟨ha, hb⟩

end ChineseRemainderConstructiveOQ05
