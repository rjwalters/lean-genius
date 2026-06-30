import Mathlib

/-
# Burnside Counting: Colorings Fixed by a Reflection of a Cycle

For the dihedral group `D_n` acting on the `n` positions of a cycle, this file counts
the `k`-colorings fixed by a **reflection**. We model the positions as `ZMod n` and the
reflection through position `0` as negation `i ↦ -i` (an involution).

A coloring `c : ZMod n → Fin k` is fixed by the reflection iff `c (-i) = c i` for all `i`,
i.e. `c` is constant on each reflection orbit `{i, -i}`. For **odd** `n = 2m+1` the only
fixed point of the reflection is `0`, so the orbits are `{0}` together with the `m` pairs
`{j, -j}` for `1 ≤ j ≤ m`; there are `m + 1 = (n+1)/2` orbits, and a fixed coloring assigns
one of `k` colors freely to each orbit. Hence the count is `k^((n+1)/2)`.

## Main results

* `reflect_involutive` — the reflection is an involution.
* `reflect_fixed_iff_zero` — for odd `n` the reflection fixes only `0`.
* `card_reflectionInvariant` — there are exactly `k^(m+1)` colorings of `ZMod (2m+1)`
  invariant under negation.
* `card_reflectionInvariant_odd` — restated for any odd `n` as `k^((n+1)/2)`.

The proof is a fully explicit bijection: a reflection-invariant coloring is determined by
its values on the fundamental domain `{0, 1, …, m}`, which it reconstructs by *folding*
each position `i` to `min(i.val, n - i.val)`.

This is the reflection (parity-dependent) counterpart of the rotation count
`k^gcd(n,r)` in `BurnsideCountingOQ03.lean`; the two reflection/rotation pieces together
feed Burnside's lemma for the full dihedral necklace count. Absent from Mathlib.
-/

namespace BurnsideCountingOQ05

variable {k : ℕ}

/-- The reflection of the `n`-cycle through position `0`, modelled as negation on `ZMod n`. -/
def reflect {n : ℕ} (i : ZMod n) : ZMod n := -i

theorem reflect_involutive {n : ℕ} : Function.Involutive (reflect (n := n)) := by
  intro i; simp [reflect]

/-- For odd `n = 2m+1`, the reflection `i ↦ -i` fixes only the position `0`. -/
theorem reflect_fixed_iff_zero (m : ℕ) (i : ZMod (2 * m + 1)) :
    reflect i = i ↔ i = 0 := by
  constructor
  · intro h
    -- `-i = i` gives `2 • i = 0`; since `2` is a unit mod the odd number `2m+1`, `i = 0`.
    have h2 : (2 : ZMod (2 * m + 1)) * i = 0 := by
      have hii : i + i = 0 := by
        have := h; simp only [reflect] at this; linear_combination -this
      linear_combination hii
    have hcop : Nat.Coprime 2 (2 * m + 1) := by
      rw [Nat.coprime_two_left]; exact ⟨m, rfl⟩
    have hu : IsUnit (2 : ZMod (2 * m + 1)) := by
      have := (ZMod.isUnit_iff_coprime 2 (2 * m + 1)).mpr hcop
      rwa [Nat.cast_ofNat] at this
    exact (hu.mul_right_eq_zero).mp h2
  · rintro rfl; simp [reflect]

/-- Inclusion of the fundamental domain `{0,…,m}` (as `Fin (m+1)`) into the cycle. -/
def incl (m : ℕ) (j : Fin (m + 1)) : ZMod (2 * m + 1) := (j.val : ZMod (2 * m + 1))

/-- Fold a position to its representative in `{0,…,m}` by `i ↦ min(i.val, n - i.val)`. -/
def fold (m : ℕ) (i : ZMod (2 * m + 1)) : Fin (m + 1) :=
  ⟨min i.val (2 * m + 1 - i.val), by have h := ZMod.val_lt i; omega⟩

theorem fold_incl (m : ℕ) (j : Fin (m + 1)) : fold m (incl m j) = j := by
  have hj : j.val < 2 * m + 1 := by omega
  apply Fin.ext
  simp only [fold, incl, ZMod.val_natCast_of_lt hj]
  have : j.val ≤ m := by omega
  omega

theorem fold_neg (m : ℕ) (i : ZMod (2 * m + 1)) : fold m (-i) = fold m i := by
  apply Fin.ext
  simp only [fold]
  rcases eq_or_ne i 0 with hi | hi
  · subst hi; simp
  · have hv := ZMod.val_lt i
    have hpos : 0 < i.val := by
      rcases Nat.eq_zero_or_pos i.val with h0 | h0
      · exact absurd ((ZMod.val_eq_zero i).mp h0) hi
      · exact h0
    rw [ZMod.neg_val, if_neg hi]
    omega

theorem incl_fold (m : ℕ) (i : ZMod (2 * m + 1)) :
    incl m (fold m i) = i ∨ incl m (fold m i) = -i := by
  have hv := ZMod.val_lt i
  rcases le_total i.val (2 * m + 1 - i.val) with h | h
  · left
    have hmin : min i.val (2 * m + 1 - i.val) = i.val := by omega
    simp only [incl, fold, hmin, ZMod.natCast_zmod_val]
  · right
    have hmin : min i.val (2 * m + 1 - i.val) = 2 * m + 1 - i.val := by omega
    simp only [incl, fold, hmin]
    have hle : i.val ≤ 2 * m + 1 := le_of_lt hv
    rw [Nat.cast_sub hle, ZMod.natCast_self, ZMod.natCast_zmod_val, zero_sub]

/-- The explicit bijection: a reflection-invariant coloring of `ZMod (2m+1)` is the same
data as an arbitrary coloring of the fundamental domain `Fin (m+1)`. -/
def reflectionInvariantEquiv (m k : ℕ) :
    {c : ZMod (2 * m + 1) → Fin k // ∀ i, c (-i) = c i} ≃ (Fin (m + 1) → Fin k) where
  toFun c j := c.1 (incl m j)
  invFun g := ⟨fun i => g (fold m i), by intro i; show g (fold m (-i)) = g (fold m i); rw [fold_neg]⟩
  left_inv := by
    rintro ⟨c, hc⟩
    apply Subtype.ext
    funext i
    show c (incl m (fold m i)) = c i
    rcases incl_fold m i with h | h
    · rw [h]
    · rw [h]; exact hc i
  right_inv := by
    intro g
    funext j
    show g (fold m (incl m j)) = g j
    rw [fold_incl]

/-- **Reflection-fixed colorings of an odd cycle.** For `n = 2m+1`, exactly `k^(m+1)`
colorings are invariant under the reflection `i ↦ -i`. -/
theorem card_reflectionInvariant (m k : ℕ) :
    Fintype.card {c : ZMod (2 * m + 1) → Fin k // ∀ i, c (-i) = c i} = k ^ (m + 1) := by
  rw [Fintype.card_congr (reflectionInvariantEquiv m k), Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]

/-- **Reflection count, odd case.** For any odd `n`, the number of `k`-colorings of the
`n`-cycle fixed by a reflection is `k^((n+1)/2)`. -/
theorem card_reflectionInvariant_odd (n k : ℕ) [NeZero n] (hn : Odd n) :
    Fintype.card {c : ZMod n → Fin k // ∀ i, c (-i) = c i} = k ^ ((n + 1) / 2) := by
  obtain ⟨m, rfl⟩ := hn
  rw [card_reflectionInvariant]
  congr 1
  omega

end BurnsideCountingOQ05
