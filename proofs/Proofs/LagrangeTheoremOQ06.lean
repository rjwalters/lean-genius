/-
The Tower Law for Subgroup Indices

Source: Open question from lagrange-theorem gallery proof (lagrange-theorem-oq-06)
Status: VERIFIED (0 axioms, 0 sorries)

For a tower of subgroups `K ≤ H ≤ G`, the index is multiplicative:

  [G : K] = [G : H] · [H : K]

where `[H : K]` is the *relative index* `K.relIndex H`. This is the
index-theoretic refinement of Lagrange's theorem. Unlike the finite divisibility
statement `|H| ∣ |G|`, the tower law holds in an *arbitrary* (possibly infinite)
group: `[G : K] = Nat.card (G ⧸ K)`, interpreted as `0` when the quotient is
infinite, and the multiplicative identity still holds.

Taking `K = ⊥` recovers the classical Lagrange index form `|G| = [G : H] · |H|`.
Iterating the law gives the chain rule for a three-step tower
`K₁ ≤ K₂ ≤ K₃ ≤ G`, and the law immediately yields the divisibility tower
`[G : H] ∣ [G : K]` and `[H : K] ∣ [G : K]`.

The analytic content (the bijection on cosets behind each factorisation) is
delegated to Mathlib's `Subgroup.relIndex_mul_index` and
`Subgroup.relIndex_mul_relIndex`. The contribution here is packaging the tower
law in standard index notation, deriving the divisibility corollaries, the
three-step chain rule, and the Lagrange specialization as a uniform family.
-/

import Mathlib

open Subgroup

namespace IndexTowerLaw

variable {G : Type*} [Group G]

/-! ## Part I: The tower law

For `K ≤ H ≤ G`, the index `[G : K]` factors as `[G : H] · [H : K]`. We write
`[G : K] = K.index` and `[H : K] = K.relIndex H` (the index of `K` inside `H`). -/

/-- **Tower law for subgroup indices.** For `K ≤ H ≤ G`,
    `[G : K] = [G : H] · [H : K]`. Here `[H : K] = K.relIndex H`. -/
theorem index_tower (K H : Subgroup G) (h : K ≤ H) :
    K.index = H.index * K.relIndex H := by
  rw [← relIndex_mul_index h]; exact mul_comm _ _

/-- **Relative tower law.** For `K ≤ H ≤ L`, the relative index of `K` in `L`
    factors through `H`: `[L : K] = [L : H] · [H : K]`. -/
theorem relIndex_tower (K H L : Subgroup G) (hKH : K ≤ H) (hHL : H ≤ L) :
    K.relIndex L = H.relIndex L * K.relIndex H := by
  rw [← relIndex_mul_relIndex K H L hKH hHL]; exact mul_comm _ _

/-! ## Part II: Divisibility corollaries

Each factor of the tower law divides the total index. -/

/-- The index of the larger subgroup divides the index of the smaller one:
    `[G : H] ∣ [G : K]` for `K ≤ H`. -/
theorem index_dvd_tower (K H : Subgroup G) (h : K ≤ H) : H.index ∣ K.index :=
  index_dvd_of_le h

/-- The relative index divides the absolute index: `[H : K] ∣ [G : K]` for
    `K ≤ H`. -/
theorem relIndex_dvd_tower (K H : Subgroup G) (h : K ≤ H) :
    K.relIndex H ∣ K.index :=
  relIndex_dvd_index_of_le h

/-! ## Part III: The three-step chain rule

Iterating the tower law over `K₁ ≤ K₂ ≤ K₃` gives a triple factorisation. -/

/-- **Chain rule.** For a three-step tower `K₁ ≤ K₂ ≤ K₃ ≤ G`,
    `[G : K₁] = [G : K₃] · [K₃ : K₂] · [K₂ : K₁]`. -/
theorem index_tower_three (K₁ K₂ K₃ : Subgroup G)
    (h₁ : K₁ ≤ K₂) (h₂ : K₂ ≤ K₃) :
    K₁.index = K₃.index * (K₂.relIndex K₃ * K₁.relIndex K₂) := by
  rw [index_tower K₁ K₃ (h₁.trans h₂), relIndex_tower K₁ K₂ K₃ h₁ h₂]

/-! ## Part IV: Lagrange's theorem as the `K = ⊥` specialization

The tower law specialises to the classical Lagrange index form when the small
subgroup is trivial: `[G : ⊥] = |G|` and `[H : ⊥] = |H|`. -/

/-- **Lagrange index form, recovered from the tower law.**
    `|G| = [G : H] · |H|`, obtained as the `K = ⊥` case of `index_tower`. -/
theorem lagrange_from_tower (H : Subgroup G) :
    Nat.card G = H.index * Nat.card H := by
  have h := index_tower ⊥ H bot_le
  rwa [index_bot, relIndex_bot_left] at h

/-- Lagrange's index form is exactly Mathlib's `index_mul_card`; the tower-law
    derivation agrees with it. -/
theorem lagrange_index_form (H : Subgroup G) :
    H.index * Nat.card H = Nat.card G :=
  H.index_mul_card

/-! ## Part V: Degenerate endpoints

The tower law is consistent with the boundary identities `[G : G] = 1` and
`[H : H] = 1`. -/

/-- Taking `H = G` (i.e. `H = ⊤`) makes the tower trivial: `[⊤ : K] = [G : K]`. -/
theorem relIndex_top_eq_index (K : Subgroup G) : K.relIndex ⊤ = K.index :=
  relIndex_top_right K

/-- The self-index is `1`, so the tower law degenerates correctly at `K = H`:
    `[G : H] = [G : H] · [H : H] = [G : H] · 1`. -/
theorem tower_self (H : Subgroup G) :
    H.index = H.index * H.relIndex H := by
  rw [relIndex_self, mul_one]

end IndexTowerLaw
