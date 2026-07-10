/-
# Erdős Problem #101 — OQ-04-OQ-01: a general-position arc has zero k-point lines for every k ≥ 3

Erdős Problem #101 concerns the maximum number of lines through exactly four
points (`fourPointLineCount`) of a planar `n`-point set with no five collinear.
The parent `Proofs/Erdos101OQ04` builds the **mod-`p` Grünbaum parabola**,
realizes it in ℝ² as an explicit `p`-point arc (`realParabolaSet`), proves it
has *no three collinear* points, and records — as the honest scope of the bare
arc — that its `fourPointLineCount` is `0` (`realParabolaSet_fourPointLineCount_zero`):
the Ω(p^{3/2}) four-point-line count must come from a sumset/grid construction
*on top of* this general-position base, not from the arc itself.

This child sharpens and uniformizes that observation.  The `fourPointLineCount`
being `0` is the `k = 4` shadow of a single general-position fact: a set with no
three collinear points has **no `k` points on a common line for any `k ≥ 3`**.
We make this precise.

  * `kPointLineCount P k` — the obvious `k`-parameterised generalization of the
    gallery's `fourPointLineCount` (`fourPointLineCount = kPointLineCount · 4`,
    `rfl`).
  * `kPointLineCount_eq_zero_of_no_three_collinear` — **the reusable engine**: if
    `P` has no three collinear points then `kPointLineCount P k = 0` for every
    `k ≥ 3`.  Any `k`-set on a line through `a ≠ b` has `k ≥ 3 > 2` points, hence
    a third point `c ∉ {a, b}`, and `a, b, c` are three distinct collinear points
    — impossible.
  * `realParabolaSet_kPointLineCount_zero` — the arc instance: the lifted
    Grünbaum parabola has zero `k`-point lines for *every* `k ≥ 3`.
  * `realParabolaSet_fourPointLineCount_zero'` — recovers the parent's headline
    as the `k = 4` special case, now via the uniform certificate.

The picture: an arc is "line-poor" at every scale `≥ 3` simultaneously; the
four-point obstruction is not special, it is the general-position property read
off at one value of `k`.

Reference: Erdős Problem #101, https://erdosproblems.com/101
-/

import Proofs.Erdos101OQ04

namespace Erdos101OQ04OQ01

open Erdos101OQ04 Erdos101OQ04.Grunbaum Classical

/-- `kPointLineCount P k` counts the `k`-element subsets of `P` that lie on a
common line (witnessed by two distinct anchors `a ≠ b` with everything collinear
with `a, b`).  For `k = 4` this is the gallery's `fourPointLineCount`. -/
noncomputable def kPointLineCount (P : PlanarPointSet) (k : ℕ) : ℕ :=
  (P.points.powerset.filter (fun S =>
    S.card = k ∧
    ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      ∀ p ∈ S, collinear a b p)).card

/-- `kPointLineCount` at `k = 4` is exactly the gallery's `fourPointLineCount`
(definitional). -/
theorem fourPointLineCount_eq_kPointLineCount (P : PlanarPointSet) :
    fourPointLineCount P = kPointLineCount P 4 := rfl

/-- **General-position engine.**  If no three points of `P` are collinear, then
for every `k ≥ 3` there are *no* `k` points on a common line: `kPointLineCount P k = 0`.

The witnessing `k`-set on a line through `a ≠ b` has `k ≥ 3 > 2 = |{a, b}|`
elements, so it contains a third point `c ∉ {a, b}`; then `a, b, c` are three
distinct collinear points, contradicting the hypothesis. -/
theorem kPointLineCount_eq_zero_of_no_three_collinear
    (P : PlanarPointSet) {k : ℕ} (hk : 3 ≤ k)
    (h3 : ∀ a b c : ℝ × ℝ, a ∈ P.points → b ∈ P.points → c ∈ P.points →
      a ≠ b → a ≠ c → b ≠ c → ¬ collinear a b c) :
    kPointLineCount P k = 0 := by
  rw [kPointLineCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro S hS
  simp only [Finset.mem_powerset] at hS
  rintro ⟨hScard, a, b, ha, hb, hab, hline⟩
  -- `|S| = k ≥ 3 > 2`, so `S` is not contained in `{a, b}`: a third point exists.
  have hthird : ∃ c ∈ S, c ∉ ({a, b} : Finset (ℝ × ℝ)) := by
    by_contra hcon
    push_neg at hcon
    have hSsub : S ⊆ ({a, b} : Finset (ℝ × ℝ)) := fun x hx => hcon x hx
    have hle := Finset.card_le_card hSsub
    rw [hScard, Finset.card_pair hab] at hle
    omega
  obtain ⟨c, hcS, hcab⟩ := hthird
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcab
  push_neg at hcab
  exact h3 a b c (hS ha) (hS hb) (hS hcS) hab
    (fun h => hcab.1 h.symm) (fun h => hcab.2 h.symm) (hline c hcS)

/-- **The lifted Grünbaum arc has zero `k`-point lines for every `k ≥ 3`.**
The uniform general-position certificate: the bare parabola is line-poor at
every scale `≥ 3`, not merely at `k = 4`. -/
theorem realParabolaSet_kPointLineCount_zero (p : ℕ) [NeZero p] [Fact p.Prime]
    (hp : p ≠ 2) {k : ℕ} (hk : 3 ≤ k) :
    kPointLineCount (realParabolaSet p hp) k = 0 :=
  kPointLineCount_eq_zero_of_no_three_collinear (realParabolaSet p hp) hk
    (fun a b c hA hB hC hab hac hbc =>
      realParabola_no_three_collinear p hp a b c hA hB hC hab hac hbc)

/-- The parent's headline `realParabolaSet_fourPointLineCount_zero` recovered as
the `k = 4` instance of the uniform certificate. -/
theorem realParabolaSet_fourPointLineCount_zero' (p : ℕ) [NeZero p]
    [Fact p.Prime] (hp : p ≠ 2) :
    fourPointLineCount (realParabolaSet p hp) = 0 := by
  rw [fourPointLineCount_eq_kPointLineCount]
  exact realParabolaSet_kPointLineCount_zero p hp (by norm_num)

/-- The three-point version: the arc has zero *triangles-on-a-line*, the
defining general-position property stated as a count. -/
theorem realParabolaSet_threePointLineCount_zero (p : ℕ) [NeZero p]
    [Fact p.Prime] (hp : p ≠ 2) :
    kPointLineCount (realParabolaSet p hp) 3 = 0 :=
  realParabolaSet_kPointLineCount_zero p hp (le_refl 3)

/-- **Universal counting upper bound.** A `k`-point line is in particular a
`k`-element subset of the `n = |P|` points, so there are at most `C(n, k)` of them:
`kPointLineCount P k ≤ (|P|).choose k`. This is the general-position-free companion of
the `= 0` lower results above — the collinearity constraint can only *cut down* the
raw subset count `C(n, k)`, never exceed it. -/
theorem kPointLineCount_le_choose (P : PlanarPointSet) (k : ℕ) :
    kPointLineCount P k ≤ P.points.card.choose k := by
  rw [kPointLineCount, ← Finset.card_powersetCard k P.points]
  apply Finset.card_le_card
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS
  rw [Finset.mem_powersetCard]
  exact ⟨hS.1, hS.2.1⟩

/-- **Vacuity below the point count.** A set with fewer than `k` points cannot carry
any `k`-point line: `|P| < k ⟹ kPointLineCount P k = 0`. Any witnessing subset `S`
satisfies `k = |S| ≤ |P| < k`, a contradiction. Together with
`kPointLineCount_le_choose` this bookends the count: it vanishes past `|P|` and never
exceeds `C(|P|, k)`. -/
theorem kPointLineCount_eq_zero_of_card_lt (P : PlanarPointSet) {k : ℕ}
    (hk : P.points.card < k) : kPointLineCount P k = 0 := by
  rw [kPointLineCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro S hS
  simp only [Finset.mem_powerset] at hS
  rintro ⟨hScard, -⟩
  have hle := Finset.card_le_card hS
  omega

end Erdos101OQ04OQ01
