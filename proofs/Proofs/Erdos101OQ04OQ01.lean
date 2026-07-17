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

/-- **Low-`k` vacuity.** A `k`-point line needs *two distinct anchors* to pin a
direction, so it carries at least two points: `kPointLineCount P k = 0` whenever
`k ≤ 1`. Any witnessing subset `S` supplies `a ≠ b` in `S`, forcing `2 ≤ |S| = k ≤ 1`.
This is the low end of the support: together with `kPointLineCount_eq_zero_of_card_lt`
(the high end, `|P| < k`) it confines the count to the band `2 ≤ k ≤ |P|`, outside of
which it vanishes identically. -/
theorem kPointLineCount_eq_zero_of_le_one (P : PlanarPointSet) {k : ℕ}
    (hk : k ≤ 1) : kPointLineCount P k = 0 := by
  rw [kPointLineCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro S hS
  simp only [Finset.mem_powerset] at hS
  rintro ⟨hScard, a, b, ha, hb, hab, -⟩
  have hsub : ({a, b} : Finset (ℝ × ℝ)) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have hle := Finset.card_le_card hsub
  rw [Finset.card_pair hab] at hle
  omega

/-- **Exact `k = 2` value: every pair is a line.** Two distinct points always lie on a
(unique) common line, so *every* `2`-element subset is a `2`-point line and
`kPointLineCount P 2 = C(|P|, 2)`. The witness for a pair `{a, b}` is the pair itself:
`collinear a b a` (degenerate, `(b₁−a₁)·0 = 0·(b₂−a₂)`) and `collinear a b b`
(`collinear_self_right`) hold trivially. This is the *equality* boundary of the generic
upper bound `kPointLineCount_le_choose` (which is `≤ C(|P|, k)` for all `k`): at `k = 2`
the collinearity constraint is vacuous, so the bound is attained. It sits at the bottom
of the support band `[2, |P|]`, one step below the general-position `= 0` region `k ≥ 3`. -/
theorem kPointLineCount_two (P : PlanarPointSet) :
    kPointLineCount P 2 = P.points.card.choose 2 := by
  rw [kPointLineCount, ← Finset.card_powersetCard 2 P.points]
  congr 1
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
  constructor
  · rintro ⟨hsub, hcard, -⟩
    exact ⟨hsub, hcard⟩
  · rintro ⟨hsub, hcard⟩
    refine ⟨hsub, hcard, ?_⟩
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
    refine ⟨a, b, Finset.mem_insert_self _ _,
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _), hab, fun p hp => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · unfold collinear; ring
    · exact collinear_self_right a _

/-- **The arc's exact `2`-point-line count.** The lifted Grünbaum parabola has
exactly `C(p, 2)` two-point lines: it has `p` points (`realParabola_card`), and by
`kPointLineCount_two` every pair is a line.  The `k = 2` value of the arc's profile. -/
theorem realParabolaSet_kPointLineCount_two (p : ℕ) [NeZero p] [Fact p.Prime]
    (hp : p ≠ 2) : kPointLineCount (realParabolaSet p hp) 2 = p.choose 2 := by
  rw [kPointLineCount_two, show (realParabolaSet p hp).points = realParabola p from rfl,
    realParabola_card p hp]

/-- **Complete line-profile of the Grünbaum arc.**  For the lifted parabola the
`k`-point-line count is determined at *every* `k` simultaneously:
`kPointLineCount (realParabolaSet p) k = C(p, 2)` if `k = 2`, and `0` otherwise.
The whole incidence profile collapses to a single nonzero value at `k = 2` — the
sharpest possible statement of "an arc is a pure pairs-only configuration."  It
unifies the three regimes established above: `k ≤ 1` vanishes
(`kPointLineCount_eq_zero_of_le_one`), `k = 2` is `C(p, 2)`
(`realParabolaSet_kPointLineCount_two`), and `k ≥ 3` vanishes by general position
(`realParabolaSet_kPointLineCount_zero`).  In particular the four-point count
`realParabolaSet_fourPointLineCount_zero` is the `k = 4 ≠ 2` instance. -/
theorem realParabolaSet_kPointLineCount_profile (p : ℕ) [NeZero p] [Fact p.Prime]
    (hp : p ≠ 2) (k : ℕ) :
    kPointLineCount (realParabolaSet p hp) k = if k = 2 then p.choose 2 else 0 := by
  rcases lt_trichotomy k 2 with hk | hk | hk
  · rw [if_neg (by omega : k ≠ 2)]
    exact kPointLineCount_eq_zero_of_le_one _ (by omega)
  · rw [hk, if_pos rfl]
    exact realParabolaSet_kPointLineCount_two p hp
  · rw [if_neg (by omega : k ≠ 2)]
    exact realParabolaSet_kPointLineCount_zero p hp (by omega)

end Erdos101OQ04OQ01
