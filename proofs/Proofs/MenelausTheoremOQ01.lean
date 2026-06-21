import Proofs.MenelausTheorem
import Mathlib.Tactic

/-
# Menelaus follow-up: signed/unsigned reconciliation and external-segment parity

Open question: `menelaus-theorem-oq-01-oq-01`
Parent: `Proofs/MenelausTheorem.lean` (`menelaus-theorem-oq-01`).

## What this adds

The parent proves the *signed* Menelaus criterion: for a non-degenerate triangle
`A B C` with transversal division parameters `t, u, v`, the three division points
`X, Y, Z` are collinear iff the product of signed side ratios

  `menelausProduct cfg = (t/(1-t)) · (u/(1-u)) · (v/(1-v)) = -1`.

Two natural questions are *not* answered by the signed criterion alone:

1. **Reconciliation with the unsigned form.** Many textbooks state Menelaus with an
   *unsigned* product equal to `1`. We show the signed criterion forces the unsigned
   product `|BX/XC| · |CY/YA| · |AZ/ZB|` to equal exactly `1` — the sign `-1` is the
   only extra information the signed statement carries.

2. **External-segment parity.** The signed ratio `s/(1-s)` of a division point is
   *negative* exactly when the point lies **outside** its segment (external division),
   and *positive* when it lies strictly between the endpoints (internal division).
   Since the signed product is `-1 < 0`, an **odd** number (one or all three) of the
   division points must be external. Conversely the Ceva-type value `+1 > 0` forces an
   **even** number (zero or two). This is the classical parity dichotomy
   `Menelaus = odd # external`, `Ceva = even # external`.

## Status
- [x] Sign of a division ratio characterises external vs internal division
- [x] Signed product `-1` ⟹ unsigned product `1` (reconciliation)
- [x] Signed product `-1` ⟹ odd number of external points
- [x] Signed product `+1` ⟹ even number of external points
- [x] Concrete witness: the parent's collinear instance has all three external
- [x] 0 sorries, 0 axioms
-/

namespace MenelausTheoremOQ01

open MenelausTheorem

set_option linter.unusedVariables false

/-- The signed side ratio `BX/XC = t/(1-t)` of the point `X` on line `BC`. -/
noncomputable def rX (cfg : MenelausConfig) : ℝ := cfg.t / (1 - cfg.t)

/-- The signed side ratio `CY/YA = u/(1-u)` of the point `Y` on line `CA`. -/
noncomputable def rY (cfg : MenelausConfig) : ℝ := cfg.u / (1 - cfg.u)

/-- The signed side ratio `AZ/ZB = v/(1-v)` of the point `Z` on line `AB`. -/
noncomputable def rZ (cfg : MenelausConfig) : ℝ := cfg.v / (1 - cfg.v)

/-- The three signed ratios multiply to the Menelaus product. Definitional. -/
theorem product_eq (cfg : MenelausConfig) :
    rX cfg * rY cfg * rZ cfg = menelausProduct cfg := rfl

/-! ### Sign of a division ratio ↔ external vs internal division -/

/-- A division point with parameter `s` (point `= (1-s)·P + s·Q`) lies **outside** the
    segment `PQ` exactly when `s < 0` or `1 < s`; in that case the signed ratio
    `s/(1-s)` is negative. -/
theorem ratio_neg_iff {s : ℝ} (hs : s ≠ 1) :
    s / (1 - s) < 0 ↔ s < 0 ∨ 1 < s := by
  have h1 : (1 : ℝ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  rw [div_neg_iff]
  constructor
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact Or.inr (by linarith)
    · exact Or.inl ha
  · rintro (h | h)
    · exact Or.inr ⟨h, by linarith⟩
    · exact Or.inl ⟨by linarith, by linarith⟩

/-- A division point lies strictly **between** the endpoints (internal division) exactly
    when `0 < s < 1`; in that case the signed ratio `s/(1-s)` is positive. -/
theorem ratio_pos_iff {s : ℝ} (hs : s ≠ 1) :
    0 < s / (1 - s) ↔ 0 < s ∧ s < 1 := by
  have h1 : (1 : ℝ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  rw [div_pos_iff]
  constructor
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · exact ⟨ha, by linarith⟩
    · exact absurd hb (by linarith)
  · rintro ⟨ha, hb⟩
    exact Or.inl ⟨ha, by linarith⟩

/-- `X` is an external division point of `BC` iff its signed ratio is negative. -/
theorem external_X_iff (cfg : MenelausConfig) :
    rX cfg < 0 ↔ cfg.t < 0 ∨ 1 < cfg.t := ratio_neg_iff cfg.t_ne_1

/-- `Y` is an external division point of `CA` iff its signed ratio is negative. -/
theorem external_Y_iff (cfg : MenelausConfig) :
    rY cfg < 0 ↔ cfg.u < 0 ∨ 1 < cfg.u := ratio_neg_iff cfg.u_ne_1

/-- `Z` is an external division point of `AB` iff its signed ratio is negative. -/
theorem external_Z_iff (cfg : MenelausConfig) :
    rZ cfg < 0 ↔ cfg.v < 0 ∨ 1 < cfg.v := ratio_neg_iff cfg.v_ne_1

/-! ### Reconciliation: signed `-1` ⟹ unsigned `1` -/

/-- **Signed/unsigned reconciliation.** When the signed Menelaus product is `-1`
    (collinear transversal), the *unsigned* product of side ratios equals `1`. The sign
    is the only extra information carried by the signed statement. -/
theorem unsigned_product_eq_one (cfg : MenelausConfig)
    (h : menelausProduct cfg = -1) :
    |rX cfg| * |rY cfg| * |rZ cfg| = 1 := by
  calc |rX cfg| * |rY cfg| * |rZ cfg|
      = |rX cfg * rY cfg * rZ cfg| := by rw [← abs_mul, ← abs_mul]
    _ = |menelausProduct cfg| := by rw [product_eq]
    _ = |(-1 : ℝ)| := by rw [h]
    _ = 1 := by norm_num

/-! ### External-segment parity -/

/-- **External parity (Menelaus).** A collinear transversal (`menelausProduct = -1`)
    crosses an **odd** number of the triangle's sides externally: either all three
    division points are external, or exactly one is (the other two internal). The four
    disjuncts list, in order, "all three external" and the three "exactly one external"
    configurations. -/
theorem external_parity_odd (cfg : MenelausConfig)
    (h : menelausProduct cfg = -1) :
    (rX cfg < 0 ∧ rY cfg < 0 ∧ rZ cfg < 0)
    ∨ (rX cfg < 0 ∧ 0 < rY cfg ∧ 0 < rZ cfg)
    ∨ (0 < rX cfg ∧ rY cfg < 0 ∧ 0 < rZ cfg)
    ∨ (0 < rX cfg ∧ 0 < rY cfg ∧ rZ cfg < 0) := by
  have key : rX cfg * rY cfg * rZ cfg = -1 := by rw [product_eq]; exact h
  have hX0 : rX cfg ≠ 0 := by rintro h0; rw [h0] at key; simp at key
  have hY0 : rY cfg ≠ 0 := by rintro h0; rw [h0] at key; simp at key
  have hZ0 : rZ cfg ≠ 0 := by rintro h0; rw [h0] at key; simp at key
  rcases lt_or_gt_of_ne hX0 with hX | hX <;>
    rcases lt_or_gt_of_ne hY0 with hY | hY <;>
      rcases lt_or_gt_of_ne hZ0 with hZ | hZ
  · exact Or.inl ⟨hX, hY, hZ⟩
  · nlinarith [mul_pos (mul_pos_of_neg_of_neg hX hY) hZ]
  · nlinarith [mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hX hY) hZ]
  · exact Or.inr (Or.inl ⟨hX, hY, hZ⟩)
  · nlinarith [mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hX hY) hZ]
  · exact Or.inr (Or.inr (Or.inl ⟨hX, hY, hZ⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hX, hY, hZ⟩))
  · nlinarith [mul_pos (mul_pos hX hY) hZ]

/-- **External parity (Ceva companion).** When the product is `+1` — the Ceva value of
    concurrency — an **even** number of division points are external: either none (all
    three internal), or exactly two. The four disjuncts list "none external" and the
    three "exactly two external" configurations. -/
theorem external_parity_even (cfg : MenelausConfig)
    (h : menelausProduct cfg = 1) :
    (0 < rX cfg ∧ 0 < rY cfg ∧ 0 < rZ cfg)
    ∨ (0 < rX cfg ∧ rY cfg < 0 ∧ rZ cfg < 0)
    ∨ (rX cfg < 0 ∧ 0 < rY cfg ∧ rZ cfg < 0)
    ∨ (rX cfg < 0 ∧ rY cfg < 0 ∧ 0 < rZ cfg) := by
  have key : rX cfg * rY cfg * rZ cfg = 1 := by rw [product_eq]; exact h
  have hX0 : rX cfg ≠ 0 := by rintro h0; rw [h0] at key; simp at key
  have hY0 : rY cfg ≠ 0 := by rintro h0; rw [h0] at key; simp at key
  have hZ0 : rZ cfg ≠ 0 := by rintro h0; rw [h0] at key; simp at key
  rcases lt_or_gt_of_ne hX0 with hX | hX <;>
    rcases lt_or_gt_of_ne hY0 with hY | hY <;>
      rcases lt_or_gt_of_ne hZ0 with hZ | hZ
  · nlinarith [mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hX hY) hZ]
  · exact Or.inr (Or.inr (Or.inr ⟨hX, hY, hZ⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨hX, hY, hZ⟩))
  · nlinarith [mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hX hY) hZ]
  · exact Or.inr (Or.inl ⟨hX, hY, hZ⟩)
  · nlinarith [mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hX hY) hZ]
  · nlinarith [mul_neg_of_pos_of_neg (mul_pos hX hY) hZ]
  · exact Or.inl ⟨hX, hY, hZ⟩

/-! ### Concrete witness -/

/-- The parent's worked collinear instance — triangle `(0,0),(1,0),(0,1)` with
    `t = u = 2`, `v = -1/3` — realises the **all-three-external** case: each division
    point lies outside its segment, and the unsigned product is `1`. -/
theorem example_all_external :
    ∃ cfg : MenelausConfig,
      menelausProduct cfg = -1 ∧
      (rX cfg < 0 ∧ rY cfg < 0 ∧ rZ cfg < 0) ∧
      |rX cfg| * |rY cfg| * |rZ cfg| = 1 := by
  refine ⟨{ A := (0, 0), B := (1, 0), C := (0, 1), t := 2, u := 2, v := -1/3,
            t_ne_1 := by norm_num, u_ne_1 := by norm_num, v_ne_1 := by norm_num,
            nondegen := by norm_num [collinearDet] }, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · unfold menelausProduct; norm_num
  · unfold rX; norm_num
  · unfold rY; norm_num
  · unfold rZ; norm_num
  · unfold rX rY rZ; norm_num

end MenelausTheoremOQ01
