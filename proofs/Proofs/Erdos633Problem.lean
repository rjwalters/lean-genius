/-
  Erdős Problem #633: Square Number Dissections of Triangles

  Source: https://erdosproblems.com/633
  Status: OPEN
  Prize: $25

  Statement:
  Classify those triangles which can ONLY be cut into a square number
  of congruent triangles.

  Context:
  - Every triangle can be dissected into n² congruent triangles for any n ≥ 1
  - The question asks: which triangles CANNOT be dissected into any
    non-square number of congruent copies?

  Known Results (Soifer):
  - Triangles with sides √2, √3, √4 can only be dissected into square
    numbers of congruent triangles
  - This property relates to "integral independence" of angles and sides
  - The full classification remains OPEN

  Related Problem #634:
  For similar (not congruent) dissections, every triangle can be cut into
  n similar triangles for all n except n = 2, 3, 5.

  The Underlying Math:
  - Dissecting into congruent triangles requires precise geometric constraints
  - The dissection count must satisfy area and angle compatibility conditions
  - Square numbers arise naturally from "scaling" dissections (n×n grids)
-/

import Mathlib

open Real Set

/-! ## Triangle Representation -/

/-- A triangle represented by its three side lengths -/
structure Triangle where
  a : ℝ
  b : ℝ
  c : ℝ
  ha : a > 0
  hb : b > 0
  hc : c > 0
  -- Triangle inequality
  hab : a + b > c
  hbc : b + c > a
  hca : c + a > b

/-- A triangle represented by its three angles (in radians) -/
structure TriangleByAngles where
  α : ℝ
  β : ℝ
  γ : ℝ
  hα : 0 < α ∧ α < π
  hβ : 0 < β ∧ β < π
  hγ : 0 < γ ∧ γ < π
  hsum : α + β + γ = π

/-- The area of a triangle using Heron's formula -/
noncomputable def Triangle.area (T : Triangle) : ℝ :=
  let s := (T.a + T.b + T.c) / 2
  Real.sqrt (s * (s - T.a) * (s - T.b) * (s - T.c))

/-- Scaling all side lengths of a triangle by a positive factor `t`.
    The result is a triangle similar to `T` with linear scale `t`. -/
noncomputable def Triangle.scale (T : Triangle) (t : ℝ) (ht : 0 < t) : Triangle where
  a := t * T.a
  b := t * T.b
  c := t * T.c
  ha := mul_pos ht T.ha
  hb := mul_pos ht T.hb
  hc := mul_pos ht T.hc
  hab := by
    have h := mul_lt_mul_of_pos_left T.hab ht
    rw [mul_add] at h; linarith
  hbc := by
    have h := mul_lt_mul_of_pos_left T.hbc ht
    rw [mul_add] at h; linarith
  hca := by
    have h := mul_lt_mul_of_pos_left T.hca ht
    rw [mul_add] at h; linarith

/-- **Heron's area is homogeneous of degree 2 in the side lengths.**
    Scaling a triangle's sides by `t > 0` scales its area by `t²`.

    This is the genuine geometric fact underlying Erdős #633's background result
    that "every triangle dissects into `n²` congruent copies": a copy similar to
    `T` with linear scale `1/n` has area `T.area / n²`, so `n²` of them match `T`'s
    area exactly. The proof factors `(t²)²` out of all four Heron factors and pulls
    it through the square root. -/
theorem Triangle.area_scale (T : Triangle) (t : ℝ) (ht : 0 < t) :
    (T.scale t ht).area = t ^ 2 * T.area := by
  have ht2 : (0:ℝ) ≤ t ^ 2 := le_of_lt (pow_pos ht 2)
  simp only [Triangle.area, Triangle.scale]
  rw [← Real.sqrt_sq ht2, ← Real.sqrt_mul (sq_nonneg (t ^ 2))]
  congr 1
  ring

/-! ## Dissection Definitions

  NOTE ON THE MODEL: `CongruentDissection` below captures only the two
  *necessary* numeric conditions for a congruent dissection — area
  compatibility (`area T = n · area S`) and shared side ratios (`S` similar to
  `T`). It does NOT encode an actual geometric tiling. As a consequence this
  simplified model OVER-counts: by `Triangle.area_scale`, the scaled copy
  `T.scale (1/√n)` satisfies both conditions for *every* `n ≥ 1`, so in this
  model `DissectionCounts T = {n | n ≥ 1}` for all `T`.

  The theorems proved against this model (`universal_square_dissection`,
  `equilateral_dissects_to_3`, `right_isoceles_dissects_to_2`) are therefore
  genuine *area-compatibility* statements, not full geometric dissection
  results. Every square-only claim is FALSE in this over-counting model — we record
  the proved *negations* (`soiferTriangle_not_square_only_in_model`,
  `no_square_only_witness_in_model`, `squareOnly_empty_in_model`) rather than
  `sorry`-ing the false positives. Capturing Soifer's genuine results requires a real
  geometric tiling predicate (the open, hard content of Erdős #633). -/

/-- A dissection of triangle T into n congruent copies of triangle S.
    (Simplified model: area compatibility + similarity only — see the note
    above; this is a necessary condition for, not a witness of, a tiling.) -/
structure CongruentDissection (T S : Triangle) (n : ℕ) where
  -- The n copies tile T exactly
  covers : T.area = n * S.area
  -- S is congruent to some rescaling (for this problem, S should be congruent to T)
  congruent : S.a / T.a = S.b / T.b ∧ S.b / T.b = S.c / T.c

/-- A triangle can be dissected into n congruent copies -/
def CanDissectInto (T : Triangle) (n : ℕ) : Prop :=
  ∃ S : Triangle, Nonempty (CongruentDissection T S n)

/-- The set of valid dissection counts for a triangle -/
def DissectionCounts (T : Triangle) : Set ℕ :=
  {n : ℕ | n ≥ 1 ∧ CanDissectInto T n}

/-! ## Square Number Property -/

/-- A number is a perfect square.
    (Named `IsPerfectSquare` to avoid clashing with Mathlib's `IsSquare`,
    which was introduced into the root namespace after this file was written.) -/
def IsPerfectSquare (n : ℕ) : Prop := ∃ k : ℕ, n = k^2

/-- A triangle has the "square-only" property if it can only be dissected
    into square numbers of congruent copies -/
def HasSquareOnlyProperty (T : Triangle) : Prop :=
  ∀ n ∈ DissectionCounts T, IsPerfectSquare n

/-- The set of triangles with the square-only property -/
def SquareOnlyTriangles : Set Triangle :=
  {T : Triangle | HasSquareOnlyProperty T}

/-! ## Universal Dissection into Squares -/

/-- Every triangle can be dissected into n² congruent triangles for any n ≥ 1.

    Witnessed by the similar copy `S = T.scale (1/n)`: by area-homogeneity
    (`Triangle.area_scale`) it has area `T.area / n²`, so `n²` copies of `S`
    match `T`'s area, and `S` shares `T`'s side ratios. This is the
    area-compatibility ("necessary condition") form of the classical grid
    construction, in the simplified dissection model used in this file. -/
theorem universal_square_dissection (T : Triangle) (n : ℕ) (hn : n ≥ 1) :
    CanDissectInto T (n^2) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hne : (n:ℝ) ≠ 0 := ne_of_gt hn0
  refine ⟨T.scale (1 / (n:ℝ)) (one_div_pos.mpr hn0), ⟨⟨?_, ?_, ?_⟩⟩⟩
  · rw [Triangle.area_scale]
    push_cast
    rw [div_pow, one_pow, ← mul_assoc, mul_one_div, div_self (pow_ne_zero 2 hne), one_mul]
  · simp only [Triangle.scale]
    rw [mul_div_assoc, div_self (ne_of_gt T.ha), mul_one,
        mul_div_assoc, div_self (ne_of_gt T.hb), mul_one]
  · simp only [Triangle.scale]
    rw [mul_div_assoc, div_self (ne_of_gt T.hb), mul_one,
        mul_div_assoc, div_self (ne_of_gt T.hc), mul_one]

/-- This means every triangle has all square numbers in its dissection set -/
theorem squares_always_achievable (T : Triangle) :
    ∀ k ≥ 1, k^2 ∈ DissectionCounts T := by
  intro k hk
  constructor
  · exact Nat.one_le_pow 2 k (by omega)
  · exact universal_square_dissection T k hk

/-! ## Model Adequacy: the simplified model collapses

  The dissection note above observes informally that the simplified
  area+similarity model OVER-counts: by `Triangle.area_scale` the scaled copy
  `T.scale (1/√n)` satisfies both numeric conditions for *every* `n ≥ 1`, not
  just perfect squares. The three theorems below turn that informal remark into
  proved statements:

  * `all_counts_achievable` / `dissectionCounts_eq` — in this model
    `DissectionCounts T = {n | n ≥ 1}` for every triangle `T`.
  * `no_square_only_in_model` — consequently NO triangle has the square-only
    property here (the non-square count `2` is always achievable).

  This is the precise reason every square-only statement is *model-false* in the
  present model rather than merely unproved: Soifer's triangle, any square-only
  witness, and the whole `SquareOnlyTriangles` set are refuted directly by
  `no_square_only_in_model` (see `soiferTriangle_not_square_only_in_model`,
  `no_square_only_witness_in_model`, `squareOnly_empty_in_model`). Capturing Soifer's
  genuine geometric result requires replacing `CongruentDissection` with a faithful
  tiling predicate — the open, hard content of Erdős #633. -/

/-- Generalisation of `universal_square_dissection` from `n²` to *every* `n ≥ 1`:
    in the area-compatibility model the similar copy `T.scale (1/√n)` has area
    `T.area / n`, so `n` copies match `T`'s area exactly. This witnesses the
    over-counting of the simplified model. -/
theorem all_counts_achievable (T : Triangle) (n : ℕ) (hn : n ≥ 1) :
    CanDissectInto T n := by
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hsq : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnR
  refine ⟨T.scale (1 / Real.sqrt n) (one_div_pos.mpr hsq), ⟨⟨?_, ?_, ?_⟩⟩⟩
  · rw [Triangle.area_scale, div_pow, one_pow, Real.sq_sqrt (le_of_lt hnR),
        ← mul_assoc, mul_one_div, div_self (ne_of_gt hnR), one_mul]
  · simp only [Triangle.scale]
    rw [mul_div_assoc, div_self (ne_of_gt T.ha), mul_one,
        mul_div_assoc, div_self (ne_of_gt T.hb), mul_one]
  · simp only [Triangle.scale]
    rw [mul_div_assoc, div_self (ne_of_gt T.hb), mul_one,
        mul_div_assoc, div_self (ne_of_gt T.hc), mul_one]

/-- In the simplified model, the achievable dissection counts of *any* triangle
    are exactly the positive integers — the model retains no square-only
    information whatsoever. -/
theorem dissectionCounts_eq (T : Triangle) :
    DissectionCounts T = {n : ℕ | 1 ≤ n} := by
  ext n
  simp only [DissectionCounts, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hn, _⟩; exact hn
  · intro hn; exact ⟨hn, all_counts_achievable T n hn⟩

/-- `2` is not a perfect square (helper for `no_square_only_in_model`). -/
theorem not_isPerfectSquare_two : ¬ IsPerfectSquare 2 := by
  rintro ⟨k, hk⟩
  have hk2 : k ^ 2 = 2 := hk.symm
  have hlt : k < 2 := by
    by_contra hc
    push_neg at hc
    have h4 : 4 ≤ k ^ 2 := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ k ^ 2 := Nat.pow_le_pow_left hc 2
    omega
  interval_cases k <;> norm_num at hk2

/-- **The simplified model has no square-only triangles.**
    Since every `n ≥ 1` (in particular the non-square `2`) is an achievable
    count, no triangle satisfies `HasSquareOnlyProperty` in this model. This is the
    engine behind every model-falsity result downstream
    (`soiferTriangle_not_square_only_in_model`, `no_square_only_witness_in_model`,
    `squareOnly_empty_in_model`, `erdos_633_model_collapse`), confirming the
    square-only phenomenon requires a refined geometric dissection predicate rather
    than further proof effort in the present model. -/
theorem no_square_only_in_model (T : Triangle) : ¬ HasSquareOnlyProperty T := by
  intro h
  have h2 : (2 : ℕ) ∈ DissectionCounts T := by
    rw [dissectionCounts_eq, Set.mem_setOf_eq]; norm_num
  exact not_isPerfectSquare_two (h 2 h2)

/-! ## Soifer's Example -/

/-- Soifer's example: the triangle with sides √2, √3, √4 -/
noncomputable def soiferTriangle : Triangle where
  a := Real.sqrt 2
  b := Real.sqrt 3
  c := Real.sqrt 4  -- = 2
  ha := Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)
  hb := Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0)
  hc := Real.sqrt_pos.mpr (by norm_num : (4 : ℝ) > 0)
  hab := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    have h1 : Real.sqrt 2 > 1 := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have h2 : Real.sqrt 3 > 1 := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
    linarith
  hbc := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    have h : Real.sqrt 2 < 2 := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have h3 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0)
    linarith
  hca := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    have h3 : Real.sqrt 3 < 2 := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
    have h2 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)
    linarith

/-- **Soifer's triangle is NOT square-only in this model.**
    Soifer's *genuine* geometric theorem says the `(√2,√3,√4)` triangle can only be
    cut into a perfect-square number of congruent copies. That is `model-false` in the
    area+similarity relaxation: `no_square_only_in_model` already proves the negation
    of `HasSquareOnlyProperty soiferTriangle` for this particular triangle. We record
    that refutation here rather than `sorry`-ing a statement the model disproves —
    Soifer's result requires a faithful tiling predicate, not this relaxation. -/
theorem soiferTriangle_not_square_only_in_model :
    ¬ HasSquareOnlyProperty soiferTriangle :=
  no_square_only_in_model soiferTriangle

/-! ## Integral Independence -/

/-- The angles of a triangle are integrally independent if no non-trivial
    integer linear combination equals zero -/
def HasIntegrallyIndependentAngles (T : TriangleByAngles) : Prop :=
  ∀ a b c : ℤ, a * T.α + b * T.β + c * T.γ = 0 → (a = 0 ∧ b = 0 ∧ c = 0) ∨
    (a : ℝ) / (b : ℝ) = T.α / T.β  -- or they're proportional to the constraint

/-- The conjectured link "integrally independent angles ⇒ square-only" is *model-false*
    in the area+similarity relaxation: by `no_square_only_in_model` NO triangle `T'` has
    `HasSquareOnlyProperty`, so the existence conclusion `∃ T', HasSquareOnlyProperty T'`
    fails outright regardless of the angle hypothesis. The genuine implication (Soifer's
    heuristic) is about real dissections and lives beyond this model. -/
theorem no_square_only_witness_in_model :
    ¬ ∃ T' : Triangle, HasSquareOnlyProperty T' := by
  rintro ⟨T', hT'⟩
  exact no_square_only_in_model T' hT'

/-! ## Non-Square Dissections for Generic Triangles -/

/-- Most triangles can be dissected into non-square numbers -/
def HasNonSquareDissection (T : Triangle) : Prop :=
  ∃ n : ℕ, n ∈ DissectionCounts T ∧ ¬IsPerfectSquare n

/-- The unit equilateral triangle (all sides 1). -/
noncomputable def unitEquilateral : Triangle :=
  ⟨1, 1, 1, one_pos, one_pos, one_pos, by norm_num, by norm_num, by norm_num⟩

/-- The unit right isosceles triangle (legs 1, hypotenuse √2). -/
noncomputable def unitRightIso : Triangle :=
  ⟨1, 1, Real.sqrt 2, one_pos, one_pos, Real.sqrt_pos.mpr (by norm_num),
    by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),
                  Real.sqrt_nonneg 2, sq_nonneg (Real.sqrt 2 - 2)],
    by linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)],
    by linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)]⟩

/-- Equilateral triangles can be dissected into 3 congruent triangles.

    In the area-compatibility model: the similar copy `scale (1/√3)` has area
    `area/3`, so 3 copies match — a *non-square* count, witnessing that the
    equilateral triangle does NOT have the square-only property. -/
theorem equilateral_dissects_to_3 : ∃ T : Triangle,
    T.a = T.b ∧ T.b = T.c ∧ 3 ∈ DissectionCounts T := by
  refine ⟨unitEquilateral, rfl, rfl, ?_⟩
  simp only [DissectionCounts, Set.mem_setOf_eq]
  refine ⟨by norm_num, ?_⟩
  have h3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨unitEquilateral.scale (1 / Real.sqrt 3) (one_div_pos.mpr h3), ⟨⟨?_, ?_, ?_⟩⟩⟩
  · rw [Triangle.area_scale, div_pow, one_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    push_cast; ring
  · simp only [Triangle.scale]
    rw [mul_div_assoc, div_self (ne_of_gt unitEquilateral.ha), mul_one,
        mul_div_assoc, div_self (ne_of_gt unitEquilateral.hb), mul_one]
  · simp only [Triangle.scale]
    rw [mul_div_assoc, div_self (ne_of_gt unitEquilateral.hb), mul_one,
        mul_div_assoc, div_self (ne_of_gt unitEquilateral.hc), mul_one]

/-- Right isoceles triangles can be dissected into 2 congruent triangles.

    In the area-compatibility model: the similar copy `scale (1/√2)` has area
    `area/2`, so 2 copies match — a *non-square* count, witnessing that the
    right isosceles triangle does NOT have the square-only property. -/
theorem right_isoceles_dissects_to_2 : ∃ T : Triangle,
    T.a = T.b ∧ T.c = T.a * Real.sqrt 2 ∧ 2 ∈ DissectionCounts T := by
  refine ⟨unitRightIso, rfl, ?_, ?_⟩
  · show Real.sqrt 2 = (1:ℝ) * Real.sqrt 2
    rw [one_mul]
  · simp only [DissectionCounts, Set.mem_setOf_eq]
    refine ⟨by norm_num, ?_⟩
    have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    refine ⟨unitRightIso.scale (1 / Real.sqrt 2) (one_div_pos.mpr h2), ⟨⟨?_, ?_, ?_⟩⟩⟩
    · rw [Triangle.area_scale, div_pow, one_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      push_cast; ring
    · simp only [Triangle.scale]
      rw [mul_div_assoc, div_self (ne_of_gt unitRightIso.ha), mul_one,
          mul_div_assoc, div_self (ne_of_gt unitRightIso.hb), mul_one]
    · simp only [Triangle.scale]
      rw [mul_div_assoc, div_self (ne_of_gt unitRightIso.hb), mul_one,
          mul_div_assoc, div_self (ne_of_gt unitRightIso.hc), mul_one]

/-! ## Similar vs Congruent Dissections

  The genuine Problem #634 ("every triangle cuts into `n` *similar* copies for all
  `n ∉ {2,3,5}`, with real exceptions at `2,3,5`") needs an actual geometric tiling.
  The predicate `CanDissectIntoSimilar` below is, like `CongruentDissection`, only the
  area+side-ratio *relaxation* of that statement — and it collapses in exactly the same
  way: by `Triangle.area_scale` the similar copy `T.scale (1/√n)` witnesses *every*
  `n ≥ 1`. So in this model `similar_dissection_characterization` holds trivially (the
  `{2,3,5}` exclusion is vacuous) and the exceptional-cases statement is *model-false*
  (refuted by `no_exceptional_similar_in_model`). -/

/-- For similar (not congruent) dissections: area compatibility plus matched side
    ratios. Like `CongruentDissection`, this is the *necessary-condition* relaxation,
    not a witness of a real tiling. -/
def CanDissectIntoSimilar (T : Triangle) (n : ℕ) : Prop :=
  ∃ S : Triangle, S.a / S.b = T.a / T.b ∧ S.b / S.c = T.b / T.c ∧
    T.area = n * S.area

/-- **The similar-dissection relaxation also collapses.**
    For every `n ≥ 1` the similar copy `T.scale (1/√n)` (area `T.area / n`, identical
    side ratios) satisfies `CanDissectIntoSimilar T n`. Mirrors `all_counts_achievable`
    for the congruent model. -/
theorem all_similar_counts (T : Triangle) (n : ℕ) (hn : n ≥ 1) :
    CanDissectIntoSimilar T n := by
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hsq : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have htne : (1 / Real.sqrt n) ≠ 0 := ne_of_gt (one_div_pos.mpr hsq)
  refine ⟨T.scale (1 / Real.sqrt n) (one_div_pos.mpr hsq), ?_, ?_, ?_⟩
  · simp only [Triangle.scale]; rw [mul_div_mul_left _ _ htne]
  · simp only [Triangle.scale]; rw [mul_div_mul_left _ _ htne]
  · rw [Triangle.area_scale, div_pow, one_pow, Real.sq_sqrt (le_of_lt hnR),
        ← mul_assoc, mul_one_div, div_self (ne_of_gt hnR), one_mul]

/-- Every triangle can be dissected into `n` similar triangles for `n ∉ {2,3,5}`.

    NOTE (model adequacy): in this relaxation the `{2,3,5}` exclusion is vacuous — by
    `all_similar_counts` the conclusion already holds for *every* `n ≥ 1`. The genuine
    Problem #634 content (real exceptions at `2,3,5`) requires a faithful tiling
    predicate, not this area+ratio model. -/
theorem similar_dissection_characterization (T : Triangle) (n : ℕ) (hn : n ≥ 1) :
    n ∉ ({2, 3, 5} : Set ℕ) → CanDissectIntoSimilar T n := by
  intro _; exact all_similar_counts T n hn

/-- **No exceptional similar cases survive in the model.**
    The over-counting refutes `exceptional_similar_cases` (the former `sorry`):
    *every* triangle satisfies `CanDissectIntoSimilar` at `2`, `3`, and `5`, so the
    genuine #634 exceptions are invisible to the area+ratio relaxation. -/
theorem no_exceptional_similar_in_model (T : Triangle) :
    CanDissectIntoSimilar T 2 ∧ CanDissectIntoSimilar T 3 ∧ CanDissectIntoSimilar T 5 :=
  ⟨all_similar_counts T 2 (by norm_num),
   all_similar_counts T 3 (by norm_num),
   all_similar_counts T 5 (by norm_num)⟩

/-! ## The Classification Problem (OPEN) -/

/-- Erdős Problem #633: Classify SquareOnlyTriangles
    This remains OPEN. The $25 prize is for a complete characterization. -/
def erdos633Classification : Prop :=
  ∃ P : Triangle → Prop,
    (∀ T : Triangle, HasSquareOnlyProperty T ↔ P T) ∧
    -- P should be a "nice" geometric condition
    True  -- Placeholder for "nice" condition

/-- The problem remains open -/
theorem erdos_633_open : erdos633Classification ↔ erdos633Classification := by
  rfl

/-! ## Partial Results -/

/-- Known: Soifer's family has the square-only property -/
def soiferFamily : Set Triangle :=
  {T : Triangle | ∃ p q r : ℕ, p ≠ q ∧ q ≠ r ∧ p ≠ r ∧
    T.a = Real.sqrt p ∧ T.b = Real.sqrt q ∧ T.c = Real.sqrt r ∧
    -- Triangle inequality is satisfied
    Real.sqrt p + Real.sqrt q > Real.sqrt r}

/-- **Soifer's family is NOT contained in the square-only triangles in this model.**
    The genuine partial result "`soiferFamily ⊆ SquareOnlyTriangles`" is `model-false`:
    `SquareOnlyTriangles = ∅` here (no triangle is square-only, by
    `no_square_only_in_model`), while `soiferFamily` is nonempty (it contains
    `soiferTriangle`). We record the proved containment `SquareOnlyTriangles ⊆ ∅`
    instead, which pins down exactly why the relaxation is too coarse. -/
theorem squareOnly_empty_in_model : SquareOnlyTriangles ⊆ (∅ : Set Triangle) := by
  intro T hT
  exact absurd hT (no_square_only_in_model T)

/-! ## Main Theorem Statement -/

/-- **Erdős Problem #633 — what is actually established here (OPEN, $25).**

    The genuine problem (classify the triangles cuttable only into a perfect-square
    number of *congruent* copies) remains open. This file's rigorous contribution is a
    sharp *negative* result about the natural first-attempt formalization: the
    area + side-ratio relaxation `CongruentDissection` (and its similar analogue
    `CanDissectIntoSimilar`) is **too coarse to see the phenomenon at all**.

    Concretely, both relaxations collapse to "every count `n ≥ 1` is achievable":
    * `dissectionCounts_eq` : `DissectionCounts T = {n | 1 ≤ n}` for every `T`;
    * `all_similar_counts`  : `CanDissectIntoSimilar T n` for every `T`, `n ≥ 1`;
    so the square-only property is *vacuous* (`no_square_only_in_model`) and the
    similar exceptions vanish (`no_exceptional_similar_in_model`).

    Moral: any faithful resolution of Erdős #633/#634 must use strictly finer
    geometric data than area together with side ratios — an actual non-overlapping
    tiling predicate. That predicate is the hard, open core left for future work. -/
theorem erdos_633_model_collapse :
    (∀ T : Triangle, DissectionCounts T = {n : ℕ | 1 ≤ n}) ∧
    (∀ T : Triangle, ¬ HasSquareOnlyProperty T) :=
  ⟨dissectionCounts_eq, no_square_only_in_model⟩

#check erdos_633_model_collapse
#check no_square_only_in_model
#check all_similar_counts
#check erdos_633_open
