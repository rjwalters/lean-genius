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

/-- Rescale a triangle by a positive factor `k`. All side lengths are
    multiplied by `k`; positivity and the triangle inequalities are preserved. -/
noncomputable def Triangle.scale (T : Triangle) (k : ℝ) (hk : 0 < k) : Triangle where
  a := k * T.a
  b := k * T.b
  c := k * T.c
  ha := mul_pos hk T.ha
  hb := mul_pos hk T.hb
  hc := mul_pos hk T.hc
  hab := by nlinarith [T.hab, mul_pos hk (show (0:ℝ) < T.a + T.b - T.c by linarith [T.hab])]
  hbc := by nlinarith [T.hbc, mul_pos hk (show (0:ℝ) < T.b + T.c - T.a by linarith [T.hbc])]
  hca := by nlinarith [T.hca, mul_pos hk (show (0:ℝ) < T.c + T.a - T.b by linarith [T.hca])]

/-- Heron area scales quadratically: scaling all sides by `k` multiplies the
    area by `k²`. This is the single geometric fact behind every "positive"
    dissection result below, since (under the area-only `CongruentDissection`
    definition) a copy of `T` shrunk by `1/√n` has exactly `1/n` of its area. -/
theorem Triangle.area_scale (T : Triangle) (k : ℝ) (hk : 0 < k) :
    (T.scale k hk).area = k ^ 2 * T.area := by
  have key : k ^ 2 = Real.sqrt (k ^ 4) := by
    rw [show (k : ℝ) ^ 4 = (k ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  simp only [Triangle.area, Triangle.scale]
  rw [key, ← Real.sqrt_mul (show (0:ℝ) ≤ k ^ 4 by positivity)]
  congr 1
  ring

/-! ## Dissection Definitions -/

/-- A dissection of triangle T into n congruent copies of triangle S -/
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

/-- A number is a perfect square -/
def IsPerfectSquare (n : ℕ) : Prop := ∃ k : ℕ, n = k^2

/-- A triangle has the "square-only" property if it can only be dissected
    into square numbers of congruent copies -/
def HasSquareOnlyProperty (T : Triangle) : Prop :=
  ∀ n ∈ DissectionCounts T, IsPerfectSquare n

/-- The set of triangles with the square-only property -/
def SquareOnlyTriangles : Set Triangle :=
  {T : Triangle | HasSquareOnlyProperty T}

/-! ## Universal Dissection into Squares -/

/-- Key lemma: under the area-only `CongruentDissection` definition, **every**
    `n ≥ 1` is a valid dissection count. The witness is `T` shrunk by `1/√n`,
    whose Heron area is exactly `(1/n)·area T` (by `area_scale`), so the area
    balance `area T = n · area S` holds and the side ratios are all `1/√n`.

    NB: this exposes that the current `DissectionCounts` definition is *too weak*
    to model genuine congruent tilings — it tracks only area and similarity,
    not an actual geometric dissection. See the note on `soifer_square_only`. -/
theorem scale_mem_dissectionCounts (T : Triangle) (n : ℕ) (hn : 1 ≤ n) :
    n ∈ DissectionCounts T := by
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsq : (0:ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hk : (0:ℝ) < 1 / Real.sqrt (n : ℝ) := one_div_pos.mpr hsq
  refine ⟨hn, T.scale (1 / Real.sqrt (n : ℝ)) hk, ⟨{ covers := ?_, congruent := ?_ }⟩⟩
  · rw [Triangle.area_scale, div_pow, one_pow, Real.sq_sqrt hn0.le, one_div, ← mul_assoc,
        mul_inv_cancel₀ hn0.ne', one_mul]
  · simp only [Triangle.scale]
    exact ⟨by rw [mul_div_assoc, mul_div_assoc, div_self T.ha.ne', div_self T.hb.ne'],
           by rw [mul_div_assoc, mul_div_assoc, div_self T.hb.ne', div_self T.hc.ne']⟩

/-- Every triangle can be dissected into n² congruent triangles for any n ≥ 1 -/
theorem universal_square_dissection (T : Triangle) (n : ℕ) (hn : n ≥ 1) :
    CanDissectInto T (n^2) :=
  (scale_mem_dissectionCounts T (n ^ 2) (Nat.one_le_pow 2 n (by omega))).2

/-- This means every triangle has all square numbers in its dissection set -/
theorem squares_always_achievable (T : Triangle) :
    ∀ k ≥ 1, k^2 ∈ DissectionCounts T := by
  intro k hk
  constructor
  · exact Nat.one_le_pow 2 k hk
  · exact universal_square_dissection T k hk

/-! ## Model Inadequacy: No Square-Only Triangle Exists (area-only model) -/

/-- `2` is not a perfect square (for the file-local `IsPerfectSquare`). -/
theorem not_isPerfectSquare_two : ¬ IsPerfectSquare 2 := by
  rintro ⟨k, hk⟩
  rcases k with _ | _ | k
  · norm_num at hk
  · norm_num at hk
  · simp only [pow_two] at hk; nlinarith

/-- Under the area-only `DissectionCounts`, **no** triangle has the square-only
    property: `scale_mem_dissectionCounts` puts `2 ∈ DissectionCounts T`, yet `2`
    is not a perfect square. This is the precise reason the area-only model fails to
    capture Erdős #633 — the genuine problem needs a real tiling predicate
    (isometric placement of congruent copies), not just an area balance. -/
theorem no_squareOnly (T : Triangle) : ¬ HasSquareOnlyProperty T := by
  intro h
  have h2 : (2 : ℕ) ∈ DissectionCounts T := scale_mem_dissectionCounts T 2 (by norm_num)
  exact not_isPerfectSquare_two (h 2 h2)

/-- Consequently `SquareOnlyTriangles` is empty in the area-only model. -/
theorem squareOnlyTriangles_empty : SquareOnlyTriangles = (∅ : Set Triangle) := by
  rw [Set.eq_empty_iff_forall_notMem]
  exact fun T => no_squareOnly T

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
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    have h1 : Real.sqrt 2 > 1 := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have h2 : Real.sqrt 3 > 1 := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
    rw [h4]; linarith
  hbc := by
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    have h : Real.sqrt 2 < 2 := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have h3 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0)
    rw [h4]; linarith
  hca := by
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    have h3 : Real.sqrt 3 < 2 := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
    have h2 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)
    rw [h4]; linarith

/-- Soifer's triangle does **not** have the square-only property *in this model*.

    The honest content: under the area-only `CongruentDissection`, every `n ≥ 1`
    (in particular `n = 2`) is a dissection count, so no triangle — including
    Soifer's (√2,√3,√4) — can be square-only here. The classical Soifer theorem
    is a statement about genuine geometric tilings, which this area-only definition
    does not model; see `no_squareOnly` and the module note. This refutation
    replaces the previously-`sorry`'d (and false-in-this-model) positive claim. -/
theorem soifer_not_square_only : ¬ HasSquareOnlyProperty soiferTriangle :=
  no_squareOnly soiferTriangle

/-! ## Integral Independence -/

/-- The angles of a triangle are integrally independent if no non-trivial
    integer linear combination equals zero -/
def HasIntegrallyIndependentAngles (T : TriangleByAngles) : Prop :=
  ∀ a b c : ℤ, a * T.α + b * T.β + c * T.γ = 0 → (a = 0 ∧ b = 0 ∧ c = 0) ∨
    (a : ℝ) / (b : ℝ) = T.α / T.β  -- or they're proportional to the constraint

/-- In the area-only model the conclusion "some triangle is square-only" is simply
    false, regardless of any integral-independence hypothesis on the angles:
    `no_squareOnly` rules out *every* triangle. This records that the intended bridge
    "integrally independent angles ⟹ square-only" cannot even be stated nonvacuously
    until `DissectionCounts` is upgraded to a tiling predicate. Replaces the
    previously-`sorry`'d (unsatisfiable-in-this-model) existential. -/
theorem no_squareOnly_triangle_in_model : ¬ ∃ T : Triangle, HasSquareOnlyProperty T := by
  rintro ⟨T, hT⟩
  exact no_squareOnly T hT

/-! ## Non-Square Dissections for Generic Triangles -/

/-- Most triangles can be dissected into non-square numbers -/
def HasNonSquareDissection (T : Triangle) : Prop :=
  ∃ n : ℕ, n ∈ DissectionCounts T ∧ ¬IsPerfectSquare n

/-- Equilateral triangles can be dissected into 3 congruent triangles.
    (Provable for the area-only definition via `scale_mem_dissectionCounts`.) -/
theorem equilateral_dissects_to_3 : ∃ T : Triangle,
    T.a = T.b ∧ T.b = T.c ∧ 3 ∈ DissectionCounts T :=
  ⟨⟨1, 1, 1, one_pos, one_pos, one_pos, by norm_num, by norm_num, by norm_num⟩,
   rfl, rfl, scale_mem_dissectionCounts _ 3 (by norm_num)⟩

/-- Right isoceles triangles can be dissected into 2 congruent triangles.
    (Provable for the area-only definition via `scale_mem_dissectionCounts`.) -/
theorem right_isoceles_dissects_to_2 : ∃ T : Triangle,
    T.a = T.b ∧ T.c = T.a * Real.sqrt 2 ∧ 2 ∈ DissectionCounts T :=
  ⟨⟨1, 1, Real.sqrt 2, one_pos, one_pos, Real.sqrt_pos.mpr (by norm_num),
    by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2],
    by linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)],
    by linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)]⟩,
   rfl, by rw [one_mul], scale_mem_dissectionCounts _ 2 (by norm_num)⟩

/-! ## Similar vs Congruent Dissections -/

/-- For similar (not congruent) dissections, the situation is different -/
def CanDissectIntoSimilar (T : Triangle) (n : ℕ) : Prop :=
  ∃ S : Triangle, S.a / S.b = T.a / T.b ∧ S.b / S.c = T.b / T.c ∧
    T.area = n * S.area

/-- Every triangle can be dissected into n similar triangles for n ≠ 2, 3, 5.
    NB: under the area-only `CanDissectIntoSimilar` definition this in fact holds
    for *every* `n ≥ 1` (the `n ∉ {2,3,5}` hypothesis is not needed), since the
    shrunk copy `T.scale (1/√n)` has the same side ratios and `1/n` the area.
    The genuine exceptions n = 2, 3, 5 only appear once one demands an actual
    geometric tiling, which this definition does not capture. -/
theorem similar_dissection_characterization (T : Triangle) (n : ℕ) (hn : n ≥ 1) :
    n ∉ ({2, 3, 5} : Set ℕ) → CanDissectIntoSimilar T n := by
  intro _
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsq : (0:ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hk : (0:ℝ) < 1 / Real.sqrt (n : ℝ) := one_div_pos.mpr hsq
  refine ⟨T.scale (1 / Real.sqrt (n : ℝ)) hk, ?_, ?_, ?_⟩
  · simp only [Triangle.scale]; rw [mul_div_mul_left _ _ hk.ne']
  · simp only [Triangle.scale]; rw [mul_div_mul_left _ _ hk.ne']
  · rw [Triangle.area_scale, div_pow, one_pow, Real.sq_sqrt hn0.le, one_div, ← mul_assoc,
        mul_inv_cancel₀ hn0.ne', one_mul]

/-- The clean fact behind the area-only similar model: **every** `n ≥ 1` is a
    similar-dissection count (the `n ∉ {2,3,5}` hypothesis in
    `similar_dissection_characterization` is never actually used in its proof). -/
theorem canDissectIntoSimilar_of_one_le (T : Triangle) (n : ℕ) (hn : n ≥ 1) :
    CanDissectIntoSimilar T n := by
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsq : (0:ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hk : (0:ℝ) < 1 / Real.sqrt (n : ℝ) := one_div_pos.mpr hsq
  refine ⟨T.scale (1 / Real.sqrt (n : ℝ)) hk, ?_, ?_, ?_⟩
  · simp only [Triangle.scale]; rw [mul_div_mul_left _ _ hk.ne']
  · simp only [Triangle.scale]; rw [mul_div_mul_left _ _ hk.ne']
  · rw [Triangle.area_scale, div_pow, one_pow, Real.sq_sqrt hn0.le, one_div, ← mul_assoc,
        mul_inv_cancel₀ hn0.ne', one_mul]

/-- Refutation of the would-be `exceptional_similar_cases`: in the area-only model
    there is **no** triangle failing to dissect into 2, 3, or 5 similar copies —
    every triangle dissects into all three. The genuine exceptions n = 2, 3, 5
    (Problem #634) only appear under a real tiling predicate. Replaces the
    previously-`sorry`'d (false-in-this-model) existential. -/
theorem no_exceptional_similar_in_model (T : Triangle) :
    CanDissectIntoSimilar T 2 ∧ CanDissectIntoSimilar T 3 ∧ CanDissectIntoSimilar T 5 :=
  ⟨canDissectIntoSimilar_of_one_le T 2 (by norm_num),
   canDissectIntoSimilar_of_one_le T 3 (by norm_num),
   canDissectIntoSimilar_of_one_le T 5 (by norm_num)⟩

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

/-- Soifer's triangle is a concrete member of `soiferFamily` (sides √2, √3, √4,
    with 2, 3, 4 distinct and √2 + √3 > √4 = 2). In particular the family is
    nonempty. -/
theorem soiferTriangle_mem_soiferFamily : soiferTriangle ∈ soiferFamily := by
  refine ⟨2, 3, 4, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · simp [soiferTriangle]
  · simp [soiferTriangle]
  · simp [soiferTriangle]
  · have := soiferTriangle.hab
    simpa [soiferTriangle] using this

/-- Soifer's family is **not** contained in the square-only triangles in the
    area-only model. Since `SquareOnlyTriangles = ∅` (`squareOnlyTriangles_empty`)
    while `soiferFamily` is nonempty (`soiferTriangle_mem_soiferFamily`), the
    inclusion `soiferFamily ⊆ SquareOnlyTriangles` is false. It would hold only
    vacuously — exactly when the family is empty:

    `soiferFamily ⊆ SquareOnlyTriangles ↔ soiferFamily = ∅`.

    This replaces the previously-`sorry`'d (false-in-this-model) inclusion, and is
    the general form of why Erdős #633 needs a genuine tiling predicate. -/
theorem soiferFamily_subset_squareOnly_iff_empty :
    soiferFamily ⊆ SquareOnlyTriangles ↔ soiferFamily = ∅ := by
  rw [squareOnlyTriangles_empty, Set.subset_empty_iff]

theorem soiferFamily_not_subset_squareOnly : ¬ soiferFamily ⊆ SquareOnlyTriangles := by
  rw [soiferFamily_subset_squareOnly_iff_empty, Set.eq_empty_iff_forall_notMem]
  push_neg
  exact ⟨soiferTriangle, soiferTriangle_mem_soiferFamily⟩

/-! ## Main Theorem Statement -/

/-- Erdős Problem #633 — model status. **OPEN.**

    Under the area-only `DissectionCounts`/`CanDissectIntoSimilar` definitions in
    this file the model provably *collapses*:
    (1) no triangle is square-only (`no_squareOnly`), and
    (2) every triangle admits every similar dissection
        (`canDissectIntoSimilar_of_one_le`).
    Hence the area balance alone cannot model the problem; a faithful formalization
    must replace these with a genuine geometric tiling predicate (isometric
    placement of congruent/similar copies with disjoint interiors and exact cover).
    Capturing Soifer's (√2,√3,√4) example then becomes the deep number-theoretic
    content worth the $25 prize.

    NB: the earlier `erdos_633 : ∃ T, HasSquareOnlyProperty T` was **false** in this
    model and has been removed in favour of this honest statement. -/
theorem erdos_633_model_inadequate :
    (∀ T : Triangle, ¬ HasSquareOnlyProperty T) ∧
    (∀ T : Triangle, ∀ n : ℕ, 1 ≤ n → CanDissectIntoSimilar T n) :=
  ⟨no_squareOnly, fun T n hn => canDissectIntoSimilar_of_one_le T n hn⟩

#check erdos_633_model_inadequate
#check no_squareOnly
#check no_exceptional_similar_in_model
#check erdos_633_open
