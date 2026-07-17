/-
  Erdős Problem #634: Triangle Dissection into Congruent Pieces

  Source: https://erdosproblems.com/634
  Status: OPEN (Partially solved, $25 prize)

  Statement:
  Find all n such that there exists at least one triangle which can
  be cut into n congruent triangles.

  Known Results:
  - WORKS: n², 2n², 3n², 6n², n²+m², 27
  - FAILS: 7, 11 (Beeson)
  - OPEN: 19, complete characterization

  Context:
  - Congruent = same size and shape (rigid motion)
  - Similar = same shape (allowing scaling)
  - For similar: all n except 2, 3, 5 work (Soifer)

  History:
  - Erdős posed the problem with $25 prize
  - Snover-Waiveris-Williams: similar to original case
  - Beeson: proved 7 and 11 fail
  - Zhang (2025): recent progress on sufficient conditions

  Formalization note (soundness):
  - `IsDissectable` requires an *abstract* tiling witness `Tiles` (covering +
    interior-disjointness) on top of area balance. Without it, area balance is
    trivially satisfiable for every n ≥ 1 (see `Erdos634AreaCollapse.lean`), which
    would make Beeson's `¬IsDissectable 7/11` axioms provably false. The `Tiles`
    abstraction is the minimal change that keeps the positive constructions and
    Beeson's negative results mutually consistent; Mathlib has no polygonal-tiling
    API to define `Tiles` outright.
  - `Similar` and `Congruent` are both stated on the *unordered* multiset of side
    lengths, so `congruent_implies_similar` holds (an order-pinned `Similar` would
    make it false, since congruence permits relabelling the vertices).

  Tags: geometry, dissection, congruent-triangles, open-problem
-/

import Mathlib

namespace Erdos634

open Finset Function

/-
## Part I: Triangles and Congruence

Basic geometric definitions.
-/

/-- A triangle represented by its three side lengths (a, b, c). -/
structure Triangle where
  a : ℝ
  b : ℝ
  c : ℝ
  ha : a > 0
  hb : b > 0
  hc : c > 0
  triangle_ineq_ab : a + b > c
  triangle_ineq_bc : b + c > a
  triangle_ineq_ca : c + a > b

/-- Two triangles are congruent if they have the same side lengths (up to ordering). -/
def Congruent (T₁ T₂ : Triangle) : Prop :=
  Multiset.ofList [T₁.a, T₁.b, T₁.c] = Multiset.ofList [T₂.a, T₂.b, T₂.c]

/-- Congruence is an equivalence relation. -/
theorem congruent_refl (T : Triangle) : Congruent T T := rfl

theorem congruent_symm {T₁ T₂ : Triangle} : Congruent T₁ T₂ → Congruent T₂ T₁ :=
  fun h => h.symm

theorem congruent_trans {T₁ T₂ T₃ : Triangle} :
    Congruent T₁ T₂ → Congruent T₂ T₃ → Congruent T₁ T₃ :=
  fun h₁ h₂ => h₁.trans h₂

/-
## Part II: Similar Triangles

A weaker notion than congruence.
-/

/-- Two triangles are similar if one side-length multiset is a positive scaling
    of the other. Like `Congruent`, this is stated on the *unordered* multiset of
    sides: geometric similarity is invariant under relabelling the vertices, so a
    faithful predicate must not pin the correspondence to the `a/b/c` order. (The
    earlier order-sensitive `T₂.a = k * T₁.a ∧ …` version was *not* implied by the
    multiset-based `Congruent` — e.g. sides `(3,4,5)` vs `(4,3,5)` are congruent
    but admit no single `k` for the fixed order — so `congruent_implies_similar`
    below was unprovable as stated. This multiset form repairs that.) -/
def Similar (T₁ T₂ : Triangle) : Prop :=
  ∃ k : ℝ, k > 0 ∧
    Multiset.ofList [T₂.a, T₂.b, T₂.c] =
      Multiset.ofList [k * T₁.a, k * T₁.b, k * T₁.c]

/-- Congruent triangles are similar (with k = 1). -/
theorem congruent_implies_similar {T₁ T₂ : Triangle}
    (h : Congruent T₁ T₂) : Similar T₁ T₂ :=
  ⟨1, one_pos, by simpa only [Congruent, one_mul] using h.symm⟩

/-- **Similarity is reflexive.** Every triangle is similar to itself with ratio `k = 1`. -/
theorem similar_refl (T : Triangle) : Similar T T :=
  ⟨1, one_pos, by simp⟩

/-- **Similarity is symmetric.** If `T₁ ~ T₂` with ratio `k`, then `T₂ ~ T₁` with the
    reciprocal ratio `k⁻¹ > 0`: scaling the side-length multiset by `k⁻¹` inverts the
    relation. -/
theorem similar_symm {T₁ T₂ : Triangle} (h : Similar T₁ T₂) : Similar T₂ T₁ := by
  obtain ⟨k, hk, hmul⟩ := h
  have hk0 : k ≠ 0 := ne_of_gt hk
  refine ⟨k⁻¹, by positivity, ?_⟩
  have hmap := congrArg (Multiset.map (fun x : ℝ => k⁻¹ * x)) hmul
  simpa [Multiset.map_coe, inv_mul_cancel_left₀ hk0] using hmap.symm

/-- **Similarity is transitive.** If `T₁ ~ T₂` with ratio `k` and `T₂ ~ T₃` with ratio `j`,
    then `T₁ ~ T₃` with the product ratio `j·k > 0`. Together with `similar_refl` and
    `similar_symm` this makes `Similar` an equivalence relation, matching the
    `congruent_refl / symm / trans` triple for `Congruent`. -/
theorem similar_trans {T₁ T₂ T₃ : Triangle} (h₁ : Similar T₁ T₂) (h₂ : Similar T₂ T₃) :
    Similar T₁ T₃ := by
  obtain ⟨k, hk, hk2⟩ := h₁
  obtain ⟨j, hj, hj2⟩ := h₂
  refine ⟨j * k, by positivity, ?_⟩
  have hmap := congrArg (Multiset.map (fun x : ℝ => j * x)) hk2
  rw [hj2]
  simpa [Multiset.map_coe, mul_assoc] using hmap

/-
## Part III: Triangle Dissection

The central concept of the problem.
-/

/-- Semiperimeter of a triangle (used in Heron's formula). -/
noncomputable def Triangle.semiperimeter (T : Triangle) : ℝ :=
  (T.a + T.b + T.c) / 2

/-- Area of a triangle via Heron's formula: √(s(s-a)(s-b)(s-c)). -/
noncomputable def Triangle.area (T : Triangle) : ℝ :=
  Real.sqrt (T.semiperimeter * (T.semiperimeter - T.a) *
             (T.semiperimeter - T.b) * (T.semiperimeter - T.c))

/-- **Congruent triangles have equal area.**  Heron's formula
`Area = √(s(s−a)(s−b)(s−c))` is a *symmetric* function of the side lengths `a, b, c`
(the semiperimeter `s` is half their sum, and the radicand's remaining factor is the
product over the three sides), so it depends only on the *multiset* `{a, b, c}` — which is
exactly what `Congruent` fixes.  Hence congruence preserves area: the area invariant on
which the `Dissection.area_partition` balance condition rests is genuinely a congruence
invariant. -/
theorem congruent_implies_equal_area {T₁ T₂ : Triangle} (h : Congruent T₁ T₂) :
    T₁.area = T₂.area := by
  have hs : T₁.semiperimeter = T₂.semiperimeter := by
    unfold Triangle.semiperimeter
    have hh := congrArg Multiset.sum h
    simp only [Congruent, Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero] at hh
    linarith
  have hprod :
      (T₂.semiperimeter - T₁.a) * ((T₂.semiperimeter - T₁.b) * (T₂.semiperimeter - T₁.c))
        = (T₂.semiperimeter - T₂.a) * ((T₂.semiperimeter - T₂.b) * (T₂.semiperimeter - T₂.c)) := by
    have hp := congrArg
      (fun m => (Multiset.map (fun x => T₂.semiperimeter - x) m).prod) h
    simpa only [Congruent, Multiset.map_coe, List.map_cons, List.map_nil,
      Multiset.prod_coe, List.prod_cons, List.prod_nil, mul_one] using hp
  unfold Triangle.area
  rw [hs]
  congr 1
  linear_combination T₂.semiperimeter * hprod

/-- A dissection of triangle T into n pieces where the pieces partition T by area.
    Note: area equality is necessary but not sufficient for a genuine tiling;
    a full formalization would also require disjointness and coverage. -/
structure Dissection (T : Triangle) (n : ℕ) where
  pieces : Fin n → Triangle
  -- The pieces partition T by area (necessary condition for a real dissection)
  area_partition : (∑ i, (pieces i).area) = T.area

/-- A valid congruent dissection: all pieces are congruent to each other. -/
def IsCongruentDissection (T : Triangle) (n : ℕ) (D : Dissection T n) : Prop :=
  ∀ i j : Fin n, Congruent (D.pieces i) (D.pieces j)

/-- **The tiling condition (abstract).** `Tiles T n pieces` asserts that the `n`
    triangular `pieces` genuinely *tile* `T`: they cover `T` and have pairwise
    disjoint interiors. Mathlib has no polygonal-tiling API, so this predicate is
    left **abstract** (declared, not defined).

    This abstraction is not cosmetic — it is exactly what keeps the file
    *consistent*. The companion `Erdos634AreaCollapse.lean` proves that the
    area-balance condition alone (`Dissection` + `IsCongruentDissection`) is
    satisfied for **every** `n ≥ 1`, so a dissectability predicate built from area
    balance *only* would make Beeson's `¬IsDissectable 7` and `¬IsDissectable 11`
    (below) provably false — an outright contradiction. Requiring the extra
    abstract `Tiles` witness blocks that trivial equal-area construction, so the
    positive constructions and Beeson's negative results can coexist without
    inconsistency. -/
axiom Tiles (T : Triangle) (n : ℕ) (pieces : Fin n → Triangle) : Prop

/-- **Definition**: `n` is dissectable if some triangle can be cut into `n`
    congruent triangles that genuinely tile it — area balance (`Dissection`),
    mutual congruence (`IsCongruentDissection`), **and** the abstract `Tiles`
    covering/disjointness witness. The `Tiles` conjunct is what makes this
    compatible with the negative results of Part V. -/
def IsDissectable (n : ℕ) : Prop :=
  ∃ T : Triangle, ∃ D : Dissection T n,
    IsCongruentDissection T n D ∧ Tiles T n D.pieces

/-
## Part IV: Known Positive Results

Values of n that ARE dissectable.
-/

/-- The unit equilateral triangle (sides all equal to 1). Used as a witness below. -/
private noncomputable def unitEquil : Triangle where
  a := 1
  b := 1
  c := 1
  ha := by norm_num
  hb := by norm_num
  hc := by norm_num
  triangle_ineq_ab := by norm_num
  triangle_ineq_bc := by norm_num
  triangle_ineq_ca := by norm_num

/-- **The known positive dissection families.** `n` matches a value that the
    literature establishes *is* dissectable into congruent triangles:
    `k²`, `2k²`, `3k²`, `6k²`, or a sum of two positive squares `k² + m²`
    (Snover–Waiveris–Williams and the classical reptiling constructions). -/
def IsKnownPositive (n : ℕ) : Prop :=
  (∃ k, k ≥ 1 ∧ n = k ^ 2) ∨
  (∃ k, k ≥ 1 ∧ n = 2 * k ^ 2) ∨
  (∃ k, k ≥ 1 ∧ n = 3 * k ^ 2) ∨
  (∃ k, k ≥ 1 ∧ n = 6 * k ^ 2) ∨
  (∃ k m, k ≥ 1 ∧ m ≥ 1 ∧ n = k ^ 2 + m ^ 2)

/-- **Known positive dissection results (axiom).** Every `IsKnownPositive n`
    admits an explicit congruent tiling in the literature. The required `Tiles`
    witness (covering + interior-disjointness) cannot be *constructed* here — for
    the very same reason Beeson's negative results below cannot be *refuted* here:
    `Tiles` is abstract and Mathlib has no polygonal-tiling API. So these known
    results are recorded as a single disclosed axiom, mirroring the axiomatized
    negative results `seven_not_dissectable`/`eleven_not_dissectable`, rather than
    left as an unproved placeholder (which would falsely claim they are proved).

    **Consistency with Beeson.** `7` and `11` are `≡ 3 (mod 4)`, so neither is a
    perfect square, twice/thrice/six-times a square, nor a sum of two positive
    squares (a prime `≡ 3 (mod 4)` is never a sum of two squares); hence neither
    satisfies `IsKnownPositive`, and this axiom never yields `IsDissectable 7` or
    `IsDissectable 11`. The positive axiom and the negative axioms therefore
    coexist without contradiction (they are simultaneously satisfiable: take
    `Tiles` to hold exactly on the known-positive `n`). -/
axiom known_positive_dissectable {n : ℕ} (h : IsKnownPositive n) : IsDissectable n

/-- Perfect squares are dissectable (the `k²` congruent-triangle reptiling). -/
theorem squares_dissectable (k : ℕ) (hk : k ≥ 1) : IsDissectable (k ^ 2) :=
  known_positive_dissectable (Or.inl ⟨k, hk, rfl⟩)

/-- `2n²` is dissectable. -/
theorem two_squares_dissectable (n : ℕ) (hn : n ≥ 1) : IsDissectable (2 * n ^ 2) :=
  known_positive_dissectable (Or.inr (Or.inl ⟨n, hn, rfl⟩))

/-- `3n²` is dissectable (equilateral-triangle subdivision). -/
theorem three_squares_dissectable (n : ℕ) (hn : n ≥ 1) : IsDissectable (3 * n ^ 2) :=
  known_positive_dissectable (Or.inr (Or.inr (Or.inl ⟨n, hn, rfl⟩)))

/-- `6n²` is dissectable. -/
theorem six_squares_dissectable (n : ℕ) (hn : n ≥ 1) : IsDissectable (6 * n ^ 2) :=
  known_positive_dissectable (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, rfl⟩))))

/-- `n² + m²` is dissectable for `n, m ≥ 1` (sum-of-two-squares construction). -/
theorem sum_squares_dissectable (n m : ℕ) (hn : n ≥ 1) (hm : m ≥ 1) :
    IsDissectable (n ^ 2 + m ^ 2) :=
  known_positive_dissectable (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, m, hn, hm, rfl⟩))))

/-- 27 is dissectable (special equilateral construction; 27 = 3·3²). -/
theorem twenty_seven_dissectable : IsDissectable 27 := by
  have : 27 = 3 * 3^2 := by norm_num
  rw [this]
  exact three_squares_dissectable 3 (by norm_num)

/-
## Part V: Beeson's Negative Results

Values of n that are NOT dissectable.
-/

/-- **Beeson's Theorem**: 7 is NOT dissectable. -/
axiom seven_not_dissectable : ¬IsDissectable 7

/-- **Beeson's Theorem**: 11 is NOT dissectable. -/
axiom eleven_not_dissectable : ¬IsDissectable 11

/-- Machine-checked consistency (I): `7` matches none of the positive families,
    so `known_positive_dissectable` can never produce `IsDissectable 7`. Together
    with the model argument in that axiom's docstring, this shows the positive
    axiom does not contradict `seven_not_dissectable`. -/
theorem not_isKnownPositive_seven : ¬ IsKnownPositive 7 := by
  have hpow : ∀ j : ℕ, j ≤ j ^ 2 := fun j => Nat.le_self_pow (by norm_num) j
  rintro (⟨k, hk, h⟩ | ⟨k, hk, h⟩ | ⟨k, hk, h⟩ | ⟨k, hk, h⟩ | ⟨k, m, hk, hm, h⟩)
  · have := hpow k; have hk7 : k ≤ 7 := by omega
    interval_cases k <;> norm_num at h
  · omega
  · omega
  · omega
  · have := hpow k; have := hpow m
    have hk7 : k ≤ 7 := by omega
    have hm7 : m ≤ 7 := by omega
    interval_cases k <;> interval_cases m <;> norm_num at h

/-- Machine-checked consistency (II): `11` matches none of the positive families,
    so `known_positive_dissectable` can never produce `IsDissectable 11`; the
    positive axiom does not contradict `eleven_not_dissectable`. -/
theorem not_isKnownPositive_eleven : ¬ IsKnownPositive 11 := by
  have hpow : ∀ j : ℕ, j ≤ j ^ 2 := fun j => Nat.le_self_pow (by norm_num) j
  rintro (⟨k, hk, h⟩ | ⟨k, hk, h⟩ | ⟨k, hk, h⟩ | ⟨k, hk, h⟩ | ⟨k, m, hk, hm, h⟩)
  · have := hpow k; have hk11 : k ≤ 11 := by omega
    interval_cases k <;> norm_num at h
  · have := hpow k; have hk11 : k ≤ 11 := by omega
    interval_cases k <;> norm_num at h
  · have := hpow k; have hk11 : k ≤ 11 := by omega
    interval_cases k <;> norm_num at h
  · omega
  · have := hpow k; have := hpow m
    have hk11 : k ≤ 11 := by omega
    have hm11 : m ≤ 11 := by omega
    interval_cases k <;> interval_cases m <;> norm_num at h

/-- The set of known non-dissectable values. -/
def KnownNonDissectable : Set ℕ := {7, 11}

/-- Both known non-dissectable values are primes of form 4k + 3. -/
theorem non_dissectable_form :
    ∀ n ∈ KnownNonDissectable, ∃ k : ℕ, n = 4 * k + 3 := by
  intro n hn
  simp [KnownNonDissectable] at hn
  cases hn with
  | inl h => exact ⟨1, h⟩
  | inr h => exact ⟨2, h⟩

/-- **Every element of `KnownNonDissectable` is genuinely non-dissectable.**
This ties the `KnownNonDissectable = {7, 11}` set back to Beeson's two theorems
(`seven_not_dissectable`, `eleven_not_dissectable`): the set is not merely a label,
its members really fail to admit a congruent tiling.  Provides a single
`n ∈ KnownNonDissectable → ¬ IsDissectable n` entry point for downstream use. -/
theorem knownNonDissectable_not_dissectable :
    ∀ n ∈ KnownNonDissectable, ¬ IsDissectable n := by
  intro n hn
  simp [KnownNonDissectable] at hn
  cases hn with
  | inl h => subst h; exact seven_not_dissectable
  | inr h => subst h; exact eleven_not_dissectable

/-
## Part VI: The Conjecture

Primes of form 4k + 3 may fail to be dissectable.
-/

/-- **Conjecture**: Primes of form 4k + 3 are not dissectable. -/
def Conjecture_4k3 : Prop :=
  ∀ p : ℕ, p.Prime → (∃ k : ℕ, p = 4 * k + 3) → ¬IsDissectable p

/-- 3 is the exception (it's dissectable as 3·1²). -/
theorem three_dissectable : IsDissectable 3 := by
  have h := three_squares_dissectable 1 (by norm_num)
  simp at h
  exact h

/-- The conjecture should exclude 3. -/
def Conjecture_4k3_refined : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 3 → (∃ k : ℕ, p = 4 * k + 3) → ¬IsDissectable p

/-- **The unrefined conjecture implies the refined one.** `Conjecture_4k3_refined` merely
    adds the hypothesis `p ≠ 3`, so it is logically weaker: anything proving non-dissectability
    for *all* primes of the form `4k+3` in particular proves it for those `≠ 3`. (The converse
    fails precisely at `p = 3`, which `three_dissectable` shows *is* dissectable, so
    `Conjecture_4k3` as stated is already false there — the refinement is the salvageable
    form.) -/
theorem conjecture_implies_refined (h : Conjecture_4k3) : Conjecture_4k3_refined :=
  fun p hp _ hk => h p hp hk

/-
## Part VII: Open Cases

Values whose dissectability is unknown.
-/

/-- 19 is the smallest open case. -/
def OpenCase_19 : Prop := IsDissectable 19 ∨ ¬IsDissectable 19

/-- 19 is of form 4k + 3. -/
theorem nineteen_form : ∃ k : ℕ, 19 = 4 * k + 3 := ⟨4, rfl⟩

/-- 19 is prime. -/
theorem nineteen_prime : Nat.Prime 19 := by decide

/-- If the conjecture holds, 19 is not dissectable. -/
theorem conjecture_implies_19 : Conjecture_4k3_refined → ¬IsDissectable 19 := by
  intro hconj
  apply hconj 19 nineteen_prime (by norm_num) nineteen_form

/-
## Part VIII: Similar Triangles (Soifer's Result)

A complete answer for the similar case.
-/

/-- A similar dissection allows scaled copies. -/
def IsSimilarDissection (T : Triangle) (n : ℕ) (D : Dissection T n) : Prop :=
  ∀ i j : Fin n, Similar (D.pieces i) (D.pieces j)

/-- n is similar-dissectable if some triangle can be cut into n similar triangles. -/
def IsSimilarDissectable (n : ℕ) : Prop :=
  ∃ T : Triangle, ∃ D : Dissection T n, IsSimilarDissection T n D

/-- **Soifer's Theorem**: All n except 2, 3, 5 are similar-dissectable. -/
axiom soifer_theorem (n : ℕ) (hn : n ≥ 1) :
    n ≠ 2 → n ≠ 3 → n ≠ 5 → IsSimilarDissectable n

/- 2, 3, 5 are NOT similar-dissectable (the Soifer exceptions). -/
/-
## Part IX: Self-Similar Dissections

Dissections where pieces are similar to the original.
-/

/-- A self-similar dissection: all pieces similar to the original. -/
def IsSelfSimilarDissection (T : Triangle) (n : ℕ) (D : Dissection T n) : Prop :=
  ∀ i : Fin n, Similar T (D.pieces i)

/-- n is self-similar-dissectable. -/
def IsSelfSimilarDissectable (n : ℕ) : Prop :=
  ∃ T : Triangle, ∃ D : Dissection T n, IsSelfSimilarDissection T n D

/- **Snover-Waiveris-Williams Theorem**: Self-similar dissection requires
    n ∈ {k², k² + m², 3k²} for some k, m. -/
/-
## Part X: Recent Progress

Zhang (2025) and other developments.
-/

/- Zhang's condition: For a ≥ b ≥ 1, large n makes n²ab dissectable. -/

/-- The set of known dissectable values. -/
def KnownDissectable : Set ℕ :=
  { n | (∃ k : ℕ, n = k^2) ∨
        (∃ k : ℕ, n = 2 * k^2) ∨
        (∃ k : ℕ, n = 3 * k^2) ∨
        (∃ k : ℕ, n = 6 * k^2) ∨
        (∃ k m : ℕ, n = k^2 + m^2) }

/-
## Part XI: Main Results

Erdős Problem #634 partial answer.
-/

/-- **Erdős Problem #634: PARTIAL ANSWER**

    Question: For which n does there exist a triangle dissectable
    into n congruent triangles?

    Known to WORK:
    - All perfect squares k²
    - All 2k², 3k², 6k²
    - All k² + m² (sum of two squares)
    - 27 (special construction)

    Known to FAIL:
    - 7 (Beeson)
    - 11 (Beeson)

    OPEN:
    - 19 (smallest unknown)
    - Complete characterization

    Prize: $25 (still unclaimed) -/
theorem erdos_634_partial :
    (∀ k : ℕ, k ≥ 1 → IsDissectable (k^2)) ∧
    ¬IsDissectable 7 ∧
    ¬IsDissectable 11 := by
  constructor
  · exact fun k hk => squares_dissectable k hk
  constructor
  · exact seven_not_dissectable
  · exact eleven_not_dissectable

/-- The answer to Erdős Problem #634. -/
def erdos_634_answer : String :=
  "OPEN: k², 2k², 3k², 6k², k²+m² work; 7, 11 fail; 19 unknown"

/-- The status of the problem. -/
def erdos_634_status : String :=
  "OPEN with $25 prize - complete characterization unknown"

#check erdos_634_partial
#check seven_not_dissectable
#check soifer_theorem

end Erdos634
