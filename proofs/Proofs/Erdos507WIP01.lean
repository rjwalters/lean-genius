/-
# Erdős Problem #507 (Heilbronn's Triangle Problem) — Foundational Lemmas

Axiom-free foundational scaffolding for the objects defined in
`Proofs/Erdos507Problem.lean`:

    triangleArea p q r = |p₁(q₂−r₂) + q₁(r₂−p₂) + r₁(p₂−q₂)| / 2,
    IsInUnitDisk P     = ∀ p ∈ P, p₁² + p₂² ≤ 1,

the shoelace area of a triangle in `ℝ²` and the unit-disk configuration
predicate underlying Heilbronn's function `heilbronn n`.

Heilbronn's triangle problem — estimating `α(n)`, the largest value such that
some `n`-point set in the unit disk keeps every triangle area `≥ α(n)` — is
**open** (the exponent `β` with `α(n) = n^{−β+o(1)}` satisfies only
`7/6 ≤ β ≤ 2`).  The deep bounds (Komlós–Pintz–Szemerédi, Cohen–Pohoata–
Zakharov) are untouched here; this file establishes the elementary geometry
of the atomic building block `triangleArea`:

* nonnegativity;
* full permutation behaviour (transpositions negate the signed area, cyclic
  rotations preserve it — so `triangleArea` is symmetric under all six
  orderings);
* the three degenerate (repeated-vertex) cases vanish;
* `triangleArea = 0 ↔ the three points are collinear` (signed area zero);
* an explicit value `triangleArea (0,0) (1,0) (0,1) = 1/2`;
* unit-disk facts: coordinate bounds `|p₁|, |p₂| ≤ 1`, and the uniform area
  bound `triangleArea p q r ≤ 3` for points in the unit disk (so
  `heilbronn n` is bounded — its `sSup` is over a bounded set);
* `minTriangleArea` facts: nonnegativity (`minTriangleArea_nonneg`) and the
  lower-bound property `minTriangleArea P ≤ triangleArea p q r` for distinct
  `p, q, r ∈ P` (`minTriangleArea_le`), obtained by descending the nine-fold
  nested `⨅` with `ciInf_le_of_le` under the junk-value semantics of an empty
  real infimum;
* `heilbronn n ≤ 3` for `n ≥ 3` (`heilbronn_le_three`): the defining `sSup` set
  is bounded above by the uniform area bound, so Heilbronn's function is finite;
* a concrete positive lower bound `heilbronn 3 ≥ 1/2` (`heilbronn_three_ge_half`)
  from the unit right triangle, hence `heilbronn 3 > 0` (`heilbronn_three_pos`) —
  separating `heilbronn 3` from the junk value `heilbronn 2 = 0`;
* the *sharp* lower bound `heilbronn 3 ≥ 3√3/4` (`heilbronn_three_ge`) from the
  inscribed equilateral triangle;
* the determinant bound `|a₁b₂ − a₂b₁| ≤ 1` in the unit disk
  (`abs_cross_le_one`, Lagrange's identity), giving the improved uniform area
  bound `triangleArea ≤ 3/2` (`triangleArea_le_three_halves`) via
  `E = (p×q)+(q×r)+(r×p)`, hence `heilbronn n ≤ 3/2` for `n ≥ 3`
  (`heilbronn_le_three_halves`, sharpening `heilbronn n ≤ 3`);
* the resulting sandwich `heilbronn 3 ∈ [3√3/4, 3/2] ≈ [1.299, 1.5]`
  (`heilbronn_three_mem_Icc`) — the conjectured exact value is the lower
  endpoint `3√3/4`, and the remaining gap is the sharp inscribed-triangle upper
  bound `heilbronn 3 ≤ 3√3/4`;
* **quantitative decay** `heilbronn n = O(1/n)`: a spread/box area bound
  (`triangleArea_le_spread` — three points within a `w × h` box span area
  `≤ w·h`) plus a `Finset` pigeonhole over `⌊(x+1)·m/2⌋₊` vertical strips give
  `heilbronn n ≤ 4/m` whenever `2(m+1) < n` (`heilbronn_le_four_div`), hence
  `heilbronn n → 0` (`heilbronn_tendsto_zero`).  This is the first bound
  exhibiting genuine decay — all the bounds above are constant in `n` — and
  formalizes the elementary "`α(n) ≪ 1/n`" pigeonhole remark of the problem
  statement.

All results are `0`-axiom / `0`-sorry.

Reference: <https://erdosproblems.com/507>
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Proofs.Erdos507Problem

namespace Erdos507WIP01

/-! ## `triangleArea`: nonnegativity -/

/-- The triangle area is nonnegative (it is an absolute value over `2`). -/
theorem triangleArea_nonneg (p q r : ℝ × ℝ) : 0 ≤ triangleArea p q r := by
  unfold triangleArea; positivity

/-! ## Permutation behaviour

The *signed* area (the bracket before the absolute value) is an alternating
function of the three vertices: transpositions negate it, cyclic rotations
fix it.  After the absolute value, `triangleArea` is therefore invariant under
every permutation of its arguments. -/

/-- Swapping the first two vertices leaves the area unchanged. -/
theorem triangleArea_swap_left (p q r : ℝ × ℝ) :
    triangleArea q p r = triangleArea p q r := by
  unfold triangleArea
  rw [show q.1 * (p.2 - r.2) + p.1 * (r.2 - q.2) + r.1 * (q.2 - p.2)
        = -(p.1 * (q.2 - r.2) + q.1 * (r.2 - p.2) + r.1 * (p.2 - q.2)) from by ring,
    abs_neg]

/-- Swapping the last two vertices leaves the area unchanged. -/
theorem triangleArea_swap_right (p q r : ℝ × ℝ) :
    triangleArea p r q = triangleArea p q r := by
  unfold triangleArea
  rw [show p.1 * (r.2 - q.2) + r.1 * (q.2 - p.2) + q.1 * (p.2 - r.2)
        = -(p.1 * (q.2 - r.2) + q.1 * (r.2 - p.2) + r.1 * (p.2 - q.2)) from by ring,
    abs_neg]

/-- Cyclic rotation of the vertices leaves the area unchanged. -/
theorem triangleArea_cyclic (p q r : ℝ × ℝ) :
    triangleArea q r p = triangleArea p q r := by
  unfold triangleArea
  rw [show q.1 * (r.2 - p.2) + r.1 * (p.2 - q.2) + p.1 * (q.2 - r.2)
        = p.1 * (q.2 - r.2) + q.1 * (r.2 - p.2) + r.1 * (p.2 - q.2) from by ring]

/-! ## Degenerate (repeated-vertex) triangles vanish -/

/-- A repeated first/second vertex gives zero area. -/
theorem triangleArea_self_left (p r : ℝ × ℝ) : triangleArea p p r = 0 := by
  unfold triangleArea
  rw [show p.1 * (p.2 - r.2) + p.1 * (r.2 - p.2) + r.1 * (p.2 - p.2) = 0 from by ring,
    abs_zero, zero_div]

/-- A repeated second/third vertex gives zero area. -/
theorem triangleArea_self_mid (p q : ℝ × ℝ) : triangleArea p q q = 0 := by
  unfold triangleArea
  rw [show p.1 * (q.2 - q.2) + q.1 * (q.2 - p.2) + q.1 * (p.2 - q.2) = 0 from by ring,
    abs_zero, zero_div]

/-- A repeated first/third vertex gives zero area. -/
theorem triangleArea_self_outer (p q : ℝ × ℝ) : triangleArea p q p = 0 := by
  unfold triangleArea
  rw [show p.1 * (q.2 - p.2) + q.1 * (p.2 - p.2) + p.1 * (p.2 - q.2) = 0 from by ring,
    abs_zero, zero_div]

/-! ## Collinearity ⟺ zero area -/

/-- `triangleArea p q r = 0` exactly when the signed area vanishes, i.e. the
    three points are collinear. -/
theorem triangleArea_eq_zero_iff (p q r : ℝ × ℝ) :
    triangleArea p q r = 0 ↔
      p.1 * (q.2 - r.2) + q.1 * (r.2 - p.2) + r.1 * (p.2 - q.2) = 0 := by
  unfold triangleArea
  rw [div_eq_zero_iff]
  simp [abs_eq_zero]

/-! ## An explicit value -/

/-- The unit right triangle `(0,0), (1,0), (0,1)` has area `1/2`. -/
theorem triangleArea_unit :
    triangleArea ((0 : ℝ), (0 : ℝ)) (1, 0) (0, 1) = 1 / 2 := by
  unfold triangleArea; norm_num

/-! ## The unit-disk predicate -/

/-- The empty configuration lies in the unit disk. -/
theorem isInUnitDisk_empty : IsInUnitDisk (∅ : Finset (ℝ × ℝ)) := by
  intro p hp; exact absurd hp (Finset.notMem_empty p)

/-- A subset of a unit-disk configuration is a unit-disk configuration. -/
theorem IsInUnitDisk.subset {P Q : Finset (ℝ × ℝ)} (h : IsInUnitDisk P)
    (hQ : Q ⊆ P) : IsInUnitDisk Q := fun p hp => h p (hQ hp)

/-- In the unit disk, the first coordinate is bounded: `|p₁| ≤ 1`. -/
theorem unitDisk_abs_fst_le {P : Finset (ℝ × ℝ)} (h : IsInUnitDisk P)
    {p : ℝ × ℝ} (hp : p ∈ P) : |p.1| ≤ 1 := by
  have hdisk : p.1 ^ 2 + p.2 ^ 2 ≤ 1 := h p hp
  have hsq : p.1 ^ 2 ≤ 1 := by nlinarith [sq_nonneg p.2]
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (p.1 - 1), sq_nonneg (p.1 + 1)]

/-- In the unit disk, the second coordinate is bounded: `|p₂| ≤ 1`. -/
theorem unitDisk_abs_snd_le {P : Finset (ℝ × ℝ)} (h : IsInUnitDisk P)
    {p : ℝ × ℝ} (hp : p ∈ P) : |p.2| ≤ 1 := by
  have hdisk : p.1 ^ 2 + p.2 ^ 2 ≤ 1 := h p hp
  have hsq : p.2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg p.1]
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (p.2 - 1), sq_nonneg (p.2 + 1)]

/-- **Uniform area bound.** Any triangle with all three vertices in the unit
    disk has area at most `3`.  In particular the `sSup` defining `heilbronn n`
    is taken over a bounded set of reals, so `heilbronn n` is finite. -/
theorem triangleArea_le_three {P : Finset (ℝ × ℝ)} (h : IsInUnitDisk P)
    {p q r : ℝ × ℝ} (hp : p ∈ P) (hq : q ∈ P) (hr : r ∈ P) :
    triangleArea p q r ≤ 3 := by
  have bp1 := unitDisk_abs_fst_le h hp
  have bp2 := unitDisk_abs_snd_le h hp
  have bq1 := unitDisk_abs_fst_le h hq
  have bq2 := unitDisk_abs_snd_le h hq
  have br1 := unitDisk_abs_fst_le h hr
  have br2 := unitDisk_abs_snd_le h hr
  -- each of the three summands has absolute value at most `2`
  have term : ∀ a b c : ℝ, |a| ≤ 1 → |b| ≤ 1 → |c| ≤ 1 → |a * (b - c)| ≤ 2 := by
    intro a b c ha hb hc
    rw [abs_mul]
    have hbc : |b - c| ≤ 2 := by
      rw [abs_le] at hb hc ⊢
      constructor <;> linarith [hb.1, hb.2, hc.1, hc.2]
    calc |a| * |b - c| ≤ 1 * 2 :=
          mul_le_mul ha hbc (abs_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  have t1 := term p.1 q.2 r.2 bp1 bq2 br2
  have t2 := term q.1 r.2 p.2 bq1 br2 bp2
  have t3 := term r.1 p.2 q.2 br1 bp2 bq2
  unfold triangleArea
  have hE : |p.1 * (q.2 - r.2) + q.1 * (r.2 - p.2) + r.1 * (p.2 - q.2)| ≤ 6 := by
    calc |p.1 * (q.2 - r.2) + q.1 * (r.2 - p.2) + r.1 * (p.2 - q.2)|
        ≤ |p.1 * (q.2 - r.2) + q.1 * (r.2 - p.2)| + |r.1 * (p.2 - q.2)| :=
          abs_add_le _ _
      _ ≤ |p.1 * (q.2 - r.2)| + |q.1 * (r.2 - p.2)| + |r.1 * (p.2 - q.2)| := by
          gcongr; exact abs_add_le _ _
      _ ≤ 6 := by linarith [t1, t2, t3]
  linarith [hE]

/-! ## `minTriangleArea`: the nested infimum over triples

`minTriangleArea P` is the infimum of `triangleArea p q r` over all ordered
triples of *distinct* points `p, q, r ∈ P`, encoded as a nine-fold nested
`⨅` (three membership binders and three distinctness binders around the value).
In a conditionally complete lattice such an `⨅` carries junk-value semantics on
empty index types, but over `ℝ` the junk value of an empty infimum is `0`
(`Real.sInf_empty`), so the two basic facts below hold unconditionally. -/

/-- A real-valued family that is everywhere nonnegative is bounded below (by
`0`).  This is the recurring side condition for `ciInf_le` on the nested
infimum of `minTriangleArea`. -/
private theorem bddBelow_range_of_nonneg {ι : Sort*} {f : ι → ℝ}
    (h : ∀ i, 0 ≤ f i) : BddBelow (Set.range f) :=
  ⟨0, by rintro _ ⟨i, rfl⟩; exact h i⟩

/-- **Nonnegativity of the minimum triangle area.**  Every value in the nested
infimum is a nonnegative `triangleArea`, and the empty-index junk value is `0`,
so `minTriangleArea P ≥ 0` for every configuration `P`. -/
theorem minTriangleArea_nonneg (P : Finset (ℝ × ℝ)) : 0 ≤ minTriangleArea P := by
  unfold minTriangleArea
  repeat' first
    | exact triangleArea_nonneg _ _ _
    | (apply Real.iInf_nonneg; intro)

/-- **The minimum triangle area is a lower bound.**  For any three *distinct*
points `p, q, r ∈ P`, the nested infimum defining `minTriangleArea P` is at most
`triangleArea p q r`.  Proof: descend through the nine `⨅` binders with
`ciInf_le_of_le`, using nonnegativity to supply the `BddBelow` side conditions. -/
theorem minTriangleArea_le {P : Finset (ℝ × ℝ)} {p q r : ℝ × ℝ}
    (hp : p ∈ P) (hq : q ∈ P) (hr : r ∈ P)
    (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) :
    minTriangleArea P ≤ triangleArea p q r := by
  unfold minTriangleArea
  -- Descend through the nine `⨅` binders with `ciInf_le_of_le`; each `BddBelow`
  -- side goal follows from nonnegativity of the (nested) `triangleArea` values.
  refine ciInf_le_of_le (bddBelow_range_of_nonneg ?_) p ?_
  · intro _; repeat' first
      | exact triangleArea_nonneg _ _ _
      | (apply Real.iInf_nonneg; intro)
  refine ciInf_le_of_le (bddBelow_range_of_nonneg ?_) hp ?_
  · intro _; repeat' first
      | exact triangleArea_nonneg _ _ _
      | (apply Real.iInf_nonneg; intro)
  refine ciInf_le_of_le (bddBelow_range_of_nonneg ?_) q ?_
  · intro _; repeat' first
      | exact triangleArea_nonneg _ _ _
      | (apply Real.iInf_nonneg; intro)
  refine ciInf_le_of_le (bddBelow_range_of_nonneg ?_) hq ?_
  · intro _; repeat' first
      | exact triangleArea_nonneg _ _ _
      | (apply Real.iInf_nonneg; intro)
  refine ciInf_le_of_le (bddBelow_range_of_nonneg ?_) r ?_
  · intro _; repeat' first
      | exact triangleArea_nonneg _ _ _
      | (apply Real.iInf_nonneg; intro)
  refine ciInf_le_of_le (bddBelow_range_of_nonneg ?_) hr ?_
  · intro _; repeat' first
      | exact triangleArea_nonneg _ _ _
      | (apply Real.iInf_nonneg; intro)
  refine ciInf_le_of_le (bddBelow_range_of_nonneg ?_) hpq ?_
  · intro _; repeat' first
      | exact triangleArea_nonneg _ _ _
      | (apply Real.iInf_nonneg; intro)
  refine ciInf_le_of_le (bddBelow_range_of_nonneg ?_) hqr ?_
  · intro _; repeat' first
      | exact triangleArea_nonneg _ _ _
      | (apply Real.iInf_nonneg; intro)
  exact ciInf_le_of_le (bddBelow_range_of_nonneg fun _ => triangleArea_nonneg p q r) hpr le_rfl

/-! ## `heilbronn`: the sSup is bounded for `n ≥ 3` -/

/-- **`heilbronn n ≤ 3` for `n ≥ 3`.**  The defining set of `heilbronn n` is
bounded above by `3`: any admissible bound `α` is `≤ triangleArea p q r` for some
distinct triple in the witness configuration (which exists since `card = n ≥ 3`),
and every unit-disk triangle has area `≤ 3` (`triangleArea_le_three`). -/
theorem heilbronn_le_three (n : ℕ) (hn : 3 ≤ n) : heilbronn n ≤ 3 := by
  unfold heilbronn
  apply Real.sSup_le
  · rintro α ⟨P, hcard, hdisk, hbound⟩
    have hcard3 : 2 < P.card := by omega
    obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := Finset.two_lt_card_iff.mp hcard3
    have h1 : α ≤ triangleArea p q r := hbound p hp q hq r hr hpq hqr hpr
    have h2 : triangleArea p q r ≤ 3 := triangleArea_le_three hdisk hp hq hr
    linarith
  · norm_num

/-! ## Existence of unit-disk configurations of every cardinality

For every `n` there is an `n`-point configuration inside the unit disk (place the
points `(k/n, 0)`, `k = 0, …, n−1`, on a horizontal chord).  This makes the
defining set of `heilbronn n` nonempty, which is exactly the side condition
`csSup_le_csSup` needs for the monotonicity result below. -/

/-- **Configurations of every size exist in the unit disk.**  For any `n` there
is a `Finset` of exactly `n` points, all inside the closed unit disk (the equally
spaced points `(k/n, 0)` on the horizontal diameter). -/
theorem exists_unitDisk_config (n : ℕ) :
    ∃ P : Finset (ℝ × ℝ), P.card = n ∧ IsInUnitDisk P := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact ⟨∅, by simp [hn], isInUnitDisk_empty⟩
  · have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have inj : Function.Injective (fun k : ℕ => ((k : ℝ) / n, (0 : ℝ))) := by
      intro a b hab
      simp only [Prod.mk.injEq] at hab
      have h1 := hab.1
      field_simp at h1
      exact_mod_cast h1
    refine ⟨(Finset.range n).image (fun k : ℕ => ((k : ℝ) / n, (0 : ℝ))), ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ inj, Finset.card_range]
    · intro p hp
      simp only [Finset.mem_image, Finset.mem_range] at hp
      obtain ⟨k, hk, rfl⟩ := hp
      have hkn : (k : ℝ) / n < 1 := by
        rw [div_lt_one (by exact_mod_cast hn)]
        exact_mod_cast hk
      have hknneg : 0 ≤ (k : ℝ) / n :=
        div_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg n)
      simp only
      nlinarith [hkn, hknneg]

/-! ## Monotonicity of `heilbronn`

Adding a point to an admissible configuration can only introduce new triples, so
it can only *decrease* the minimum triangle area.  Hence `heilbronn` is antitone
for `n ≥ 3`: every witness configuration for `n + 1` restricts (by deleting one
point) to a witness for `n` achieving the same bound, so the defining set for
`n + 1` is contained in that for `n`. -/

/-- The defining set of `heilbronn n` is bounded above by `3` once `n ≥ 3`: any
admissible bound is `≤` the area of some distinct triple, and every unit-disk
triangle has area `≤ 3`.  (This is the boundedness half of `heilbronn_le_three`,
isolated for reuse in the monotonicity proof.) -/
private theorem heilbronn_defining_bddAbove (n : ℕ) (hn : 3 ≤ n) :
    BddAbove { α : ℝ | ∃ P : Finset (ℝ × ℝ), P.card = n ∧ IsInUnitDisk P ∧
      ∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P, p ≠ q → q ≠ r → p ≠ r →
        triangleArea p q r ≥ α } := by
  refine ⟨3, ?_⟩
  rintro α ⟨P, hcard, hdisk, hbound⟩
  have hcard3 : 2 < P.card := by omega
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := Finset.two_lt_card_iff.mp hcard3
  have h1 : α ≤ triangleArea p q r := hbound p hp q hq r hr hpq hqr hpr
  have h2 : triangleArea p q r ≤ 3 := triangleArea_le_three hdisk hp hq hr
  linarith

/-- **`heilbronn n` is nonnegative for `n ≥ 3`.**  The bound `0` is admissible for
any configuration (all areas are nonnegative) and an `n`-point unit-disk
configuration exists, so `0` lies in the defining set of the `sSup`. -/
theorem heilbronn_nonneg (n : ℕ) (hn : 3 ≤ n) : 0 ≤ heilbronn n := by
  unfold heilbronn
  obtain ⟨P, hcard, hdisk⟩ := exists_unitDisk_config n
  refine le_csSup (heilbronn_defining_bddAbove n hn) ?_
  exact ⟨P, hcard, hdisk, fun p _ q _ r _ _ _ _ => triangleArea_nonneg p q r⟩

/-- **One-step monotonicity.**  `heilbronn (n + 1) ≤ heilbronn n` for `n ≥ 3`.
Every witness configuration for `n + 1` restricts, by deleting one point, to an
`n`-point witness achieving the same lower bound, so the defining set for `n + 1`
is contained in that for `n`; both `sSup`s are over bounded, nonempty sets. -/
theorem heilbronn_succ_le (n : ℕ) (hn : 3 ≤ n) :
    heilbronn (n + 1) ≤ heilbronn n := by
  unfold heilbronn
  apply csSup_le_csSup (heilbronn_defining_bddAbove n hn)
  · -- the defining set for `n + 1` is nonempty: the all-zero bound is admissible
    obtain ⟨P, hcard, hdisk⟩ := exists_unitDisk_config (n + 1)
    exact ⟨0, P, hcard, hdisk, fun p _ q _ r _ _ _ _ => triangleArea_nonneg p q r⟩
  · -- containment: delete one point from an `(n+1)`-witness to get an `n`-witness
    rintro α ⟨P, hcard, hdisk, hbound⟩
    have hpos : 0 < P.card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    refine ⟨P.erase x, ?_, IsInUnitDisk.subset hdisk (Finset.erase_subset x P), ?_⟩
    · rw [Finset.card_erase_of_mem hx, hcard]
      omega
    · intro p hp q hq r hr hpq hqr hpr
      exact hbound p (Finset.mem_of_mem_erase hp) q (Finset.mem_of_mem_erase hq)
        r (Finset.mem_of_mem_erase hr) hpq hqr hpr

/-- **Monotonicity of `heilbronn`.**  For `3 ≤ m ≤ n`, `heilbronn n ≤ heilbronn m`:
Heilbronn's function is antitone on `{n ∣ n ≥ 3}`.  (Below `3` the defining `sSup`
is over an unbounded set and takes the junk value `0`, so monotonicity is stated
from `3` onward.) -/
theorem heilbronn_antitone {m n : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) :
    heilbronn n ≤ heilbronn m := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    exact le_trans (heilbronn_succ_le k (le_trans hm hk)) ih

/-- **Heilbronn's function is bounded into `[0, 3]`.**  Combining `heilbronn_nonneg`
and `heilbronn_le_three`, for `n ≥ 3` the value `heilbronn n` lies in the unit-disk
area envelope `0 ≤ heilbronn n ≤ 3`.  (The true order of magnitude is
`n^{−β+o(1)}` with `7/6 ≤ β ≤ 2`, far below `3`, but that is the open deep content;
this records the elementary two-sided bound the foundational lemmas already give.) -/
theorem heilbronn_mem_Icc (n : ℕ) (hn : 3 ≤ n) : heilbronn n ∈ Set.Icc (0 : ℝ) 3 :=
  ⟨heilbronn_nonneg n hn, heilbronn_le_three n hn⟩

/-! ## A concrete positive lower bound at `n = 3`

The `heilbronn_nonneg` bound above (`0 ≤ heilbronn n`) does not separate the
`n ≥ 3` regime from the junk value `heilbronn 2 = 0`; a genuine *positive*
witness is needed.  The unit right triangle `(0,0), (1,0), (0,1)` is a
three-point unit-disk configuration all of whose orderings have `triangleArea`
equal to `1/2` (`triangleArea_unit` together with the permutation lemmas), so
`1/2` is admissible for `heilbronn 3`.  This gives `heilbronn 3 ≥ 1/2 > 0`,
confirming that `heilbronn 3 > heilbronn 2 = 0` and hence that the `n ≥ 3`
hypothesis on the monotonicity lemmas is forced rather than cosmetic. -/

/-- **`heilbronn 3 ≥ 1/2`.**  The right triangle `(0,0), (1,0), (0,1)` lies in the
unit disk and every ordering of its three distinct vertices has `triangleArea`
exactly `1/2`, so `1/2` lies in the defining `sSup` set of `heilbronn 3`
(`le_csSup`, using `heilbronn_defining_bddAbove` for boundedness). -/
theorem heilbronn_three_ge_half : (1 : ℝ) / 2 ≤ heilbronn 3 := by
  unfold heilbronn
  refine le_csSup (heilbronn_defining_bddAbove 3 (by norm_num)) ?_
  refine ⟨{((0 : ℝ), (0 : ℝ)), (1, 0), (0, 1)}, ?_, ?_, ?_⟩
  · -- the three vertices are distinct, so the configuration has cardinality `3`
    rw [Finset.card_eq_three]
    exact ⟨(0, 0), (1, 0), (0, 1),
      by simp [Prod.ext_iff], by simp [Prod.ext_iff], by simp [Prod.ext_iff], rfl⟩
  · -- each vertex lies in the closed unit disk
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> norm_num
  · -- every ordered distinct triple has area `1/2 ≥ 1/2`
    intro p hp q hq r hr hpq hqr hpr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq hr
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
        rcases hr with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hpq
        | exact absurd rfl hqr
        | exact absurd rfl hpr
        | (show (1 : ℝ) / 2 ≤ triangleArea _ _ _; unfold triangleArea; norm_num)

/-- **`heilbronn 3` is strictly positive.**  Immediate from
`heilbronn_three_ge_half`.  Since `heilbronn 2 = 0` (no distinct triple exists
below `n = 3`, so the defining `sSup` collapses to its junk value `0`), this
shows Heilbronn's function is *not* monotone across the `2 → 3` boundary — the
reason the monotonicity lemmas are stated only from `n = 3` onward. -/
theorem heilbronn_three_pos : 0 < heilbronn 3 :=
  lt_of_lt_of_le (by norm_num) heilbronn_three_ge_half

/-! ## The sharp lower bound at `n = 3` -/

/-- **`heilbronn 3 ≥ 3√3/4`.**  The equilateral triangle inscribed in the unit circle,
`(1,0), (−1/2, √3/2), (−1/2, −√3/2)`, has all three vertices on the boundary of the unit
disk, and every ordering of its vertices has `triangleArea` equal to `3√3/4` — the area of
the largest triangle inscribable in a radius-`1` disk.  Hence `3√3/4` is admissible for the
`sSup` defining `heilbronn 3`.  This sharpens the crude right-triangle witness
`heilbronn 3 ≥ 1/2` to the *conjectured exact value*: the matching upper bound
`heilbronn 3 ≤ 3√3/4` (every unit-disk triangle has area `≤ 3√3/4`) would pin
`heilbronn 3 = 3√3/4`, improving the current `heilbronn 3 ≤ 3`. -/
theorem heilbronn_three_ge : 3 * Real.sqrt 3 / 4 ≤ heilbronn 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrt_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  -- every ordering of the inscribed equilateral triangle has area `3√3/4`
  have hval : triangleArea ((1 : ℝ), (0 : ℝ)) (-(1/2), Real.sqrt 3 / 2)
      (-(1/2), -(Real.sqrt 3 / 2)) = 3 * Real.sqrt 3 / 4 := by
    unfold triangleArea
    rw [show ((1:ℝ), (0:ℝ)).1 * (((-(1/2) : ℝ), Real.sqrt 3 / 2).2
              - ((-(1/2):ℝ), -(Real.sqrt 3 / 2)).2)
          + ((-(1/2):ℝ), Real.sqrt 3 / 2).1 * (((-(1/2):ℝ), -(Real.sqrt 3 / 2)).2
              - ((1:ℝ),(0:ℝ)).2)
          + ((-(1/2):ℝ), -(Real.sqrt 3 / 2)).1 * (((1:ℝ),(0:ℝ)).2
              - ((-(1/2):ℝ), Real.sqrt 3 / 2).2)
          = 3 * Real.sqrt 3 / 2 from by ring]
    rw [abs_of_nonneg (by positivity)]
    ring
  unfold heilbronn
  refine le_csSup (heilbronn_defining_bddAbove 3 (by norm_num)) ?_
  refine ⟨{((1 : ℝ), (0 : ℝ)), (-(1/2), Real.sqrt 3 / 2), (-(1/2), -(Real.sqrt 3 / 2))},
    ?_, ?_, ?_⟩
  · -- the three vertices are distinct, so the configuration has cardinality `3`
    rw [Finset.card_eq_three]
    refine ⟨((1:ℝ),(0:ℝ)), (-(1/2), Real.sqrt 3 / 2), (-(1/2), -(Real.sqrt 3 / 2)),
      ?_, ?_, ?_, rfl⟩
    · intro h; rw [Prod.ext_iff] at h; norm_num at h
    · intro h; rw [Prod.ext_iff] at h; norm_num at h
    · intro h; rw [Prod.ext_iff] at h; have h2 := h.2; linarith [hsqrt_pos]
  · -- each vertex lies in the closed unit disk (all three on the boundary)
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · show (1:ℝ) ^ 2 + (0:ℝ) ^ 2 ≤ 1; norm_num
    · show (-(1/2):ℝ) ^ 2 + (Real.sqrt 3 / 2) ^ 2 ≤ 1; nlinarith [h3]
    · show (-(1/2):ℝ) ^ 2 + (-(Real.sqrt 3 / 2)) ^ 2 ≤ 1; nlinarith [h3]
  · -- every ordered distinct triple has area `3√3/4 ≥ 3√3/4` (permutation-invariant)
    intro p hp q hq r hr hpq hqr hpr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq hr
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
        rcases hr with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hpq
        | exact absurd rfl hqr
        | exact absurd rfl hpr
        | exact ge_of_eq hval
        | (rw [triangleArea_swap_right]; exact ge_of_eq hval)
        | (rw [triangleArea_swap_left]; exact ge_of_eq hval)
        | (rw [triangleArea_cyclic]; exact ge_of_eq hval)
        | (rw [triangleArea_cyclic, triangleArea_cyclic]; exact ge_of_eq hval)
        | (rw [triangleArea_swap_left, triangleArea_cyclic]; exact ge_of_eq hval)

/-! ## An improved uniform upper bound: `area ≤ 3/2`

The crude bound `triangleArea ≤ 3` (`triangleArea_le_three`) came from bounding
each of the three signed-area summands by `2`.  A sharper argument uses that the
signed area is a *sum of three 2×2 determinants* (cross products) taken from the
origin:

    E := p₁(q₂−r₂) + q₁(r₂−p₂) + r₁(p₂−q₂)
       = (p × q) + (q × r) + (r × p),   where  a × b := a₁b₂ − a₂b₁.

For points in the unit disk each determinant satisfies `|a × b| ≤ |a|·|b| ≤ 1`
(Lagrange's identity `(a×b)² = |a|²|b|² − ⟨a,b⟩² ≤ |a|²|b|²`), so `|E| ≤ 3` and
`triangleArea = |E|/2 ≤ 3/2`.  This improves `heilbronn n ≤ 3` to
`heilbronn n ≤ 3/2` for every `n ≥ 3`, and combined with the sharp lower bound
`heilbronn 3 ≥ 3√3/4` it sandwiches `heilbronn 3 ∈ [3√3/4, 3/2] ≈ [1.299, 1.5]`.
(The exact value is conjectured to be the lower endpoint `3√3/4`; closing the
gap needs the sharp maximal-inscribed-triangle bound, still open here.) -/

/-- **Determinant bound in the unit disk.**  For two points `a, b` in the closed
unit disk, the `2×2` determinant `a₁b₂ − a₂b₁` (the cross product / twice the
signed area of the triangle `O a b`) has absolute value at most `1`.  This is
Lagrange's identity: `(a₁b₂−a₂b₁)² = (a₁²+a₂²)(b₁²+b₂²) − (a₁b₁+a₂b₂)²`, and both
squared norms are `≤ 1`. -/
theorem abs_cross_le_one {P : Finset (ℝ × ℝ)} (h : IsInUnitDisk P)
    {a b : ℝ × ℝ} (ha : a ∈ P) (hb : b ∈ P) :
    |a.1 * b.2 - a.2 * b.1| ≤ 1 := by
  have hda : a.1 ^ 2 + a.2 ^ 2 ≤ 1 := h a ha
  have hdb : b.1 ^ 2 + b.2 ^ 2 ≤ 1 := h b hb
  have hA : (0 : ℝ) ≤ a.1 ^ 2 + a.2 ^ 2 := by positivity
  have hAB : (a.1 ^ 2 + a.2 ^ 2) * (b.1 ^ 2 + b.2 ^ 2) ≤ 1 := by nlinarith [hda, hdb, hA]
  -- Lagrange: (a×b)² = |a|²|b|² − ⟨a,b⟩² ≤ |a|²|b|² ≤ 1
  have hsq : (a.1 * b.2 - a.2 * b.1) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (a.1 * b.1 + a.2 * b.2), hAB]
  rw [abs_le]
  constructor <;>
    nlinarith [hsq, sq_nonneg (a.1 * b.2 - a.2 * b.1 - 1),
      sq_nonneg (a.1 * b.2 - a.2 * b.1 + 1)]

/-- **Improved uniform area bound `area ≤ 3/2`.**  Any triangle with all three
vertices in the unit disk has area at most `3/2`.  Write the signed area as the
sum of three determinants `E = (p×q) + (q×r) + (r×p)`; each has `|·| ≤ 1`
(`abs_cross_le_one`), so `|E| ≤ 3` and `triangleArea = |E|/2 ≤ 3/2`.  This
sharpens `triangleArea_le_three`. -/
theorem triangleArea_le_three_halves {P : Finset (ℝ × ℝ)} (h : IsInUnitDisk P)
    {p q r : ℝ × ℝ} (hp : p ∈ P) (hq : q ∈ P) (hr : r ∈ P) :
    triangleArea p q r ≤ 3 / 2 := by
  have c1 := abs_cross_le_one h hp hq
  have c2 := abs_cross_le_one h hq hr
  have c3 := abs_cross_le_one h hr hp
  unfold triangleArea
  have hE : |p.1 * (q.2 - r.2) + q.1 * (r.2 - p.2) + r.1 * (p.2 - q.2)| ≤ 3 := by
    have hid : p.1 * (q.2 - r.2) + q.1 * (r.2 - p.2) + r.1 * (p.2 - q.2)
        = (p.1 * q.2 - p.2 * q.1) + (q.1 * r.2 - q.2 * r.1) + (r.1 * p.2 - r.2 * p.1) := by
      ring
    rw [hid]
    calc |(p.1 * q.2 - p.2 * q.1) + (q.1 * r.2 - q.2 * r.1) + (r.1 * p.2 - r.2 * p.1)|
        ≤ |(p.1 * q.2 - p.2 * q.1) + (q.1 * r.2 - q.2 * r.1)| + |r.1 * p.2 - r.2 * p.1| :=
          abs_add_le _ _
      _ ≤ |p.1 * q.2 - p.2 * q.1| + |q.1 * r.2 - q.2 * r.1| + |r.1 * p.2 - r.2 * p.1| := by
          gcongr; exact abs_add_le _ _
      _ ≤ 3 := by linarith [c1, c2, c3]
  linarith [hE]

/-- **`heilbronn n ≤ 3/2` for `n ≥ 3`.**  Every admissible bound `α` in the
defining `sSup` is `≤` the area of some distinct triple in the witness
configuration, and every unit-disk triangle has area `≤ 3/2`
(`triangleArea_le_three_halves`).  Improves `heilbronn_le_three`. -/
theorem heilbronn_le_three_halves (n : ℕ) (hn : 3 ≤ n) : heilbronn n ≤ 3 / 2 := by
  unfold heilbronn
  apply Real.sSup_le
  · rintro α ⟨P, hcard, hdisk, hbound⟩
    have hcard3 : 2 < P.card := by omega
    obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := Finset.two_lt_card_iff.mp hcard3
    have h1 : α ≤ triangleArea p q r := hbound p hp q hq r hr hpq hqr hpr
    have h2 : triangleArea p q r ≤ 3 / 2 := triangleArea_le_three_halves hdisk hp hq hr
    linarith
  · norm_num

/-- **Sandwich for `heilbronn 3`.**  Combining the sharp lower bound
`heilbronn 3 ≥ 3√3/4` (`heilbronn_three_ge`, the inscribed equilateral triangle)
with the improved upper bound `heilbronn 3 ≤ 3/2` (`heilbronn_le_three_halves`)
locates `heilbronn 3` in the interval `[3√3/4, 3/2] ≈ [1.299, 1.5]`.  The
conjectured exact value is the lower endpoint `3√3/4`; the remaining gap is the
sharp maximal-inscribed-triangle upper bound `heilbronn 3 ≤ 3√3/4`. -/
theorem heilbronn_three_mem_Icc :
    heilbronn 3 ∈ Set.Icc (3 * Real.sqrt 3 / 4) (3 / 2) :=
  ⟨heilbronn_three_ge, heilbronn_le_three_halves 3 (by norm_num)⟩

/-! ## A concrete lower bound at `n = 4`: the inscribed square

The `n = 3` ladder above pins `heilbronn 3` inside `[3√3/4, 3/2]`.  The next rung
is a genuine *four-point* witness: the square inscribed in the unit circle.  Its
four vertices `(1,0), (0,1), (−1,0), (0,−1)` produce exactly four unordered
triples, and each spans a right triangle of area exactly `1` (each triple omits
one vertex; the remaining three form half of the inscribed square, which has
area `2`).  Hence `1` is admissible for the `sSup` defining `heilbronn 4`, giving
the first nontrivial lower bound beyond `n = 3` — and, with the Lagrange upper
bound `heilbronn n ≤ 3/2`, a second sandwich `heilbronn 4 ∈ [1, 3/2]` of width
`1/2`. -/

/-- **`heilbronn 4 ≥ 1`.**  The square inscribed in the unit circle,
`(1,0), (0,1), (−1,0), (0,−1)`, is a four-point unit-disk configuration in which
every ordering of every distinct vertex triple has `triangleArea` exactly `1`,
so `1` lies in the defining `sSup` set of `heilbronn 4` (`le_csSup`, using
`heilbronn_defining_bddAbove` for boundedness). -/
theorem heilbronn_four_ge : (1 : ℝ) ≤ heilbronn 4 := by
  unfold heilbronn
  refine le_csSup (heilbronn_defining_bddAbove 4 (by norm_num)) ?_
  refine ⟨{((1 : ℝ), (0 : ℝ)), (0, 1), (-1, 0), (0, -1)}, ?_, ?_, ?_⟩
  · -- the four vertices are distinct, so the configuration has cardinality `4`
    rw [Finset.card_insert_of_notMem (by norm_num [Prod.ext_iff]),
      Finset.card_insert_of_notMem (by norm_num [Prod.ext_iff]),
      Finset.card_insert_of_notMem (by norm_num [Prod.ext_iff]),
      Finset.card_singleton]
  · -- each vertex lies on the boundary of the closed unit disk
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  · -- every ordered distinct triple has area exactly `1 ≥ 1`
    intro p hp q hq r hr hpq hqr hpr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq hr
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
        rcases hr with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hpq
        | exact absurd rfl hqr
        | exact absurd rfl hpr
        | (show (1 : ℝ) ≤ triangleArea _ _ _; unfold triangleArea; norm_num)

/-- **`heilbronn 4` is strictly positive** — immediate from `heilbronn_four_ge`. -/
theorem heilbronn_four_pos : 0 < heilbronn 4 :=
  lt_of_lt_of_le (by norm_num) heilbronn_four_ge

/-- **Sandwich at `n = 4`:** `heilbronn 4 ∈ [1, 3/2]`.  Lower bound from the
inscribed square (`heilbronn_four_ge`); upper bound from the Lagrange bound
`heilbronn n ≤ 3/2` (`heilbronn_le_three_halves`).  Note the lower bound is *not*
claimed sharp: whether the inscribed square is the optimal four-point
configuration in the disk is part of the open quantitative problem. -/
theorem heilbronn_four_mem_Icc : heilbronn 4 ∈ Set.Icc (1 : ℝ) (3 / 2) :=
  ⟨heilbronn_four_ge, heilbronn_le_three_halves 4 (by norm_num)⟩

/-! ## Quantitative decay: `heilbronn n = O(1/n)`

All the upper bounds above (`heilbronn n ≤ 3`, `≤ 3/2`) are *constant* in `n` —
they witness finiteness but not decay.  The elementary pigeonhole argument
sketched in the problem statement shows that Heilbronn's function actually
**decays**: cut the unit disk into `m + 1` vertical strips of width `2/m`; once
`2(m+1) < n`, some strip must contain three of the `n` points, and three points
sharing a strip of width `2/m` and height `2` span a triangle of area at most
`(2/m)·2 = 4/m`.  Hence `heilbronn n ≤ 4/m` for every admissible `m`, so
`heilbronn n → 0`.  This is qualitatively stronger than the constant bounds:
combined with `heilbronn_antitone` it shows Heilbronn's function is a strictly
decaying-to-zero sequence, matching the (much finer) known asymptotic
`α(n) = n^{−β+o(1)}` with `7/6 ≤ β ≤ 2` at the crudest exponent level. -/

/-- **Spread bound for the triangle area.**  If the `x`-coordinates of `p, q`
lie within `w` of `r.1` and their `y`-coordinates within `h` of `r.2`, then the
triangle `p q r` has area at most `w · h`.  Proof: the shoelace signed area
equals the `2×2` determinant `(p₁−r₁)(q₂−r₂) − (q₁−r₁)(p₂−r₂)`, whose two
products are each `≤ w·h` in absolute value, so `|signed area| ≤ 2wh` and
`triangleArea = |signed area| / 2 ≤ wh`. -/
theorem triangleArea_le_spread (p q r : ℝ × ℝ) {w h : ℝ}
    (hpx : |p.1 - r.1| ≤ w) (hqx : |q.1 - r.1| ≤ w)
    (hpy : |p.2 - r.2| ≤ h) (hqy : |q.2 - r.2| ≤ h)
    (hw : 0 ≤ w) :
    triangleArea p q r ≤ w * h := by
  have hA : |(p.1 - r.1) * (q.2 - r.2)| ≤ w * h := by
    rw [abs_mul]; exact mul_le_mul hpx hqy (abs_nonneg _) hw
  have hB : |(q.1 - r.1) * (p.2 - r.2)| ≤ w * h := by
    rw [abs_mul]; exact mul_le_mul hqx hpy (abs_nonneg _) hw
  have key : |(p.1 - r.1) * (q.2 - r.2) - (q.1 - r.1) * (p.2 - r.2)|
      ≤ |(p.1 - r.1) * (q.2 - r.2)| + |(q.1 - r.1) * (p.2 - r.2)| := by
    have h := abs_add_le ((p.1 - r.1) * (q.2 - r.2)) (-((q.1 - r.1) * (p.2 - r.2)))
    rwa [abs_neg, ← sub_eq_add_neg] at h
  unfold triangleArea
  have hid : p.1 * (q.2 - r.2) + q.1 * (r.2 - p.2) + r.1 * (p.2 - q.2)
      = (p.1 - r.1) * (q.2 - r.2) - (q.1 - r.1) * (p.2 - r.2) := by ring
  rw [hid]
  linarith [key, hA, hB]

/-- **Same-strip `x`-spread bound.**  If two points `pt₁, pt₂` (both with
`x`-coordinate `≥ −1`) fall in the same strip `⌊(x+1)·m/2⌋₊`, their
`x`-coordinates differ by at most `2/m`, stated division-free as
`|pt₁.1 − pt₂.1| · m ≤ 2`.  Equal `⌊·⌋₊` forces both `(x+1)m/2` into a common
unit interval `[j, j+1)`. -/
private theorem strip_spread {pt₁ pt₂ : ℝ × ℝ} {m : ℕ}
    (h₁ : -1 ≤ pt₁.1) (h₂ : -1 ≤ pt₂.1)
    (hfe : ⌊(pt₁.1 + 1) * m / 2⌋₊ = ⌊(pt₂.1 + 1) * m / 2⌋₊) :
    |pt₁.1 - pt₂.1| * m ≤ 2 := by
  have hnn1 : (0 : ℝ) ≤ (pt₁.1 + 1) * m / 2 :=
    div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg m)) (by norm_num)
  have hnn2 : (0 : ℝ) ≤ (pt₂.1 + 1) * m / 2 :=
    div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg m)) (by norm_num)
  have l1 := Nat.floor_le hnn1
  have u1 := Nat.lt_floor_add_one ((pt₁.1 + 1) * m / 2)
  have l2 := Nat.floor_le hnn2
  have u2 := Nat.lt_floor_add_one ((pt₂.1 + 1) * m / 2)
  rw [hfe] at l1 u1
  have goalform : |pt₁.1 - pt₂.1| * (m : ℝ) = |(pt₁.1 - pt₂.1) * m| := by
    rw [abs_mul, Nat.abs_cast]
  have hDm : (pt₁.1 - pt₂.1) * (m : ℝ)
      = 2 * ((pt₁.1 + 1) * m / 2) - 2 * ((pt₂.1 + 1) * m / 2) := by ring
  rw [goalform, abs_le]
  constructor
  · rw [hDm]; linarith [l1, u2]
  · rw [hDm]; linarith [u1, l2]

/-- **Pigeonhole decay bound.**  For every number of strips `m ≥ 1` with
`2(m + 1) < n`, Heilbronn's function satisfies `heilbronn n ≤ 4/m`.  Since the
right-hand side can be made arbitrarily small by taking `m` (hence `n`) large,
this is the first bound exhibiting genuine decay `heilbronn n → 0` (all previous
uniform bounds are constant).  Proof: in any witnessing `n`-point configuration,
map each point to its strip index `⌊(x+1)·m/2⌋₊ ∈ {0,…,m}`; as `(m+1)·2 < n`,
some strip holds three distinct points (`Finset` pigeonhole), and those three —
sharing a strip of width `2/m` and lying in the disk (height `≤ 2`) — span a
triangle of area `≤ (2/m)·2 = 4/m` (`triangleArea_le_spread`), bounding the
admissible `α`. -/
theorem heilbronn_le_four_div (n m : ℕ) (hm : 1 ≤ m) (hmn : 2 * (m + 1) < n) :
    heilbronn n ≤ 4 / m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  unfold heilbronn
  apply Real.sSup_le
  · rintro α ⟨P, hcard, hdisk, hbound⟩
    -- Each point maps to its vertical strip index in `{0, …, m}`.
    have hmaps : ∀ pt ∈ P, ⌊(pt.1 + 1) * m / 2⌋₊ ∈ Finset.range (m + 1) := by
      intro pt hpt
      rw [Finset.mem_range]
      have hx : |pt.1| ≤ 1 := unitDisk_abs_fst_le hdisk hpt
      have hxn : -1 ≤ pt.1 := (abs_le.mp hx).1
      have hx1 : pt.1 ≤ 1 := (abs_le.mp hx).2
      have hnn : (0 : ℝ) ≤ (pt.1 + 1) * m / 2 :=
        div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg m)) (by norm_num)
      have h2m : (pt.1 + 1) * (m : ℝ) ≤ 2 * m :=
        mul_le_mul_of_nonneg_right (by linarith) hmR.le
      exact (Nat.floor_lt hnn).mpr (by push_cast; linarith [h2m])
    have hcardgt : (Finset.range (m + 1)).card * 2 < P.card := by
      rw [Finset.card_range, hcard]; omega
    obtain ⟨y, -, hy3⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hcardgt
    -- The fiber (points in one strip) has `> 2` elements: extract three distinct.
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hy3
    simp only [Finset.mem_filter] at ha hb hc
    obtain ⟨haP, hay⟩ := ha
    obtain ⟨hbP, hby⟩ := hb
    obtain ⟨hcP, hcy⟩ := hc
    have hxa : -1 ≤ a.1 := (abs_le.mp (unitDisk_abs_fst_le hdisk haP)).1
    have hxb : -1 ≤ b.1 := (abs_le.mp (unitDisk_abs_fst_le hdisk hbP)).1
    have hxc : -1 ≤ c.1 := (abs_le.mp (unitDisk_abs_fst_le hdisk hcP)).1
    -- `x`-spread within the strip: `|Δx| · m ≤ 2`, i.e. `|Δx| ≤ 2/m`.
    have hwa : |a.1 - c.1| ≤ 2 / m := by
      rw [le_div_iff₀ hmR]; exact strip_spread hxa hxc (by rw [hay, hcy])
    have hwb : |b.1 - c.1| ≤ 2 / m := by
      rw [le_div_iff₀ hmR]; exact strip_spread hxb hxc (by rw [hby, hcy])
    -- `y`-spread across the disk: `|Δy| ≤ 2`.
    have hya : |a.2 - c.2| ≤ 2 := by
      have g1 := abs_le.mp (unitDisk_abs_snd_le hdisk haP)
      have g2 := abs_le.mp (unitDisk_abs_snd_le hdisk hcP)
      rw [abs_le]; constructor <;> linarith [g1.1, g1.2, g2.1, g2.2]
    have hyb : |b.2 - c.2| ≤ 2 := by
      have g1 := abs_le.mp (unitDisk_abs_snd_le hdisk hbP)
      have g2 := abs_le.mp (unitDisk_abs_snd_le hdisk hcP)
      rw [abs_le]; constructor <;> linarith [g1.1, g1.2, g2.1, g2.2]
    have harea : triangleArea a b c ≤ 2 / m * 2 :=
      triangleArea_le_spread a b c hwa hwb hya hyb (by positivity)
    have hα : α ≤ triangleArea a b c := hbound a haP b hbP c hcP hab hbc hac
    have heq : (2 : ℝ) / m * 2 = 4 / m := by ring
    linarith [hα, harea, heq]
  · positivity

/-- **Heilbronn's function tends to `0`.**  A direct consequence of the
pigeonhole decay bound `heilbronn n ≤ 4/m` (`heilbronn_le_four_div`): given
`ε > 0`, pick `m > 4/ε`; then for all `n > 2(m+1)` we have
`0 ≤ heilbronn n ≤ 4/m < ε`.  This is the qualitative content the constant
bounds `heilbronn n ≤ 3/2` cannot supply — Heilbronn's function is a genuinely
null sequence (consistent with the known `α(n) = n^{−β+o(1)}`, `7/6 ≤ β ≤ 2`). -/
theorem heilbronn_tendsto_zero :
    Filter.Tendsto heilbronn Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_gt (4 / ε)
  have hmpos : 0 < m := by
    exact_mod_cast lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ 4 / ε) hm
  refine ⟨2 * (m + 1) + 1, fun n hn => ?_⟩
  have hmn : 2 * (m + 1) < n := by omega
  have hbound := heilbronn_le_four_div n m hmpos hmn
  have hpos := heilbronn_nonneg n (by omega)
  have h4m : 4 / (m : ℝ) < ε := by
    rw [div_lt_iff₀ (show (0 : ℝ) < m by exact_mod_cast hmpos)]
    rw [div_lt_iff₀ hε] at hm
    linarith [hm]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hpos]
  linarith [hbound, h4m]

/-! ## A concrete lower bound at `n = 5`: a rational near-pentagon

The natural five-point witness is the regular pentagon inscribed in the unit
circle, whose minimum triangle area is `(2 sin 72° − sin 36°)/2 ≈ 0.6572`.  Its
coordinates, however, involve the nested radicals of `cos(2π/5)` — every one of
the ten triangle areas would be an expression in `√5` and `√(10 ± 2√5)`, far
outside `norm_num`'s reach (this is exactly why the `n = 5` rung was deferred
when the `n = 4` square was formalized).

Rational points are dense on the unit circle, so we instead perturb each
pentagon vertex to a nearby *Pythagorean-triple* point:

    A = (1, 0)              (angle    0°)
    B = (7/25,  24/25)      (angle  73.7°, near  72°)
    C = (−4/5,  3/5)        (angle 143.1°, near 144°)
    D = (−4/5, −3/5)        (angle 216.9°, near 216°)
    E = (7/25, −24/25)      (angle 286.3°, near 288°)

All five points lie *exactly* on the unit circle (`3² + 4² = 5²`,
`7² + 24² = 25²`), and every one of the ten triangle areas is an exact rational:

    ABC = ADE = BCD = CDE = 81/125,   ABE = 432/625,
    BCE = BDE = 648/625,              ABD = ACD = ACE = 27/25.

The minimum is `81/125 = 0.648` — within `1.5%` of the conjectured optimum
`≈ 0.6572` — and the whole certificate is a kernel-friendly `norm_num`
computation.  This yields the third sandwich of the elementary ladder:
`heilbronn 5 ∈ [81/125, 3/2]`. -/

/-- **`heilbronn 5 ≥ 81/125`.**  The rational near-pentagon
`(1,0), (7/25, 24/25), (−4/5, 3/5), (−4/5, −3/5), (7/25, −24/25)` — five
Pythagorean-triple points lying exactly on the unit circle near the vertices of
the regular pentagon — has minimum triangle area exactly `81/125`, so `81/125`
lies in the defining `sSup` set of `heilbronn 5` (`le_csSup`, using
`heilbronn_defining_bddAbove` for boundedness).  All ten triple areas are
rational (`81/125`, `432/625`, `648/625`, `27/25`), so every ordering of every
distinct triple is discharged by `norm_num` — no radicals appear anywhere,
unlike for the exact regular pentagon. -/
theorem heilbronn_five_ge : (81 / 125 : ℝ) ≤ heilbronn 5 := by
  unfold heilbronn
  refine le_csSup (heilbronn_defining_bddAbove 5 (by norm_num)) ?_
  refine ⟨{((1 : ℝ), (0 : ℝ)), (7 / 25, 24 / 25), (-(4 / 5), 3 / 5),
    (-(4 / 5), -(3 / 5)), (7 / 25, -(24 / 25))}, ?_, ?_, ?_⟩
  · -- the five vertices are distinct, so the configuration has cardinality `5`
    rw [Finset.card_insert_of_notMem (by norm_num [Prod.ext_iff]),
      Finset.card_insert_of_notMem (by norm_num [Prod.ext_iff]),
      Finset.card_insert_of_notMem (by norm_num [Prod.ext_iff]),
      Finset.card_insert_of_notMem (by norm_num [Prod.ext_iff]),
      Finset.card_singleton]
  · -- each vertex lies exactly on the boundary of the closed unit disk
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · -- every ordered distinct triple has area `≥ 81/125`
    intro p hp q hq r hr hpq hqr hpr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq hr
    rcases hp with rfl | rfl | rfl | rfl | rfl <;>
        rcases hq with rfl | rfl | rfl | rfl | rfl <;>
        rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl hpq
        | exact absurd rfl hqr
        | exact absurd rfl hpr
        | (show (81 / 125 : ℝ) ≤ triangleArea _ _ _; unfold triangleArea; norm_num)

/-- **`heilbronn 5` is strictly positive** — immediate from `heilbronn_five_ge`. -/
theorem heilbronn_five_pos : 0 < heilbronn 5 :=
  lt_of_lt_of_le (by norm_num) heilbronn_five_ge

/-- **Sandwich at `n = 5`:** `heilbronn 5 ∈ [81/125, 3/2]`.  Lower bound from the
rational near-pentagon (`heilbronn_five_ge`); upper bound from the Lagrange bound
`heilbronn n ≤ 3/2` (`heilbronn_le_three_halves`).  The lower bound is *not*
claimed sharp — the true five-point optimum is conjecturally the regular
pentagon's `(2 sin 72° − sin 36°)/2 ≈ 0.6572`, and `81/125 = 0.648` sits within
`1.5%` of it. -/
theorem heilbronn_five_mem_Icc : heilbronn 5 ∈ Set.Icc (81 / 125 : ℝ) (3 / 2) :=
  ⟨heilbronn_five_ge, heilbronn_le_three_halves 5 (by norm_num)⟩

end Erdos507WIP01
