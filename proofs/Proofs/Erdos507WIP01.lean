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
  separating `heilbronn 3` from the junk value `heilbronn 2 = 0`.

All results are `0`-axiom / `0`-sorry.

Reference: <https://erdosproblems.com/507>
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
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

end Erdos507WIP01
