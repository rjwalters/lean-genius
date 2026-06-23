import Mathlib

/-
# The Oscillation of Thomae's Function

## Open Question (lebesgue-measure-oq-01-oq-01-oq-01-oq-02)
Quantify the discontinuity of Thomae's function via the **oscillation function**.
Prove that the oscillation of Thomae's function at a rational `p/q` (in lowest
terms) is exactly `1/q`, that it vanishes at every irrational, and that the level
set `{x | oscillation thomae x ≥ ε}` is finite in every bounded interval — the
finer, oscillation-theoretic form of Lebesgue's criterion.

## Answer: YES — `oscillation thomae (p/q) = 1/q`
Working with Mathlib's `oscillation f x = ⨅ S ∈ (𝓝 x).map f, EMetric.diam S`
(`Mathlib.Analysis.Oscillation`), we prove, for `r : ℚ` with reduced denominator
`d = r.den`:

  `oscillation thomae r = ENNReal.ofReal (1 / d)`.

The two inequalities use complementary facts about Thomae's function:

* **Upper bound** `≤ 1/d`.  A single key lemma (`exists_nbhd_thomae_le`) shows
  that for any threshold `v > 0` with `thomae a ≤ v`, some ball around `a`
  keeps `thomae ≤ v`: the points where `thomae > v` are rationals of denominator
  `< 1/v`, finitely many near `a`, and none equal to `a`. Taking `v = 1/d`
  bounds the image of a small ball inside `[0, 1/d]`, so its diameter — hence the
  oscillation — is `≤ 1/d`.
* **Lower bound** `≥ 1/d`.  Every neighborhood of `a = r` contains `a` itself
  (where `thomae = 1/d`) and, since the irrationals are dense
  (`dense_irrational`), an irrational point (where `thomae = 0`). So every set in
  the mapped neighborhood filter has diameter `≥ 1/d`.

At an irrational `x` the same key lemma gives `thomae ≤ ε` on a small ball for
*every* `ε > 0`, so the oscillation is `0` — recovering continuity at the
irrationals (`Oscillation.eq_zero_iff_continuousAt`).

Finally `{x ∈ [a,b] | ofReal ε ≤ oscillation thomae x}` is finite: every such `x`
is rational with `1/x.den ≥ ε`, i.e. `x.den ≤ 1/ε`, and rationals of bounded
denominator in a bounded interval form a finite set. This is the oscillation form
of Lebesgue's criterion: the discontinuity set is a countable union of finite
level sets, hence null.

## Self-containment
The Thomae infrastructure (definition, value at rationals/irrationals, finiteness
of bounded-denominator rationals) is reproved here so the file builds against the
current Mathlib independently of the sibling entries.
-/

namespace LebesgueMeasureOQ01OQ01OQ01OQ02

open MeasureTheory Topology

open Classical in
/-- Thomae's function (popcorn function): `1/q.den` if `x` is rational, `0` if
irrational. -/
noncomputable def thomae : ℝ → ℝ := fun x =>
  if h : ∃ q : ℚ, (q : ℝ) = x then 1 / (h.choose.den : ℝ) else 0

/-- `thomae = 0` at irrationals. -/
theorem thomae_irrational {x : ℝ} (hx : Irrational x) : thomae x = 0 := by
  have hne : ¬ ∃ q : ℚ, (q : ℝ) = x := by
    rintro ⟨q, rfl⟩; exact hx ⟨q, rfl⟩
  simp only [thomae, dif_neg hne]

/-- `thomae` at a rational `q` equals `1/q.den`. -/
theorem thomae_rat (q : ℚ) : thomae (q : ℝ) = 1 / (q.den : ℝ) := by
  have hq : ∃ r : ℚ, (r : ℝ) = (q : ℝ) := ⟨q, rfl⟩
  have heq : hq.choose = q := Rat.cast_inj.mp hq.choose_spec
  simp only [thomae, dif_pos hq, heq]

/-- Thomae's function is non-negative. -/
theorem thomae_nonneg (x : ℝ) : 0 ≤ thomae x := by
  simp only [thomae]
  split <;> positivity

-- ============================================================
-- PART 0: Finiteness of bounded-denominator rationals
-- ============================================================

/-- `q.num = q * q.den` over `ℝ`. -/
private lemma rat_num_eq_mul_den (q : ℚ) : (q.num : ℝ) = (q : ℝ) * q.den := by
  have hd : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.pos.ne'
  have hq_eq : (q.num : ℚ) = q * q.den := (div_eq_iff hd).mp (Rat.num_div_den q)
  exact_mod_cast hq_eq

/-- Rationals with bounded denominator in `[x-1, x+1]` form a finite set. -/
private lemma finite_rat_bounded (x : ℝ) (N : ℕ) :
    Set.Finite {q : ℚ | |(q : ℝ) - x| ≤ 1 ∧ q.den ≤ N} := by
  apply Set.Finite.subset (Finset.finite_toSet
    ((Finset.range (N + 1)).biUnion fun d =>
      (Finset.Icc ⌊(x - 1) * (d : ℝ)⌋ ⌈(x + 1) * (d : ℝ)⌉).image
        fun n : ℤ => (n : ℚ) / (d : ℚ)))
  intro q hq
  obtain ⟨habs, hden⟩ := hq
  rw [Finset.mem_coe]
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_Icc]
  have habs' := abs_le.mp habs
  have hq_lower : x - 1 ≤ (q : ℝ) := by linarith [habs'.1]
  have hq_upper : (q : ℝ) ≤ x + 1 := by linarith [habs'.2]
  have hden_pos : (0 : ℝ) < (q.den : ℝ) := Nat.cast_pos.mpr q.pos
  have hq_num := rat_num_eq_mul_den q
  refine ⟨q.den, Nat.lt_succ_of_le hden, q.num, ⟨?_, ?_⟩, ?_⟩
  · have hle : (x - 1) * (q.den : ℝ) ≤ (q.num : ℝ) := by
      rw [hq_num]; nlinarith [hq_lower, hden_pos]
    have := (Int.floor_le ((x - 1) * (q.den : ℝ))).trans hle
    exact_mod_cast this
  · have hge : (q.num : ℝ) ≤ (x + 1) * (q.den : ℝ) := by
      rw [hq_num]; nlinarith [hq_upper, hden_pos]
    have := hge.trans (Int.le_ceil ((x + 1) * (q.den : ℝ)))
    exact_mod_cast this
  · exact Rat.num_div_den q

/-- From a point `x` and a finite set `S` of rationals none of which casts to `x`,
there is a positive minimum distance from `x` to the set. -/
private lemma pos_min_dist {x : ℝ} (S : Finset ℚ) (hS : ∀ q ∈ S, (q : ℝ) ≠ x) :
    ∃ δ > 0, ∀ q ∈ S, δ ≤ |x - (q : ℝ)| := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert a s _ ih =>
    have hS' : ∀ q ∈ s, (q : ℝ) ≠ x := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    obtain ⟨δ₀, hδ₀, hq₀⟩ := ih hS'
    have ha : (a : ℝ) ≠ x := hS a (Finset.mem_insert_self a s)
    refine ⟨min δ₀ |x - (a : ℝ)|, lt_min hδ₀ ?_, fun q hq' => ?_⟩
    · rw [abs_pos, sub_ne_zero]; exact fun h => ha h.symm
    · rcases Finset.mem_insert.mp hq' with rfl | hq''
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hq₀ q hq'')

-- ============================================================
-- PART 1: A uniform local bound for Thomae's function
-- ============================================================

/-- **Key lemma.** If `thomae a ≤ v` with `v > 0`, then `thomae ≤ v` on a whole
ball around `a`. The exceptional points (where `thomae > v`) are rationals of
denominator `< 1/v` — finitely many near `a`, and none equal to `a`. -/
theorem exists_nbhd_thomae_le (a : ℝ) (v : ℝ) (hv : 0 < v) (hav : thomae a ≤ v) :
    ∃ δ > 0, ∀ y ∈ Metric.ball a δ, thomae y ≤ v := by
  -- Choose `N` with `1/v ≤ N`, so `thomae q > v → q.den ≤ N`.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 : ℝ) / v ≤ N := ⟨⌈(1 : ℝ) / v⌉₊, Nat.le_ceil _⟩
  -- The exceptional rationals near `a`.
  set T : Set ℚ := {q : ℚ | |(q : ℝ) - a| ≤ 1 ∧ v < 1 / (q.den : ℝ)} with hTdef
  have hTfin : T.Finite := by
    apply Set.Finite.subset (finite_rat_bounded a N)
    intro q hq
    obtain ⟨habs, hvq⟩ := hq
    refine ⟨habs, ?_⟩
    -- `v < 1/q.den → q.den < 1/v ≤ N`
    have hden_pos : (0 : ℝ) < (q.den : ℝ) := Nat.cast_pos.mpr q.pos
    have hlt : (q.den : ℝ) < 1 / v := by
      rw [lt_div_iff₀ hv]
      have h1 : v * (q.den : ℝ) < 1 := (lt_div_iff₀ hden_pos).mp hvq
      linarith [h1, mul_comm v (q.den : ℝ)]
    have : (q.den : ℝ) < (N : ℝ) := lt_of_lt_of_le hlt hN
    exact_mod_cast this.le
  -- None of the exceptional rationals casts to `a`.
  have hne : ∀ q ∈ hTfin.toFinset, (q : ℝ) ≠ a := by
    intro q hq hcast
    rw [Set.Finite.mem_toFinset] at hq
    have hvq : v < 1 / (q.den : ℝ) := hq.2
    rw [← thomae_rat q, hcast] at hvq
    exact absurd (hav.trans_lt hvq) (lt_irrefl _)
  obtain ⟨δ, hδ, hdist⟩ := pos_min_dist hTfin.toFinset hne
  refine ⟨min δ 1, lt_min hδ one_pos, fun y hy => ?_⟩
  rw [Metric.mem_ball, Real.dist_eq] at hy
  have hy1 : |y - a| < 1 := lt_of_lt_of_le hy (min_le_right _ _)
  have hyδ : |y - a| < δ := lt_of_lt_of_le hy (min_le_left _ _)
  by_cases hirr : Irrational y
  · rw [thomae_irrational hirr]; exact hv.le
  · simp only [Irrational, not_not] at hirr
    obtain ⟨q, hq⟩ := hirr
    rw [← hq, thomae_rat]
    by_contra hcon
    push_neg at hcon
    -- `v < 1/q.den` so `q ∈ T`, contradicting the minimum distance.
    have hmem : q ∈ hTfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      refine ⟨?_, hcon⟩
      rw [hq]; exact hy1.le
    have := hdist q hmem
    rw [← hq] at hyδ
    rw [abs_sub_comm] at this
    linarith

-- ============================================================
-- PART 2: The oscillation of Thomae's function
-- ============================================================

/-- The image of a `thomae`-ball of bounded values has small diameter:
if `thomae ≤ v` on `Metric.ball a δ` then the EMetric diameter of the image is
`≤ ofReal v`. -/
private lemma diam_image_le {a v δ : ℝ} (_hv : 0 ≤ v)
    (hδ : ∀ y ∈ Metric.ball a δ, thomae y ≤ v) :
    EMetric.diam (thomae '' Metric.ball a δ) ≤ ENNReal.ofReal v := by
  apply EMetric.diam_le
  rintro u ⟨x, hx, rfl⟩ w ⟨y, hy, rfl⟩
  rw [edist_dist, Real.dist_eq]
  apply ENNReal.ofReal_le_ofReal
  rw [abs_le]
  constructor
  · linarith [thomae_nonneg x, hδ y hy]
  · linarith [hδ x hx, thomae_nonneg y]

/-- **The oscillation of Thomae's function at a rational `r` is exactly `1/r.den`.**
This is the sharp, quantitative form of the discontinuity of Thomae's function. -/
theorem oscillation_thomae_rat (r : ℚ) :
    oscillation thomae (r : ℝ) = ENNReal.ofReal (1 / (r.den : ℝ)) := by
  have hdpos : (0 : ℝ) < (r.den : ℝ) := Nat.cast_pos.mpr r.pos
  have hvpos : (0 : ℝ) < 1 / (r.den : ℝ) := by positivity
  refine le_antisymm ?_ ?_
  · -- Upper bound: a small ball keeps `thomae ≤ 1/r.den`.
    obtain ⟨δ, hδ, hball⟩ :=
      exists_nbhd_thomae_le (r : ℝ) (1 / (r.den : ℝ)) hvpos (le_of_eq (thomae_rat r))
    have hmem : thomae '' Metric.ball (r : ℝ) δ ∈ (𝓝 (r : ℝ)).map thomae :=
      Filter.image_mem_map (Metric.ball_mem_nhds _ hδ)
    calc oscillation thomae (r : ℝ)
        ≤ EMetric.diam (thomae '' Metric.ball (r : ℝ) δ) := biInf_le _ hmem
      _ ≤ ENNReal.ofReal (1 / (r.den : ℝ)) := diam_image_le hvpos.le hball
  · -- Lower bound: every neighborhood meets `r` (value `1/r.den`) and an
    -- irrational (value `0`), so every set in the mapped filter has diameter
    -- `≥ 1/r.den`.
    rw [oscillation]
    refine le_iInf₂ fun S hS => ?_
    rw [Filter.mem_map, mem_nhds_iff] at hS
    obtain ⟨U, hUsub, hUopen, haU⟩ := hS
    obtain ⟨y, hyirr, hyU⟩ := dense_irrational.exists_mem_open hUopen ⟨(r : ℝ), haU⟩
    have haS : thomae (r : ℝ) ∈ S := hUsub haU
    have hyS : thomae y ∈ S := hUsub hyU
    calc ENNReal.ofReal (1 / (r.den : ℝ))
        = edist (thomae (r : ℝ)) (thomae y) := by
          rw [thomae_rat r, thomae_irrational hyirr, edist_dist, Real.dist_eq,
            sub_zero, abs_of_nonneg hvpos.le]
      _ ≤ EMetric.diam S := EMetric.edist_le_diam_of_mem haS hyS

/-- **The oscillation of Thomae's function vanishes at every irrational.**
Equivalently, Thomae's function is continuous at the irrationals. -/
theorem oscillation_thomae_irrational {x : ℝ} (hx : Irrational x) :
    oscillation thomae x = 0 := by
  refine le_antisymm ?_ (zero_le _)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  rw [zero_add]
  obtain ⟨δ, hδ, hball⟩ :=
    exists_nbhd_thomae_le x (ε : ℝ) (by exact_mod_cast hε) (by rw [thomae_irrational hx]; positivity)
  have hmem : thomae '' Metric.ball x δ ∈ (𝓝 x).map thomae :=
    Filter.image_mem_map (Metric.ball_mem_nhds _ hδ)
  calc oscillation thomae x
      ≤ EMetric.diam (thomae '' Metric.ball x δ) := biInf_le _ hmem
    _ ≤ ENNReal.ofReal (ε : ℝ) := diam_image_le (by positivity) hball
    _ = (ε : ENNReal) := ENNReal.ofReal_coe_nnreal

/-- Thomae's function is continuous at every irrational (oscillation form). -/
theorem thomae_continuousAt_irrational {x : ℝ} (hx : Irrational x) :
    ContinuousAt thomae x :=
  (Oscillation.eq_zero_iff_continuousAt thomae x).mp (oscillation_thomae_irrational hx)

-- ============================================================
-- PART 3: Finiteness of the oscillation level sets
-- ============================================================

/-- Rationals of bounded denominator in a bounded interval form a finite set. -/
private lemma finite_rat_Icc (a b : ℝ) (N : ℕ) :
    Set.Finite {q : ℚ | a ≤ (q : ℝ) ∧ (q : ℝ) ≤ b ∧ q.den ≤ N} := by
  apply Set.Finite.subset (Finset.finite_toSet
    ((Finset.range (N + 1)).biUnion fun d =>
      (Finset.Icc ⌊a * (d : ℝ)⌋ ⌈b * (d : ℝ)⌉).image
        fun n : ℤ => (n : ℚ) / (d : ℚ)))
  intro q hq
  obtain ⟨hqa, hqb, hden⟩ := hq
  rw [Finset.mem_coe]
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_Icc]
  have hden_pos : (0 : ℝ) < (q.den : ℝ) := Nat.cast_pos.mpr q.pos
  have hq_num := rat_num_eq_mul_den q
  refine ⟨q.den, Nat.lt_succ_of_le hden, q.num, ⟨?_, ?_⟩, ?_⟩
  · have hle : a * (q.den : ℝ) ≤ (q.num : ℝ) := by
      rw [hq_num]; nlinarith [hqa, hden_pos]
    have := (Int.floor_le (a * (q.den : ℝ))).trans hle
    exact_mod_cast this
  · have hge : (q.num : ℝ) ≤ b * (q.den : ℝ) := by
      rw [hq_num]; nlinarith [hqb, hden_pos]
    have := hge.trans (Int.le_ceil (b * (q.den : ℝ)))
    exact_mod_cast this
  · exact Rat.num_div_den q

/-- **The oscillation level sets are finite (oscillation form of Lebesgue's
criterion).** For `ε > 0`, only finitely many points of any bounded interval
`[a,b]` have oscillation `≥ ε`. Hence the discontinuity set is a countable union
of finite sets, so null. -/
theorem oscillation_levelSet_finite (ε : ℝ) (hε : 0 < ε) (a b : ℝ) :
    Set.Finite {x : ℝ | a ≤ x ∧ x ≤ b ∧ ENNReal.ofReal ε ≤ oscillation thomae x} := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 : ℝ) / ε ≤ N := ⟨⌈(1 : ℝ) / ε⌉₊, Nat.le_ceil _⟩
  -- Every such `x` is a rational with denominator `≤ N`.
  apply Set.Finite.subset
    ((finite_rat_Icc a b N).image ((↑) : ℚ → ℝ))
  intro x hx
  obtain ⟨hxa, hxb, hosc⟩ := hx
  -- `x` cannot be irrational: there the oscillation is `0 < ε`.
  by_cases hirr : Irrational x
  · rw [oscillation_thomae_irrational hirr] at hosc
    exact absurd (lt_of_lt_of_le (by positivity) hosc) (lt_irrefl _)
  · simp only [Irrational, not_not] at hirr
    obtain ⟨q, hq⟩ := hirr
    refine ⟨q, ⟨?_, ?_, ?_⟩, hq⟩
    · rw [hq]; exact hxa
    · rw [hq]; exact hxb
    · -- `ofReal ε ≤ oscillation = ofReal (1/q.den)` forces `q.den ≤ N`.
      rw [← hq, oscillation_thomae_rat q] at hosc
      have hdpos : (0 : ℝ) < (q.den : ℝ) := Nat.cast_pos.mpr q.pos
      have hle : ε ≤ 1 / (q.den : ℝ) :=
        (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hosc
      have hlt : (q.den : ℝ) ≤ 1 / ε := by
        rw [le_div_iff₀ hε]
        have h1 : ε * (q.den : ℝ) ≤ 1 := (le_div_iff₀ hdpos).mp hle
        linarith [h1, mul_comm ε (q.den : ℝ)]
      have : (q.den : ℝ) ≤ (N : ℝ) := hlt.trans hN
      exact_mod_cast this

end LebesgueMeasureOQ01OQ01OQ01OQ02
