/-
  Erdős Problem #1038 — WIP-01: the extremal quadratic x² − 1 realizes the supremum 2√2

  The gallery stub `Erdos1038Problem` sets up the sublevel-set problem — for monic
  real-rooted polynomials with roots in `[-1,1]`, study `|{x : |f(x)| < 1}|` — but
  proves no theorems (the extremal facts are only sketched in prose).  This file
  formalizes the concrete extremal computation noted there:

      the quadratic `x² − 1 = (x−1)(x+1)` is admissible, and its sublevel set
      `{x : |x² − 1| < 1} = (−√2, √2) ∖ {0}` has Lebesgue measure `2√2`,

  the supremum value (Erdős–Herzog–Piranian 1958, confirmed by Tao 2025).  The
  full supremum *bound* over all admissible `f` needs logarithmic potential theory
  beyond Mathlib and is not attempted; this is the matching lower witness.

  * `quadratic_admissible`        — `x² − 1` is monic with both roots in `[-1,1]`.
  * `mem_sublevelSet_quadratic`   — `x ∈ sublevelSet (x²−1) ↔ 0 < x² ∧ x² < 2`.
  * `sublevelSet_quadratic`       — `= Set.Ioo (−√2) √2 ∖ {0}`.
  * `sublevelMeasure_quadratic`   — `= ENNReal.ofReal (2√2)`.
  * `sublevelSup`                 — the supremum of sublevel measures over admissible `f`.
  * `le_sublevelSup`              — `2√2 ≤ sublevelSup` (the provable half of `= 2√2`).

  On the infimum side (the companion quantity, whose exact value
  `2^(4/3) − 1 ≤ inf ≤ 1.835` is open), we compute a second exact witness — the
  linear polynomial `X`, with sublevel set `(−1, 1)` of measure `2` — and record the
  matching machine-checkable bound:

  * `sublevelMeasure_linear`      — `|{x : |x| < 1}| = 2`.
  * `sublevelInf`                 — the infimum of sublevel measures over admissible `f`.
  * `sublevelInf_le_two`          — `sublevelInf ≤ 2` (linear witness; not claimed tight).
  * `sublevelInf_eq_zero`         — `sublevelInf = 0` (exact): the literal predicate only
                                    constrains the roots `f` *has*, so the rootless monic
                                    `X² + 1` is vacuously admissible with an empty sublevel
                                    set.  This sharpens the `≤ 2` bound and pins down the
                                    faithfulness gap — the *intended* infimum `2^(4/3) − 1`
                                    needs the extra hypothesis `f.roots.card = f.natDegree`
                                    (complete splitting over `ℝ`).

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Erdős–Herzog–Piranian (1958); Tao, *Sublevel Sets of Logarithmic
  Potentials* (2025); https://erdosproblems.com/1038.
-/

import Mathlib

open scoped Real ENNReal
open MeasureTheory Polynomial Set

namespace Erdos1038WIP01

/-- A monic polynomial with all roots real and in `[-1,1]` (re-declared to be
    self-contained against the stub). -/
def MonicRealRootedIn01 (f : Polynomial ℝ) : Prop :=
  f.Monic ∧ (∀ r ∈ f.roots, r ∈ Set.Icc (-1 : ℝ) 1)

/-- The sublevel set `{x : |f(x)| < 1}`. -/
def sublevelSet (f : Polynomial ℝ) : Set ℝ := {x | |f.eval x| < 1}

/-- Lebesgue measure of the sublevel set. -/
noncomputable def sublevelMeasure (f : Polynomial ℝ) : ℝ≥0∞ := volume (sublevelSet f)

/-- The extremal quadratic `x² − 1`. -/
noncomputable def q : Polynomial ℝ := X ^ 2 - C 1

@[simp] theorem eval_q (x : ℝ) : q.eval x = x ^ 2 - 1 := by
  simp [q]

/-- **The quadratic `x² − 1` is admissible**: monic with both roots in `[-1,1]`. -/
theorem quadratic_admissible : MonicRealRootedIn01 q := by
  constructor
  · -- monic
    simpa [q] using monic_X_pow_sub_C (1 : ℝ) (n := 2) (by norm_num)
  · -- roots in [-1, 1]
    intro r hr
    rw [Polynomial.mem_roots'] at hr
    have hroot : r ^ 2 - 1 = 0 := by simpa using hr.2
    rw [Set.mem_Icc]
    constructor <;> nlinarith [hroot]

/-- **Membership in the sublevel set of `x² − 1`** in elementary form. -/
theorem mem_sublevelSet_quadratic (x : ℝ) :
    x ∈ sublevelSet q ↔ 0 < x ^ 2 ∧ x ^ 2 < 2 := by
  simp only [sublevelSet, Set.mem_setOf_eq, eval_q, abs_lt]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- **The sublevel set of `x² − 1` is `(−√2, √2) ∖ {0}`.** -/
theorem sublevelSet_quadratic :
    sublevelSet q = Set.Ioo (-Real.sqrt 2) (Real.sqrt 2) \ {0} := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  ext x
  rw [mem_sublevelSet_quadratic, Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h0, h2⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · nlinarith [hs, hspos, sq_nonneg (x + Real.sqrt 2)]
    · nlinarith [hs, hspos, sq_nonneg (x - Real.sqrt 2)]
    · intro hx; rw [hx] at h0; simpa using h0
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨?_, ?_⟩
    · have : x ≠ 0 := h3
      positivity
    · nlinarith [hs, hspos, h1, h2]

/-- **The extremal quadratic realizes the supremum `2√2`.**  The sublevel set
    `(−√2, √2) ∖ {0}` has Lebesgue measure `2√2` (removing the single point `0`
    does not change the measure). -/
theorem sublevelMeasure_quadratic :
    sublevelMeasure q = ENNReal.ofReal (2 * Real.sqrt 2) := by
  unfold sublevelMeasure
  rw [sublevelSet_quadratic, measure_diff_null (by simp), Real.volume_Ioo]
  congr 1
  ring

/-- The **supremum of sublevel-set measures** over all admissible monic polynomials
    (monic, all roots real and in `[-1,1]`).  Erdős–Herzog–Piranian (1958) conjectured
    and Tao (2025) proved this supremum equals `2√2`.  It is introduced here as a Lean
    object so the extremal witness can be tied to it. -/
noncomputable def sublevelSup : ℝ≥0∞ :=
  ⨆ (f : Polynomial ℝ) (_ : MonicRealRootedIn01 f), sublevelMeasure f

/-- **Supremum lower bound: `2√2 ≤ sublevelSup`.**  The admissible quadratic `x² − 1`
    attains sublevel measure `2√2`, so the supremum is at least `2√2`.  This is the
    machine-checkable half of the Erdős–Herzog–Piranian/Tao result `sublevelSup = 2√2`;
    the matching *upper* bound needs logarithmic potential theory beyond Mathlib and is
    not attempted here. -/
theorem le_sublevelSup : ENNReal.ofReal (2 * Real.sqrt 2) ≤ sublevelSup :=
  le_iSup_of_le q (le_iSup_of_le quadratic_admissible sublevelMeasure_quadratic.ge)

/-! ### The infimum side: a second exact witness

The companion extremal quantity is the *infimum* of `sublevelMeasure` over admissible
`f`, whose exact value is open (`2^(4/3) − 1 ≤ inf ≤ 1.835`).  Here we compute a second
polynomial exactly — the linear `X`, whose sublevel set is `(−1, 1)` — and use it to bound
the infimum from above. -/

/-- **The linear polynomial `X` (single root `0`) is admissible**: monic with its one
    root `0 ∈ [-1,1]`. -/
theorem linear_admissible : MonicRealRootedIn01 (X : Polynomial ℝ) := by
  refine ⟨monic_X, ?_⟩
  intro r hr
  rw [Polynomial.mem_roots'] at hr
  have hroot : r = 0 := by simpa using hr.2
  subst hroot
  simp [Set.mem_Icc]

/-- **The sublevel set of `X` is `(−1, 1)`**: `|x| < 1 ↔ x ∈ (−1, 1)`. -/
theorem sublevelSet_linear : sublevelSet (X : Polynomial ℝ) = Set.Ioo (-1 : ℝ) 1 := by
  ext x
  simp only [sublevelSet, Set.mem_setOf_eq, Polynomial.eval_X, abs_lt, Set.mem_Ioo]

/-- **The sublevel set of `X` has Lebesgue measure `2`.** -/
theorem sublevelMeasure_linear :
    sublevelMeasure (X : Polynomial ℝ) = ENNReal.ofReal 2 := by
  unfold sublevelMeasure
  rw [sublevelSet_linear, Real.volume_Ioo]
  congr 1
  ring

/-- The **infimum of sublevel-set measures** over all admissible monic polynomials.  Its
    exact value is open: `2^(4/3) − 1 ≤ sublevelInf ≤ 1.835` (the upper bound and the exact
    value need logarithmic potential theory beyond Mathlib).  Introduced as a Lean object so
    a concrete witness can bound it. -/
noncomputable def sublevelInf : ℝ≥0∞ :=
  ⨅ (f : Polynomial ℝ) (_ : MonicRealRootedIn01 f), sublevelMeasure f

/-- **Infimum upper bound: `sublevelInf ≤ 2`.**  The admissible linear polynomial `X`
    attains sublevel measure `2`, so the infimum is at most `2`.  This is a genuine
    machine-checked upper bound on the (open) infimum; it is *not* claimed tight — the true
    infimum is `≤ 1.835 < 2`, whose witness lies beyond the elementary computations
    available here. -/
theorem sublevelInf_le_two : sublevelInf ≤ ENNReal.ofReal 2 :=
  iInf_le_of_le X (iInf_le_of_le linear_admissible sublevelMeasure_linear.le)

/-! ### The literal predicate is not faithful on the infimum side: `sublevelInf = 0`

`MonicRealRootedIn01 f` only constrains the real roots that `f` actually *has*
(`∀ r ∈ f.roots, r ∈ [-1,1]`); it does **not** force `f` to split over `ℝ`.  A monic
polynomial with no real roots — e.g. `X² + 1`, whose real-root multiset is empty — is
therefore *vacuously* admissible, and its sublevel set `{x : |x² + 1| < 1}` is empty.

Consequently the infimum object degenerates: `sublevelInf = 0`, strictly below the
`≤ 2` linear bound above and far below the *intended* value `2^(4/3) − 1 ≈ 1.52`.  The
intended infimum lives under the **faithful** hypothesis that `f` splits completely with
all roots real in `[-1,1]` (`f.roots.card = f.natDegree`), which `X² + 1` fails.  This
records the gap precisely rather than papering over it. -/

/-- **`X² + 1` is (vacuously) admissible**: it is monic and has no real roots, so the
    root condition holds vacuously. -/
theorem sq_add_one_admissible : MonicRealRootedIn01 (X ^ 2 + C 1 : Polynomial ℝ) := by
  refine ⟨by simpa using monic_X_pow_add_C (1 : ℝ) (two_ne_zero), ?_⟩
  intro r hr
  rw [Polynomial.mem_roots'] at hr
  exfalso
  have hroot : r ^ 2 + 1 = 0 := by simpa using hr.2
  nlinarith [sq_nonneg r]

/-- **The sublevel set of `X² + 1` is empty**: `|x² + 1| ≥ 1` for every real `x`. -/
theorem sublevelSet_sq_add_one : sublevelSet (X ^ 2 + C 1 : Polynomial ℝ) = ∅ := by
  ext x
  simp only [sublevelSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
  have hev : (X ^ 2 + C 1 : Polynomial ℝ).eval x = x ^ 2 + 1 := by simp
  rw [hev, abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg x]

/-- **The sublevel set of `X² + 1` has Lebesgue measure `0`.** -/
theorem sublevelMeasure_sq_add_one :
    sublevelMeasure (X ^ 2 + C 1 : Polynomial ℝ) = 0 := by
  unfold sublevelMeasure
  rw [sublevelSet_sq_add_one, measure_empty]

/-- **The infimum degenerates to `0` under the literal predicate.**  Because the monic
    `X² + 1` has no real roots it is admissible with an empty (measure-`0`) sublevel set,
    so `sublevelInf = 0`.  This sharpens `sublevelInf_le_two` and shows the literal
    predicate is *not* the faithful formalization of "all roots real in `[-1,1]`": the
    intended infimum `2^(4/3) − 1` requires the extra hypothesis `f.roots.card =
    f.natDegree` (complete splitting), which excludes `X² + 1`. -/
theorem sublevelInf_eq_zero : sublevelInf = 0 :=
  le_antisymm
    (iInf_le_of_le (X ^ 2 + C 1)
      (iInf_le_of_le sq_add_one_admissible sublevelMeasure_sq_add_one.le))
    (zero_le _)

/-! ### The faithful predicate: `f` splits completely with all roots in `[-1,1]`

The literal predicate `MonicRealRootedIn01` is unfaithful because it only constrains
the real roots `f` *has*, so a monic with unreal roots (e.g. `X² + 1`) slips through and
collapses the infimum to `0`.  The **faithful** predicate strengthens it with the
splitting condition `f.roots.card = f.natDegree`: `f` has exactly `deg f` real roots
(counted with multiplicity), i.e. `f` splits over `ℝ`.  Both exact witnesses computed
above — the quadratic `X² − 1` and the linear `X` — satisfy it, so the supremum lower
bound `2√2` transfers to the faithful object, while `X² + 1` is now correctly excluded. -/

/-- The **faithful** admissibility predicate: monic, all roots real in `[-1,1]`, **and**
    `f` splits completely over `ℝ` (`f.roots.card = f.natDegree`, so the multiset of real
    roots accounts for the full degree). -/
def MonicRealRootedIn01' (f : Polynomial ℝ) : Prop :=
  MonicRealRootedIn01 f ∧ f.roots.card = f.natDegree

/-- **The roots of `X² − 1` are `{1, −1}`.** -/
theorem q_roots : q.roots = {1, -1} := by
  have hq : q = (X - C 1) * (X - C (-1)) := by simp only [q, C_neg, C_1]; ring
  rw [hq, roots_mul (by rw [← hq]; exact quadratic_admissible.1.ne_zero),
    roots_X_sub_C, roots_X_sub_C]
  rfl

/-- **The quadratic `X² − 1` is faithfully admissible**: it splits over `ℝ` with two
    real roots `±1`, so `roots.card = 2 = natDegree`. -/
theorem quadratic_faithful : MonicRealRootedIn01' q := by
  refine ⟨quadratic_admissible, ?_⟩
  have hnd : q.natDegree = 2 := by simp only [q]; compute_degree!
  rw [q_roots, hnd]
  rfl

/-- **The linear polynomial `X` is faithfully admissible**: its single real root `0`
    accounts for the full degree, `roots.card = 1 = natDegree`. -/
theorem linear_faithful : MonicRealRootedIn01' (X : Polynomial ℝ) := by
  refine ⟨linear_admissible, ?_⟩
  rw [roots_X, natDegree_X]
  rfl

/-- **The faithful predicate excludes `X² + 1`.**  It has no real roots (`roots.card = 0`)
    but `natDegree = 2`, so the splitting condition fails — precisely the polynomial that
    degenerated the literal infimum is ruled out here. -/
theorem sq_add_one_not_faithful :
    ¬ MonicRealRootedIn01' (X ^ 2 + C 1 : Polynomial ℝ) := by
  rintro ⟨_, hcard⟩
  have h0 : (X ^ 2 + C 1 : Polynomial ℝ).roots = 0 := by
    by_contra h
    obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero h
    rw [Polynomial.mem_roots'] at hr
    have : r ^ 2 + 1 = 0 := by simpa using hr.2
    nlinarith [sq_nonneg r]
  have hnd : (X ^ 2 + C 1 : Polynomial ℝ).natDegree = 2 := by compute_degree!
  rw [h0, Multiset.card_zero, hnd] at hcard
  exact absurd hcard (by norm_num)

/-- The **supremum of sublevel measures over faithfully admissible `f`** — the intended
    formalization of the Erdős–Herzog–Piranian/Tao supremum (`= 2√2`). -/
noncomputable def sublevelSup' : ℝ≥0∞ :=
  ⨆ (f : Polynomial ℝ) (_ : MonicRealRootedIn01' f), sublevelMeasure f

/-- **Faithful supremum lower bound: `2√2 ≤ sublevelSup'`.**  The quadratic `X² − 1` is
    faithfully admissible with sublevel measure `2√2`, so the lower witness transfers
    intact to the faithful object.  This is the machine-checkable half of the intended
    `sublevelSup' = 2√2`. -/
theorem le_sublevelSup' : ENNReal.ofReal (2 * Real.sqrt 2) ≤ sublevelSup' :=
  le_iSup_of_le q (le_iSup_of_le quadratic_faithful sublevelMeasure_quadratic.ge)

/-- **The faithful supremum is dominated by the literal one.**  Every faithfully
    admissible `f` is admissible, so restricting the supremum to the smaller set can only
    lower it: `sublevelSup' ≤ sublevelSup`. -/
theorem sublevelSup'_le_sublevelSup : sublevelSup' ≤ sublevelSup := by
  refine iSup_le fun f => iSup_le fun hf => ?_
  exact le_iSup_of_le f (le_iSup_of_le hf.1 le_rfl)

/-- The **infimum of sublevel measures over faithfully admissible `f`** — the intended
    infimum object (`2^(4/3) − 1 ≤ · ≤ 1.835`, exact value open), no longer degenerated
    by `X² + 1`. -/
noncomputable def sublevelInf' : ℝ≥0∞ :=
  ⨅ (f : Polynomial ℝ) (_ : MonicRealRootedIn01' f), sublevelMeasure f

/-- **Faithful infimum upper bound: `sublevelInf' ≤ 2`.**  The linear `X` is faithfully
    admissible with sublevel measure `2`.  Unlike `sublevelInf` (which collapses to `0`
    via the excluded `X² + 1`), this bound is over the intended domain; it is genuine but
    not claimed tight (the true faithful infimum is `≤ 1.835`). -/
theorem sublevelInf'_le_two : sublevelInf' ≤ ENNReal.ofReal 2 :=
  iInf_le_of_le X (iInf_le_of_le linear_faithful sublevelMeasure_linear.le)

/-- **The literal infimum lies below the faithful one.**  Restricting the infimum to the
    smaller faithful set can only raise it: `sublevelInf ≤ sublevelInf'`.  Combined with
    `sublevelInf_eq_zero` this says `0 = sublevelInf ≤ sublevelInf'` — the faithful
    predicate removes the spurious `0`. -/
theorem sublevelInf_le_sublevelInf' : sublevelInf ≤ sublevelInf' := by
  refine le_iInf fun f => le_iInf fun hf => ?_
  exact iInf_le_of_le f (iInf_le_of_le hf.1 le_rfl)

end Erdos1038WIP01
