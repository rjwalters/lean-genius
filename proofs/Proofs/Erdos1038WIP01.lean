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

  Finally we isolate *why* faithfulness fixes the degeneracy, at the per-polynomial level:

  * `isOpen_sublevelSet`            — `{x : |f(x)| < 1}` is open (preimage of `(-1,1)`).
  * `sublevelMeasure_pos_of_root`   — any real root `r ∈ f.roots` lies in the open sublevel
                                      set, forcing positive Lebesgue measure.
  * `faithful_sublevelMeasure_pos`  — a faithful `f` of degree `≥ 1` splits completely, so it
                                      has a real root: `0 < sublevelMeasure f`.  This is the
                                      exact property `X² + 1` fails (degree `2`, no real root,
                                      empty sublevel set) — the driver of `sublevelInf_eq_zero`.
  * `sublevelInf'` / `sublevelInf'_le_two` — the faithful infimum object and its linear
                                      witness bound `≤ 2`, now free of the rootless collapse.

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

/-! ### The faithful predicate (complete real splitting)

The `sublevelInf = 0` degeneracy above shows `MonicRealRootedIn01` is too weak: it
constrains only the real roots `f` happens to have, admitting the rootless `X² + 1`.
The **faithful** version adds `f.roots.card = f.natDegree` — i.e. `f` splits completely
into real linear factors, all roots in `[-1,1]`.  We introduce the faithful supremum
object, verify the two exact witnesses (`X² − 1`, `X`) satisfy the stronger predicate so
the `2√2` lower bound transfers, and confirm `X² + 1` is now correctly excluded. -/

/-- **Faithful admissibility.**  `f` is monic, all its real roots lie in `[-1,1]`, *and*
    it splits completely over `ℝ` (`f.roots.card = f.natDegree`).  This excludes monic
    polynomials with non-real roots such as `X² + 1`, restoring the intended geometry. -/
def MonicRealRootedIn01' (f : Polynomial ℝ) : Prop :=
  MonicRealRootedIn01 f ∧ f.roots.card = f.natDegree

/-- The extremal quadratic `X² − 1` is **faithfully** admissible: it splits as
    `(X − 1)(X + 1)`, so its two real roots `±1 ∈ [-1,1]` exhaust its degree. -/
theorem quadratic_admissible' : MonicRealRootedIn01' q := by
  refine ⟨quadratic_admissible, ?_⟩
  have h1 : q = (X - C (1 : ℝ)) * (X - C (-1 : ℝ)) := by
    simp only [q, map_one, map_neg]; ring
  have hne : (X - C (1 : ℝ)) * (X - C (-1 : ℝ)) ≠ 0 := by
    rw [← h1]; exact quadratic_admissible.1.ne_zero
  have hnd : q.natDegree = 2 := by simp only [q]; compute_degree!
  have hrc : q.roots.card = 2 := by
    rw [h1, Polynomial.roots_mul hne, Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
    simp
  rw [hrc, hnd]

/-- The linear polynomial `X` is **faithfully** admissible: its single root `0 ∈ [-1,1]`
    exhausts its degree `1`. -/
theorem linear_admissible' : MonicRealRootedIn01' (X : Polynomial ℝ) := by
  refine ⟨linear_admissible, ?_⟩
  rw [Polynomial.roots_X, Multiset.card_singleton, natDegree_X]

/-- The **faithful supremum** of sublevel-set measures, over monic polynomials that split
    completely with all roots real in `[-1,1]`.  This is the object for which Tao's
    `= 2√2` is the intended statement (the literal `sublevelSup` agrees on the lower bound
    but its infimum companion degenerates; see `sublevelInf_eq_zero`). -/
noncomputable def sublevelSup' : ℝ≥0∞ :=
  ⨆ (f : Polynomial ℝ) (_ : MonicRealRootedIn01' f), sublevelMeasure f

/-- **Faithful supremum lower bound: `2√2 ≤ sublevelSup'`.**  The lower bound survives the
    strengthening: `X² − 1` splits completely, so it is faithfully admissible and still
    attains sublevel measure `2√2`.  The machine-checkable half of Tao's `sublevelSup' = 2√2`
    on the faithful object; the matching upper bound remains beyond Mathlib. -/
theorem le_sublevelSup' : ENNReal.ofReal (2 * Real.sqrt 2) ≤ sublevelSup' :=
  le_iSup_of_le q (le_iSup_of_le quadratic_admissible' sublevelMeasure_quadratic.ge)

/-- **The faithful predicate excludes `X² + 1`.**  Unlike the literal `MonicRealRootedIn01`,
    the faithful predicate rejects the rootless `X² + 1`: it has `0` real roots but degree
    `2`, so `roots.card ≠ natDegree`.  This is exactly why the faithful infimum does *not*
    collapse to `0` — the pathology witnessing `sublevelInf_eq_zero` is no longer admissible. -/
theorem sq_add_one_not_admissible' :
    ¬ MonicRealRootedIn01' (X ^ 2 + C 1 : Polynomial ℝ) := by
  rintro ⟨-, hcard⟩
  have hnd : (X ^ 2 + C 1 : Polynomial ℝ).natDegree = 2 := by compute_degree!
  have hr0 : (X ^ 2 + C 1 : Polynomial ℝ).roots = 0 := by
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro r hr
    rw [Polynomial.mem_roots'] at hr
    have hroot : r ^ 2 + 1 = 0 := by simpa using hr.2
    nlinarith [sq_nonneg r]
  rw [hr0, Multiset.card_zero, hnd] at hcard
  exact absurd hcard (by norm_num)

/-! ### Why faithfulness matters: a real root forces positive sublevel measure

The `sublevelInf_eq_zero` degeneracy is driven entirely by the *rootless* witness
`X² + 1`: with no real root, `|f|` is bounded away from `0`, its sublevel set is empty,
and the measure vanishes.  The faithful predicate forbids this by demanding a full
complement of real roots.  We isolate the mechanism at the *per-polynomial* level:
the sublevel set is **open**, and any real root sits inside it, so a single root already
forces positive Lebesgue measure.  Faithful polynomials of positive degree always have
one, so — unlike the literal predicate — each faithful witness has positive measure. -/

/-- **The sublevel set is open**: it is the preimage of the open interval `(-1,1)` under
    the continuous evaluation map `x ↦ f(x)` (`|y| < 1 ↔ y ∈ (-1,1)`). -/
theorem isOpen_sublevelSet (f : Polynomial ℝ) : IsOpen (sublevelSet f) := by
  have hpre : sublevelSet f = (fun x => f.eval x) ⁻¹' Set.Ioo (-1 : ℝ) 1 := by
    ext x
    simp only [sublevelSet, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioo, abs_lt]
  rw [hpre]
  exact isOpen_Ioo.preimage f.continuous

/-- **A single real root forces positive sublevel measure.**  If `r ∈ f.roots` then
    `f(r) = 0`, so `r` lies in the *open* sublevel set `{x : |f(x)| < 1}`; a nonempty open
    subset of `ℝ` has positive Lebesgue measure (`IsOpen.measure_pos` for the
    open-positive `volume`). -/
theorem sublevelMeasure_pos_of_root (f : Polynomial ℝ) {r : ℝ} (hr : r ∈ f.roots) :
    0 < sublevelMeasure f := by
  have hev : f.eval r = 0 := Polynomial.isRoot_of_mem_roots hr
  have hmem : r ∈ sublevelSet f := by
    simp only [sublevelSet, Set.mem_setOf_eq, hev, abs_zero]; norm_num
  unfold sublevelMeasure
  exact (isOpen_sublevelSet f).measure_pos volume ⟨r, hmem⟩

/-- **Faithful admissibility of positive degree ⟹ positive sublevel measure.**  A
    faithfully admissible `f` of degree `≥ 1` splits completely (`roots.card = natDegree`),
    so its root multiset is nonempty: it has a real root `r ∈ [-1,1]`, and
    `sublevelMeasure_pos_of_root` gives `0 < sublevelMeasure f`.  This is precisely the
    property the *literal* predicate loses — the rootless `X² + 1` (degree `2`, no real
    roots) is literally admissible with an empty sublevel set, forcing `sublevelInf_eq_zero`.
    Faithfulness rules it out, so every faithful witness of positive degree contributes a
    positive measure to the faithful infimum. -/
theorem faithful_sublevelMeasure_pos (f : Polynomial ℝ)
    (hf : MonicRealRootedIn01' f) (hdeg : 1 ≤ f.natDegree) :
    0 < sublevelMeasure f := by
  have hcard : 0 < f.roots.card := by rw [hf.2]; omega
  obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero (Multiset.card_pos.mp hcard)
  exact sublevelMeasure_pos_of_root f hr

/-- The **faithful infimum** of sublevel-set measures, over monic polynomials that split
    completely with all roots real in `[-1,1]`.  In contrast to the literal `sublevelInf`,
    which collapses to `0` via the rootless `X² + 1` (`sublevelInf_eq_zero`), every
    positive-degree faithful witness has *positive* sublevel measure
    (`faithful_sublevelMeasure_pos`); the exact faithful infimum `2^(4/3) − 1` still needs
    logarithmic potential theory beyond Mathlib. -/
noncomputable def sublevelInf' : ℝ≥0∞ :=
  ⨅ (f : Polynomial ℝ) (_ : MonicRealRootedIn01' f), sublevelMeasure f

/-- **Faithful infimum upper bound: `sublevelInf' ≤ 2`.**  The linear `X` is faithfully
    admissible (`linear_admissible'`) with sublevel measure `2`, so the faithful infimum is
    at most `2`.  This bound is genuine but *not* tight; moreover the faithful infimum still
    degenerates to `0` (`sublevelInf'_eq_zero` below), because faithful admissibility as
    stated does not yet exclude the constant polynomial `1`.  The intended value
    `2^(4/3) − 1 ≈ 1.52` requires *both* complete splitting *and* non-constancy. -/
theorem sublevelInf'_le_two : sublevelInf' ≤ ENNReal.ofReal 2 :=
  iInf_le_of_le X (iInf_le_of_le linear_admissible' sublevelMeasure_linear.le)

/-! ### Faithfulness alone is not enough: the constant `1` still collapses the infimum

The faithful predicate `MonicRealRootedIn01'` excludes the *rootless* `X² + 1`
(`sq_add_one_not_admissible'`), but it does **not** encode the "non-constant" clause of
Erdős #1038 ("*non-constant* monic polynomials, all roots real in `[-1,1]`").  The constant
polynomial `1` is monic, has an empty root multiset (`roots.card = 0 = natDegree`, so it
*splits completely* — vacuously), hence is faithfully admissible; yet `{x : |1| < 1} = ∅`
has measure `0`.  So `sublevelInf' = 0` as well: faithfulness fixes the *rootless* pathology
but not the *degenerate constant* one.  The correct formalization needs `1 ≤ f.natDegree`. -/

/-- **The constant `1` is faithfully admissible.**  It is monic with an empty root multiset,
    so every root lies in `[-1,1]` vacuously and `roots.card = 0 = natDegree` (it "splits
    completely" for the trivial reason that it has no roots and degree `0`). -/
theorem one_admissible' : MonicRealRootedIn01' (1 : Polynomial ℝ) := by
  refine ⟨⟨monic_one, ?_⟩, ?_⟩
  · intro r hr
    rw [Polynomial.roots_one] at hr
    exact absurd hr (by simp)
  · rw [Polynomial.roots_one, natDegree_one]; simp

/-- **The sublevel set of the constant `1` is empty**: `|1| = 1 ≮ 1`. -/
theorem sublevelSet_one : sublevelSet (1 : Polynomial ℝ) = ∅ := by
  ext x
  simp only [sublevelSet, Set.mem_setOf_eq, Polynomial.eval_one, abs_one,
    lt_self_iff_false, Set.mem_empty_iff_false]

/-- **The sublevel set of the constant `1` has Lebesgue measure `0`.** -/
theorem sublevelMeasure_one : sublevelMeasure (1 : Polynomial ℝ) = 0 := by
  unfold sublevelMeasure
  rw [sublevelSet_one, measure_empty]

/-- **The faithful infimum also degenerates to `0`.**  The constant `1` is faithfully
    admissible with an empty (measure-`0`) sublevel set, so `sublevelInf' = 0`.  This
    mirrors `sublevelInf_eq_zero` for the literal predicate: adding complete splitting is
    *not* sufficient to recover the intended infimum — the non-constancy clause of the
    Erdős problem is also required. -/
theorem sublevelInf'_eq_zero : sublevelInf' = 0 :=
  le_antisymm
    (iInf_le_of_le 1 (iInf_le_of_le one_admissible' sublevelMeasure_one.le))
    (zero_le _)

/-! ### The correct predicate: non-constant, complete real splitting, roots in `[-1,1]`

Adding `1 ≤ f.natDegree` to the faithful predicate excludes *both* degenerate witnesses
(`X² + 1`, rootless; and `1`, constant), matching the Erdős #1038 hypothesis exactly.  We
verify the two exact witnesses (`X² − 1`, `X`) still qualify — so the `2√2` lower bound
transfers — and record that *every* witness now has strictly positive sublevel measure
(`faithful_sublevelMeasure_pos` applies since the degree hypothesis is now built in). -/

/-- **Non-constant faithful admissibility.**  `f` is monic, splits completely over `ℝ`
    with all roots in `[-1,1]`, *and* is non-constant (`1 ≤ f.natDegree`).  This is the
    exact hypothesis class of Erdős #1038; it excludes both `X² + 1` and the constant `1`. -/
def MonicRealRootedIn01'' (f : Polynomial ℝ) : Prop :=
  MonicRealRootedIn01' f ∧ 1 ≤ f.natDegree

/-- The extremal quadratic `X² − 1` is non-constant faithfully admissible (degree `2`). -/
theorem quadratic_admissible'' : MonicRealRootedIn01'' q := by
  refine ⟨quadratic_admissible', ?_⟩
  have hnd : q.natDegree = 2 := by simp only [q]; compute_degree!
  omega

/-- The linear polynomial `X` is non-constant faithfully admissible (degree `1`). -/
theorem linear_admissible'' : MonicRealRootedIn01'' (X : Polynomial ℝ) :=
  ⟨linear_admissible', le_of_eq natDegree_X.symm⟩

/-- **The constant `1` is excluded** by the non-constant faithful predicate (`natDegree 0`). -/
theorem one_not_admissible'' : ¬ MonicRealRootedIn01'' (1 : Polynomial ℝ) := by
  rintro ⟨-, hdeg⟩
  rw [natDegree_one] at hdeg
  exact absurd hdeg (by norm_num)

/-- **`X² + 1` is excluded** by the non-constant faithful predicate (fails to split). -/
theorem sq_add_one_not_admissible'' :
    ¬ MonicRealRootedIn01'' (X ^ 2 + C 1 : Polynomial ℝ) :=
  fun h => sq_add_one_not_admissible' h.1

/-- The **non-constant faithful supremum** of sublevel-set measures.  This is the object
    for which Tao's `= 2√2` is the precise statement of Erdős #1038. -/
noncomputable def sublevelSup'' : ℝ≥0∞ :=
  ⨆ (f : Polynomial ℝ) (_ : MonicRealRootedIn01'' f), sublevelMeasure f

/-- **Non-constant faithful supremum lower bound: `2√2 ≤ sublevelSup''`.**  `X² − 1` is
    non-constant, splits completely, and attains sublevel measure `2√2`, so the `2√2` lower
    bound of Tao's theorem transfers to the correctly-formalized supremum. -/
theorem le_sublevelSup'' : ENNReal.ofReal (2 * Real.sqrt 2) ≤ sublevelSup'' :=
  le_iSup_of_le q (le_iSup_of_le quadratic_admissible'' sublevelMeasure_quadratic.ge)

/-- The **non-constant faithful infimum** of sublevel-set measures — the object whose value
    is the open `2^(4/3) − 1 ≤ inf ≤ 1.835` of Erdős #1038.  Unlike `sublevelInf` and
    `sublevelInf'`, this infimum has *no* measure-`0` witness: every admissible `f` is
    non-constant and splits completely, so it has a real root and positive measure
    (`nonconstant_faithful_sublevelMeasure_pos`).  Whether the infimum itself is positive
    (it is, `= 2^(4/3) − 1`) needs logarithmic potential theory beyond Mathlib. -/
noncomputable def sublevelInf'' : ℝ≥0∞ :=
  ⨅ (f : Polynomial ℝ) (_ : MonicRealRootedIn01'' f), sublevelMeasure f

/-- **Non-constant faithful infimum upper bound: `sublevelInf'' ≤ 2`.**  Witnessed by the
    linear `X` (measure `2`).  Genuine but not tight (true value `≈ 1.52`). -/
theorem sublevelInf''_le_two : sublevelInf'' ≤ ENNReal.ofReal 2 :=
  iInf_le_of_le X (iInf_le_of_le linear_admissible'' sublevelMeasure_linear.le)

/-- **Every non-constant faithful witness has positive sublevel measure.**  Because the
    degree hypothesis `1 ≤ f.natDegree` is now part of the predicate, `f` splits with a
    nonempty real-root multiset, so `faithful_sublevelMeasure_pos` applies.  This is the
    structural payoff: unlike `sublevelInf` (undercut by `X² + 1`) and `sublevelInf'`
    (undercut by `1`), the non-constant faithful infimum is an infimum of *strictly
    positive* measures — the correct setting for the open value `2^(4/3) − 1`. -/
theorem nonconstant_faithful_sublevelMeasure_pos (f : Polynomial ℝ)
    (hf : MonicRealRootedIn01'' f) : 0 < sublevelMeasure f :=
  faithful_sublevelMeasure_pos f hf.1 hf.2

end Erdos1038WIP01
