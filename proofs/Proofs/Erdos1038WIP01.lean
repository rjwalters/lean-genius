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
                                      witness bound `≤ 2`, free of the *positive-degree*
                                      rootless witness `X² + 1`.

  But faithfulness alone is still not enough — the degree-`0` constant `1` slips through:

  * `sublevelInf'_eq_zero`         — `sublevelInf' = 0` (exact): the monic constant `1`
                                    (no roots, `roots.card = 0 = natDegree`) is faithfully
                                    admissible with an empty sublevel set, so the *faithful*
                                    infimum also collapses — parallel to `sublevelInf_eq_zero`.
                                    The genuinely non-degenerate object needs `1 ≤ natDegree`.
  * `MonicRealRootedIn01Pos` / `sublevelInfPos` — the positive-degree faithful predicate and
                                    its infimum, excluding *both* `X² + 1` (non-splitting) and
                                    `1` (degree `0`).  Every witness has positive measure
                                    (`sublevelMeasurePos_pos`); `sublevelInfPos ≤ 2` and
                                    `sublevelInf' ≤ sublevelInfPos`.  This is the object for
                                    which the conjectured `2^(4/3) − 1` is the intended value.

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
    (zero_le)

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
    at most `2`.  Unlike the literal `sublevelInf_le_two`, this bound is *not* undercut to `0`
    by a rootless witness; the true faithful infimum `2^(4/3) − 1 ≈ 1.52 < 2` lies below it
    but beyond the elementary witnesses available here. -/
theorem sublevelInf'_le_two : sublevelInf' ≤ ENNReal.ofReal 2 :=
  iInf_le_of_le X (iInf_le_of_le linear_admissible' sublevelMeasure_linear.le)

/-! ### An infinite faithful family attaining the bound `2` at every degree

The linear witness `X` (measure `2`) is only the first member of a whole family
realising the upper bound `sublevelInf' ≤ 2`.  For any centre `c ∈ [-1,1]` and any
multiplicity `n ≥ 1`, the pure power `(X − c)^n` — a single root `c` of order `n`,
hence a faithful monic polynomial of degree `n` with its root in `[-1,1]` — has
sublevel set exactly the length-`2` interval `(c-1, c+1)` (because
`|(x-c)^n| < 1 ↔ |x-c| < 1`), so its measure is `2` regardless of `n` or `c`.
Thus the bound `2` is *attained*, not merely approached, by a faithful witness of
**every** degree; the conjectured true infimum `2^(4/3) − 1` (if it is indeed below
`2`) can therefore only be reached by polynomials with genuinely distinct roots, not
by clustering a single root. -/

/-- **Sublevel set of a pure power `(X − c)^n`** (`n ≥ 1`): the open interval
    `(c-1, c+1)`.  Since `|(x-c)^n| = |x-c|^n` and `a^n < 1 ↔ a < 1` for `a ≥ 0`,
    `n ≥ 1`, the condition `|f(x)| < 1` is just `|x - c| < 1`. -/
theorem sublevelSet_translate_pow (c : ℝ) {n : ℕ} (hn : n ≠ 0) :
    sublevelSet ((X - C c) ^ n) = Set.Ioo (c - 1) (c + 1) := by
  ext x
  simp only [sublevelSet, Set.mem_setOf_eq, eval_pow, eval_sub, eval_X, eval_C,
    Set.mem_Ioo]
  rw [abs_pow, pow_lt_one_iff_of_nonneg (abs_nonneg _) hn, abs_lt]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- **Sublevel measure of `(X − c)^n` is exactly `2`** for every centre `c` and
    every multiplicity `n ≥ 1` — the length of `(c-1, c+1)`.  Generalises
    `sublevelMeasure_linear` (`c = 0, n = 1`). -/
theorem sublevelMeasure_translate_pow (c : ℝ) {n : ℕ} (hn : n ≠ 0) :
    sublevelMeasure ((X - C c) ^ n) = ENNReal.ofReal 2 := by
  unfold sublevelMeasure
  rw [sublevelSet_translate_pow c hn, Real.volume_Ioo]
  congr 1; ring

/-- **`(X − c)^n` is faithfully admissible for `c ∈ [-1,1]`, `n ≥ 1`.**  It is monic
    (a power of the monic `X − c`), its only root is `c ∈ [-1,1]` (with multiplicity
    `n`), and it splits completely: `roots.card = n = natDegree`. -/
theorem translate_pow_admissible' {c : ℝ} (hc : c ∈ Set.Icc (-1 : ℝ) 1) {n : ℕ}
    (hn : n ≠ 0) : MonicRealRootedIn01' ((X - C c) ^ n) := by
  have hmonic : ((X - C c) ^ n).Monic := (monic_X_sub_C c).pow n
  refine ⟨⟨hmonic, ?_⟩, ?_⟩
  · intro r hr
    rw [Polynomial.roots_pow, Polynomial.roots_X_sub_C,
      Multiset.mem_nsmul_of_ne_zero hn, Multiset.mem_singleton] at hr
    rwa [hr]
  · rw [Polynomial.roots_pow, Polynomial.roots_X_sub_C, Multiset.card_nsmul,
      Multiset.card_singleton, mul_one, Polynomial.natDegree_pow,
      Polynomial.natDegree_X_sub_C, mul_one]

/-- **The bound `2` is attained at every degree.**  For each `n ≥ 1` the faithful
    witness `(X - 0)^n = X^n` realises sublevel measure exactly `2`, so the faithful
    infimum lies at or below `2` and this value is genuinely achieved (not merely a
    limit) by a splitting polynomial of degree `n`. -/
theorem sublevelInf'_le_two_attained (n : ℕ) (hn : n ≠ 0) :
    sublevelInf' ≤ ENNReal.ofReal 2 :=
  iInf_le_of_le ((X - C (0 : ℝ)) ^ n)
    (iInf_le_of_le (translate_pow_admissible' (by norm_num) hn)
      (sublevelMeasure_translate_pow 0 hn).le)

/-! ### A distinct-root family filling `(2, 2√2)`: the quadratics `X² − d`

The measure-`2` witnesses above all cluster a *single* root (multiplicity `n`), so they
attain only the value `2`.  To reach the intermediate measures `2 < m < 2√2` one needs
genuinely **distinct** roots.  The one-parameter family `X² − d` (`0 ≤ d ≤ 1`), which
factors as `(X − √d)(X + √d)` with two roots `±√d ∈ [-1,1]`, does exactly this: for
`0 ≤ d < 1` its sublevel set is the interval `(−√(d+1), √(d+1))` (the lower constraint
`d − 1 < x²` is vacuous since `d < 1 ≤ x² + 1`), so its measure is `2√(d+1)`, which sweeps
continuously from `2` (at `d = 0`, a double root — the `X²` member of the previous family)
up towards `2√2` (as `d → 1`, recovering the extremal `q = X² − 1`).  Thus every value in
`(2, 2√2)` is a faithful sublevel measure, realised by a *distinct-root* quadratic. -/

/-- **Sublevel set of `X² − d`** for `0 ≤ d < 1`: the open interval `(−√(d+1), √(d+1))`.
    The condition `|x² − d| < 1` is `d − 1 < x² < d + 1`; since `d < 1` the left half is
    automatic (`x² ≥ 0 > d − 1`), leaving `x² < d + 1`, i.e. `|x| < √(d+1)`. -/
theorem sublevelSet_Xsq_sub_C {d : ℝ} (hd : 0 ≤ d) (hd1 : d < 1) :
    sublevelSet (X ^ 2 - C d) = Set.Ioo (-Real.sqrt (d + 1)) (Real.sqrt (d + 1)) := by
  have hsq : Real.sqrt (d + 1) ^ 2 = d + 1 := Real.sq_sqrt (by linarith)
  have hpos : 0 < Real.sqrt (d + 1) := Real.sqrt_pos.mpr (by linarith)
  ext x
  have hev : (X ^ 2 - C d : Polynomial ℝ).eval x = x ^ 2 - d := by simp
  simp only [sublevelSet, Set.mem_setOf_eq, hev, abs_lt, Set.mem_Ioo]
  constructor
  · rintro ⟨_, h2⟩
    refine ⟨?_, ?_⟩
    · nlinarith [hsq, hpos, sq_nonneg (x + Real.sqrt (d + 1))]
    · nlinarith [hsq, hpos, sq_nonneg (x - Real.sqrt (d + 1))]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · nlinarith [sq_nonneg x]
    · nlinarith [hsq, hpos, h1, h2]

/-- **Sublevel measure of `X² − d` is `2√(d+1)`** for `0 ≤ d < 1` — the length of the
    interval `(−√(d+1), √(d+1))`.  As `d` ranges over `[0, 1)` this sweeps `[2, 2√2)`,
    filling the gap between the clustered-root family (fixed at `2`) and the extremal
    `q = X² − 1` (measure `2√2`). -/
theorem sublevelMeasure_Xsq_sub_C {d : ℝ} (hd : 0 ≤ d) (hd1 : d < 1) :
    sublevelMeasure (X ^ 2 - C d) = ENNReal.ofReal (2 * Real.sqrt (d + 1)) := by
  unfold sublevelMeasure
  rw [sublevelSet_Xsq_sub_C hd hd1, Real.volume_Ioo]
  congr 1
  ring

/-- **`X² − d` is faithfully admissible for `d ∈ [0,1]`.**  It factors as
    `(X − √d)(X + √d)`, hence is monic with both roots `±√d ∈ [-1,1]` (as `0 ≤ √d ≤ 1`)
    and splits completely (`roots.card = 2 = natDegree`).  For `d ∈ (0,1)` the two roots
    are *distinct*, distinguishing this family from the pure powers `(X − c)^n`. -/
theorem Xsq_sub_C_admissible' {d : ℝ} (hd : d ∈ Set.Icc (0 : ℝ) 1) :
    MonicRealRootedIn01' (X ^ 2 - C d) := by
  obtain ⟨hd0, hd1⟩ := hd
  have hval : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hd0
  have hsd0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hsd : Real.sqrt d ≤ 1 := by
    nlinarith [Real.sq_sqrt hd0, Real.sqrt_nonneg d]
  have hfac : (X ^ 2 - C d : Polynomial ℝ)
      = (X - C (Real.sqrt d)) * (X - C (-Real.sqrt d)) := by
    have h1 : (X - C (Real.sqrt d)) * (X - C (-Real.sqrt d))
        = X ^ 2 - C (Real.sqrt d) * C (Real.sqrt d) := by
      simp only [map_neg]; ring
    rw [h1, ← map_mul, hval]
  have hmonic : (X ^ 2 - C d : Polynomial ℝ).Monic := by
    rw [hfac]; exact (monic_X_sub_C _).mul (monic_X_sub_C _)
  have hne : (X ^ 2 - C d : Polynomial ℝ) ≠ 0 := hmonic.ne_zero
  refine ⟨⟨hmonic, ?_⟩, ?_⟩
  · intro r hr
    rw [hfac, Polynomial.roots_mul (by rw [← hfac]; exact hne),
      Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C, Multiset.mem_add,
      Multiset.mem_singleton, Multiset.mem_singleton] at hr
    rw [Set.mem_Icc]
    rcases hr with h | h <;> subst h <;> constructor <;> linarith
  · have hcard : (X ^ 2 - C d : Polynomial ℝ).roots.card = 2 := by
      rw [hfac, Polynomial.roots_mul (by rw [← hfac]; exact hne),
        Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
      simp
    have hnd : (X ^ 2 - C d : Polynomial ℝ).natDegree = 2 := by compute_degree!
    rw [hcard, hnd]

/-- **Every measure `2√(d+1)` (`0 ≤ d < 1`) is a faithful lower bound for `sublevelSup'`.**
    The distinct-root quadratic `X² − d` is faithfully admissible with sublevel measure
    `2√(d+1)`, so `2√(d+1) ≤ sublevelSup'`.  As `d → 1` this reproduces the extremal
    `2√2 ≤ sublevelSup'` (`le_sublevelSup'`) as a limit of distinct-root witnesses. -/
theorem le_sublevelSup'_Xsq {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) :
    ENNReal.ofReal (2 * Real.sqrt (d + 1)) ≤ sublevelSup' :=
  le_iSup_of_le (X ^ 2 - C d)
    (le_iSup_of_le (Xsq_sub_C_admissible' ⟨hd0, le_of_lt hd1⟩)
      (sublevelMeasure_Xsq_sub_C hd0 hd1).ge)

/-- **The quadratic family sweeps its measure interval strictly monotonically.** For
    `0 ≤ d₁ < d₂ < 1`, the sublevel measure of `X² − d₁` is strictly smaller than that of
    `X² − d₂`: deepening the constant term (spreading the two roots `±√d` apart) strictly
    enlarges the sublevel set `(−√(d+1), √(d+1))`. The measure `2√(d+1)` is strictly
    increasing in `d`, so the sweep of `[2, 2√2)` by `exists_faithful_sublevelMeasure_eq`
    is order-preserving — each target value is hit by a *unique* `d`. -/
theorem sublevelMeasure_Xsq_sub_C_lt {d₁ d₂ : ℝ} (hd₁ : 0 ≤ d₁) (hd₂ : d₂ < 1)
    (h : d₁ < d₂) :
    sublevelMeasure (X ^ 2 - C d₁) < sublevelMeasure (X ^ 2 - C d₂) := by
  rw [sublevelMeasure_Xsq_sub_C hd₁ (lt_trans h hd₂),
    sublevelMeasure_Xsq_sub_C (le_trans hd₁ h.le) hd₂,
    ENNReal.ofReal_lt_ofReal_iff
      (mul_pos two_pos (Real.sqrt_pos.mpr (by linarith)))]
  have hsqrt : Real.sqrt (d₁ + 1) < Real.sqrt (d₂ + 1) :=
    Real.sqrt_lt_sqrt (by linarith) (by linarith)
  linarith

/-- **The quadratic sublevel measure is strictly monotone on `[0, 1)`.** The `StrictMonoOn`
    packaging of `sublevelMeasure_Xsq_sub_C_lt`: `d ↦ sublevelMeasure (X² − d)` is strictly
    increasing on `Set.Ico 0 1`. Hence the parametrisation of the elementary measure spectrum
    `[2, 2√2)` by the constant term is an order isomorphism onto its image. -/
theorem sublevelMeasure_Xsq_sub_C_strictMonoOn :
    StrictMonoOn (fun d : ℝ => sublevelMeasure (X ^ 2 - C d)) (Set.Ico 0 1) :=
  fun _ ha _ hb hab => sublevelMeasure_Xsq_sub_C_lt ha.1 hb.2 hab

/-- **Every measure `m ∈ [2, 2√2)` is realised exactly by a faithful distinct-root
    quadratic.**  This formalizes the surjectivity claim above: solving `2√(d+1) = m`
    gives `d = m²/4 − 1`, which lies in `[0, 1)` precisely when `2 ≤ m < 2√2`, so the
    faithfully-admissible `X² − d` has sublevel measure exactly `ofReal m`.  Thus the whole
    half-open interval `[2, 2√2)` of measure values is *attained* by genuinely distinct-root
    witnesses — the elementary lower half of the extremal spectrum `[2, 2√2]`. -/
theorem exists_faithful_sublevelMeasure_eq {m : ℝ} (hm : 2 ≤ m)
    (hm2 : m < 2 * Real.sqrt 2) :
    ∃ f : Polynomial ℝ, MonicRealRootedIn01' f ∧
      sublevelMeasure f = ENNReal.ofReal m := by
  have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hm0 : (0 : ℝ) ≤ m := by linarith
  set d : ℝ := m ^ 2 / 4 - 1 with hd_def
  have hmsq : m ^ 2 < 8 := by
    have hlt : m ^ 2 < (2 * Real.sqrt 2) ^ 2 :=
      sq_lt_sq' (by linarith [Real.sqrt_nonneg 2]) hm2
    calc m ^ 2 < (2 * Real.sqrt 2) ^ 2 := hlt
      _ = 8 := by rw [mul_pow, hsqrt2]; norm_num
  have hd0 : 0 ≤ d := by rw [hd_def]; nlinarith
  have hd1 : d < 1 := by rw [hd_def]; linarith
  refine ⟨X ^ 2 - C d, Xsq_sub_C_admissible' ⟨hd0, hd1.le⟩, ?_⟩
  rw [sublevelMeasure_Xsq_sub_C hd0 hd1]
  congr 1
  have hdp1 : d + 1 = (m / 2) ^ 2 := by rw [hd_def]; ring
  rw [hdp1, Real.sqrt_sq (by linarith : (0 : ℝ) ≤ m / 2)]
  ring

/-- **Every value in `[2, 2√2)` is a lower bound for the faithful supremum.**  Combining
    `exists_faithful_sublevelMeasure_eq` (each such `m` is an attained faithful measure)
    with the definition of `sublevelSup'` as a supremum shows `ofReal m ≤ sublevelSup'` for
    all `2 ≤ m < 2√2`.  Letting `m → 2√2` this recovers `le_sublevelSup'` as the supremum of
    a whole continuum of distinct-root witnesses, not just the single extremal `X² − 1`. -/
theorem le_sublevelSup'_of_mem {m : ℝ} (hm : 2 ≤ m) (hm2 : m < 2 * Real.sqrt 2) :
    ENNReal.ofReal m ≤ sublevelSup' := by
  obtain ⟨f, hf, hmeas⟩ := exists_faithful_sublevelMeasure_eq hm hm2
  rw [← hmeas]
  exact le_iSup_of_le f (le_iSup_of_le hf le_rfl)

/-- **The extremal endpoint `2√2` is itself attained** — closing the attained interval.
    `exists_faithful_sublevelMeasure_eq` realises every `m ∈ [2, 2√2)` by a distinct-root
    quadratic `X² − d`, but stops *short* of the endpoint (`d < 1`).  The endpoint is
    supplied by the boundary case `d = 1`, i.e. the extremal quadratic `q = X² − 1`
    itself, whose sublevel measure is exactly `2√2` (`sublevelMeasure_quadratic`) and which
    is faithfully admissible (`quadratic_admissible'`).  Hence every measure value in the
    *closed* interval `[2, 2√2]` is attained by a faithful admissible polynomial — the full
    elementary sup-side spectrum, endpoint included. -/
theorem exists_faithful_sublevelMeasure_eq_Icc {m : ℝ} (hm : 2 ≤ m)
    (hm2 : m ≤ 2 * Real.sqrt 2) :
    ∃ f : Polynomial ℝ, MonicRealRootedIn01' f ∧
      sublevelMeasure f = ENNReal.ofReal m := by
  rcases eq_or_lt_of_le hm2 with hmeq | hmlt
  · exact ⟨q, quadratic_admissible', by rw [sublevelMeasure_quadratic, hmeq]⟩
  · exact exists_faithful_sublevelMeasure_eq hm hmlt

/-- **The closed interval `[2, 2√2]` lies inside the attained faithful-measure spectrum.**
    Set-level form of `exists_faithful_sublevelMeasure_eq_Icc`: every real `m` between the
    clustered-root minimum `2` and the extremal maximum `2√2` is the (real) sublevel
    measure of some faithfully admissible monic polynomial.  This is the complete
    elementary description of the lower half `[2, 2√2]` of the extremal spectrum
    `[2^(4/3) − 1, 2√2]` — no potential theory, endpoint included. -/
theorem Icc_subset_faithful_attained :
    Set.Icc (2 : ℝ) (2 * Real.sqrt 2) ⊆
      {m : ℝ | ∃ f : Polynomial ℝ, MonicRealRootedIn01' f ∧
        sublevelMeasure f = ENNReal.ofReal m} :=
  fun _ hm => exists_faithful_sublevelMeasure_eq_Icc hm.1 hm.2

/-! ### The faithful and literal extremal objects are ordered

The faithful predicate `MonicRealRootedIn01'` is *stronger* than `MonicRealRootedIn01`
(it adds `roots.card = natDegree`), so the supremum/infimum over the smaller faithful
family are pinched inside the literal ones: `sublevelSup' ≤ sublevelSup` and
`sublevelInf ≤ sublevelInf'`.  Together with `le_sublevelSup'` (`2√2 ≤ sublevelSup'`)
this sandwiches the faithful supremum: `2√2 ≤ sublevelSup' ≤ sublevelSup`. -/

/-- **`sublevelSup' ≤ sublevelSup`.**  Every faithfully admissible `f` is admissible, so the
    supremum over the faithful family is bounded by the supremum over the larger literal
    family. -/
theorem sublevelSup'_le_sublevelSup : sublevelSup' ≤ sublevelSup :=
  iSup_le fun f => iSup_le fun hf => le_iSup_of_le f (le_iSup_of_le hf.1 le_rfl)

/-- **`sublevelInf ≤ sublevelInf'`.**  Every faithfully admissible `f` is admissible, so the
    infimum over the larger literal family is bounded by the infimum over the faithful one.
    (The literal side is in fact `0` by `sublevelInf_eq_zero`; this records the qualitative
    ordering that survives independent of that collapse.) -/
theorem sublevelInf_le_sublevelInf' : sublevelInf ≤ sublevelInf' :=
  le_iInf fun f => le_iInf fun hf => iInf_le_of_le f (iInf_le_of_le hf.1 le_rfl)

/-! ### The faithful extremal problem is non-degenerate: `sublevelInf' < sublevelSup'`

The two elementary witnesses bound the faithful extremal object from *both* sides:
the linear `X` gives `sublevelInf' ≤ 2` and the quadratic `X² − 1` gives
`2√2 ≤ sublevelSup'`.  Since `2 < 2√2` (as `1 < √2`), these two bounds do not overlap,
so the faithful supremum is *strictly* greater than the faithful infimum.  This records
— with no potential theory — that the Erdős #1038 sublevel problem is genuinely
non-degenerate: the sup and inf are separated, independently of their exact endpoints
`2^(4/3) − 1` and `2√2`. -/

/-- **The faithful infimum is strictly below the faithful supremum.**  Chaining
    `sublevelInf' ≤ ofReal 2` (`sublevelInf'_le_two`) through the strict numeric gap
    `2 < 2√2` (from `1 < √2`) into `ofReal (2√2) ≤ sublevelSup'` (`le_sublevelSup'`) shows
    the faithful extremal spread is nonzero. -/
theorem sublevelInf'_lt_sublevelSup' : sublevelInf' < sublevelSup' := by
  have hgap : ENNReal.ofReal 2 < ENNReal.ofReal (2 * Real.sqrt 2) := by
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have h1 : (1 : ℝ) < Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    nlinarith [h1]
  calc sublevelInf' ≤ ENNReal.ofReal 2 := sublevelInf'_le_two
    _ < ENNReal.ofReal (2 * Real.sqrt 2) := hgap
    _ ≤ sublevelSup' := le_sublevelSup'

/-- **The literal supremum is strictly positive**, hence `sublevelInf < sublevelSup`.
    The literal infimum collapses to `0` (`sublevelInf_eq_zero`) via the rootless
    `X² + 1`, while `2√2 ≤ sublevelSup` keeps the supremum positive; the strict ordering
    survives the collapse. -/
theorem sublevelInf_lt_sublevelSup : sublevelInf < sublevelSup := by
  rw [sublevelInf_eq_zero]
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (2 * Real.sqrt 2) := by
    rw [ENNReal.ofReal_pos]; positivity
  exact lt_of_lt_of_le hpos le_sublevelSup

/-! ### An elementary finite upper bound: `sublevelSup' ≤ 4`

The *sharp* upper bound `sublevelSup' = 2√2` is Tao's 2025 theorem and needs
logarithmic potential theory absent from Mathlib.  A **non-tight but honest and fully
elementary** upper bound is nonetheless available and pins the faithful supremum inside a
concrete finite interval `[2√2, 4]`, so the extremal quantity is provably finite.

The mechanism is purely geometric.  For faithfully admissible `f` (monic, split, all
roots real in `[-1,1]`) we have `f = ∏_{r ∈ roots} (X − r)`, so for `|x| ≥ 2` every factor
satisfies `|x − r| ≥ |x| − |r| ≥ 2 − 1 = 1`; the product of such factors has absolute value
`≥ 1`, hence `x ∉ {|f| < 1}`.  Therefore `sublevelSet f ⊆ (−2, 2)` and
`sublevelMeasure f ≤ vol(−2, 2) = 4`, uniformly in `f`. -/

/-- Absolute value distributes over a multiset product of reals. -/
theorem abs_multiset_prod (s : Multiset ℝ) :
    |s.prod| = (s.map (fun t => |t|)).prod := by
  refine Multiset.induction (by simp) (fun a s ih => ?_) s
  simp [Multiset.prod_cons, abs_mul, ih]

/-- **Outside `[−2, 2]` a faithfully admissible polynomial has `|f| ≥ 1`.**  Writing
`f = ∏_{r} (X − r)` over its (real, `[-1,1]`) roots, each factor obeys
`|x − r| ≥ |x| − |r| ≥ 2 − 1 = 1` when `|x| ≥ 2`, so the product has absolute value `≥ 1`. -/
theorem one_le_abs_eval_of_ge_two {f : Polynomial ℝ} (hf : MonicRealRootedIn01' f)
    {x : ℝ} (hx : 2 ≤ |x|) : 1 ≤ |f.eval x| := by
  have hrep : (f.roots.map fun a => X - C a).prod = f :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hf.1.1 hf.2
  have heval : f.eval x = (f.roots.map (fun r => x - r)).prod := by
    conv_lhs => rw [← hrep]
    rw [eval_multiset_prod, Multiset.map_map]
    exact congrArg _ (Multiset.map_congr rfl (fun r _ => by simp))
  rw [heval, abs_multiset_prod, Multiset.map_map]
  refine Multiset.one_le_prod (fun a ha => ?_)
  simp only [Multiset.mem_map, Function.comp_apply] at ha
  obtain ⟨r, hr, rfl⟩ := ha
  have hr1 : r ∈ Set.Icc (-1 : ℝ) 1 := hf.1.2 r hr
  have hrle : |r| ≤ 1 := abs_le.mpr ⟨hr1.1, hr1.2⟩
  have hsub : |x| - |r| ≤ |x - r| := by
    have := abs_sub_abs_le_abs_sub x r; linarith [abs_nonneg (x - r)]
  linarith

/-- **The faithful sublevel set is confined to `(−2, 2)`.** -/
theorem sublevelSet_subset_Ioo {f : Polynomial ℝ} (hf : MonicRealRootedIn01' f) :
    sublevelSet f ⊆ Set.Ioo (-2 : ℝ) 2 := by
  intro x hx
  simp only [sublevelSet, Set.mem_setOf_eq] at hx
  by_contra hcon
  have hxge : 2 ≤ |x| := by
    rw [Set.mem_Ioo, not_and_or] at hcon
    rcases hcon with h | h
    · rw [not_lt] at h; rw [abs_of_nonpos (by linarith)]; linarith
    · rw [not_lt] at h; rw [abs_of_nonneg (by linarith)]; linarith
  exact absurd hx (not_lt.mpr (one_le_abs_eval_of_ge_two hf hxge))

/-- **Uniform bound `sublevelMeasure f ≤ 4`** for every faithfully admissible `f`,
    from `sublevelSet f ⊆ (−2, 2)` and `vol(−2, 2) = 4`. -/
theorem sublevelMeasure_le_four {f : Polynomial ℝ} (hf : MonicRealRootedIn01' f) :
    sublevelMeasure f ≤ ENNReal.ofReal 4 := by
  have h : sublevelMeasure f ≤ volume (Set.Ioo (-2 : ℝ) 2) :=
    measure_mono (sublevelSet_subset_Ioo hf)
  rwa [Real.volume_Ioo, show (2 : ℝ) - (-2) = 4 by norm_num] at h

/-- **`sublevelSup' ≤ 4`.**  The elementary, machine-checked upper bound on the faithful
    supremum, complementing the lower bound `le_sublevelSup'` (`2√2 ≤ sublevelSup'`).
    Together they confine `sublevelSup' ∈ [2√2, 4]` with no potential theory; Tao's sharp
    `= 2√2` sits inside this interval and remains beyond Mathlib. -/
theorem sublevelSup'_le_four : sublevelSup' ≤ ENNReal.ofReal 4 :=
  iSup_le fun f => iSup_le fun hf => sublevelMeasure_le_four hf

/-- **The faithful supremum is sandwiched: `2√2 ≤ sublevelSup' ≤ 4`.**  A fully elementary,
    axiom-free localisation of the open Erdős #1038 extremal constant to a concrete finite
    interval. -/
theorem sublevelSup'_mem_Icc :
    ENNReal.ofReal (2 * Real.sqrt 2) ≤ sublevelSup' ∧ sublevelSup' ≤ ENNReal.ofReal 4 :=
  ⟨le_sublevelSup', sublevelSup'_le_four⟩

/-! ### Boundedness and finiteness

The `⊆ (−2, 2)` confinement gives more than the numeric `≤ 4` bound: the faithful sublevel
set is a *bounded* set (complementing `isOpen_sublevelSet`, so it is a bounded open set), each
faithful sublevel *measure* is finite, and — packaging the `≤ 4` supremum bound as a
`⊤`-finiteness statement — the extremal supremum `sublevelSup'` is itself finite. The Erdős
#1038 extremal constant is therefore a genuine real number, not `∞`, with no potential theory. -/

/-- **The faithful sublevel set is bounded.**  It is confined to `(−2, 2)`
(`sublevelSet_subset_Ioo`), a bounded interval; together with `isOpen_sublevelSet` this
exhibits it as a bounded open subset of `ℝ`. -/
theorem isBounded_sublevelSet {f : Polynomial ℝ} (hf : MonicRealRootedIn01' f) :
    Bornology.IsBounded (sublevelSet f) :=
  Metric.isBounded_Ioo (-2 : ℝ) 2 |>.subset (sublevelSet_subset_Ioo hf)

/-- **Each faithful sublevel measure is finite** (`< ⊤`), from the uniform `≤ 4` bound. -/
theorem sublevelMeasure_lt_top {f : Polynomial ℝ} (hf : MonicRealRootedIn01' f) :
    sublevelMeasure f < ⊤ :=
  lt_of_le_of_lt (sublevelMeasure_le_four hf) ENNReal.ofReal_lt_top

/-- **Each faithful sublevel measure is finite** (`≠ ⊤`), the `Ne` form of
`sublevelMeasure_lt_top`. -/
theorem sublevelMeasure_ne_top {f : Polynomial ℝ} (hf : MonicRealRootedIn01' f) :
    sublevelMeasure f ≠ ⊤ :=
  (sublevelMeasure_lt_top hf).ne

/-- **The faithful extremal supremum is finite** (`sublevelSup' < ⊤`).  Packaging
`sublevelSup' ≤ 4` as a `⊤`-finiteness statement: the open Erdős #1038 extremal constant is a
genuine finite real number, not `∞`. -/
theorem sublevelSup'_lt_top : sublevelSup' < ⊤ :=
  lt_of_le_of_lt sublevelSup'_le_four ENNReal.ofReal_lt_top

/-- **The faithful extremal supremum is finite** (`sublevelSup' ≠ ⊤`), the `Ne` form of
`sublevelSup'_lt_top`. -/
theorem sublevelSup'_ne_top : sublevelSup' ≠ ⊤ :=
  sublevelSup'_lt_top.ne

/-! ### Faithfulness alone is still not enough: `sublevelInf' = 0` via the constant `1`

The faithful predicate `MonicRealRootedIn01'` excludes the rootless *positive-degree*
witness `X² + 1` (`sq_add_one_not_admissible'`), which is why `faithful_sublevelMeasure_pos`
needs the hypothesis `1 ≤ f.natDegree`.  But the predicate does **not** exclude the
degree-`0` constant polynomial `1`: it is monic, has no real roots, and trivially splits
(`roots.card = 0 = natDegree`).  Its sublevel set `{x : |1| < 1}` is empty, so — exactly
as on the literal side (`sublevelInf_eq_zero`) — the *faithful* infimum still degenerates:
`sublevelInf' = 0`.  The genuinely non-degenerate object therefore needs the additional
constraint `1 ≤ f.natDegree` (positive degree), under which every witness has positive
measure.  This isolates the last faithfulness gap. -/

/-- **The constant `1` is faithfully admissible**: monic, no roots, `roots.card = 0 =
    natDegree`.  It is the degree-`0` witness the faithful predicate fails to exclude
    (mirroring how the literal predicate fails to exclude the rootless `X² + 1`). -/
theorem one_admissible' : MonicRealRootedIn01' (1 : Polynomial ℝ) := by
  refine ⟨⟨monic_one, ?_⟩, ?_⟩
  · intro r hr
    simp at hr
  · simp

/-- **The sublevel set of the constant `1` is empty**: `|1| < 1` is false. -/
theorem sublevelSet_one : sublevelSet (1 : Polynomial ℝ) = ∅ := by
  ext x
  simp [sublevelSet]

/-- **The sublevel set of the constant `1` has Lebesgue measure `0`.** -/
theorem sublevelMeasure_one : sublevelMeasure (1 : Polynomial ℝ) = 0 := by
  unfold sublevelMeasure
  rw [sublevelSet_one, measure_empty]

/-- **The faithful infimum still collapses: `sublevelInf' = 0`.**  Parallel to
    `sublevelInf_eq_zero` on the literal side — the degree-`0` constant `1` is faithfully
    admissible with an empty (measure-`0`) sublevel set, so `sublevelInf' = 0`.  This
    sharpens `sublevelInf'_le_two` and shows faithfulness *alone* does not restore the
    intended infimum geometry: the rootless collapse is only pushed from the positive-degree
    `X² + 1` down to the degree-`0` constant `1`.  Excluding it needs the extra hypothesis
    `1 ≤ f.natDegree` (see `sublevelInfPos`). -/
theorem sublevelInf'_eq_zero : sublevelInf' = 0 :=
  le_antisymm
    (iInf_le_of_le 1 (iInf_le_of_le one_admissible' sublevelMeasure_one.le))
    (zero_le _)

/-! ### The genuinely non-degenerate object: positive-degree faithful admissibility

`sublevelInf'_eq_zero` shows the faithful predicate is *still* too weak on the infimum
side.  The correct restriction adds `1 ≤ f.natDegree`, excluding *both* the non-splitting
`X² + 1` (via faithfulness) and the degree-`0` constant `1` (via positive degree).  Over
this class every witness has *positive* sublevel measure (`faithful_sublevelMeasure_pos`),
so no single polynomial drags the infimum to `0`; this is the object for which the
conjectured elementary infimum `2^(4/3) − 1 ≈ 1.52` is the intended value. -/

/-- **Positive-degree faithful admissibility.**  The faithful predicate together with
    `1 ≤ f.natDegree`: monic, complete real splitting with all roots in `[-1,1]`, and degree
    at least `1`.  Excludes both the non-splitting `X² + 1` and the degree-`0` constant `1`,
    leaving exactly the polynomials for which the sublevel geometry is non-degenerate. -/
def MonicRealRootedIn01Pos (f : Polynomial ℝ) : Prop :=
  MonicRealRootedIn01' f ∧ 1 ≤ f.natDegree

/-- The linear polynomial `X` is positive-degree faithfully admissible (degree `1`). -/
theorem linear_admissiblePos : MonicRealRootedIn01Pos (X : Polynomial ℝ) :=
  ⟨linear_admissible', by simp⟩

/-- The extremal quadratic `q = X² − 1` is positive-degree faithfully admissible (degree `2`). -/
theorem quadratic_admissiblePos : MonicRealRootedIn01Pos q := by
  refine ⟨quadratic_admissible', ?_⟩
  have hnd : q.natDegree = 2 := by simp only [q]; compute_degree!
  omega

/-- **Every positive-degree faithful witness has positive sublevel measure.**  Immediate
    from `faithful_sublevelMeasure_pos`: the degree constraint forces a real root, which lies
    in the *open* sublevel set, making it nonempty and hence of positive Lebesgue measure. -/
theorem sublevelMeasurePos_pos {f : Polynomial ℝ} (hf : MonicRealRootedIn01Pos f) :
    0 < sublevelMeasure f :=
  faithful_sublevelMeasure_pos f hf.1 hf.2

/-- The **positive-degree faithful infimum**: the infimum of `sublevelMeasure` over monic
    polynomials that split completely into real roots in `[-1,1]` *and* have positive degree.
    Unlike `sublevelInf'` (which collapses to `0` via the constant `1`, `sublevelInf'_eq_zero`),
    every witness here has positive measure (`sublevelMeasurePos_pos`); this is the object for
    which the conjectured `2^(4/3) − 1` is the intended value.  Its exact value still needs
    logarithmic potential theory beyond Mathlib. -/
noncomputable def sublevelInfPos : ℝ≥0∞ :=
  ⨅ (f : Polynomial ℝ) (_ : MonicRealRootedIn01Pos f), sublevelMeasure f

/-- **Upper bound `sublevelInfPos ≤ 2`.**  The linear `X` is positive-degree faithfully
    admissible with sublevel measure `2`, so the positive-degree infimum is at most `2`.
    Unlike `sublevelInf'_le_two`, this bound is *not* undercut to `0` by a degenerate witness
    (`sublevelInf'_eq_zero`); the true value `2^(4/3) − 1 < 2` lies below it but beyond the
    elementary witnesses available here. -/
theorem sublevelInfPos_le_two : sublevelInfPos ≤ ENNReal.ofReal 2 :=
  iInf_le_of_le X (iInf_le_of_le linear_admissiblePos sublevelMeasure_linear.le)

/-- **`sublevelInf' ≤ sublevelInfPos`.**  The positive-degree family is a *subset* of the
    faithful family, so the infimum over it is at least the faithful infimum.  Combined with
    `sublevelInf'_eq_zero` this shows `0 = sublevelInf' ≤ sublevelInfPos ≤ 2`, with the crucial
    qualitative difference that — unlike `sublevelInf'` — no *single* witness of `sublevelInfPos`
    has measure `0` (`sublevelMeasurePos_pos`). -/
theorem sublevelInf'_le_sublevelInfPos : sublevelInf' ≤ sublevelInfPos :=
  le_iInf fun f => le_iInf fun hf => iInf_le_of_le f (iInf_le_of_le hf.1 le_rfl)

/-! ### The general faithful quadratic `(X − a)(X − b)` and the exact degree-`2` spectrum

The quadratic families studied so far are *special*: `X² − d` centres its two roots at
`±√d` (symmetric about `0`), and `(X − c)^n` clusters a *single* root.  The **general**
monic real quadratic with two roots in `[-1,1]` is `(X − a)(X − b)` for arbitrary
`a, b ∈ [-1,1]`.  Completing the square,
`(X − a)(X − b) = (X − m)² − ((a − b)/2)²` with `m = (a + b)/2`, reduces it to the centred
family shifted by `m`.  Two fully elementary consequences:

* its sublevel measure is exactly `√((a − b)² + 4)` — a closed form for the *entire*
  degree-`2` spectrum in terms of the root separation `|a − b|` alone
  (`sublevelMeasure_quadraticGen`).  As `|a − b|` runs over `[0, 2]` this sweeps `[2, 2√2]`,
  matching (and re-deriving) the symmetric `X² − d` family without the `d < 1` restriction;
* since `0 ≤ (a − b)² ≤ 4`, this measure is `≥ 2`, with equality iff `a = b`
  (`sublevelMeasure_quadraticGen_ge_two`).

The second point pins the **degree-`2` infimum exactly**: `sublevelInfDeg2 = 2`
(`sublevelInfDeg2_eq_two`), attained by any double root `(X − c)²`.  This sharply separates
the elementary degree-`2` slice from the conjectured true infimum `2^(4/3) − 1 ≈ 1.52 < 2`:
the extremal small-measure witnesses **cannot** be quadratic — they require unboundedly many
distinct roots (degree `→ ∞`), beyond the reach of the degree-`2` analysis. -/

/-- The **general monic real quadratic** with roots `a, b`: `(X − a)(X − b)`. -/
noncomputable def quadraticGen (a b : ℝ) : Polynomial ℝ := (X - C a) * (X - C b)

/-- Evaluation of the general quadratic: `(x − a)(x − b)`. -/
theorem quadraticGen_eval (a b x : ℝ) :
    (quadraticGen a b).eval x = (x - a) * (x - b) := by
  simp [quadraticGen]

/-- The general quadratic is monic (a product of two monic linear factors). -/
theorem quadraticGen_monic (a b : ℝ) : (quadraticGen a b).Monic :=
  (monic_X_sub_C a).mul (monic_X_sub_C b)

/-- The general quadratic has degree `2`. -/
theorem quadraticGen_natDegree (a b : ℝ) : (quadraticGen a b).natDegree = 2 := by
  rw [quadraticGen]; compute_degree!

/-- **`(X − a)(X − b)` is faithfully admissible for `a, b ∈ [-1,1]`.**  It is monic with
    both roots `a, b ∈ [-1,1]` and splits completely (`roots.card = 2 = natDegree`). -/
theorem quadraticGen_admissible' {a b : ℝ} (ha : a ∈ Set.Icc (-1 : ℝ) 1)
    (hb : b ∈ Set.Icc (-1 : ℝ) 1) : MonicRealRootedIn01' (quadraticGen a b) := by
  have hne : ((X - C a) * (X - C b) : Polynomial ℝ) ≠ 0 :=
    mul_ne_zero (monic_X_sub_C a).ne_zero (monic_X_sub_C b).ne_zero
  refine ⟨⟨quadraticGen_monic a b, ?_⟩, ?_⟩
  · intro r hr
    rw [quadraticGen, Polynomial.roots_mul hne, Polynomial.roots_X_sub_C,
      Polynomial.roots_X_sub_C, Multiset.mem_add, Multiset.mem_singleton,
      Multiset.mem_singleton] at hr
    rcases hr with h | h <;> subst h <;> assumption
  · have hcard : (quadraticGen a b).roots.card = 2 := by
      rw [quadraticGen, Polynomial.roots_mul hne, Polynomial.roots_X_sub_C,
        Polynomial.roots_X_sub_C]
      simp
    rw [hcard, quadraticGen_natDegree]

/-- **Every faithful quadratic has sublevel measure `≥ 2`.**  Completing the square,
    `(x − a)(x − b) = (x − m)² − ((a − b)/2)²` with `m = (a + b)/2`.  Since `(a − b)² ≤ 4`
    (as `a, b ∈ [-1,1]`), on the punctured interval `(m − 1, m + 1) ∖ {m}` — where
    `0 < (x − m)²` and `(x − m)² < 1` — the value `(x − a)(x − b)` stays in `(−1, 1)`.  That
    punctured interval, of Lebesgue measure `2`, is contained in the sublevel set, so the
    sublevel measure is `≥ 2`; equality forces the two roots to coincide. -/
theorem sublevelMeasure_quadraticGen_ge_two {a b : ℝ} (ha : a ∈ Set.Icc (-1 : ℝ) 1)
    (hb : b ∈ Set.Icc (-1 : ℝ) 1) :
    ENNReal.ofReal 2 ≤ sublevelMeasure (quadraticGen a b) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  have hD : (a - b) ^ 2 ≤ 4 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ a - b + 2)
      (by linarith : (0:ℝ) ≤ 2 - (a - b))]
  have hsub : Set.Ioo ((a + b) / 2 - 1) ((a + b) / 2 + 1) \ {(a + b) / 2}
      ⊆ sublevelSet (quadraticGen a b) := by
    intro x hx
    obtain ⟨hxIoo, hxne⟩ := hx
    rw [Set.mem_Ioo] at hxIoo
    rw [Set.mem_singleton_iff] at hxne
    have hxm : 2 * x - a - b ≠ 0 := fun h => hxne (by linarith)
    have hsqpos : 0 < (2 * x - a - b) ^ 2 :=
      (sq_nonneg _).lt_of_ne (Ne.symm (pow_ne_zero 2 hxm))
    simp only [sublevelSet, Set.mem_setOf_eq, quadraticGen_eval, abs_lt]
    refine ⟨?_, ?_⟩
    · nlinarith [hsqpos, hD]
    · nlinarith [mul_pos (by linarith [hxIoo.2] : (0:ℝ) < 2 - (2 * x - a - b))
        (by linarith [hxIoo.1] : (0:ℝ) < 2 + (2 * x - a - b)), sq_nonneg (a - b)]
  have hvol : volume (Set.Ioo ((a + b) / 2 - 1) ((a + b) / 2 + 1) \ {(a + b) / 2})
      = ENNReal.ofReal 2 := by
    rw [measure_diff_null (measure_singleton _), Real.volume_Ioo]
    congr 1; ring
  calc ENNReal.ofReal 2
      = volume (Set.Ioo ((a + b) / 2 - 1) ((a + b) / 2 + 1) \ {(a + b) / 2}) := hvol.symm
    _ ≤ sublevelMeasure (quadraticGen a b) := by
        unfold sublevelMeasure; exact measure_mono hsub

/-- **Exact sublevel measure of the general quadratic: `√((a − b)² + 4)`.**  Completing the
    square gives `(x − a)(x − b) = (x − m)² − ((a − b)/2)²` with `m = (a + b)/2`, so
    `{x : |f(x)| < 1}` is the interval `((a + b − s)/2, (a + b + s)/2)` with
    `s = √((a − b)² + 4)` (up to the single measure-zero centre `m` when the two roots are
    exactly `±1`), of length `s`.  This is a closed form for the *entire* degree-`2` spectrum
    in terms of the root separation `|a − b|`: it equals `2` when `a = b` and `2√2` when
    `{a, b} = {−1, 1}`, and interpolates monotonically between. -/
theorem sublevelMeasure_quadraticGen {a b : ℝ} (ha : a ∈ Set.Icc (-1 : ℝ) 1)
    (hb : b ∈ Set.Icc (-1 : ℝ) 1) :
    sublevelMeasure (quadraticGen a b) = ENNReal.ofReal (Real.sqrt ((a - b) ^ 2 + 4)) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  set s : ℝ := Real.sqrt ((a - b) ^ 2 + 4) with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = (a - b) ^ 2 + 4 := Real.sq_sqrt (by positivity)
  have hD : (a - b) ^ 2 ≤ 4 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ a - b + 2)
      (by linarith : (0:ℝ) ≤ 2 - (a - b))]
  have hup : sublevelSet (quadraticGen a b)
      ⊆ Set.Ioo ((a + b - s) / 2) ((a + b + s) / 2) := by
    intro x hx
    simp only [sublevelSet, Set.mem_setOf_eq, quadraticGen_eval, abs_lt] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hkey : (2 * x - a - b) ^ 2 < s ^ 2 := by nlinarith [hx2, hs2]
    rw [Set.mem_Ioo]
    refine ⟨?_, ?_⟩
    · nlinarith [hkey, hspos, sq_nonneg (2 * x - a - b + s)]
    · nlinarith [hkey, hspos, sq_nonneg (2 * x - a - b - s)]
  have hlo : Set.Ioo ((a + b - s) / 2) ((a + b + s) / 2) \ {(a + b) / 2}
      ⊆ sublevelSet (quadraticGen a b) := by
    intro x hx
    obtain ⟨hxIoo, hxne⟩ := hx
    rw [Set.mem_Ioo] at hxIoo
    rw [Set.mem_singleton_iff] at hxne
    have hxm : 2 * x - a - b ≠ 0 := fun h => hxne (by linarith)
    have hsqpos : 0 < (2 * x - a - b) ^ 2 :=
      (sq_nonneg _).lt_of_ne (Ne.symm (pow_ne_zero 2 hxm))
    have hkey : (2 * x - a - b) ^ 2 < s ^ 2 := by
      nlinarith [mul_pos (by linarith [hxIoo.2] : (0:ℝ) < a + b + s - 2 * x)
        (by linarith [hxIoo.1] : (0:ℝ) < 2 * x - (a + b - s)), hspos]
    simp only [sublevelSet, Set.mem_setOf_eq, quadraticGen_eval, abs_lt]
    refine ⟨?_, ?_⟩
    · nlinarith [hsqpos, hD]
    · nlinarith [hkey, hs2]
  have hvolIoo : volume (Set.Ioo ((a + b - s) / 2) ((a + b + s) / 2)) = ENNReal.ofReal s := by
    rw [Real.volume_Ioo]; congr 1; ring
  have hupM : sublevelMeasure (quadraticGen a b) ≤ ENNReal.ofReal s := by
    unfold sublevelMeasure
    calc volume (sublevelSet (quadraticGen a b))
        ≤ volume (Set.Ioo ((a + b - s) / 2) ((a + b + s) / 2)) := measure_mono hup
      _ = ENNReal.ofReal s := hvolIoo
  have hloM : ENNReal.ofReal s ≤ sublevelMeasure (quadraticGen a b) := by
    unfold sublevelMeasure
    calc ENNReal.ofReal s
        = volume (Set.Ioo ((a + b - s) / 2) ((a + b + s) / 2) \ {(a + b) / 2}) := by
            rw [measure_diff_null (measure_singleton _), hvolIoo]
      _ ≤ volume (sublevelSet (quadraticGen a b)) := measure_mono hlo
  exact le_antisymm hupM hloM

/-! ### The degree-`2` faithful infimum is exactly `2` -/

/-- Positive-degree faithful admissibility restricted to **degree exactly `2`**: a monic
    quadratic that splits into two real roots, both in `[-1,1]`. -/
def MonicRealRootedIn01Deg2 (f : Polynomial ℝ) : Prop :=
  MonicRealRootedIn01' f ∧ f.natDegree = 2

/-- The **degree-`2` faithful infimum** of sublevel-set measures. -/
noncomputable def sublevelInfDeg2 : ℝ≥0∞ :=
  ⨅ (f : Polynomial ℝ) (_ : MonicRealRootedIn01Deg2 f), sublevelMeasure f

/-- **Every faithful degree-`2` polynomial is `(X − a)(X − b)` with `a, b ∈ [-1,1]`**, so it
    has sublevel measure `≥ 2`.  A monic degree-`2` polynomial that splits completely has a
    root multiset of card `2 = {a, b}`, hence factors as `(X − a)(X − b)`
    (`prod_multiset_X_sub_C_of_monic_of_roots_card_eq`); admissibility puts `a, b ∈ [-1,1]`,
    and `sublevelMeasure_quadraticGen_ge_two` applies. -/
theorem two_le_sublevelMeasure_of_deg2 {f : Polynomial ℝ}
    (hf : MonicRealRootedIn01Deg2 f) : ENNReal.ofReal 2 ≤ sublevelMeasure f := by
  obtain ⟨hf', hdeg⟩ := hf
  have hc2 : f.roots.card = 2 := by rw [hf'.2, hdeg]
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hc2
  have hprod : (f.roots.map fun r => X - C r).prod = f :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hf'.1.1 hf'.2
  have hfeq : f = quadraticGen a b := by
    rw [hab] at hprod
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton] at hprod
    show f = (X - C a) * (X - C b)
    exact hprod.symm
  have ha : a ∈ Set.Icc (-1 : ℝ) 1 := hf'.1.2 a (by rw [hab]; simp)
  have hb : b ∈ Set.Icc (-1 : ℝ) 1 := hf'.1.2 b (by rw [hab]; simp)
  rw [hfeq]
  exact sublevelMeasure_quadraticGen_ge_two ha hb

/-- **The degree-`2` faithful infimum is `≤ 2`**, attained by the double root `X² = (X − 0)²`
    (`quadraticGen 0 0`), whose sublevel set `(−1, 1)` has measure `2`. -/
theorem sublevelInfDeg2_le_two : sublevelInfDeg2 ≤ ENNReal.ofReal 2 := by
  have hadm : MonicRealRootedIn01Deg2 (quadraticGen 0 0) :=
    ⟨quadraticGen_admissible' (by norm_num) (by norm_num), quadraticGen_natDegree 0 0⟩
  have hmeas : sublevelMeasure (quadraticGen 0 0) = ENNReal.ofReal 2 := by
    have hpow : quadraticGen 0 0 = (X - C (0 : ℝ)) ^ 2 := by rw [quadraticGen]; ring
    rw [hpow, sublevelMeasure_translate_pow 0 (by norm_num)]
  exact iInf_le_of_le (quadraticGen 0 0) (iInf_le_of_le hadm hmeas.le)

/-- **The degree-`2` faithful infimum is exactly `2`.**  Every monic quadratic splitting into
    two real roots in `[-1,1]` has sublevel measure `≥ 2` (`two_le_sublevelMeasure_of_deg2`),
    and the double root `X²` attains `2` (`sublevelInfDeg2_le_two`).  This pins the degree-`2`
    slice of the extremal spectrum: **the conjectured true infimum `2^(4/3) − 1 ≈ 1.52 < 2`
    cannot be realised by a quadratic** — small-measure witnesses require unboundedly many
    distinct roots (degree `→ ∞`), beyond this elementary degree-`2` analysis. -/
theorem sublevelInfDeg2_eq_two : sublevelInfDeg2 = ENNReal.ofReal 2 :=
  le_antisymm sublevelInfDeg2_le_two
    (le_iInf fun _ => le_iInf fun hf => two_le_sublevelMeasure_of_deg2 hf)

/-! ### The degree-`2` faithful supremum is exactly `2√2`

The dual of `sublevelInfDeg2_eq_two`.  The exact closed form `√((a − b)² + 4)`
(`sublevelMeasure_quadraticGen`) is **increasing** in the root separation `|a − b|`, which for
`a, b ∈ [-1,1]` is maximised at `|a − b| = 2` (roots `±1`).  Hence the degree-`2` sublevel
measure never exceeds `√(4 + 4) = √8 = 2√2`, and that bound is *attained* by `x² − 1`
(`quadraticGen 1 (-1)`).  So the degree-`2` restriction of the Erdős #1038 supremum is
**exactly `2√2`** — and it already matches the conjectured true supremum `2√2` (Tao 2025).
Unlike the infimum side, where the elementary degree-`2` value `2` is strictly above the true
infimum `2^(4/3) − 1`, on the supremum side the quadratic `x² − 1` is already a *global*
extremiser: the extremal witness is elementary even though the matching upper bound over *all*
degrees needs logarithmic potential theory. -/

/-- **Every faithful quadratic `(X − a)(X − b)` with `a, b ∈ [-1,1]` has sublevel measure
    `≤ 2√2`.**  The exact value `√((a − b)² + 4)` is bounded by `√8 = 2√2` because the root
    separation satisfies `(a − b)² ≤ 4`. -/
theorem sublevelMeasure_quadraticGen_le {a b : ℝ} (ha : a ∈ Set.Icc (-1 : ℝ) 1)
    (hb : b ∈ Set.Icc (-1 : ℝ) 1) :
    sublevelMeasure (quadraticGen a b) ≤ ENNReal.ofReal (2 * Real.sqrt 2) := by
  rw [sublevelMeasure_quadraticGen ha hb]
  apply ENNReal.ofReal_le_ofReal
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  have hD : (a - b) ^ 2 ≤ 4 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ a - b + 2)
      (by linarith : (0:ℝ) ≤ 2 - (a - b))]
  have h8 : (2:ℝ) * Real.sqrt 2 = Real.sqrt 8 := by
    rw [show (8:ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  rw [h8]
  exact Real.sqrt_le_sqrt (by linarith)

/-- **Every faithful degree-`2` polynomial has sublevel measure `≤ 2√2`.**  It factors as
    `(X − a)(X − b)` with `a, b ∈ [-1,1]` (as in `two_le_sublevelMeasure_of_deg2`), and
    `sublevelMeasure_quadraticGen_le` applies. -/
theorem sublevelMeasure_le_two_sqrt_two_of_deg2 {f : Polynomial ℝ}
    (hf : MonicRealRootedIn01Deg2 f) :
    sublevelMeasure f ≤ ENNReal.ofReal (2 * Real.sqrt 2) := by
  obtain ⟨hf', hdeg⟩ := hf
  have hc2 : f.roots.card = 2 := by rw [hf'.2, hdeg]
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hc2
  have hprod : (f.roots.map fun r => X - C r).prod = f :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hf'.1.1 hf'.2
  have hfeq : f = quadraticGen a b := by
    rw [hab] at hprod
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton] at hprod
    show f = (X - C a) * (X - C b)
    exact hprod.symm
  have ha : a ∈ Set.Icc (-1 : ℝ) 1 := hf'.1.2 a (by rw [hab]; simp)
  have hb : b ∈ Set.Icc (-1 : ℝ) 1 := hf'.1.2 b (by rw [hab]; simp)
  rw [hfeq]
  exact sublevelMeasure_quadraticGen_le ha hb

/-- The **degree-`2` faithful supremum** of sublevel-set measures. -/
noncomputable def sublevelSupDeg2 : ℝ≥0∞ :=
  ⨆ (f : Polynomial ℝ) (_ : MonicRealRootedIn01Deg2 f), sublevelMeasure f

/-- **The degree-`2` faithful supremum is `≤ 2√2`** (`sublevelMeasure_le_two_sqrt_two_of_deg2`
    applied under the supremum). -/
theorem sublevelSupDeg2_le_two_sqrt_two :
    sublevelSupDeg2 ≤ ENNReal.ofReal (2 * Real.sqrt 2) :=
  iSup_le fun _ => iSup_le fun hf => sublevelMeasure_le_two_sqrt_two_of_deg2 hf

/-- **`2√2 ≤` the degree-`2` faithful supremum**, attained by `x² − 1 = (X − 1)(X + 1)`
    (`quadraticGen 1 (-1)`), whose sublevel measure is `√((1 − (−1))² + 4) = √8 = 2√2`. -/
theorem le_sublevelSupDeg2 :
    ENNReal.ofReal (2 * Real.sqrt 2) ≤ sublevelSupDeg2 := by
  have hadm : MonicRealRootedIn01Deg2 (quadraticGen 1 (-1)) :=
    ⟨quadraticGen_admissible' (by norm_num) (by norm_num), quadraticGen_natDegree 1 (-1)⟩
  have hmeas : sublevelMeasure (quadraticGen 1 (-1)) = ENNReal.ofReal (2 * Real.sqrt 2) := by
    rw [sublevelMeasure_quadraticGen (by norm_num) (by norm_num)]
    congr 1
    rw [show ((1:ℝ) - (-1)) ^ 2 + 4 = 8 by norm_num, show (8:ℝ) = 2 ^ 2 * 2 by norm_num,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  exact le_iSup_of_le (quadraticGen 1 (-1)) (le_iSup_of_le hadm hmeas.ge)

/-- **The degree-`2` faithful supremum is exactly `2√2`.**  Every monic quadratic splitting
    into two real roots in `[-1,1]` has sublevel measure `≤ 2√2`
    (`sublevelSupDeg2_le_two_sqrt_two`), and `x² − 1` attains `2√2` (`le_sublevelSupDeg2`).
    This pins the degree-`2` slice of the extremal supremum: it is `2√2` — *already equal* to
    the conjectured true supremum, with the extremal polynomial `x² − 1` an explicit global
    extremiser (contrast the infimum, where the degree-`2` value `2` strictly exceeds the true
    infimum `2^(4/3) − 1`). -/
theorem sublevelSupDeg2_eq_two_sqrt_two :
    sublevelSupDeg2 = ENNReal.ofReal (2 * Real.sqrt 2) :=
  le_antisymm sublevelSupDeg2_le_two_sqrt_two le_sublevelSupDeg2

/-- **The degree-`2` faithful spectrum spans exactly `[2, 2√2]`.**  Combining
    `sublevelInfDeg2_eq_two` and `sublevelSupDeg2_eq_two_sqrt_two`: over all monic quadratics
    splitting into two roots in `[-1,1]`, the sublevel measure ranges from `2` (double root) to
    `2√2` (roots `±1`), both attained.  Equivalently the closed form `√((a − b)² + 4)` traverses
    `[2, 2√2]` as `|a − b|` runs over `[0, 2]`. -/
theorem sublevelInfDeg2_lt_sublevelSupDeg2 : sublevelInfDeg2 < sublevelSupDeg2 := by
  rw [sublevelInfDeg2_eq_two, sublevelSupDeg2_eq_two_sqrt_two]
  apply ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

end Erdos1038WIP01
