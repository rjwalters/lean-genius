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

end Erdos1038WIP01
