/-
# Sturm's Theorem Implies Descartes' Rule of Signs (OQ-01-OQ-03)

**Problem.** Show that Sturm's theorem implies Descartes' rule of signs.

## What this file does

Sturm's theorem (1829) computes the EXACT number of real roots of a squarefree
polynomial in an interval `(a, b]` as a difference of sign-variation counts of the
Sturm sequence:

  #{roots of p in (a, b]} = σ_p(a) − σ_p(b).

Descartes' rule of signs (1637) gives a coefficient-only UPPER BOUND on the number
of positive roots, with an even defect:

  #{positive roots of p} ≤ V(p)   and   V(p) − #{positive roots} is even,

where `V(p) = signChangesInCoeffs p` is the number of sign changes in the
coefficient sequence.

We make precise the sense in which the second statement is a *consequence* of the
first.  Applying Sturm on the interval `(0, B]` with `B` beyond every positive root
gives the exact positive-root count as a Sturm sign-variation drop
`σ_p(0) − σ_p(B)`.  Descartes' two laws then follow from three coefficient-comparison
facts that bridge the Sturm variation `σ_p(0)` to the coefficient variation `V(p)`:

  (B1)  `σ_p(0) ≤ V(p)`                      (the Sturm variation at 0 is at most V)
  (B2)  `Even (V(p) − σ_p(0))`               (and matches V in parity)
  (B3)  `Even (σ_p(B))`                       (the tail variation is even)

We isolate these in a `SturmReduction` structure and **prove**, by elementary
arithmetic, that any polynomial admitting such data satisfies Descartes' upper-bound
and parity laws *as stated in the gallery's base file* `DescartesRuleOfSigns`.  Thus
the genuinely analytic core is fully concentrated in Sturm's exact-count theorem plus
the comparison facts (B1)–(B3); the descent to Descartes is pure combinatorics.

The Sturm → root-count half is then **validated axiom-free** on linear polynomials
`X − c` (`c > 0`), reusing the gallery's axiom-free Sturm computations: there
`σ(0) − σ(B) = 1 = #{positive roots}` with no appeal to any axiom.

## Honest accounting

* The abstract reduction lemmas (`upper_bound_core`, `parity_core`) and the linear
  validation (`linear_sturm_count`, `linear_positiveRoots`) are fully machine-checked,
  axiom-free.
* `SturmReduction` packages the assumptions (B1)–(B3) together with Sturm's exact
  count as structure fields.  Per the project's axiom-integrity policy these fields
  are mathematical assumptions; obtaining them for a *general* polynomial requires
  Sturm's theorem (already axiomatized in the gallery as `sturm_exact_count_axiom`)
  and the standard Sturm/Descartes comparison theory, which we do not re-derive here.
  The result is therefore a *reduction*, not an unconditional proof of Descartes.
-/

import Proofs.DescartesRuleOfSigns
import Proofs.DescartesRuleOfSignsOQ02OQ01OQ02

namespace DescartesRuleOfSignsOQ01OQ03

open Polynomial
open DescartesRuleOfSigns (countPositiveRoots signChangesInCoeffs)
open SturmTheorem (sturmVariations sturm_linear_left sturm_linear_right)

/- ## § 1. Abstract reduction skeleton (verified, axiom-free)

The logical content of "Sturm's exact count ⟹ Descartes' bound + parity" is the
following pair of statements about natural numbers.  Read `pos` as the positive-root
count, `hi = σ(0)`, `lo = σ(B)`, and `bound = V(p)`. -/

/-- **Upper-bound core.**  If an exact count is realised as a difference `hi − lo`
of a non-increasing pair (`lo ≤ hi`) and the high end is dominated by `bound`, then
the count is dominated by `bound`. -/
theorem upper_bound_core {pos hi lo bound : ℕ}
    (hcount : pos = hi - lo) (hle : lo ≤ hi) (hbound : hi ≤ bound) :
    pos ≤ bound := by
  omega

/-- **Parity core.**  Under the same exact-count hypothesis, if the gap `bound − hi`
is even and the tail `lo` is even, then `bound − pos` is even.  (Working modulo 2,
`bound − pos = (bound − hi) + lo`.) -/
theorem parity_core {pos hi lo bound : ℕ}
    (hcount : pos = hi - lo) (hle : lo ≤ hi) (hbound : hi ≤ bound)
    (hgap : (bound - hi) % 2 = 0) (htail : lo % 2 = 0) :
    (bound - pos) % 2 = 0 := by
  omega

/- ## § 2. The Sturm-to-Descartes reduction data

For a fixed polynomial `p`, a `SturmReduction p` records the facts that connect
Sturm's sign-variation count to Descartes' coefficient sign-change count.  Each
field is an assumption: a general construction of this data is exactly Sturm's
theorem plus the classical comparison estimates. -/

/-- Bridge data witnessing that Descartes' rule for the positive roots of `p`
descends from Sturm's exact-count theorem.  `B` is any bound beyond every positive
root of `p`. -/
structure SturmReduction (p : ℝ[X]) where
  /-- A real bound past which `p` has no positive roots. -/
  B : ℝ
  /-- The bound is positive (so that `(0, B]` is a genuine interval of positives). -/
  hB : 0 < B
  /-- **Sturm's exact count on `(0, B]`.**  Every positive root lies in `(0, B]`, so
  the positive-root count equals the Sturm variation drop `σ(0) − σ(B)`. -/
  pos_eq : countPositiveRoots p = sturmVariations p 0 - sturmVariations p B
  /-- **Antitonicity of the Sturm count** (`lo ≤ hi`): `σ(B) ≤ σ(0)`. -/
  sturm_le : sturmVariations p B ≤ sturmVariations p 0
  /-- **(B1) Coefficient comparison:** the Sturm variation at `0` is at most the
  number of coefficient sign changes. -/
  bridge_bound : sturmVariations p 0 ≤ signChangesInCoeffs p
  /-- **(B2) Coefficient parity:** that gap is even. -/
  bridge_parity : Even (signChangesInCoeffs p - sturmVariations p 0)
  /-- **(B3) Tail parity:** the Sturm variation at the right end is even. -/
  tail_even : Even (sturmVariations p B)

/-- **Descartes' upper bound, derived from Sturm.**  For any polynomial admitting
Sturm-reduction data, the number of positive roots is at most the number of
coefficient sign changes. -/
theorem descartes_upper_bound_via_sturm {p : ℝ[X]} (d : SturmReduction p) :
    countPositiveRoots p ≤ signChangesInCoeffs p :=
  upper_bound_core d.pos_eq d.sturm_le d.bridge_bound

/-- **Descartes' parity law, derived from Sturm.**  The defect between coefficient
sign changes and positive roots is even. -/
theorem descartes_parity_via_sturm {p : ℝ[X]} (d : SturmReduction p) :
    Even (signChangesInCoeffs p - countPositiveRoots p) := by
  rw [Nat.even_iff]
  have hgap : (signChangesInCoeffs p - sturmVariations p 0) % 2 = 0 :=
    Nat.even_iff.mp d.bridge_parity
  have htail : (sturmVariations p d.B) % 2 = 0 := Nat.even_iff.mp d.tail_even
  exact parity_core d.pos_eq d.sturm_le d.bridge_bound hgap htail

/-- **Descartes' rule of signs (combined), derived from Sturm.**  There is an even
overshoot `2k` of coefficient sign changes above the positive-root count. -/
theorem descartes_rule_via_sturm {p : ℝ[X]} (d : SturmReduction p) :
    ∃ k : ℕ, countPositiveRoots p + 2 * k = signChangesInCoeffs p := by
  have hbound := descartes_upper_bound_via_sturm d
  obtain ⟨m, hm⟩ := descartes_parity_via_sturm d
  exact ⟨m, by omega⟩

/- ## § 2½. Computing the two-term coefficient sign-change count (verified, axiom-free)

The gallery's base file only ever *axiomatised* concrete sign-change counts
(`example_x2_minus_1_sign_changes` and friends are `axiom` declarations, because the
`countSignChanges` definition filters over `Fin n × Fin n` with a classically-decided
predicate that `decide` cannot reduce).  Here we discharge the length-2 case by hand:
a two-term real sequence whose entries have opposite signs has exactly one sign change.
This lets the linear validation below assume *nothing* about the coefficient count. -/

/-- **Sign-change count of a two-term sequence.**  If the two entries of `f : Fin 2 → ℝ`
have opposite signs (`f 0 * f 1 < 0`) then `f` has exactly one sign change.  Proved by
exhibiting the single qualifying index pair `(0, 1)`; axiom-free. -/
theorem countSignChanges_two {f : Fin 2 → ℝ} (h : f 0 * f 1 < 0) :
    DescartesRuleOfSigns.countSignChanges f = 1 := by
  have h0 : f 0 ≠ 0 := fun he => by rw [he, zero_mul] at h; exact lt_irrefl 0 h
  have h1 : f 1 ≠ 0 := fun he => by rw [he, mul_zero] at h; exact lt_irrefl 0 h
  unfold DescartesRuleOfSigns.countSignChanges
  rw [Finset.card_eq_one]
  refine ⟨(0, 1), ?_⟩
  ext ⟨i, j⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    decide_eq_true_eq, DescartesRuleOfSigns.SignChangeBetween,
    DescartesRuleOfSigns.oppositeSign, Prod.mk.injEq]
  constructor
  · rintro ⟨hij, -, -, -, -⟩
    fin_cases i <;> fin_cases j <;>
      first
        | exact ⟨rfl, rfl⟩
        | exact absurd hij (by decide)
  · rintro ⟨rfl, rfl⟩
    refine ⟨by decide, h0, h1, ?_, h⟩
    intro k hk0 hk1
    fin_cases k <;>
      first
        | exact absurd hk0 (by decide)
        | exact absurd hk1 (by decide)

/- ## § 2¾. Three-term coefficient sign-change counts (verified, axiom-free)

Quadratics `a·X² + b·X + c` produce a length-3 coefficient sequence.  For the
degree-2 examples the gallery's base file *axiomatised* (`example_x2_minus_1_sign_changes`,
`example_x2_plus_1_sign_changes`) the middle coefficient of the coefficient sequence is
`0`, so the count is governed entirely by the signs of the two outer entries:

* opposite outer signs (`f 0 · f 2 < 0`) — exactly one sign change (across the zero);
* equal or vanishing outer signs (`0 ≤ f 0 · f 2`) — no sign change at all.

We prove both, extending `countSignChanges_two` from `Fin 2` to the `Fin 3`
middle-zero pattern.  These discharge the base file's two quadratic sign-change
axioms with fully machine-checked, axiom-free evaluations (see § 4). -/

/-- **One sign change across a zero.**  If `f : Fin 3 → ℝ` has a zero middle entry
(`f 1 = 0`) and outer entries of opposite sign (`f 0 · f 2 < 0`), then `f` has exactly
one sign change — the pair `(0, 2)` jumping over the vanishing middle term.  Axiom-free. -/
theorem countSignChanges_three_mid_zero_pos {f : Fin 3 → ℝ}
    (hmid : f 1 = 0) (h : f 0 * f 2 < 0) :
    DescartesRuleOfSigns.countSignChanges f = 1 := by
  have h0 : f 0 ≠ 0 := fun he => by rw [he, zero_mul] at h; exact lt_irrefl 0 h
  have h2 : f 2 ≠ 0 := fun he => by rw [he, mul_zero] at h; exact lt_irrefl 0 h
  unfold DescartesRuleOfSigns.countSignChanges
  rw [Finset.card_eq_one]
  refine ⟨(0, 2), ?_⟩
  ext ⟨i, j⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    decide_eq_true_eq, DescartesRuleOfSigns.SignChangeBetween,
    DescartesRuleOfSigns.oppositeSign, Prod.mk.injEq]
  constructor
  · rintro ⟨hij, hi0, hj0, -, -⟩
    have hi1 : i ≠ 1 := by rintro rfl; exact hi0 hmid
    have hj1 : j ≠ 1 := by rintro rfl; exact hj0 hmid
    fin_cases i <;> fin_cases j <;>
      first
        | exact ⟨rfl, rfl⟩
        | (exfalso; revert hij hi1 hj1; decide)
  · rintro ⟨rfl, rfl⟩
    refine ⟨by decide, h0, h2, ?_, h⟩
    intro k hk0 hk2
    fin_cases k <;>
      first
        | exact hmid
        | exact absurd hk0 (by decide)
        | exact absurd hk2 (by decide)

/-- **No sign change with a zero middle and non-opposite outer entries.**  If `f 1 = 0`
and the outer entries do not have strictly opposite signs (`0 ≤ f 0 · f 2` — covering
equal signs *and* a vanishing outer entry), then `f` has no sign change.  Axiom-free. -/
theorem countSignChanges_three_mid_zero_zero {f : Fin 3 → ℝ}
    (hmid : f 1 = 0) (h : 0 ≤ f 0 * f 2) :
    DescartesRuleOfSigns.countSignChanges f = 0 := by
  unfold DescartesRuleOfSigns.countSignChanges
  rw [Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  rintro ⟨i, j⟩ -
  simp only [decide_eq_true_eq, DescartesRuleOfSigns.SignChangeBetween,
    DescartesRuleOfSigns.oppositeSign]
  rintro ⟨hij, hi0, hj0, -, hopp⟩
  have hi1 : i ≠ 1 := by rintro rfl; exact hi0 hmid
  have hj1 : j ≠ 1 := by rintro rfl; exact hj0 hmid
  have hij02 : i = 0 ∧ j = 2 := by
    fin_cases i <;> fin_cases j <;>
      first
        | exact ⟨rfl, rfl⟩
        | (exfalso; revert hij hi1 hj1; decide)
  obtain ⟨rfl, rfl⟩ := hij02
  exact absurd hopp (not_lt.mpr h)

/- ## § 2⅞. Three-term counts with a NON-zero middle (verified, axiom-free)

The `§ 2¾` lemmas handle a *zero* middle coefficient (the quadratics the base
file happened to axiomatise, `X² ± 1`).  A general quadratic `a·X² + b·X + c`
with `b ≠ 0` has a nonzero middle entry, and then the count is governed by the
two *adjacent* pairs `(0,1)` and `(1,2)` — the jump-over pair `(0,2)` is
impossible once the middle entry is nonzero.  The count is therefore
`[f 0·f 1 < 0] + [f 1·f 2 < 0]`, taking each of the values `0, 1, 2`.  We record
the four sign patterns explicitly, which — together with `§ 2¾` — give the
complete `Fin 3` sign-change count for every real length-3 sequence.  The value
`2` (both adjacent pairs alternate) is genuinely new: a zero middle can never
produce two sign changes, so this is exactly the quadratic case Descartes' bound
allows to be *tight* (two coefficient sign changes, up to two positive roots). -/

/-- **Two sign changes (strictly alternating).**  If both adjacent pairs of a
`Fin 3 → ℝ` sequence have opposite signs (`f 0·f 1 < 0` and `f 1·f 2 < 0`, e.g.
the pattern `+ − +`), then `f` has exactly two sign changes — the pairs `(0,1)`
and `(1,2)`.  Axiom-free.  This is the maximal count for a length-3 sequence and
is unreachable with a zero middle entry. -/
theorem countSignChanges_three_alternating {f : Fin 3 → ℝ}
    (h01 : f 0 * f 1 < 0) (h12 : f 1 * f 2 < 0) :
    DescartesRuleOfSigns.countSignChanges f = 2 := by
  have hf0 : f 0 ≠ 0 := fun he => by rw [he, zero_mul] at h01; exact lt_irrefl 0 h01
  have hf1 : f 1 ≠ 0 := fun he => by rw [he, mul_zero] at h01; exact lt_irrefl 0 h01
  have hf2 : f 2 ≠ 0 := fun he => by rw [he, mul_zero] at h12; exact lt_irrefl 0 h12
  unfold DescartesRuleOfSigns.countSignChanges
  rw [Finset.card_eq_two]
  refine ⟨(0, 1), (1, 2), by decide, ?_⟩
  ext ⟨i, j⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, decide_eq_true_eq, DescartesRuleOfSigns.SignChangeBetween,
    DescartesRuleOfSigns.oppositeSign, Prod.mk.injEq]
  constructor
  · rintro ⟨hij, _, _, hbtw, _⟩
    fin_cases i <;> fin_cases j <;>
      first
        | exact Or.inl ⟨rfl, rfl⟩
        | exact Or.inr ⟨rfl, rfl⟩
        | exact absurd (hbtw 1 (by decide) (by decide)) hf1
        | exact absurd hij (by decide)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine ⟨by decide, hf0, hf1, ?_, h01⟩
      intro k hk0 hk1
      fin_cases k <;>
        first
          | exact absurd hk0 (by decide)
          | exact absurd hk1 (by decide)
    · refine ⟨by decide, hf1, hf2, ?_, h12⟩
      intro k hk1 hk2
      fin_cases k <;>
        first
          | exact absurd hk1 (by decide)
          | exact absurd hk2 (by decide)

/-- **One sign change, left pair (nonzero middle).**  If the first adjacent pair
alternates (`f 0·f 1 < 0`) but the second does not (`0 ≤ f 1·f 2`), then `f` has
exactly one sign change — the pair `(0,1)`. -/
theorem countSignChanges_three_mid_ne_left {f : Fin 3 → ℝ}
    (h01 : f 0 * f 1 < 0) (h12 : 0 ≤ f 1 * f 2) :
    DescartesRuleOfSigns.countSignChanges f = 1 := by
  have hf0 : f 0 ≠ 0 := fun he => by rw [he, zero_mul] at h01; exact lt_irrefl 0 h01
  have hf1 : f 1 ≠ 0 := fun he => by rw [he, mul_zero] at h01; exact lt_irrefl 0 h01
  unfold DescartesRuleOfSigns.countSignChanges
  rw [Finset.card_eq_one]
  refine ⟨(0, 1), ?_⟩
  ext ⟨i, j⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    decide_eq_true_eq, DescartesRuleOfSigns.SignChangeBetween,
    DescartesRuleOfSigns.oppositeSign, Prod.mk.injEq]
  constructor
  · rintro ⟨hij, _, _, hbtw, hopp⟩
    fin_cases i <;> fin_cases j <;>
      first
        | exact ⟨rfl, rfl⟩
        | exact absurd (hbtw 1 (by decide) (by decide)) hf1
        | exact absurd hopp (not_lt.mpr h12)
        | exact absurd hij (by decide)
  · rintro ⟨rfl, rfl⟩
    refine ⟨by decide, hf0, hf1, ?_, h01⟩
    intro k hk0 hk1
    fin_cases k <;>
      first
        | exact absurd hk0 (by decide)
        | exact absurd hk1 (by decide)

/-- **One sign change, right pair (nonzero middle).**  If the second adjacent
pair alternates (`f 1·f 2 < 0`) but the first does not (`0 ≤ f 0·f 1`), then `f`
has exactly one sign change — the pair `(1,2)`. -/
theorem countSignChanges_three_mid_ne_right {f : Fin 3 → ℝ}
    (h01 : 0 ≤ f 0 * f 1) (h12 : f 1 * f 2 < 0) :
    DescartesRuleOfSigns.countSignChanges f = 1 := by
  have hf1 : f 1 ≠ 0 := fun he => by rw [he, zero_mul] at h12; exact lt_irrefl 0 h12
  have hf2 : f 2 ≠ 0 := fun he => by rw [he, mul_zero] at h12; exact lt_irrefl 0 h12
  unfold DescartesRuleOfSigns.countSignChanges
  rw [Finset.card_eq_one]
  refine ⟨(1, 2), ?_⟩
  ext ⟨i, j⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    decide_eq_true_eq, DescartesRuleOfSigns.SignChangeBetween,
    DescartesRuleOfSigns.oppositeSign, Prod.mk.injEq]
  constructor
  · rintro ⟨hij, _, _, hbtw, hopp⟩
    fin_cases i <;> fin_cases j <;>
      first
        | exact ⟨rfl, rfl⟩
        | exact absurd (hbtw 1 (by decide) (by decide)) hf1
        | exact absurd hopp (not_lt.mpr h01)
        | exact absurd hij (by decide)
  · rintro ⟨rfl, rfl⟩
    refine ⟨by decide, hf1, hf2, ?_, h12⟩
    intro k hk1 hk2
    fin_cases k <;>
      first
        | exact absurd hk1 (by decide)
        | exact absurd hk2 (by decide)

/-- **No sign change (nonzero middle, both pairs non-alternating).**  If the
middle entry is nonzero (`f 1 ≠ 0`) and neither adjacent pair has strictly
opposite signs (`0 ≤ f 0·f 1` and `0 ≤ f 1·f 2`, e.g. the pattern `+ + +`), then
`f` has no sign change.  Axiom-free. -/
theorem countSignChanges_three_mid_ne_zero {f : Fin 3 → ℝ}
    (hmid : f 1 ≠ 0) (h01 : 0 ≤ f 0 * f 1) (h12 : 0 ≤ f 1 * f 2) :
    DescartesRuleOfSigns.countSignChanges f = 0 := by
  unfold DescartesRuleOfSigns.countSignChanges
  rw [Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  rintro ⟨i, j⟩ -
  simp only [decide_eq_true_eq, DescartesRuleOfSigns.SignChangeBetween,
    DescartesRuleOfSigns.oppositeSign]
  rintro ⟨hij, _, _, hbtw, hopp⟩
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd (hbtw 1 (by decide) (by decide)) hmid
      | exact absurd hopp (not_lt.mpr h01)
      | exact absurd hopp (not_lt.mpr h12)
      | exact absurd hij (by decide)

/- ## § 3. Axiom-free validation of the Sturm half on linear polynomials

For `p = X − c` with `c > 0`, the gallery already proves (axiom-free) that the
Sturm sign-variation count is `1` to the left of `c` and `0` to the right.  We use
this to verify the Sturm exact-count identity `#{positive roots} = σ(0) − σ(B)`
for `p`, with no axioms whatsoever. -/

section Linear

variable (c : ℝ)

/-- For `c > 0` the polynomial `X − c` has exactly one positive root. -/
theorem linear_positiveRoots (hc : 0 < c) :
    countPositiveRoots (X - C c) = 1 := by
  have hne : (X - C c : ℝ[X]) ≠ 0 := (monic_X_sub_C c).ne_zero
  unfold countPositiveRoots
  rw [if_neg hne, roots_X_sub_C, Multiset.filter_singleton]
  simp [hc]

/-- **Sturm exact count, verified for `X − c` (`c > 0`), axiom-free.**  With the
right endpoint `B = c + 1` beyond the root, the positive-root count equals the Sturm
variation drop `σ(0) − σ(B) = 1 − 0`. -/
theorem linear_sturm_count (hc : 0 < c) :
    countPositiveRoots (X - C c)
      = sturmVariations (X - C c) 0 - sturmVariations (X - C c) (c + 1) := by
  have h0 : sturmVariations (X - C c) 0 = 1 := sturm_linear_left c 0 hc
  have hB : sturmVariations (X - C c) (c + 1) = 0 :=
    sturm_linear_right c (c + 1) (by linarith)
  have hp : countPositiveRoots (X - C c) = 1 := linear_positiveRoots c hc
  omega

/-- **Coefficient sign-change count of `X − c` (`c > 0`), computed axiom-free.**  The
coefficient sequence of `X − c` is `[1, −c]` (leading coefficient `1`, constant term
`−c`), whose two entries have opposite signs — exactly one sign change.  This discharges
the coefficient fact that `linearReduction` previously took as an unproved hypothesis. -/
theorem linear_signChanges (hc : 0 < c) :
    signChangesInCoeffs (X - C c) = 1 := by
  have hne : (X - C c : ℝ[X]) ≠ 0 := (monic_X_sub_C c).ne_zero
  unfold signChangesInCoeffs
  rw [dif_neg hne, natDegree_X_sub_C]
  apply countSignChanges_two
  have e0 : DescartesRuleOfSigns.coeffSequence (X - C c) 1 0 = 1 := by
    simp [DescartesRuleOfSigns.coeffSequence, coeff_sub, coeff_X_one]
  have e1 : DescartesRuleOfSigns.coeffSequence (X - C c) 1 1 = -c := by
    simp [DescartesRuleOfSigns.coeffSequence, coeff_sub, coeff_X_zero, coeff_C]
  rw [e0, e1]
  simpa using hc

/-- The full `SturmReduction` data for `X − c` (`c > 0`).  The Sturm half is
discharged axiom-free; the coefficient-comparison facts (B1)–(B3) are now *also*
discharged axiom-free, using the computed count `V(X − c) = 1` (`linear_signChanges`).
For this polynomial the reduction therefore carries **no standing assumption**. -/
def linearReduction (hc : 0 < c) :
    SturmReduction (X - C c) where
  B := c + 1
  hB := by linarith
  pos_eq := linear_sturm_count c hc
  sturm_le := by
    have h0 : sturmVariations (X - C c) 0 = 1 := sturm_linear_left c 0 hc
    have hB : sturmVariations (X - C c) (c + 1) = 0 :=
      sturm_linear_right c (c + 1) (by linarith)
    omega
  bridge_bound := by
    have h0 : sturmVariations (X - C c) 0 = 1 := sturm_linear_left c 0 hc
    have hV : signChangesInCoeffs (X - C c) = 1 := linear_signChanges c hc
    omega
  bridge_parity := by
    rw [Nat.even_iff]
    have h0 : sturmVariations (X - C c) 0 = 1 := sturm_linear_left c 0 hc
    have hV : signChangesInCoeffs (X - C c) = 1 := linear_signChanges c hc
    omega
  tail_even := by
    rw [Nat.even_iff]
    have hB : sturmVariations (X - C c) (c + 1) = 0 :=
      sturm_linear_right c (c + 1) (by linarith)
    omega

/-- End-to-end check: feeding the linear data through the reduction reproduces
Descartes' upper bound for `X − c`, now **unconditionally** — no coefficient count is
assumed, only `c > 0`. -/
theorem linear_descartes_bound (hc : 0 < c) :
    countPositiveRoots (X - C c) ≤ signChangesInCoeffs (X - C c) :=
  descartes_upper_bound_via_sturm (linearReduction c hc)

end Linear

/- ## § 4. De-axiomatizing the base file's quadratic sign-change examples

The gallery's base file `DescartesRuleOfSigns` states the two concrete counts
`signChangesInCoeffs (X² − 1) = 1` and `signChangesInCoeffs (X² + 1) = 0` as `axiom`
declarations (the classically-decided filter in `countSignChanges` does not reduce under
`decide`).  With the `Fin 3` machinery of § 2¾ we now discharge both **axiom-free**,
showing those base axioms are removable. -/

section Quadratic

/-- **`X² − 1` has exactly one coefficient sign change, computed axiom-free.**  The
coefficient sequence is `[1, 0, −1]`: a zero middle with opposite outer signs, hence one
sign change.  This is exactly the statement of the base file's `example_x2_minus_1_sign_changes`
axiom, now proved. -/
theorem x2_minus_1_signChanges :
    signChangesInCoeffs (X ^ 2 - 1 : ℝ[X]) = 1 := by
  have hne : (X ^ 2 - 1 : ℝ[X]) ≠ 0 := by
    intro h
    have : (X ^ 2 - 1 : ℝ[X]).coeff 2 = 0 := by rw [h]; simp
    simp [coeff_sub, coeff_X_pow, coeff_one] at this
  have hdeg : (X ^ 2 - 1 : ℝ[X]).natDegree = 2 := by compute_degree!
  unfold signChangesInCoeffs
  rw [dif_neg hne, hdeg]
  apply countSignChanges_three_mid_zero_pos
  · simp [DescartesRuleOfSigns.coeffSequence, coeff_sub, coeff_X_pow, coeff_one]
  · have e0 : DescartesRuleOfSigns.coeffSequence (X ^ 2 - 1 : ℝ[X]) 2 0 = 1 := by
      simp [DescartesRuleOfSigns.coeffSequence, coeff_sub, coeff_X_pow, coeff_one]
    have e2 : DescartesRuleOfSigns.coeffSequence (X ^ 2 - 1 : ℝ[X]) 2 2 = -1 := by
      simp [DescartesRuleOfSigns.coeffSequence, coeff_sub, coeff_X_pow, coeff_one]
    rw [e0, e2]; norm_num

/-- **`X² + 1` has no coefficient sign change, computed axiom-free.**  The coefficient
sequence is `[1, 0, 1]`: a zero middle with equal outer signs, hence no sign change.  This
is exactly the statement of the base file's `example_x2_plus_1_sign_changes` axiom, now
proved. -/
theorem x2_plus_1_signChanges :
    signChangesInCoeffs (X ^ 2 + 1 : ℝ[X]) = 0 := by
  have hne : (X ^ 2 + 1 : ℝ[X]) ≠ 0 := by
    intro h
    have : (X ^ 2 + 1 : ℝ[X]).coeff 2 = 0 := by rw [h]; simp
    simp [coeff_add, coeff_X_pow, coeff_one] at this
  have hdeg : (X ^ 2 + 1 : ℝ[X]).natDegree = 2 := by compute_degree!
  unfold signChangesInCoeffs
  rw [dif_neg hne, hdeg]
  apply countSignChanges_three_mid_zero_zero
  · simp [DescartesRuleOfSigns.coeffSequence, coeff_add, coeff_X_pow, coeff_one]
  · have e0 : DescartesRuleOfSigns.coeffSequence (X ^ 2 + 1 : ℝ[X]) 2 0 = 1 := by
      simp [DescartesRuleOfSigns.coeffSequence, coeff_add, coeff_X_pow, coeff_one]
    have e2 : DescartesRuleOfSigns.coeffSequence (X ^ 2 + 1 : ℝ[X]) 2 2 = 1 := by
      simp [DescartesRuleOfSigns.coeffSequence, coeff_add, coeff_X_pow, coeff_one]
    rw [e0, e2]; norm_num

/-- **`X² − X + 1` has two coefficient sign changes, computed axiom-free.**  The
coefficient sequence is `[1, −1, 1]` (leading to constant): a strictly
alternating pattern `+ − +` with nonzero middle, hence two sign changes — the
maximal count, unreachable by the middle-zero `§ 2¾` lemmas.  This exercises the
new `countSignChanges_three_alternating` and shows Descartes' bound is *attained*
at the coefficient level (two sign changes allow up to two positive roots). -/
theorem x2_minus_x_plus_1_signChanges :
    signChangesInCoeffs (X ^ 2 - X + 1 : ℝ[X]) = 2 := by
  have hne : (X ^ 2 - X + 1 : ℝ[X]) ≠ 0 := by
    intro h
    have : (X ^ 2 - X + 1 : ℝ[X]).coeff 2 = 0 := by rw [h]; simp
    simp [coeff_add, coeff_sub, coeff_X_pow, coeff_X, coeff_one] at this
  have hdeg : (X ^ 2 - X + 1 : ℝ[X]).natDegree = 2 := by compute_degree!
  unfold signChangesInCoeffs
  rw [dif_neg hne, hdeg]
  apply countSignChanges_three_alternating
  · have e0 : DescartesRuleOfSigns.coeffSequence (X ^ 2 - X + 1 : ℝ[X]) 2 0 = 1 := by
      simp [DescartesRuleOfSigns.coeffSequence, coeff_add, coeff_sub, coeff_X_pow,
        coeff_X, coeff_one]
    have e1 : DescartesRuleOfSigns.coeffSequence (X ^ 2 - X + 1 : ℝ[X]) 2 1 = -1 := by
      simp [DescartesRuleOfSigns.coeffSequence, coeff_add, coeff_sub, coeff_X_pow,
        coeff_X, coeff_one]
    rw [e0, e1]; norm_num
  · have e1 : DescartesRuleOfSigns.coeffSequence (X ^ 2 - X + 1 : ℝ[X]) 2 1 = -1 := by
      simp [DescartesRuleOfSigns.coeffSequence, coeff_add, coeff_sub, coeff_X_pow,
        coeff_X, coeff_one]
    have e2 : DescartesRuleOfSigns.coeffSequence (X ^ 2 - X + 1 : ℝ[X]) 2 2 = 1 := by
      simp [DescartesRuleOfSigns.coeffSequence, coeff_add, coeff_sub, coeff_X_pow,
        coeff_X, coeff_one]
    rw [e1, e2]; norm_num

end Quadratic

/- ## § 5. General `Fin n` vanishing of the sign-change count (verified, axiom-free)

The length-2 and length-3 lemmas above resolve small cases by enumerating index
pairs.  One implication, however, holds for *every* length `n`: a sequence whose
entries all share a sign (all `≥ 0`, or all `≤ 0`) has **no** sign change, because
`SignChangeBetween` demands a strictly-negative product `f i · f j < 0`.  These are
the general (arbitrary-`n`) companions of `countSignChanges_two` and
`countSignChanges_three_mid_zero_zero`, and they yield the "no Descartes sign
variation from one-signed coefficients" fact for polynomials of *any* degree
(`signChangesInCoeffs_eq_zero_of_coeff_nonneg`) — the coefficient-side statement
behind "a polynomial with nonnegative coefficients has no positive roots". -/

/-- **A nonnegative sequence has no sign change.**  For any length `n`, if every
entry of `f : Fin n → ℝ` is `≥ 0` then `countSignChanges f = 0`: a sign change
requires a strictly-negative product `f i · f j`, impossible when both factors are
nonnegative.  Axiom-free, general in `n`. -/
theorem countSignChanges_eq_zero_of_nonneg {n : ℕ} {f : Fin n → ℝ}
    (h : ∀ i, 0 ≤ f i) : DescartesRuleOfSigns.countSignChanges f = 0 := by
  unfold DescartesRuleOfSigns.countSignChanges
  rw [Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  rintro ⟨i, j⟩ -
  simp only [decide_eq_true_eq, DescartesRuleOfSigns.SignChangeBetween,
    DescartesRuleOfSigns.oppositeSign]
  rintro ⟨-, -, -, -, hopp⟩
  exact absurd hopp (not_lt.mpr (mul_nonneg (h i) (h j)))

/-- **A nonpositive sequence has no sign change.**  Dual of
`countSignChanges_eq_zero_of_nonneg`: if every entry of `f : Fin n → ℝ` is `≤ 0`
then `countSignChanges f = 0` (a product of two nonpositive reals is nonnegative).
Axiom-free, general in `n`. -/
theorem countSignChanges_eq_zero_of_nonpos {n : ℕ} {f : Fin n → ℝ}
    (h : ∀ i, f i ≤ 0) : DescartesRuleOfSigns.countSignChanges f = 0 := by
  unfold DescartesRuleOfSigns.countSignChanges
  rw [Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  rintro ⟨i, j⟩ -
  simp only [decide_eq_true_eq, DescartesRuleOfSigns.SignChangeBetween,
    DescartesRuleOfSigns.oppositeSign]
  rintro ⟨-, -, -, -, hopp⟩
  have hprod : 0 ≤ f i * f j := by
    have := mul_nonneg (neg_nonneg.mpr (h i)) (neg_nonneg.mpr (h j))
    rwa [neg_mul_neg] at this
  exact absurd hopp (not_lt.mpr hprod)

/-- **A polynomial with nonnegative coefficients has no coefficient sign change.**
`signChangesInCoeffs p = 0` whenever every coefficient of `p` is `≥ 0`.  Immediate
from `countSignChanges_eq_zero_of_nonneg` applied to the coefficient sequence
`coeffSequence p p.natDegree` (`i ↦ p.coeff (natDegree − i) ≥ 0`); the `p = 0`
branch of `signChangesInCoeffs` is `0` by definition.  Classical reading: a real
polynomial whose coefficients are all one sign exhibits no Descartes sign variation
(and hence, via Descartes' rule, no positive root). -/
theorem signChangesInCoeffs_eq_zero_of_coeff_nonneg {p : ℝ[X]}
    (h : ∀ k, 0 ≤ p.coeff k) :
    DescartesRuleOfSigns.signChangesInCoeffs p = 0 := by
  unfold DescartesRuleOfSigns.signChangesInCoeffs
  split
  · rfl
  · exact countSignChanges_eq_zero_of_nonneg fun i => h _

end DescartesRuleOfSignsOQ01OQ03
