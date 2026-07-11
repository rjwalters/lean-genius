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

/- ## § 6. The sharp general `Fin n` bound: `V ≤ n − 1`, attained by alternation
   (verified, axiom-free)

Section 5 handled the *one-signed* extreme (`V = 0`).  Here we settle the opposite
extreme for arbitrary length `n`.  Two facts, both general in `n` and axiom-free:

* **Upper bound (unconditional).**  `countSignChanges f ≤ n − 1` for *every*
  `f : Fin n → ℝ`.  The point is that a sign-change pair `(i, j)` is determined by
  its *left* index `i`: if `(i, j)` and `(i, j′)` were both sign changes with
  `j < j′`, then `f j ≠ 0` (from the first) contradicts "all entries strictly
  between `i` and `j′` vanish" (from the second).  So `i ↦ (i, j)` is injective and
  `i < j < n` forces `i ≤ n − 2`; there are at most `n − 1` such left indices.

* **Sharpness (attained).**  A *nowhere-zero, strictly sign-alternating* sequence
  (`f i ≠ 0` for all `i`, and `f i · f j < 0` whenever `j = i + 1`) has
  `countSignChanges f = n − 1` exactly.  Because no entry vanishes, the "all-between
  zero" clause forces every sign-change pair to be *adjacent* (`j = i + 1`), and
  every adjacent pair alternates, so the sign changes biject with the `n − 1`
  adjacent index pairs.  This generalises `countSignChanges_three_alternating`
  (`n = 3`, value `2`) to all lengths, and shows the upper bound above is sharp.

Together these say: at the coefficient level Descartes' variation count `V(p)` never
exceeds the degree and is realised at the degree by a fully alternating coefficient
pattern (corollary `signChangesInCoeffs_le_natDegree`). -/

/-- **Unconditional upper bound on the sign-change count.**  For every real sequence
`f : Fin n → ℝ`, `countSignChanges f ≤ n − 1`.  Proof: the left index `i` of a
sign-change pair `(i, j)` determines the pair (a second `j′ > j` would put the
nonzero `f j` strictly between `i` and `j′`, contradicting the all-between-zero
clause), so `(i, j) ↦ i.val` is injective from the sign-change set into
`{0, …, n − 2}`.  Axiom-free, general in `n`. -/
theorem countSignChanges_le {n : ℕ} (f : Fin n → ℝ) :
    DescartesRuleOfSigns.countSignChanges f ≤ n - 1 := by
  unfold DescartesRuleOfSigns.countSignChanges
  rw [← Finset.card_range (n - 1)]
  apply Finset.card_le_card_of_injOn (fun p => p.1.val)
  · -- MapsTo: the left index of any sign-change pair lies in `{0, …, n-2}`.
    intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      decide_eq_true_eq, DescartesRuleOfSigns.SignChangeBetween] at hp
    obtain ⟨hlt, -, -, -, -⟩ := hp
    have hij : p.1.val < p.2.val := Fin.lt_def.mp hlt
    have hj : p.2.val < n := p.2.isLt
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  · -- InjOn: the left index determines the pair.
    intro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      decide_eq_true_eq, DescartesRuleOfSigns.SignChangeBetween,
      DescartesRuleOfSigns.oppositeSign] at hp hq
    obtain ⟨hplt, -, hp2ne, hpbtw, -⟩ := hp
    obtain ⟨hqlt, -, hq2ne, hqbtw, -⟩ := hq
    have hp1 : p.1 = q.1 := Fin.ext hpq
    have hkey : p.2.val = q.2.val := by
      rcases lt_trichotomy p.2.val q.2.val with h | h | h
      · exact absurd (hqbtw p.2 (hp1 ▸ hplt) (Fin.lt_def.mpr h)) hp2ne
      · exact h
      · exact absurd (hpbtw q.2 (hp1 ▸ hqlt) (Fin.lt_def.mpr h)) hq2ne
    exact Prod.ext_iff.mpr ⟨hp1, Fin.ext hkey⟩

/-- **The upper bound is sharp: alternation attains `n − 1`.**  If `f : Fin n → ℝ`
is nowhere zero (`hnz`) and every adjacent pair alternates in sign
(`halt : ∀ i j, j = i + 1 ⟹ f i · f j < 0`), then `countSignChanges f = n − 1`.
Because no entry vanishes, the all-between-zero clause of a sign change forces the
pair to be adjacent, so the sign changes biject with the `n − 1` adjacent pairs.
Axiom-free, general in `n`; generalises `countSignChanges_three_alternating`. -/
theorem countSignChanges_alternating {n : ℕ} {f : Fin n → ℝ}
    (hnz : ∀ i, f i ≠ 0)
    (halt : ∀ i j : Fin n, j.val = i.val + 1 → f i * f j < 0) :
    DescartesRuleOfSigns.countSignChanges f = n - 1 := by
  -- Every sign-change pair is adjacent: no zeros means nothing can lie between.
  have adj : ∀ i j : Fin n,
      DescartesRuleOfSigns.SignChangeBetween f i j → j.val = i.val + 1 := by
    intro i j h
    unfold DescartesRuleOfSigns.SignChangeBetween at h
    obtain ⟨hij, -, -, hbtw, -⟩ := h
    have hlt : i.val < j.val := Fin.lt_def.mp hij
    by_contra hne
    have hgap : i.val + 1 < j.val := by omega
    have hk : i.val + 1 < n := lt_trans hgap j.isLt
    exact hnz _ (hbtw ⟨i.val + 1, hk⟩ (Fin.lt_def.mpr (Nat.lt_succ_self _))
      (Fin.lt_def.mpr hgap))
  unfold DescartesRuleOfSigns.countSignChanges
  rw [show n - 1 = (Finset.range (n - 1)).card from (Finset.card_range _).symm]
  refine Finset.card_bij' (fun p _ => p.1.val)
    (fun m hm => (⟨m, by have := Finset.mem_range.mp hm; omega⟩,
                  ⟨m + 1, by have := Finset.mem_range.mp hm; omega⟩))
    ?_ ?_ ?_ ?_
  · -- left index of a sign-change pair lands in `range (n-1)`
    rintro ⟨i, j⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hp
    have hadj := adj i j hp
    have hj : j.val < n := j.isLt
    have hlt : i.val < n - 1 := by omega
    exact Finset.mem_range.mpr hlt
  · -- each adjacent pair is a genuine sign change
    intro m hm
    have hmr : m < n - 1 := Finset.mem_range.mp hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
      DescartesRuleOfSigns.SignChangeBetween, DescartesRuleOfSigns.oppositeSign]
    refine ⟨Fin.lt_def.mpr (Nat.lt_succ_self _), hnz _, hnz _, ?_, halt _ _ rfl⟩
    intro k hk1 hk2
    have h1 : m < k.val := Fin.lt_def.mp hk1
    have h2 : k.val < m + 1 := Fin.lt_def.mp hk2
    omega
  · -- round trip: pair ↦ left index ↦ pair
    rintro ⟨i, j⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hp
    have hadj := adj i j hp
    exact Prod.ext_iff.mpr ⟨Fin.ext rfl, Fin.ext hadj.symm⟩
  · -- round trip: index ↦ pair ↦ index
    intro m _
    rfl

/-- **Descartes' variation count is bounded by the degree.**  For any nonzero real
polynomial `p`, the number of coefficient sign changes is at most `natDegree p`.
Immediate from `countSignChanges_le` on the length-`(natDegree p + 1)` coefficient
sequence.  Classical reading: `V(p) ≤ deg p`, with equality attainable when the
coefficients strictly alternate (`countSignChanges_alternating`). -/
theorem signChangesInCoeffs_le_natDegree {p : ℝ[X]} (hp : p ≠ 0) :
    DescartesRuleOfSigns.signChangesInCoeffs p ≤ p.natDegree := by
  unfold DescartesRuleOfSigns.signChangesInCoeffs
  rw [dif_neg hp]
  have h := countSignChanges_le (DescartesRuleOfSigns.coeffSequence p p.natDegree)
  simpa using h

/- ## § 7. Invariances of the sign-change count (verified, axiom-free)

The classical theory of Descartes' rule exploits *symmetries* of the coefficient
sign-change count `V`, each of which leaves the positive-root count untouched and so
is forced to leave `V` untouched too:

* **Scaling.**  Multiplying a polynomial by a nonzero constant `c` rescales every
  coefficient by `c`; the positive roots are unchanged.  Correspondingly the
  sequence-level count `countSignChanges` is invariant under `f ↦ c · f` for any
  `c ≠ 0` — the sign-change predicate sees only the product `(c f i)(c f j) = c² f i f j`
  (and `c² > 0`) together with the non-vanishing of the entries, both preserved by a
  nonzero rescaling.  Negation (`c = −1`, flipping every sign) is a special case.

* **Reversal.**  Reading the coefficient list backwards corresponds to the reciprocal
  polynomial `Xⁿ p(1/X)`, whose positive roots are the reciprocals of those of `p` —
  again the same count.  At the sequence level, precomposing with `Fin.rev` preserves
  `countSignChanges`: a sign change of the reversed sequence at `(i, j)` is exactly a
  sign change of the original at `(rev j, rev i)`.

We prove the two sequence-level invariances (`countSignChanges_const_smul`,
`countSignChanges_comp_rev`), record negation as a corollary, and lift the scaling law
to polynomials (`signChangesInCoeffs_C_mul`).  All axiom-free. -/

/-- **Scaling invariance.**  Multiplying every entry of `f : Fin n → ℝ` by a nonzero
constant `c` does not change the number of sign changes: a sign change depends only on
`(c f i)(c f j) = c² · f i f j` (with `c² > 0`) and on the non-vanishing of the entries,
both preserved by a nonzero rescaling.  Axiom-free, general in `n`. -/
theorem countSignChanges_const_smul {n : ℕ} {c : ℝ} (hc : c ≠ 0) (f : Fin n → ℝ) :
    DescartesRuleOfSigns.countSignChanges (fun i => c * f i)
      = DescartesRuleOfSigns.countSignChanges f := by
  have hcc : (0 : ℝ) < c * c := by
    rcases lt_or_gt_of_ne hc with h | h
    · exact mul_pos_of_neg_of_neg h h
    · exact mul_pos h h
  unfold DescartesRuleOfSigns.countSignChanges
  congr 1
  ext ⟨i, j⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
    DescartesRuleOfSigns.SignChangeBetween, DescartesRuleOfSigns.oppositeSign]
  constructor
  · rintro ⟨hij, hi, hj, hbtw, hopp⟩
    refine ⟨hij, ?_, ?_, ?_, ?_⟩
    · exact fun h => hi (by rw [h, mul_zero])
    · exact fun h => hj (by rw [h, mul_zero])
    · intro k hk1 hk2
      exact (mul_eq_zero.mp (hbtw k hk1 hk2)).resolve_left hc
    · have e : c * f i * (c * f j) = c * c * (f i * f j) := by ring
      rw [e] at hopp
      by_contra hcon
      push_neg at hcon
      exact absurd hopp (not_lt.mpr (mul_nonneg hcc.le hcon))
  · rintro ⟨hij, hi, hj, hbtw, hopp⟩
    refine ⟨hij, mul_ne_zero hc hi, mul_ne_zero hc hj, ?_, ?_⟩
    · intro k hk1 hk2
      rw [hbtw k hk1 hk2, mul_zero]
    · have e : c * f i * (c * f j) = c * c * (f i * f j) := by ring
      rw [e]
      exact mul_neg_of_pos_of_neg hcc hopp

/-- **Negation invariance.**  Flipping the sign of every entry preserves the count —
the `c = −1` case of `countSignChanges_const_smul`.  Classically, `p ↦ −p` (indeed any
negative rescaling) leaves Descartes' sign-change count unchanged.  Axiom-free. -/
theorem countSignChanges_neg {n : ℕ} (f : Fin n → ℝ) :
    DescartesRuleOfSigns.countSignChanges (fun i => -f i)
      = DescartesRuleOfSigns.countSignChanges f := by
  have h := countSignChanges_const_smul (c := -1) (by norm_num) f
  simpa using h

/-- **Reversal invariance.**  Precomposing a sequence with `Fin.rev` (reading it
backwards) preserves the number of sign changes.  A sign change of the reversed
sequence `fun i => f i.rev` at `(i, j)` corresponds bijectively to a sign change of `f`
at `(j.rev, i.rev)`: reversal is order-reversing (`i < j ↔ j.rev < i.rev`), carries the
non-vanishing along, and — being an involution — maps the "all strictly between vanish"
clause across.  Axiom-free, general in `n`.  Classically this is the reciprocal-
polynomial symmetry `p ↦ Xⁿ p(1/X)`, which reciprocates the positive roots and hence
leaves both the root count and `V(p)` unchanged. -/
theorem countSignChanges_comp_rev {n : ℕ} (f : Fin n → ℝ) :
    DescartesRuleOfSigns.countSignChanges (fun i => f i.rev)
      = DescartesRuleOfSigns.countSignChanges f := by
  unfold DescartesRuleOfSigns.countSignChanges
  refine Finset.card_bij' (fun p _ => (p.2.rev, p.1.rev))
    (fun q _ => (q.2.rev, q.1.rev)) ?_ ?_ ?_ ?_
  · -- forward: a sign change of the reversed sequence maps to one of `f`
    rintro ⟨i, j⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
      DescartesRuleOfSigns.SignChangeBetween, DescartesRuleOfSigns.oppositeSign] at hp ⊢
    obtain ⟨hij, hi, hj, hbtw, hopp⟩ := hp
    refine ⟨Fin.rev_lt_rev.mpr hij, hj, hi, ?_, ?_⟩
    · intro k hk1 hk2
      have := hbtw k.rev (Fin.lt_rev_iff.mp hk2) (Fin.rev_lt_iff.mp hk1)
      rwa [Fin.rev_rev] at this
    · rw [mul_comm]; exact hopp
  · -- backward: a sign change of `f` maps to one of the reversed sequence
    rintro ⟨i, j⟩ hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
      DescartesRuleOfSigns.SignChangeBetween, DescartesRuleOfSigns.oppositeSign,
      Fin.rev_rev] at hq ⊢
    obtain ⟨hij, hi, hj, hbtw, hopp⟩ := hq
    refine ⟨Fin.rev_lt_rev.mpr hij, hj, hi, ?_, ?_⟩
    · intro k hk1 hk2
      exact hbtw k.rev (Fin.lt_rev_iff.mp hk2) (Fin.rev_lt_iff.mp hk1)
    · rw [mul_comm]; exact hopp
  · -- round trip `(i,j) ↦ (rev j, rev i) ↦ (i,j)`
    rintro ⟨i, j⟩ _
    simp only [Fin.rev_rev]
  · -- round trip in the other direction
    rintro ⟨i, j⟩ _
    simp only [Fin.rev_rev]

/-- **Scaling invariance for polynomials.**  Multiplying a polynomial by a nonzero
constant leaves Descartes' coefficient sign-change count unchanged: `V(c · p) = V(p)`
for `c ≠ 0`.  The coefficient sequence of `C c * p` is `c` times that of `p`, the degree
is unchanged, and `countSignChanges_const_smul` finishes.  Axiom-free. -/
theorem signChangesInCoeffs_C_mul {c : ℝ} (hc : c ≠ 0) (p : ℝ[X]) :
    DescartesRuleOfSigns.signChangesInCoeffs (C c * p)
      = DescartesRuleOfSigns.signChangesInCoeffs p := by
  unfold DescartesRuleOfSigns.signChangesInCoeffs
  by_cases hp : p = 0
  · subst hp; simp
  · have hCp : C c * p ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hc) hp
    rw [dif_neg hCp, dif_neg hp]
    have hdeg : (C c * p).natDegree = p.natDegree := natDegree_C_mul hc
    rw [hdeg]
    have hcoe : DescartesRuleOfSigns.coeffSequence (C c * p) p.natDegree
        = fun i => c * DescartesRuleOfSigns.coeffSequence p p.natDegree i := by
      funext i
      simp [DescartesRuleOfSigns.coeffSequence, coeff_C_mul]
    rw [hcoe]
    exact countSignChanges_const_smul hc _

/-- **Negation invariance for polynomials.**  Negating a polynomial leaves Descartes'
coefficient sign-change count unchanged: `V(−p) = V(p)`.  This is the `c = −1` case of
the scaling invariance `signChangesInCoeffs_C_mul` (since `−p = C(−1)·p`), and the
polynomial-level companion of the sequence lemma `countSignChanges_neg`.  Classically it
reflects that `p` and `−p` have the *same* roots — in particular the same positive roots —
so Descartes' bound is identical for both.  Axiom-free. -/
theorem signChangesInCoeffs_neg (p : ℝ[X]) :
    DescartesRuleOfSigns.signChangesInCoeffs (-p)
      = DescartesRuleOfSigns.signChangesInCoeffs p := by
  have h := signChangesInCoeffs_C_mul (c := -1) (by norm_num) p
  rwa [show (C (-1 : ℝ)) * p = -p by rw [map_neg, map_one, neg_one_mul]] at h

/-- **Scaling invariance, `•`-form.**  The `smul` counterpart of
`signChangesInCoeffs_C_mul`: scaling a polynomial by a nonzero real `c` via the
module action leaves Descartes' coefficient sign-change count unchanged,
`V(c • p) = V(p)`.  Immediate from `smul_eq_C_mul` and `signChangesInCoeffs_C_mul`.
Axiom-free. -/
theorem signChangesInCoeffs_smul {c : ℝ} (hc : c ≠ 0) (p : ℝ[X]) :
    DescartesRuleOfSigns.signChangesInCoeffs (c • p)
      = DescartesRuleOfSigns.signChangesInCoeffs p := by
  rw [smul_eq_C_mul]
  exact signChangesInCoeffs_C_mul hc p

/-- **Descartes' bound is invariant under monic normalisation.**  For `p ≠ 0`,
rescaling by the inverse leading coefficient — which produces a *monic* polynomial
with the same roots — leaves the sign-change count unchanged:
`V(leadingCoeff(p)⁻¹ • p) = V(p)`.  Thus Descartes' rule may be applied to the monic
normalisation of any polynomial without affecting the bound.  The `c = leadingCoeff⁻¹`
case of `signChangesInCoeffs_smul` (`leadingCoeff p ≠ 0` since `p ≠ 0`).  Axiom-free. -/
theorem signChangesInCoeffs_leadingCoeff_inv_smul {p : ℝ[X]} (hp : p ≠ 0) :
    DescartesRuleOfSigns.signChangesInCoeffs (p.leadingCoeff⁻¹ • p)
      = DescartesRuleOfSigns.signChangesInCoeffs p :=
  signChangesInCoeffs_smul (inv_ne_zero (leadingCoeff_ne_zero.mpr hp)) p

/- ## § 8. Polynomial-level sharpness of Descartes' bound (verified, axiom-free)

`signChangesInCoeffs_le_natDegree` shows `V(p) ≤ deg p` for every nonzero `p`.  The
companion fact is that this bound is *attained*: a polynomial whose coefficient
sequence is nowhere zero and strictly sign-alternating has `V(p) = deg p` exactly.
This lifts the sequence-level sharpness `countSignChanges_alternating` to the
polynomial level, so the pair "`V(p) ≤ deg p`, and equality for a fully alternating
coefficient pattern" is now stated directly for polynomials.  Classical reading:
Descartes' upper bound cannot be improved in general — for every degree `d` there is
a degree-`d` polynomial with `d` positive real roots realising `V(p) = d`. -/

/-- **The degree bound is sharp: a strictly alternating coefficient pattern attains
`V(p) = deg p`.**  If every coefficient `p.coeff k` for `k ≤ natDegree p` is nonzero
(`hnz`) and consecutive coefficients have opposite signs
(`halt : p.coeff k · p.coeff (k+1) < 0` for `k < natDegree p`), then the coefficient
sign-change count equals the degree.  Direct application of the sequence-level
`countSignChanges_alternating` to `coeffSequence p (natDegree p)` (whose entries read
`p.coeff (natDegree p − i)`, so the sequence is nowhere zero and adjacent-alternating).
The polynomial-level companion of `signChangesInCoeffs_le_natDegree`; axiom-free. -/
theorem signChangesInCoeffs_eq_natDegree_of_alternating {p : ℝ[X]} (hp : p ≠ 0)
    (hnz : ∀ k, k ≤ p.natDegree → p.coeff k ≠ 0)
    (halt : ∀ k, k < p.natDegree → p.coeff k * p.coeff (k + 1) < 0) :
    DescartesRuleOfSigns.signChangesInCoeffs p = p.natDegree := by
  unfold DescartesRuleOfSigns.signChangesInCoeffs
  rw [dif_neg hp]
  have h := countSignChanges_alternating
    (f := DescartesRuleOfSigns.coeffSequence p p.natDegree)
    (by -- nowhere zero: every entry is a coefficient of index `≤ natDegree`
      intro i
      simp only [DescartesRuleOfSigns.coeffSequence]
      exact hnz _ (Nat.sub_le _ _))
    (by -- adjacent alternation: entries `i` and `i+1` read consecutive coefficients
      intro i j hj
      simp only [DescartesRuleOfSigns.coeffSequence]
      have hjle : j.val ≤ p.natDegree := Nat.lt_succ_iff.mp j.isLt
      set k := p.natDegree - j.val with hk
      have e1 : p.natDegree - i.val = k + 1 := by omega
      have hklt : k < p.natDegree := by omega
      rw [e1, mul_comm]
      exact halt k hklt)
  simpa using h

/-- **`X³ − X² + X − 1` has three coefficient sign changes, computed axiom-free.**
The coefficient sequence is `[1, −1, 1, −1]` (leading to constant): a strictly
alternating length-4 pattern, so `V = 3 = deg`, the maximal (Descartes-tight) count
for a cubic — the polynomial `(X−1)(X²+1)` indeed has its lone positive root at the
count parity permits.  First concrete degree-3 validation in this file, obtained by
feeding the four coefficient facts through the general
`signChangesInCoeffs_eq_natDegree_of_alternating`. -/
theorem x3_minus_x2_plus_x_minus_1_signChanges :
    signChangesInCoeffs (X ^ 3 - X ^ 2 + X - 1 : ℝ[X]) = 3 := by
  set p : ℝ[X] := X ^ 3 - X ^ 2 + X - 1 with hp_def
  have c0 : p.coeff 0 = -1 := by
    simp [hp_def, coeff_add, coeff_sub, coeff_X_pow, coeff_X, coeff_one]
  have c1 : p.coeff 1 = 1 := by
    simp [hp_def, coeff_add, coeff_sub, coeff_X_pow, coeff_X, coeff_one]
  have c2 : p.coeff 2 = -1 := by
    simp [hp_def, coeff_add, coeff_sub, coeff_X_pow, coeff_X, coeff_one]
  have c3 : p.coeff 3 = 1 := by
    simp [hp_def, coeff_add, coeff_sub, coeff_X_pow, coeff_X, coeff_one]
  have hne : p ≠ 0 := by intro h; rw [h] at c3; simp at c3
  have hdeg : p.natDegree = 3 := by rw [hp_def]; compute_degree!
  rw [signChangesInCoeffs_eq_natDegree_of_alternating hne ?_ ?_, hdeg]
  · rw [hdeg]; intro k hk; interval_cases k <;> norm_num [c0, c1, c2, c3]
  · rw [hdeg]; intro k hk; interval_cases k <;> norm_num [c0, c1, c2, c3]

/- ## § 9. Reversal invariance at the polynomial level (verified, axiom-free)

`countSignChanges_comp_rev` (§ 7) shows the *sequence-level* sign-change count is
invariant under reading a sequence backwards.  The polynomial operation this
implements is coefficient reversal `p ↦ p.reverse`, classically the reciprocal
substitution `x ↦ 1/x` (`p.reverse = Xⁿ · p(1/X)` up to the leading power), which
reciprocates the positive roots and so must leave `V(p)` unchanged.  When the
constant term is nonzero (`p.coeff 0 ≠ 0`) there is no trailing-degree collapse, the
degree is preserved (`natDegree p.reverse = natDegree p`), and the reversed
coefficient sequence is *exactly* the original read backwards
(`coeffSequence p.reverse = coeffSequence p ∘ Fin.rev`).  The sequence-level lemma
then delivers `V(p.reverse) = V(p)` directly. -/

/-- **Reversal invariance for polynomials.**  For a polynomial with nonzero constant
term (`p.coeff 0 ≠ 0`), coefficient reversal preserves Descartes' sign-change count:
`V(p.reverse) = V(p)`.  The nonzero constant term keeps `natTrailingDegree p = 0`, so
`natDegree p.reverse = natDegree p` and `coeffSequence p.reverse` is
`coeffSequence p ∘ Fin.rev`; the sequence-level `countSignChanges_comp_rev` closes it.
Classically the reciprocal-polynomial symmetry `x ↦ 1/x`, which permutes the positive
roots and hence leaves the count invariant.  Axiom-free. -/
theorem signChangesInCoeffs_reverse {p : ℝ[X]} (h0 : p.coeff 0 ≠ 0) :
    DescartesRuleOfSigns.signChangesInCoeffs p.reverse
      = DescartesRuleOfSigns.signChangesInCoeffs p := by
  have hp : p ≠ 0 := fun h => h0 (by rw [h]; simp)
  have hrev : p.reverse ≠ 0 := fun h => hp (reverse_eq_zero.mp h)
  have htd : p.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (Or.inr h0)
  have hdeg : p.reverse.natDegree = p.natDegree := by
    rw [reverse_natDegree, htd, Nat.sub_zero]
  unfold DescartesRuleOfSigns.signChangesInCoeffs
  rw [dif_neg hrev, dif_neg hp, hdeg]
  have hseq : DescartesRuleOfSigns.coeffSequence p.reverse p.natDegree
      = fun i => DescartesRuleOfSigns.coeffSequence p p.natDegree i.rev := by
    funext i
    simp only [DescartesRuleOfSigns.coeffSequence]
    rw [coeff_reverse]
    congr 1
    have hrevval : (i.rev).val = p.natDegree - i.val := by rw [Fin.val_rev]; omega
    rw [revAt_le (Nat.sub_le _ _), hrevval]
  rw [hseq]
  exact countSignChanges_comp_rev _

end DescartesRuleOfSignsOQ01OQ03
