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

/-- **A polynomial with nonpositive coefficients has no coefficient sign change.**
Dual of `signChangesInCoeffs_eq_zero_of_coeff_nonneg`: `signChangesInCoeffs p = 0`
whenever every coefficient of `p` is `≤ 0`.  Immediate from
`countSignChanges_eq_zero_of_nonpos` applied to the coefficient sequence
`coeffSequence p p.natDegree`; the `p = 0` branch is `0` by definition.  This
supplies the polynomial-level companion of the sequence-level `nonpos` lemma,
matching the existing `nonneg` pair.  Classical reading: a real polynomial whose
coefficients are all `≤ 0` (equivalently `−p` has nonnegative coefficients)
exhibits no Descartes sign variation, hence — via Descartes' rule — no positive
root. -/
theorem signChangesInCoeffs_eq_zero_of_coeff_nonpos {p : ℝ[X]}
    (h : ∀ k, p.coeff k ≤ 0) :
    DescartesRuleOfSigns.signChangesInCoeffs p = 0 := by
  unfold DescartesRuleOfSigns.signChangesInCoeffs
  split
  · rfl
  · exact countSignChanges_eq_zero_of_nonpos fun i => h _

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

/-- **Reversal invariance for polynomials.**  For a polynomial with nonzero
constant term (`p.coeff 0 ≠ 0`, so `0` is not a root and the reversal keeps the
same degree), Descartes' coefficient sign-change count is unchanged by reversing
the coefficient list: `V(reverse p) = V(p)`.  This lifts the sequence-level
`countSignChanges_comp_rev` to polynomials, completing the invariance trio
alongside scaling (`signChangesInCoeffs_C_mul`) and negation
(`signChangesInCoeffs_neg`).  The coefficient sequence of `reverse p` is exactly
that of `p` read backwards (`Fin.rev`): `(reverse p).coeff (d − i) = p.coeff i`
via `coeff_reverse` and `revAt_le`, which is `coeffSequence p d (i.rev)`.
Classically this is the reciprocal-polynomial symmetry `p ↦ Xⁿ p(1/X)`, whose
positive roots are the reciprocals of those of `p` — the same count.  Axiom-free. -/
theorem signChangesInCoeffs_reverse {p : ℝ[X]} (h0 : p.coeff 0 ≠ 0) :
    DescartesRuleOfSigns.signChangesInCoeffs (reverse p)
      = DescartesRuleOfSigns.signChangesInCoeffs p := by
  have hp : p ≠ 0 := fun h => h0 (by rw [h]; simp)
  have hrev0 : reverse p ≠ 0 := fun h => hp (reverse_eq_zero.mp h)
  have htd : p.natTrailingDegree = 0 := Nat.le_zero.mp (natTrailingDegree_le_of_ne_zero h0)
  have hdeg : (reverse p).natDegree = p.natDegree := by
    rw [reverse_natDegree, htd, Nat.sub_zero]
  unfold DescartesRuleOfSigns.signChangesInCoeffs
  rw [dif_neg hrev0, dif_neg hp, hdeg]
  have hcoe : DescartesRuleOfSigns.coeffSequence (reverse p) p.natDegree
      = fun i => DescartesRuleOfSigns.coeffSequence p p.natDegree i.rev := by
    funext i
    have hi : i.val ≤ p.natDegree := Nat.lt_succ_iff.mp i.isLt
    simp only [DescartesRuleOfSigns.coeffSequence]
    rw [coeff_reverse, revAt_le (Nat.sub_le _ _), Fin.val_rev]
    congr 1
    omega
  rw [hcoe]
  exact countSignChanges_comp_rev _

/-- **Reversal and negation together.**  Combining `signChangesInCoeffs_reverse`
with `signChangesInCoeffs_neg`: reversing *and* negating a polynomial with nonzero
constant term leaves Descartes' sign-change count fixed, `V(reverse (−p)) = V(p)`.
Axiom-free. -/
theorem signChangesInCoeffs_reverse_neg {p : ℝ[X]} (h0 : p.coeff 0 ≠ 0) :
    DescartesRuleOfSigns.signChangesInCoeffs (reverse (-p))
      = DescartesRuleOfSigns.signChangesInCoeffs p := by
  have h0' : (-p).coeff 0 ≠ 0 := by rw [coeff_neg]; exact neg_ne_zero.mpr h0
  rw [signChangesInCoeffs_reverse h0', signChangesInCoeffs_neg]

/-- **Reversal and scaling together.**  Combining `signChangesInCoeffs_reverse` with
`signChangesInCoeffs_smul`: reversing a nonzero-scaled polynomial with nonzero constant
term leaves Descartes' sign-change count fixed, `V(reverse (c • p)) = V(p)` for `c ≠ 0`
and `p.coeff 0 ≠ 0`.  Completes the invariance combinations alongside
`signChangesInCoeffs_reverse_neg`: the count is stable under the full group generated by
reversal and nonzero scaling.  Axiom-free. -/
theorem signChangesInCoeffs_reverse_smul {c : ℝ} (hc : c ≠ 0) {p : ℝ[X]}
    (h0 : p.coeff 0 ≠ 0) :
    DescartesRuleOfSigns.signChangesInCoeffs (reverse (c • p))
      = DescartesRuleOfSigns.signChangesInCoeffs p := by
  have h0' : (c • p).coeff 0 ≠ 0 := by
    rw [coeff_smul, smul_eq_mul]; exact mul_ne_zero hc h0
  rw [signChangesInCoeffs_reverse h0', signChangesInCoeffs_smul hc]

/-- **Invariance under a pointwise-positive weight.**  Multiplying a sequence entrywise by
*any* strictly positive weight `g i > 0` leaves the number of sign changes unchanged: the
non-vanishing pattern is preserved (a positive factor cannot create or destroy a zero) and each
`oppositeSign` test `g i·f i · (g j·f j) = (g i·g j)·(f i·f j) < 0` has the same truth value as
`f i·f j < 0` because `g i·g j > 0`.  This strictly generalises the positive case of
`countSignChanges_const_smul` (constant weight `g ≡ c`) to a *per-index* positive weight, and is
the combinatorial engine behind dilation invariance `signChangesInCoeffs_comp_C_mul_X`.
Axiom-free, general in `n`. -/
theorem countSignChanges_mul_pos {n : ℕ} {g : Fin n → ℝ} (hg : ∀ i, 0 < g i) (f : Fin n → ℝ) :
    DescartesRuleOfSigns.countSignChanges (fun i => g i * f i)
      = DescartesRuleOfSigns.countSignChanges f := by
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
      exact (mul_eq_zero.mp (hbtw k hk1 hk2)).resolve_left (hg k).ne'
    · have e : g i * f i * (g j * f j) = g i * g j * (f i * f j) := by ring
      rw [e] at hopp
      by_contra hcon
      push_neg at hcon
      exact absurd hopp (not_lt.mpr (mul_nonneg (mul_pos (hg i) (hg j)).le hcon))
  · rintro ⟨hij, hi, hj, hbtw, hopp⟩
    refine ⟨hij, mul_ne_zero (hg i).ne' hi, mul_ne_zero (hg j).ne' hj, ?_, ?_⟩
    · intro k hk1 hk2
      rw [hbtw k hk1 hk2, mul_zero]
    · have e : g i * f i * (g j * f j) = g i * g j * (f i * f j) := by ring
      rw [e]
      exact mul_neg_of_pos_of_neg (mul_pos (hg i) (hg j)) hopp

/-- **Positive-dilation invariance: `V(p(cX)) = V(p)` for `c > 0`.**  Descartes' sign-change
count is unchanged by a positive rescaling of the variable `p(X) ↦ p(cX)`.  Indeed
`(p(cX)).coeff k = c^k · p.coeff k` (`comp_C_mul_X_coeff`), so the coefficient sequence is the
original scaled entrywise by the strictly positive weights `c^{d-i}`; `countSignChanges_mul_pos`
then leaves the count fixed.  Classically this reflects that `p(cX)` has positive roots `r/c` —
the positive roots of `p` scaled by `1/c > 0` — so both the positive-root count and its Descartes
bound `V` are preserved.  This completes the invariance family alongside scaling
(`signChangesInCoeffs_smul`), negation (`signChangesInCoeffs_neg`), and reversal
(`signChangesInCoeffs_reverse`).  Axiom-free. -/
theorem signChangesInCoeffs_comp_C_mul_X {c : ℝ} (hc : 0 < c) (p : ℝ[X]) :
    DescartesRuleOfSigns.signChangesInCoeffs (p.comp (C c * X))
      = DescartesRuleOfSigns.signChangesInCoeffs p := by
  unfold DescartesRuleOfSigns.signChangesInCoeffs
  by_cases hp : p = 0
  · subst hp; simp
  · have hc0 : c ≠ 0 := hc.ne'
    have hcomp0 : p.comp (C c * X) ≠ 0 := by
      rw [Ne, comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_of_ne_zero hc0)]
      exact hp
    have hdeg : (p.comp (C c * X)).natDegree = p.natDegree := by
      rw [natDegree_comp, natDegree_C_mul_X c hc0, mul_one]
    rw [dif_neg hcomp0, dif_neg hp, hdeg]
    have hcoe : DescartesRuleOfSigns.coeffSequence (p.comp (C c * X)) p.natDegree
        = fun i => c ^ (p.natDegree - i.val) *
            DescartesRuleOfSigns.coeffSequence p p.natDegree i := by
      funext i
      simp only [DescartesRuleOfSigns.coeffSequence]
      rw [comp_C_mul_X_coeff]
      ring
    rw [hcoe]
    exact countSignChanges_mul_pos (fun i => pow_pos hc _) _

/- ## § 9. The reflection `p(X) ↦ p(−X)` and Descartes for negative roots
   (verified, axiom-free)

The invariances of § 7 all *fix* the positive-root count and hence `V`.  The
reflection `X ↦ −X` is different: it sends the positive roots of `p` to the
*negative* roots and vice versa, and it is the transformation underlying the
second half of Descartes' rule (`#{negative roots of p} ≤ V(p(−X))`).  Unlike a
positive dilation, `p(−X)` alternates the signs of the coefficients
(`(p(−X)).coeff k = (−1)^k · p.coeff k`), so it does *not* preserve `V`.

Instead there is a sharp **complementarity**.  For a *nowhere-zero* coefficient
pattern (no interior gaps), every one of the `n − 1` adjacent gaps is a sign
change of exactly one of `p`, `p(−X)`: a persistence of sign in `p` becomes a
change in `p(−X)` and vice versa.  Hence

    V(p) + V(p(−X)) = deg p              (all coefficients `0 … deg p` nonzero).

This is the exact combinatorial identity behind "Descartes bounds the positive
*and* the negative roots": for a full (gap-free) polynomial the two Descartes
counts partition the degree.  We prove it first at the level of sequences
(`countSignChanges_alternate_add`) and then transport it to polynomials. -/

/-- For a **nowhere-zero** sequence, a sign change can only occur between *adjacent*
indices (no zeros can sit between to be skipped over), so the sign-change set is the
set of adjacent pairs `(i, i+1)` with `f i · f (i+1) < 0`. -/
theorem countSignChanges_nowhere_zero {n : ℕ} {f : Fin n → ℝ} (hnz : ∀ i, f i ≠ 0) :
    DescartesRuleOfSigns.countSignChanges f
      = (Finset.univ.filter (fun p : Fin n × Fin n =>
          p.2.val = p.1.val + 1 ∧ f p.1 * f p.2 < 0)).card := by
  classical
  unfold DescartesRuleOfSigns.countSignChanges
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
  constructor
  · intro hsc
    obtain ⟨hij, _hi, hj, hbtw, hopp⟩ := hsc
    refine ⟨?_, hopp⟩
    have hlt : p.1.val < p.2.val := Fin.lt_def.mp hij
    by_contra hne
    have hgap : p.1.val + 1 < p.2.val := by omega
    have hk : p.1.val + 1 < n := lt_trans hgap p.2.isLt
    exact hnz _ (hbtw ⟨p.1.val + 1, hk⟩ (Fin.lt_def.mpr (Nat.lt_succ_self _))
      (Fin.lt_def.mpr hgap))
  · rintro ⟨hadj, hopp⟩
    refine ⟨Fin.lt_def.mpr (by omega), hnz _, hnz _, ?_, hopp⟩
    intro k hk1 hk2
    have a := Fin.lt_def.mp hk1
    have b := Fin.lt_def.mp hk2
    omega

/-- The set of adjacent index pairs `{(i, j) : j = i + 1}` in `Fin n × Fin n` has
cardinality `n − 1`: the left index `i` ranges over `{0, …, n − 2}` and determines
the pair. -/
theorem card_adjacent (n : ℕ) :
    (Finset.univ.filter (fun p : Fin n × Fin n => p.2.val = p.1.val + 1)).card = n - 1 := by
  classical
  rw [show n - 1 = (Finset.range (n - 1)).card from (Finset.card_range _).symm]
  refine Finset.card_bij' (fun p _ => p.1.val)
    (fun m hm => (⟨m, by have := Finset.mem_range.mp hm; omega⟩,
                  ⟨m + 1, by have := Finset.mem_range.mp hm; omega⟩))
    ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hj : j.val < n := j.isLt
    have hlt : i.val < n - 1 := by omega
    exact Finset.mem_range.mpr hlt
  · intro m hm
    have hmr : m < n - 1 := Finset.mem_range.mp hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · rintro ⟨i, j⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact Prod.ext_iff.mpr ⟨Fin.ext rfl, Fin.ext hp.symm⟩
  · intro m _
    rfl

/-! ### General `Fin n` sign-change bounds (the length-3 template, uniformized)

The `Fin 3` results (`countSignChanges_three_alternating = 2`,
`countSignChanges_three_mid_ne_zero = 0`) are the `n = 3` instances of three general facts,
all one-line corollaries of `countSignChanges_nowhere_zero` (which routes every count through
the adjacent-opposite-sign pairs) and `card_adjacent` (there are exactly `n − 1` adjacent
pairs).  Together they pin the two extremes and the ceiling of the count for a nowhere-zero
sequence: the strictly alternating pattern realises the maximum `n − 1`, a constant-sign
pattern realises `0`, and no sequence exceeds `n − 1` — the sequence-level shadow of the
Descartes degree bound `V(p) ≤ deg p`. -/

/-- **Universal sign-change ceiling.**  A nowhere-zero `f : Fin n → ℝ` has at most `n − 1`
sign changes: every sign change is carried by an adjacent index pair, and there are only
`n − 1` of those (`card_adjacent`).  The sequence-level form of the Descartes bound
`V(p) ≤ deg p`, and the ceiling the `Fin 3` counts (`≤ 2`) all respect. -/
theorem countSignChanges_le_of_nowhere_zero {n : ℕ} {f : Fin n → ℝ} (hnz : ∀ i, f i ≠ 0) :
    DescartesRuleOfSigns.countSignChanges f ≤ n - 1 := by
  classical
  rw [countSignChanges_nowhere_zero hnz, ← card_adjacent n]
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact hp.1

/-- **Maximal count: strict alternation.**  If *every* adjacent pair of a nowhere-zero
`f : Fin n → ℝ` has opposite signs (`f i · f j < 0` whenever `j = i + 1`), then `f` attains
the ceiling: `V(f) = n − 1`.  The general form of `countSignChanges_three_alternating` (`= 2`);
every one of the `n − 1` adjacent gaps is a genuine sign change. -/
theorem countSignChanges_alternating_eq {n : ℕ} {f : Fin n → ℝ} (hnz : ∀ i, f i ≠ 0)
    (halt : ∀ i j : Fin n, j.val = i.val + 1 → f i * f j < 0) :
    DescartesRuleOfSigns.countSignChanges f = n - 1 := by
  classical
  rw [countSignChanges_nowhere_zero hnz]
  have hset : (Finset.univ.filter (fun p : Fin n × Fin n =>
        p.2.val = p.1.val + 1 ∧ f p.1 * f p.2 < 0))
      = Finset.univ.filter (fun p : Fin n × Fin n => p.2.val = p.1.val + 1) := by
    apply Finset.filter_congr
    rintro ⟨i, j⟩ _
    constructor
    · rintro ⟨h, _⟩; exact h
    · intro h; exact ⟨h, halt i j h⟩
  rw [hset, card_adjacent]

/-- **Zero count: constant sign.**  If *every* adjacent pair of a nowhere-zero
`f : Fin n → ℝ` has the same sign (`0 < f i · f j` whenever `j = i + 1`), then `f` has no sign
changes: `V(f) = 0`.  The general form of `countSignChanges_three_mid_ne_zero` (`= 0`); the
adjacent-opposite-sign set is empty. -/
theorem countSignChanges_same_sign_eq_zero {n : ℕ} {f : Fin n → ℝ} (hnz : ∀ i, f i ≠ 0)
    (hsame : ∀ i j : Fin n, j.val = i.val + 1 → 0 < f i * f j) :
    DescartesRuleOfSigns.countSignChanges f = 0 := by
  classical
  rw [countSignChanges_nowhere_zero hnz, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨i, j⟩ _ ⟨hadj, hopp⟩
  exact absurd (hsame i j hadj) (by linarith)

/-- **Reflection complementarity (sequence form).**  For a nowhere-zero sequence
`f : Fin n → ℝ`, the sign changes of `f` and of its sign-alternated version
`i ↦ (−1)^i · f i` together cover each of the `n − 1` adjacent gaps *exactly once*:

    `V(f) + V(alt f) = n − 1`.

Because no entry vanishes, both counts are carried entirely by adjacent pairs; and
for an adjacent pair `(i, i+1)`, `(alt f) i · (alt f)(i+1) = −(f i · f (i+1))`, so the
"opposite sign" test holds for exactly one of `f`, `alt f`.  The two sign-change sets
therefore partition the adjacent pairs, whose count is `n − 1` (`card_adjacent`).
Axiom-free. -/
theorem countSignChanges_alternate_add {n : ℕ} {f : Fin n → ℝ} (hnz : ∀ i, f i ≠ 0) :
    DescartesRuleOfSigns.countSignChanges f
      + DescartesRuleOfSigns.countSignChanges (fun i => (-1 : ℝ) ^ (i : ℕ) * f i)
      = n - 1 := by
  classical
  set g : Fin n → ℝ := fun i => (-1 : ℝ) ^ (i : ℕ) * f i with hg
  have hgnz : ∀ i, g i ≠ 0 := fun i =>
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (hnz i)
  have gprod : ∀ i j : Fin n, j.val = i.val + 1 → g i * g j = -(f i * f j) := by
    intro i j hij
    simp only [hg]
    have hpow : (-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (j : ℕ) = -1 := by
      rw [← pow_add]; exact Odd.neg_one_pow ⟨(i : ℕ), by omega⟩
    linear_combination (f i * f j) * hpow
  rw [countSignChanges_nowhere_zero hnz, countSignChanges_nowhere_zero hgnz]
  set Adj : Finset (Fin n × Fin n) :=
    Finset.univ.filter (fun p : Fin n × Fin n => p.2.val = p.1.val + 1) with hAdj
  have hF : (Finset.univ.filter (fun p : Fin n × Fin n =>
        p.2.val = p.1.val + 1 ∧ f p.1 * f p.2 < 0))
      = Adj.filter (fun p => f p.1 * f p.2 < 0) := by
    rw [hAdj, Finset.filter_filter]
  have hG : (Finset.univ.filter (fun p : Fin n × Fin n =>
        p.2.val = p.1.val + 1 ∧ g p.1 * g p.2 < 0))
      = Adj.filter (fun p => ¬ f p.1 * f p.2 < 0) := by
    rw [hAdj, Finset.filter_filter]
    apply Finset.filter_congr
    rintro ⟨i, j⟩ _
    constructor
    · rintro ⟨hadj, hopp⟩
      refine ⟨hadj, ?_⟩
      rw [gprod i j hadj] at hopp
      intro hc; linarith
    · rintro ⟨hadj, hopp⟩
      refine ⟨hadj, ?_⟩
      rw [gprod i j hadj]
      have hfij : f i * f j ≠ 0 := mul_ne_zero (hnz i) (hnz j)
      rcases lt_or_gt_of_ne hfij with h | h
      · exact absurd h hopp
      · linarith
  rw [hF, hG, Finset.filter_card_add_filter_neg_card_eq_card, hAdj, card_adjacent]

/-- **Reflection complementarity (polynomial form) — Descartes for positive *and*
negative roots.**  If every coefficient `p.coeff 0, …, p.coeff (deg p)` is nonzero
(a *gap-free* polynomial), then

    `V(p) + V(p(−X)) = deg p`.

The two Descartes bounds — `V(p)` on the positive roots and `V(p(−X))` on the
negative roots — therefore *partition* the degree: no gap can be a sign persistence
for both `p` and its reflection.  Proof: `(p(−X)).coeff k = (−1)^k · p.coeff k`
(`comp_C_mul_X_coeff` at `c = −1`), so up to the global nonzero factor `(−1)^{deg p}`
the reflected coefficient sequence is the sign-alternation of `p`'s; the global factor
leaves `V` unchanged (`countSignChanges_const_smul`) and
`countSignChanges_alternate_add` closes it (`n = deg p + 1`, `n − 1 = deg p`).
Axiom-free. -/
theorem signChangesInCoeffs_comp_neg_X_add {p : ℝ[X]} (hp : p ≠ 0)
    (hnz : ∀ k, k ≤ p.natDegree → p.coeff k ≠ 0) :
    DescartesRuleOfSigns.signChangesInCoeffs p
      + DescartesRuleOfSigns.signChangesInCoeffs (p.comp (-X))
      = p.natDegree := by
  classical
  set d := p.natDegree with hd
  have hXeq : (-X : ℝ[X]) = C (-1) * X := by
    rw [C_neg, C_1, neg_mul, one_mul]
  have hcomp_ne : p.comp (-X) ≠ 0 := by
    rw [hXeq, Ne, comp_C_mul_X_eq_zero_iff
      (mem_nonZeroDivisors_of_ne_zero (by norm_num : (-1 : ℝ) ≠ 0))]
    exact hp
  have hdeg : (p.comp (-X)).natDegree = d := by
    rw [hXeq, natDegree_comp, natDegree_C_mul_X (-1) (by norm_num), mul_one, hd]
  unfold DescartesRuleOfSigns.signChangesInCoeffs
  rw [dif_neg hp, dif_neg hcomp_ne, hdeg]
  set cp : Fin (d + 1) → ℝ := DescartesRuleOfSigns.coeffSequence p d with hcp
  have hcpnz : ∀ i, cp i ≠ 0 := by
    intro i
    rw [hcp]
    simp only [DescartesRuleOfSigns.coeffSequence]
    exact hnz _ (by have := i.isLt; omega)
  have hbridge : DescartesRuleOfSigns.coeffSequence (p.comp (-X)) d
      = fun (i : Fin (d + 1)) => ((-1 : ℝ) ^ d) * ((-1 : ℝ) ^ (i : ℕ) * cp i) := by
    funext i
    have hile : (i : ℕ) ≤ d := by have := i.isLt; omega
    have hexp : ((-1 : ℝ)) ^ (d - (i : ℕ)) = (-1) ^ d * (-1) ^ (i : ℕ) := by
      have h1 : (-1 : ℝ) ^ d = (-1) ^ (d - (i : ℕ)) * (-1) ^ (i : ℕ) := by
        rw [← pow_add, Nat.sub_add_cancel hile]
      have h2 : ((-1 : ℝ) ^ (i : ℕ)) * (-1) ^ (i : ℕ) = 1 := by
        rw [← pow_add]; exact Even.neg_one_pow ⟨(i : ℕ), by ring⟩
      calc (-1 : ℝ) ^ (d - (i : ℕ))
          = (-1) ^ (d - (i : ℕ)) * ((-1) ^ (i : ℕ) * (-1) ^ (i : ℕ)) := by rw [h2]; ring
        _ = ((-1) ^ (d - (i : ℕ)) * (-1) ^ (i : ℕ)) * (-1) ^ (i : ℕ) := by ring
        _ = (-1) ^ d * (-1) ^ (i : ℕ) := by rw [← h1]
    simp only [DescartesRuleOfSigns.coeffSequence, hcp]
    rw [hXeq, comp_C_mul_X_coeff, hexp]
    ring
  rw [hbridge, countSignChanges_const_smul (pow_ne_zero d (by norm_num : (-1 : ℝ) ≠ 0))]
  have hmain := countSignChanges_alternate_add hcpnz
  simpa using hmain

/-- **Explicit reflected count — the negative-root Descartes bound in closed form.**  For a
gap-free polynomial the complementarity `signChangesInCoeffs_comp_neg_X_add`
(`V(p) + V(p(−X)) = deg p`) rearranges to the explicit value

    `V(p(−X)) = deg p − V(p)`.

This is the form actually cited for the *negative* half of Descartes' rule: the number of
negative roots of `p` is bounded by `deg p − V(p)`, the degree minus the positive-root bound.
Immediate (`omega`) from the additive identity. Axiom-free. -/
theorem signChangesInCoeffs_comp_neg_X_eq_sub {p : ℝ[X]} (hp : p ≠ 0)
    (hnz : ∀ k, k ≤ p.natDegree → p.coeff k ≠ 0) :
    DescartesRuleOfSigns.signChangesInCoeffs (p.comp (-X))
      = p.natDegree - DescartesRuleOfSigns.signChangesInCoeffs p := by
  have h := signChangesInCoeffs_comp_neg_X_add hp hnz
  omega

/-- **Fully-alternating ⟺ reflection sign-constant.**  For a gap-free polynomial the two
extremes of the complementarity `V(p) + V(p(−X)) = deg p` coincide: the reflection `p(−X)`
has *no* sign changes (all its coefficients share a sign) **iff** `p` is *fully alternating*
(`V(p) = deg p`, every adjacent coefficient pair flips sign).  The Descartes reading: `p`
attains the maximal positive-root bound `deg p` exactly when `p(−X)` attains the minimal
one `0`.  Immediate (`omega`) from the additive identity. Axiom-free. -/
theorem signChangesInCoeffs_comp_neg_X_eq_zero_iff {p : ℝ[X]} (hp : p ≠ 0)
    (hnz : ∀ k, k ≤ p.natDegree → p.coeff k ≠ 0) :
    DescartesRuleOfSigns.signChangesInCoeffs (p.comp (-X)) = 0
      ↔ DescartesRuleOfSigns.signChangesInCoeffs p = p.natDegree := by
  have h := signChangesInCoeffs_comp_neg_X_add hp hnz
  omega

/- ## § 6. Monomials have no sign changes (axiom-free)

The base of the whole variation calculus: a sequence with **at most one** nonzero entry has
zero sign changes (a sign change needs two distinct nonzero entries), so a single monomial
`c · X^k` — including the constant `C c` and the pure power `X^k` — sits at `V = 0`, the
minimal Descartes bound, matching the obvious fact that `c · X^k` has no positive roots. -/

/-- **Subsingleton support ⟹ no sign changes.**  If at most one index carries a nonzero value
(`f i ≠ 0 → f j ≠ 0 → i = j`), then `countSignChanges f = 0`: any sign change supplies two
distinct nonzero indices `i < j`, contradicting the hypothesis.  Axiom-free, general in `n`.
Complements `countSignChanges_eq_zero_of_nonneg`/`_nonpos` (all-one-sign) with the
all-but-one-zero case. -/
theorem countSignChanges_eq_zero_of_support_subsingleton {n : ℕ} {f : Fin n → ℝ}
    (h : ∀ i j, f i ≠ 0 → f j ≠ 0 → i = j) :
    DescartesRuleOfSigns.countSignChanges f = 0 := by
  unfold DescartesRuleOfSigns.countSignChanges
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
    DescartesRuleOfSigns.SignChangeBetween] at hx
  obtain ⟨hlt, hi, hj, -, -⟩ := hx
  exact absurd (h x.1 x.2 hi hj) (ne_of_lt hlt)

/-- **A single monomial has no coefficient sign changes.**  For any `c` and `k`,
`V(c · X^k) = 0`: after removing the `c = 0` case (`c · X^k = 0`, `V = 0` by definition) the
coefficient sequence of `monomial k c` is supported at the single index `k`, so
`countSignChanges_eq_zero_of_support_subsingleton` applies.  Axiom-free. -/
theorem signChangesInCoeffs_monomial (c : ℝ) (k : ℕ) :
    DescartesRuleOfSigns.signChangesInCoeffs (monomial k c) = 0 := by
  by_cases hc : c = 0
  · subst hc
    have h0 : (monomial k (0 : ℝ)) = 0 := by simp
    rw [h0]
    simp [DescartesRuleOfSigns.signChangesInCoeffs]
  · have hne : (monomial k c : ℝ[X]) ≠ 0 := by
      intro h
      apply hc
      have hcoe := congrArg (fun q : ℝ[X] => q.coeff k) h
      simpa [coeff_monomial] using hcoe
    have hdeg : (monomial k c : ℝ[X]).natDegree = k := by
      rw [natDegree_monomial]; simp [hc]
    rw [DescartesRuleOfSigns.signChangesInCoeffs, dif_neg hne]
    apply countSignChanges_eq_zero_of_support_subsingleton
    have hzero : ∀ t : Fin ((monomial k c).natDegree + 1),
        DescartesRuleOfSigns.coeffSequence (monomial k c) (monomial k c).natDegree t ≠ 0 →
        t.val = 0 := by
      intro t ht
      unfold DescartesRuleOfSigns.coeffSequence at ht
      rw [coeff_monomial] at ht
      have h2 := t.isLt
      split_ifs at ht with hcond
      · omega
      · exact absurd rfl ht
    intro i j hi hj
    have hi0 := hzero i hi
    have hj0 := hzero j hj
    exact Fin.ext (by omega)

/-- **A constant polynomial has no coefficient sign changes.**  `V(C c) = 0` for every `c`
(a constant is the monomial `C c = monomial 0 c`).  Axiom-free. -/
theorem signChangesInCoeffs_C (c : ℝ) :
    DescartesRuleOfSigns.signChangesInCoeffs (C c) = 0 := by
  rw [← monomial_zero_left]
  exact signChangesInCoeffs_monomial c 0

/-- **A pure power has no coefficient sign changes.**  `V(X^k) = 0` for every `k`
(`X^k = monomial k 1`).  Axiom-free. -/
theorem signChangesInCoeffs_X_pow (k : ℕ) :
    DescartesRuleOfSigns.signChangesInCoeffs (X ^ k : ℝ[X]) = 0 := by
  rw [X_pow_eq_monomial]
  exact signChangesInCoeffs_monomial 1 k

/-! ## § 12. The general quadratic sign-change count

The `§ 4` quadratic results (`x2_minus_1_signChanges`, `x2_plus_1_signChanges`,
`x2_minus_x_plus_1_signChanges`) computed `signChangesInCoeffs` for three *hardcoded*
polynomials.  This section generalises them to the full three-parameter family
`a·X² + b·X + c` with `a ≠ 0`, closing the standing next-step "full `Fin 3` sign-change
count for quadratics with nonzero middle term".

The key is a single coefficient-sequence identity: for a genuine quadratic the
highest-degree-first coefficient vector `coeffSequence p 2` is exactly `![a, b, c]`
(`coeffSequence_quadratic`).  Feeding that through the `§ 2¾` `Fin 3` engine gives a
closed form for the coefficient sign-change count in terms of the sign pattern of the
coefficients `(a, b, c)` — for a nonzero middle `b` this is the complete case split
(two changes when strictly alternating, one when exactly one adjacent pair alternates,
zero when neither does).  The three hardcoded `§ 4` examples are special cases (their
middle coefficient is `0`, handled by the middle-zero lemmas instead). -/

section QuadraticFamily

/-- **Coefficient vector of a genuine quadratic.**  For `a ≠ 0` the highest-degree-first
coefficient sequence of `a·X² + b·X + c` is `![a, b, c]`.  Combines
`natDegree_quadratic` with the term-by-term coefficient computation. -/
theorem coeffSequence_quadratic {a b c : ℝ} (ha : a ≠ 0) :
    DescartesRuleOfSigns.coeffSequence (C a * X ^ 2 + C b * X + C c) 2 = ![a, b, c] := by
  funext i
  fin_cases i <;>
    simp [DescartesRuleOfSigns.coeffSequence, coeff_add, coeff_C_mul_X_pow,
      coeff_C_mul_X, coeff_C]

/-- **Sign-change count of a general quadratic.**  For `a ≠ 0`, the coefficient
sign-change count of `a·X² + b·X + c` is the length-3 sequence sign-change count of
`![a, b, c]`.  This reduces the whole three-parameter family to the `Fin 3` engine of
`§ 2¾`, generalising the hardcoded `§ 4` examples. -/
theorem signChangesInCoeffs_quadratic {a b c : ℝ} (ha : a ≠ 0) :
    signChangesInCoeffs (C a * X ^ 2 + C b * X + C c)
      = DescartesRuleOfSigns.countSignChanges ![a, b, c] := by
  have hdeg : (C a * X ^ 2 + C b * X + C c : ℝ[X]).natDegree = 2 := natDegree_quadratic ha
  have hne : (C a * X ^ 2 + C b * X + C c : ℝ[X]) ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hdeg; exact absurd hdeg (by norm_num)
  unfold signChangesInCoeffs
  rw [dif_neg hne, hdeg, coeffSequence_quadratic ha]

/-- **Two sign changes — the strictly alternating quadratic.**  If `a·b < 0` and
`b·c < 0` (sign pattern `+ − +` or `− + −`) then `a·X² + b·X + c` has two coefficient
sign changes, the maximum for a quadratic (Descartes' bound is *attained*: up to two
positive roots).  Generalises `x2_minus_x_plus_1_signChanges`. -/
theorem signChangesInCoeffs_quadratic_alternating {a b c : ℝ} (ha : a ≠ 0)
    (h01 : a * b < 0) (h12 : b * c < 0) :
    signChangesInCoeffs (C a * X ^ 2 + C b * X + C c) = 2 := by
  rw [signChangesInCoeffs_quadratic ha]
  exact countSignChanges_three_alternating (by simpa using h01) (by simpa using h12)

/-- **One sign change — left pair alternates.**  If `a·b < 0` but `0 ≤ b·c`, then
`a·X² + b·X + c` has exactly one coefficient sign change (across the `a,b` pair). -/
theorem signChangesInCoeffs_quadratic_one_left {a b c : ℝ} (ha : a ≠ 0)
    (h01 : a * b < 0) (h12 : 0 ≤ b * c) :
    signChangesInCoeffs (C a * X ^ 2 + C b * X + C c) = 1 := by
  rw [signChangesInCoeffs_quadratic ha]
  exact countSignChanges_three_mid_ne_left (by simpa using h01) (by simpa using h12)

/-- **One sign change — right pair alternates.**  If `0 ≤ a·b` but `b·c < 0`, then
`a·X² + b·X + c` has exactly one coefficient sign change (across the `b,c` pair). -/
theorem signChangesInCoeffs_quadratic_one_right {a b c : ℝ} (ha : a ≠ 0)
    (h01 : 0 ≤ a * b) (h12 : b * c < 0) :
    signChangesInCoeffs (C a * X ^ 2 + C b * X + C c) = 1 := by
  rw [signChangesInCoeffs_quadratic ha]
  exact countSignChanges_three_mid_ne_right (by simpa using h01) (by simpa using h12)

/-- **No sign change — nonzero middle, neither pair alternates.**  If `b ≠ 0`,
`0 ≤ a·b` and `0 ≤ b·c` (sign pattern `+ + +` or `− − −`) then `a·X² + b·X + c` has no
coefficient sign change, hence (Descartes) no positive roots.  Together with the three
preceding corollaries this is the complete sign-change classification for a quadratic
with nonzero middle coefficient. -/
theorem signChangesInCoeffs_quadratic_no_change {a b c : ℝ} (ha : a ≠ 0)
    (hb : b ≠ 0) (h01 : 0 ≤ a * b) (h12 : 0 ≤ b * c) :
    signChangesInCoeffs (C a * X ^ 2 + C b * X + C c) = 0 := by
  rw [signChangesInCoeffs_quadratic ha]
  exact countSignChanges_three_mid_ne_zero (by simpa using hb)
    (by simpa using h01) (by simpa using h12)

/-- **One sign change — zero middle, opposite outer signs.**  If `b = 0` and `a·c < 0`
(sign pattern `+ 0 −` or `− 0 +`) then `a·X² + c` has exactly one coefficient sign change,
jumping over the vanishing middle term.  This is the *general* form of the base file's
`X² − 1` example, and — being the `b = 0` complement of `signChangesInCoeffs_quadratic_one_left`
/ `_one_right` — completes the sign-change classification to **every** real quadratic. -/
theorem signChangesInCoeffs_quadratic_mid_zero_one {a b c : ℝ} (ha : a ≠ 0)
    (hb : b = 0) (hac : a * c < 0) :
    signChangesInCoeffs (C a * X ^ 2 + C b * X + C c) = 1 := by
  rw [signChangesInCoeffs_quadratic ha]
  exact countSignChanges_three_mid_zero_pos (by simpa using hb) (by simpa using hac)

/-- **No sign change — zero middle, non-opposite outer signs.**  If `b = 0` and `0 ≤ a·c`
then `a·X² + c` has no coefficient sign change: the general form of `X² + 1`.  With
`signChangesInCoeffs_quadratic_mid_zero_one` and the four nonzero-middle corollaries, the
coefficient sign-change count of an arbitrary real quadratic is now determined in **all**
sign configurations of `(a, b, c)`. -/
theorem signChangesInCoeffs_quadratic_mid_zero_no_change {a b c : ℝ} (ha : a ≠ 0)
    (hb : b = 0) (hac : 0 ≤ a * c) :
    signChangesInCoeffs (C a * X ^ 2 + C b * X + C c) = 0 := by
  rw [signChangesInCoeffs_quadratic ha]
  exact countSignChanges_three_mid_zero_zero (by simpa using hb) (by simpa using hac)

/-- **Concrete tight witness `X² − 3X + 2 = (X − 1)(X − 2)`.**  Coefficient sequence
`[1, −3, 2]` (`+ − +`), so exactly two coefficient sign changes — matching its two positive
roots `1, 2`.  A degree-`2` polynomial *attaining* Descartes' upper bound with distinct
positive roots (the base file's examples `X² ± 1` only realise `V = 1` and `V = 0`). -/
theorem signChanges_x2_sub_3x_add_2 :
    signChangesInCoeffs (C 1 * X ^ 2 + C (-3) * X + C 2 : ℝ[X]) = 2 :=
  signChangesInCoeffs_quadratic_alternating (by norm_num) (by norm_num) (by norm_num)

end QuadraticFamily

end DescartesRuleOfSignsOQ01OQ03
