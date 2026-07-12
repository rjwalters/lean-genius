import Mathlib.Tactic
import Proofs.ETranscendentalOQ02

/-
# The contrapositive of `normal_imp_irrational`: rationals are never normal

## Context

The parent entry `ETranscendentalOQ02` ("Is e a Normal Number?") proves the
positive implication

  `normal_imp_irrational : IsNormalInBase b x → Irrational x`   (base `b ≥ 2`),

using that a rational's base-`b` expansion is eventually periodic and hence has a
missing digit block, so some block frequency tends to `0` rather than to the
positive normal value `b^(-k)`.

The open-question child `e-transcendental-oq-02-oq-06` asks to package the
*contrapositive* as a reusable standalone lemma:

  `x ∈ ℚ  ⇒  ¬ IsNormalInBase b x`.

That is exactly what a downstream user needs to rule out normality of a concrete
number once it is known to be rational. This file records the contrapositive and
its immediate specializations (rational / integer / natural casts, and the
absolute-normality level), each obtained from `normal_imp_irrational` and the
Mathlib facts `Rat.not_irrational` / `Int.not_irrational` / `Nat.not_irrational`.

None of these introduce assumptions: they are corollaries of a theorem already
machine-checked in the parent file. The only `axiom` in the parent
(`e_absolutely_normal`, the genuinely open conjecture that `e` is normal) is not
used here.

## Results

- `rational_not_normal`      : `¬ IsNormalInBase b (q : ℝ)` for `q : ℚ`.
- `intCast_not_normal`       : `¬ IsNormalInBase b (n : ℝ)` for `n : ℤ`.
- `natCast_not_normal`       : `¬ IsNormalInBase b (n : ℝ)` for `n : ℕ`.
- `normal_ne_ratCast`        : a normal number differs from every rational.
- `rational_not_absolutely_normal` : `¬ IsAbsolutelyNormal (q : ℝ)`.
-/

open ETranscendentalOQ02

namespace ETranscendentalOQ02OQ06

/-- **Rationals are never normal (the contrapositive of `normal_imp_irrational`).**
    If `q : ℚ`, then `(q : ℝ)` is not normal in any base `b ≥ 2`: normality would
    force irrationality by `normal_imp_irrational`, contradicting
    `Rat.not_irrational`. This is the standalone contrapositive requested by the
    `e-transcendental-oq-02-oq-06` open question. -/
theorem rational_not_normal (b : ℕ) (hb : 2 ≤ b) (q : ℚ) :
    ¬ IsNormalInBase b (q : ℝ) :=
  fun hn => q.not_irrational (normal_imp_irrational b hb (q : ℝ) hn)

/-- **Integers are never normal.**  Specialization of `rational_not_normal` to
    integer casts, via `Int.not_irrational`. -/
theorem intCast_not_normal (b : ℕ) (hb : 2 ≤ b) (n : ℤ) :
    ¬ IsNormalInBase b (n : ℝ) :=
  fun hn => (Int.not_irrational n) (normal_imp_irrational b hb (n : ℝ) hn)

/-- **Naturals are never normal.**  Specialization of `rational_not_normal` to
    natural-number casts, via `Nat.not_irrational`. -/
theorem natCast_not_normal (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    ¬ IsNormalInBase b (n : ℝ) :=
  fun hn => (Nat.not_irrational n) (normal_imp_irrational b hb (n : ℝ) hn)

/-- **A normal number is distinct from every rational.**  The pointwise form of
    the contrapositive: if `x` is normal in base `b ≥ 2`, then `x ≠ (q : ℝ)` for
    every `q : ℚ`. Immediate from `rational_not_normal` (substituting a purported
    equality would make a rational normal). -/
theorem normal_ne_ratCast (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (hx : IsNormalInBase b x)
    (q : ℚ) : x ≠ (q : ℝ) := by
  rintro rfl
  exact rational_not_normal b hb q hx

/-- **Rationals are not absolutely normal.**  A rational cannot be normal in even
    a single base, so in particular it is not normal in *every* base. Uses
    `IsAbsolutelyNormal` at the concrete base `2`. -/
theorem rational_not_absolutely_normal (q : ℚ) :
    ¬ IsAbsolutelyNormal (q : ℝ) :=
  fun hn => rational_not_normal 2 (le_refl 2) q (hn 2 (le_refl 2))

/-- **A normal number is distinct from every integer.**  Integer specialization of
    `normal_ne_ratCast`: if `x` is normal in base `b ≥ 2`, then `x ≠ (n : ℝ)` for every
    `n : ℤ`. Immediate from `intCast_not_normal`. -/
theorem normal_ne_intCast (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (hx : IsNormalInBase b x)
    (n : ℤ) : x ≠ (n : ℝ) := by
  rintro rfl
  exact intCast_not_normal b hb n hx

/-- **A normal number is distinct from every natural number.**  Natural specialization of
    `normal_ne_ratCast`, via `natCast_not_normal`. -/
theorem normal_ne_natCast (b : ℕ) (hb : 2 ≤ b) (x : ℝ) (hx : IsNormalInBase b x)
    (n : ℕ) : x ≠ (n : ℝ) := by
  rintro rfl
  exact natCast_not_normal b hb n hx

/-- **Absolute normality implies irrationality.**  An absolutely normal number is in
    particular normal in base `2`, hence irrational by `normal_imp_irrational`. The
    absolute-normality specialization of the parent's positive implication, and the exact
    strength used in `rational_not_absolutely_normal`. -/
theorem absolutelyNormal_imp_irrational (x : ℝ) (hx : IsAbsolutelyNormal x) :
    Irrational x :=
  normal_imp_irrational 2 (le_refl 2) x (hx 2 (le_refl 2))

/-- **Integers are not absolutely normal.**  An integer is not normal in base `2`, so it
    fails absolute normality. Integer analogue of `rational_not_absolutely_normal`. -/
theorem intCast_not_absolutely_normal (n : ℤ) : ¬ IsAbsolutelyNormal (n : ℝ) :=
  fun hn => intCast_not_normal 2 (le_refl 2) n (hn 2 (le_refl 2))

/-- **Naturals are not absolutely normal.**  Natural analogue of
    `rational_not_absolutely_normal`. -/
theorem natCast_not_absolutely_normal (n : ℕ) : ¬ IsAbsolutelyNormal (n : ℝ) :=
  fun hn => natCast_not_normal 2 (le_refl 2) n (hn 2 (le_refl 2))

/-!
### Set-level packaging

The pointwise corollaries above are most reusable as statements about the *set* of
normal numbers: it is contained in the irrationals and is disjoint from the rationals.
These are the exact forms a downstream argument invokes when it wants to conclude a
whole family of numbers (e.g. `Set.range ((↑) : ℚ → ℝ)`) contains no normal number.
-/

/-- **The normal numbers of base `b` form a subset of the irrationals.**  Set-inclusion
    packaging of the parent's pointwise `normal_imp_irrational`. -/
theorem setOf_normal_subset_irrational (b : ℕ) (hb : 2 ≤ b) :
    {x : ℝ | IsNormalInBase b x} ⊆ {x : ℝ | Irrational x} :=
  fun x hx => normal_imp_irrational b hb x hx

/-- **The absolutely normal numbers form a subset of the irrationals.**  Absolute-normality
    analogue of `setOf_normal_subset_irrational`, via `absolutelyNormal_imp_irrational`. -/
theorem setOf_absolutelyNormal_subset_irrational :
    {x : ℝ | IsAbsolutelyNormal x} ⊆ {x : ℝ | Irrational x} :=
  fun x hx => absolutelyNormal_imp_irrational x hx

/-- **The base-`b` normal numbers are disjoint from the rationals.**  The set-level
    contrapositive: no `q : ℚ` casts to a base-`b`-normal real. Directly from
    `rational_not_normal`. This is the reusable "a rational is never in the normal set"
    fact for `Set.range ((↑) : ℚ → ℝ)`. -/
theorem normal_disjoint_ratCast (b : ℕ) (hb : 2 ≤ b) :
    Disjoint {x : ℝ | IsNormalInBase b x} (Set.range ((↑) : ℚ → ℝ)) := by
  rw [Set.disjoint_left]
  rintro x hx ⟨q, rfl⟩
  exact rational_not_normal b hb q hx

/-- **The absolutely normal numbers are disjoint from the rationals.**  Absolute-normality
    analogue of `normal_disjoint_ratCast`, via `rational_not_absolutely_normal`. -/
theorem absolutelyNormal_disjoint_ratCast :
    Disjoint {x : ℝ | IsAbsolutelyNormal x} (Set.range ((↑) : ℚ → ℝ)) := by
  rw [Set.disjoint_left]
  rintro x hx ⟨q, rfl⟩
  exact rational_not_absolutely_normal q hx

end ETranscendentalOQ02OQ06
