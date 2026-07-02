import Proofs.PythagoreanTheoremOQ04
import Mathlib.Tactic

/-!
# The canonical Gaussian generator of a primitive triple (pythagorean-theorem-oq-04-oq-01)

## What this proves

`pythagorean-theorem-oq-04` establishes that every primitive Pythagorean triple `(x, y, z)`
(with `x` odd, `z > 0`) is the square of a Gaussian integer `g = m + ni`, and that this
generator is unique *up to sign*: any two generators `g, h` of the same triple satisfy
`g = h` or `g = -h` (`generator_unique_up_to_sign`).

This file **promotes the up-to-sign uniqueness to a genuine `∃!`** by pinning the sign.

* **Canonical sign form.** Call `g = a + bi` *canonical* (`IsCanonical`) when `a > 0`, or
  `a = 0` and `b > 0`. For every nonzero `g`, exactly one of `g` and `-g` is canonical
  (`isCanonical_or_neg`, `not_isCanonical_neg_of_isCanonical`) — so canonicity selects a
  distinguished representative of the sign pair `{g, -g}`.

* **Existence & uniqueness of the canonical generator** (`canonical_generator_existsUnique`).
  Combining completeness (`gaussian_completeness`) with up-to-sign uniqueness, every
  primitive triple has *exactly one* canonical Gaussian generator `g` with `x + yi = g²`.

* **The fibre has exactly two points** (`sqRoots_eq_pair`, `sqRoots_ncard_two`). The set of
  Gaussian square roots of `x + yi` is precisely `{g, -g}`, a two-element set (squaring is
  two-to-one in the domain `ℤ[i]`). Fixing the sign picks one of the two.

Together these upgrade "unique up to `{±1}`" into a bona-fide classification: primitive
triples correspond bijectively to *canonical* Gaussian generators.

## Status

- [x] Complete proof, no sorries
- [x] 0 `axiom` declarations, no structure-encoded assumptions
- [x] Reuses only the verified parent entry `PythagoreanTheoremOQ04`
-/

namespace PythagoreanTheoremOQ04OQ01

open Zsqrtd PythagoreanTheoremOQ04

local notation "ℤ[i]" => GaussianInt

/-! ## Canonical sign form -/

/-- A Gaussian integer `a + bi` is in **canonical sign form** when its real part is
positive, or it is purely imaginary with positive imaginary part. This picks out a
distinguished representative of each sign pair `{g, -g}`. -/
def IsCanonical (g : ℤ[i]) : Prop := 0 < g.re ∨ (g.re = 0 ∧ 0 < g.im)

/-- `g` and `-g` are never both canonical. -/
theorem not_isCanonical_neg_of_isCanonical {g : ℤ[i]} (h : IsCanonical g) :
    ¬ IsCanonical (-g) := by
  rcases h with hre | ⟨hre0, him⟩ <;>
    rintro (hre' | ⟨hre0', him'⟩) <;>
      simp only [Zsqrtd.re_neg, Zsqrtd.im_neg] at * <;> omega

/-- For a nonzero Gaussian integer, at least one of `g` and `-g` is canonical. -/
theorem isCanonical_or_neg {g : ℤ[i]} (hg : g ≠ 0) :
    IsCanonical g ∨ IsCanonical (-g) := by
  have hne : g.re ≠ 0 ∨ g.im ≠ 0 := by
    by_contra h
    push_neg at h
    apply hg
    apply Zsqrtd.ext
    · simpa using h.1
    · simpa using h.2
  unfold IsCanonical
  simp only [Zsqrtd.re_neg, Zsqrtd.im_neg]
  omega

/-- Exactly one of `g` and `-g` is canonical (for `g ≠ 0`): canonicity is a genuine
sign-selection. -/
theorem isCanonical_xor_neg {g : ℤ[i]} (hg : g ≠ 0) :
    (IsCanonical g ∧ ¬ IsCanonical (-g)) ∨ (¬ IsCanonical g ∧ IsCanonical (-g)) := by
  rcases isCanonical_or_neg hg with h | h
  · exact Or.inl ⟨h, not_isCanonical_neg_of_isCanonical h⟩
  · refine Or.inr ⟨fun hc => not_isCanonical_neg_of_isCanonical hc h, h⟩

/-! ## The square-root fibre `{g, -g}` -/

/-- The set of Gaussian square roots of `w = g²` is exactly the sign pair `{g, -g}`. -/
theorem sqRoots_eq_pair (w g : ℤ[i]) (hg : w = g ^ 2) :
    {h : ℤ[i] | h ^ 2 = w} = {g, -g} := by
  ext h
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [hg]
  exact gaussianInt_sq_eq_iff h g

/-- A nonzero Gaussian integer differs from its negative. -/
theorem ne_neg_self {g : ℤ[i]} (hg : g ≠ 0) : g ≠ -g := by
  intro hgg
  apply hg
  have hre := congrArg Zsqrtd.re hgg
  have him := congrArg Zsqrtd.im hgg
  simp only [Zsqrtd.re_neg, Zsqrtd.im_neg] at hre him
  apply Zsqrtd.ext
  · simpa using (by omega : g.re = 0)
  · simpa using (by omega : g.im = 0)

/-- **Squaring is two-to-one.** For a nonzero generator `g`, the fibre of `· ^ 2` over
`w = g²` has exactly two elements, namely `g` and `-g`. -/
theorem sqRoots_ncard_two (w g : ℤ[i]) (hg : w = g ^ 2) (hg0 : g ≠ 0) :
    {h : ℤ[i] | h ^ 2 = w}.ncard = 2 := by
  rw [sqRoots_eq_pair w g hg, Set.ncard_pair (ne_neg_self hg0)]

/-! ## Existence and uniqueness of the canonical generator -/

/-- **The canonical generator: existence and uniqueness.** Every primitive Pythagorean
triple `(x, y, z)` with `x` odd and `z > 0` has *exactly one* canonical Gaussian generator:
a unique `g : ℤ[i]` in canonical sign form with `x + yi = g²`.

This promotes the up-to-sign uniqueness of `pythagorean-theorem-oq-04` to a genuine `∃!`:
completeness supplies a generator, up-to-sign uniqueness confines it to `{g, -g}`, and
canonicity singles out one of the two. -/
theorem canonical_generator_existsUnique {x y z : ℤ} (h : PythagoreanTriple x y z)
    (hco : Int.gcd x y = 1) (hodd : x % 2 = 1) (hpos : 0 < z) :
    ∃! g : ℤ[i], (⟨x, y⟩ : ℤ[i]) = g ^ 2 ∧ IsCanonical g := by
  obtain ⟨m, n, hsq, _, _⟩ := gaussian_completeness h hco hodd hpos
  set g₀ : ℤ[i] := ⟨m, n⟩ with hg0def
  -- `⟨x, y⟩ ≠ 0` because `x` is odd, hence `g₀ ≠ 0`.
  have hxy_ne : (⟨x, y⟩ : ℤ[i]) ≠ 0 := by
    intro hz
    rw [Zsqrtd.ext_iff] at hz
    simp only [Zsqrtd.re_zero, Zsqrtd.im_zero] at hz
    omega
  have hg0_ne : g₀ ≠ 0 := by
    intro hz; apply hxy_ne; rw [hsq, hz]; ring
  rcases isCanonical_or_neg hg0_ne with hcan | hcan
  · -- `g₀` itself is canonical.
    refine ⟨g₀, ⟨hsq, hcan⟩, ?_⟩
    rintro h' ⟨hh'sq, hh'can⟩
    rcases (gaussianInt_sq_eq_iff h' g₀).mp (by rw [← hh'sq, ← hsq]) with he | he
    · exact he
    · exact absurd (he ▸ hh'can) (not_isCanonical_neg_of_isCanonical hcan)
  · -- `-g₀` is the canonical generator.
    have hsq' : (⟨x, y⟩ : ℤ[i]) = (-g₀) ^ 2 := by rw [neg_sq]; exact hsq
    refine ⟨-g₀, ⟨hsq', hcan⟩, ?_⟩
    rintro h' ⟨hh'sq, hh'can⟩
    rcases (gaussianInt_sq_eq_iff h' (-g₀)).mp (by rw [← hh'sq, ← hsq']) with he | he
    · exact he
    · rw [neg_neg] at he
      rw [he] at hh'can
      exact absurd hcan (not_isCanonical_neg_of_isCanonical hh'can)

/-! ## Worked example: the (3, 4, 5) triple -/

/-- The canonical generator of `(3, 4, 5)` is `2 + i`: it is canonical (`re = 2 > 0`) and
squares to `3 + 4i`. -/
example : IsCanonical (⟨2, 1⟩ : ℤ[i]) := Or.inl (by decide)

example : (⟨3, 4⟩ : ℤ[i]) = (⟨2, 1⟩ : ℤ[i]) ^ 2 := by rw [gaussianInt_sq]; norm_num

/-- The Gaussian square roots of `3 + 4i` are exactly `{2 + i, -2 - i}` — a two-point set. -/
example : {h : ℤ[i] | h ^ 2 = (⟨3, 4⟩ : ℤ[i])}.ncard = 2 := by
  refine sqRoots_ncard_two _ (⟨2, 1⟩ : ℤ[i]) ?_ ?_
  · rw [gaussianInt_sq]; norm_num
  · intro hz
    rw [Zsqrtd.ext_iff] at hz
    simp only [Zsqrtd.re_zero, Zsqrtd.im_zero] at hz
    omega

end PythagoreanTheoremOQ04OQ01
