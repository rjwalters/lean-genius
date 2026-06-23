import Mathlib
import Proofs.MasonStothersOQ01

/-
# Davenport's inequality from Mason–Stothers (characteristic zero)

Davenport's inequality is the classical statement that a polynomial of the shape
`f³ - g²` cannot have too small a degree relative to `f`: if `f, g` are coprime
non-constant polynomials over a characteristic-zero field with `f³ ≠ g²`, then

  `deg f + 2 ≤ 2 · deg (f³ - g²)`,

i.e. `deg (f³ - g²) ≥ ½ deg f + 1`.  It quantifies how close `f³` and `g²` can
be, and is the polynomial shadow of Hall's conjecture on `|x³ - y²|` for integers.

This file derives it as a direct `0`-axiom corollary of
`MasonStothersOQ01.mason_stothers_charZero` (the characteristic-zero form of the
polynomial ABC theorem proved in the parent entry).

## Proof sketch

Apply Mason–Stothers in the form `a + b = c` to the coprime triple

  `a = f³,  b = -g²,  c = f³ - g²`.

Coprimality of `f, g` gives coprimality of `f³, -g²`, and `a = f³` is non-constant,
so the escape clause is excluded in characteristic zero and we get

  `deg(f³) + 1 ≤ deg rad(a·b·c)`   and   `deg(g²) + 1 ≤ deg rad(a·b·c)`.

The key combinatorial input is an *upper* bound on the radical's degree:

  `rad(f³·g²·c) ∣ f·g·c`,

obtained from `radical_mul_dvd` (which needs **no** coprimality), `radical_pow`
(`rad(pⁿ) = rad p`) and `radical_dvd_self`.  Hence

  `deg rad(a·b·c) ≤ deg f + deg g + deg c`.

Feeding the two Mason–Stothers bounds and this upper bound to `omega`:

  `3·deg f + 1 ≤ deg f + deg g + deg c`     (from `f³`)
  `2·deg g + 1 ≤ deg f + deg g + deg c`     (from `g²`)

add to give `deg f + 2 ≤ 2·deg c`, which is Davenport's inequality.

Everything is a `0`-axiom derivation from Mathlib's `Polynomial.abc`.
-/

open Polynomial UniqueFactorizationMonoid UniqueFactorizationDomain

namespace MasonStothersOQ01OQ02

variable {k : Type*} [Field k] [DecidableEq k]

/-- The radical of a product `f³ · g² · c` divides `f · g · c`, **without any
coprimality hypotheses**.  This is the radical-degree input to Davenport's
inequality: it bounds the number of distinct roots of `f³·g²·c` by
`deg f + deg g + deg c`.  Proof: `radical_mul_dvd` splits the product, `radical_pow`
collapses the powers (`rad(fⁿ) = rad f`), and `radical_dvd_self` returns to `f, g, c`. -/
theorem radical_cube_sq_mul_dvd (f g c : k[X]) :
    radical (f ^ 3 * g ^ 2 * c) ∣ f * g * c := by
  have hrf : radical f ∣ f := radical_dvd_self
  have hrg : radical g ∣ g := radical_dvd_self
  have hrc : radical c ∣ c := radical_dvd_self
  have h1 : radical (f ^ 3 * g ^ 2) ∣ f * g :=
    calc radical (f ^ 3 * g ^ 2)
          ∣ radical (f ^ 3) * radical (g ^ 2) := radical_mul_dvd
      _ = radical f * radical g := by
            rw [radical_pow f (by norm_num), radical_pow g (by norm_num)]
      _ ∣ f * g := mul_dvd_mul hrf hrg
  calc radical (f ^ 3 * g ^ 2 * c)
        ∣ radical (f ^ 3 * g ^ 2) * radical c := radical_mul_dvd
    _ ∣ (f * g) * c := mul_dvd_mul h1 hrc

/-- **Davenport's inequality.**

For coprime polynomials `f, g` over a characteristic-zero field with `f`
non-constant, `g ≠ 0` and `f³ ≠ g²`,

  `deg f + 2 ≤ 2 · deg (f³ - g²)`,

equivalently `deg (f³ - g²) ≥ ½ deg f + 1`.  Derived directly from the
characteristic-zero Mason–Stothers bound. -/
theorem davenport [CharZero k] {f g : k[X]} (hf : f.natDegree ≠ 0) (hg : g ≠ 0)
    (hcop : IsCoprime f g) (hne : f ^ 3 ≠ g ^ 2) :
    f.natDegree + 2 ≤ 2 * (f ^ 3 - g ^ 2).natDegree := by
  -- nonzeroness of the three terms `a = f³`, `b = -g²`, `c = f³ - g²`
  have hf0 : f ≠ 0 := fun h => hf (by simp [h])
  have ha : (f ^ 3) ≠ 0 := pow_ne_zero 3 hf0
  have hb : (-g ^ 2) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 hg)
  have hc : (f ^ 3 - g ^ 2) ≠ 0 := sub_ne_zero.mpr hne
  -- coprimality `f³` ⟂ `-g²` and the additive relation `f³ + (-g²) = f³ - g²`
  have hcop' : IsCoprime (f ^ 3) (-g ^ 2) := (hcop.pow).neg_right
  have hsum : f ^ 3 + (-g ^ 2) = f ^ 3 - g ^ 2 := by ring
  -- non-triviality: `f³` is non-constant since `f` is
  have hnontriv : (f ^ 3).natDegree ≠ 0 ∨ (-g ^ 2).natDegree ≠ 0 ∨
      (f ^ 3 - g ^ 2).natDegree ≠ 0 :=
    Or.inl (by rw [Polynomial.natDegree_pow]; omega)
  -- Mason–Stothers in characteristic zero
  obtain ⟨b1, b2, _⟩ :=
    MasonStothersOQ01.mason_stothers_charZero ha hb hc hcop' hsum hnontriv
  -- rewrite `radical (f³ · (-g²) · c)` as `radical (f³ · g² · c)` (differ by the unit `-1`)
  have hrad : radical (f ^ 3 * -g ^ 2 * (f ^ 3 - g ^ 2)) =
      radical (f ^ 3 * g ^ 2 * (f ^ 3 - g ^ 2)) := by
    rw [show f ^ 3 * -g ^ 2 * (f ^ 3 - g ^ 2)
          = -(f ^ 3 * g ^ 2 * (f ^ 3 - g ^ 2)) by ring, radical_neg]
  rw [hrad] at b1 b2
  -- upper bound on the radical degree via `radical_cube_sq_mul_dvd`
  have hfgc : f * g * (f ^ 3 - g ^ 2) ≠ 0 := mul_ne_zero (mul_ne_zero hf0 hg) hc
  have hub : (radical (f ^ 3 * g ^ 2 * (f ^ 3 - g ^ 2))).natDegree ≤
      f.natDegree + g.natDegree + (f ^ 3 - g ^ 2).natDegree := by
    refine (natDegree_le_of_dvd (radical_cube_sq_mul_dvd f g (f ^ 3 - g ^ 2)) hfgc).trans_eq ?_
    rw [natDegree_mul (mul_ne_zero hf0 hg) hc, natDegree_mul hf0 hg]
  -- degrees of `f³` and `-g²`
  have hdf3 : (f ^ 3).natDegree = 3 * f.natDegree := natDegree_pow f 3
  have hdg2 : (-g ^ 2).natDegree = 2 * g.natDegree := by
    rw [natDegree_neg, natDegree_pow]
  rw [hdf3] at b1
  rw [hdg2] at b2
  omega

/-- **Davenport, height form.**  Restated as a lower bound on the degree of
`f³ - g²` directly: `deg (f³ - g²) ≥ ½ deg f + 1` rendered over `ℕ` as
`2 ≤ 2·deg(f³-g²) - deg f`.  Equivalent to `davenport`; provided for convenience. -/
theorem natDegree_cube_sub_sq_ge [CharZero k] {f g : k[X]} (hf : f.natDegree ≠ 0)
    (hg : g ≠ 0) (hcop : IsCoprime f g) (hne : f ^ 3 ≠ g ^ 2) :
    f.natDegree / 2 + 1 ≤ (f ^ 3 - g ^ 2).natDegree := by
  have h := davenport hf hg hcop hne
  omega

end MasonStothersOQ01OQ02
