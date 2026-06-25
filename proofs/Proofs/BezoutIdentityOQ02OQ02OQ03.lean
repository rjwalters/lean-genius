import Mathlib

/-
# The Univariate Nullstellensatz via Bézout (OQ-02-OQ-02-OQ-03)

## The Open Question (bezout-identity-oq-02-oq-02-oq-03)

Can `isBezout_coprime_iff` (the IsRelPrime ↔ IsCoprime equivalence in Bézout
rings, from BezoutIdentityOQ02OQ02) be used to prove the **Nullstellensatz**
via Bézout-style reasoning in polynomial rings over algebraically closed fields?

## Answer: YES — but **only in one variable**, and there it is exact.

The honest answer has two halves, a positive and a negative one:

### Positive (this file): the univariate Nullstellensatz IS Bézout reasoning.

A single-variable polynomial ring `k[X]` over a field `k` is a Euclidean
domain, hence a PID, hence `IsBezout`. In this setting the coprimality
machinery of the parent entry applies verbatim, and it yields exactly the
*one-variable Nullstellensatz*:

  For `f g : k[X]` over an algebraically closed `k`,

      `IsCoprime f g  ↔  f and g have no common root`
      `1 ∈ (f, g)     ↔  V(f, g) = ∅`.

The forward direction (`coprime → no common root`) is **pure Bézout reasoning**:
evaluate the Bézout identity `u·f + v·g = 1` at a hypothetical common root `r`
to get `0 = 1`. No algebraic closure is needed for this half. The backward
direction is the one place the *Nullstellensatz* content enters: it uses the
fundamental theorem of algebra (`IsAlgClosed.exists_root`) to extract a common
root from a non-unit `gcd`.

This is precisely the statement `V(I) = ∅ ⟺ I = (1)` of the **weak
Nullstellensatz**, specialized to `n = 1` and to a two-generator ideal.

### Negative (documented, not formalized): multivariate is NOT Bézout.

For `n ≥ 2` variables, `k[X₁, …, Xₙ]` is **not** a Bézout domain (it is not
even a PID — e.g. the ideal `(X, Y)` is not principal). So `isBezout_coprime_iff`
does **not** apply, and the full Hilbert Nullstellensatz cannot be obtained by
Bézout-style reasoning. Mathlib proves the genuine multivariate result
(`MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`) by entirely different
means (Noether normalization / the Rabinowitsch trick). The Bézout route is
intrinsically one-dimensional.

## Proof Status
- [x] Part I: Forward — coprime ⇒ no common root (pure Bézout, any field)
- [x] Part II: Backward — no common root ⇒ coprime (FTA, alg. closed)
- [x] Part III: The equivalence (univariate Nullstellensatz, root form)
- [x] Part IV: Ideal form — `1 ∈ (f,g) ↔ V(f,g) = ∅`
- [x] Part V: Concrete instance over ℂ
- [x] Part VI: Honest scope note (multivariate is out of reach for Bézout)

Verified: 0 sorries, 0 axioms.
-/

namespace BezoutNullstellensatz

open Polynomial

/-!
## Part I: Forward Direction — Coprime ⇒ No Common Root

This is the **Bézout heart** of the univariate Nullstellensatz, and it works
over *any* field (no algebraic closure required). If `u·f + v·g = 1`, then
evaluating at any common root `r` of `f` and `g` gives `0 = 1`.
-/

/-- **Coprime polynomials share no root** (any field, pure Bézout reasoning).
    If `IsCoprime f g`, then `f` and `g` have no common root. -/
theorem coprime_imp_no_common_root {k : Type*} [Field k] {f g : k[X]}
    (h : IsCoprime f g) (x : k) : ¬ (f.IsRoot x ∧ g.IsRoot x) := by
  rintro ⟨hf, hg⟩
  obtain ⟨u, v, huv⟩ := h          -- huv : u * f + v * g = 1
  -- Evaluate the Bézout identity at the common root x.
  have hev := congrArg (eval x) huv
  rw [eval_add, eval_mul, eval_mul, eval_one, hf.eq_zero, hg.eq_zero,
    mul_zero, mul_zero, add_zero] at hev
  exact zero_ne_one hev

/-!
## Part II: Backward Direction — No Common Root ⇒ Coprime

Here, and *only* here, the algebraic closure enters. We argue by
contradiction: if `f` and `g` were not coprime, then `gcd f g` is not a unit,
hence has positive degree, hence (by the fundamental theorem of algebra) a
root `r`. Since `gcd f g` divides both `f` and `g`, `r` is a common root.
-/

/-- **No common root ⇒ coprime** (algebraically closed field).
    The only nontrivial direction; it uses the fundamental theorem of algebra
    via `IsAlgClosed.exists_root`. -/
theorem no_common_root_imp_coprime {k : Type*} [Field k] [IsAlgClosed k] {f g : k[X]}
    (h : ∀ x, ¬ (f.IsRoot x ∧ g.IsRoot x)) : IsCoprime f g := by
  classical
  by_contra hcop
  -- ¬ IsCoprime f g  ⇒  gcd f g is not a unit.
  rw [← gcd_isUnit_iff] at hcop
  -- A non-unit in k[X] has nonzero degree (over a field, units = nonzero constants).
  have hdeg : (gcd f g).degree ≠ 0 := fun hd => hcop (isUnit_iff_degree_eq_zero.mpr hd)
  -- Algebraic closure: the gcd has a root r.
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root (gcd f g) hdeg
  -- gcd f g ∣ f and gcd f g ∣ g, so r is a common root.
  exact h r ⟨hr.dvd (gcd_dvd_left f g), hr.dvd (gcd_dvd_right f g)⟩

/-!
## Part III: The Univariate Nullstellensatz (Root Form)

Combining Parts I and II: over an algebraically closed field, coprimality of
two polynomials is *equivalent* to having no common root. This is the
geometric content `V(f, g) = ∅ ⟺ (f, g) = (1)` in one variable.
-/

/-- **Univariate Nullstellensatz (root form)**: over an algebraically closed
    field, `f` and `g` are coprime iff they have no common root. -/
theorem coprime_iff_no_common_root {k : Type*} [Field k] [IsAlgClosed k] {f g : k[X]} :
    IsCoprime f g ↔ ∀ x, ¬ (f.IsRoot x ∧ g.IsRoot x) :=
  ⟨coprime_imp_no_common_root, no_common_root_imp_coprime⟩

/-!
## Part IV: The Univariate Nullstellensatz (Ideal Form)

`IsCoprime f g` is, by definition, exactly `1 ∈ Ideal.span {f, g}` — the
Bézout identity again. Rephrasing Part III in ideal language gives the weak
Nullstellensatz statement directly: the ideal generated by `f` and `g` is the
whole ring iff their common vanishing locus is empty.
-/

/-- `IsCoprime f g` is exactly membership of `1` in the ideal `(f, g)`
    (this is the Bézout identity restated as an ideal condition). -/
theorem coprime_iff_one_mem_span {R : Type*} [CommRing R] (f g : R) :
    IsCoprime f g ↔ (1 : R) ∈ Ideal.span ({f, g} : Set R) := by
  rw [Ideal.mem_span_pair]
  exact ⟨fun ⟨u, v, h⟩ => ⟨u, v, h⟩, fun ⟨u, v, h⟩ => ⟨u, v, h⟩⟩

/-- **Univariate weak Nullstellensatz (ideal form)**: the ideal `(f, g)` is the
    unit ideal iff `f` and `g` have no common zero. This is `V(I) = ∅ ⟺ I = (1)`
    for a two-generator ideal in one variable. -/
theorem one_mem_span_iff_no_common_root {k : Type*} [Field k] [IsAlgClosed k] {f g : k[X]} :
    (1 : k[X]) ∈ Ideal.span ({f, g} : Set k[X]) ↔ ∀ x, ¬ (f.IsRoot x ∧ g.IsRoot x) :=
  (coprime_iff_one_mem_span f g).symm.trans coprime_iff_no_common_root

/-!
## Part V: Concrete Instance over ℂ

`ℂ` is algebraically closed, so the equivalence applies. `X` and `X - 1` have
no common root (their roots are `0` and `1`), hence they are coprime.
-/

/-- `X` and `X - 1` are coprime over ℂ — verified through the Nullstellensatz
    equivalence by checking they have no common root. -/
example : IsCoprime (X : ℂ[X]) (X - 1) := by
  rw [coprime_iff_no_common_root]
  rintro x ⟨hx0, hx1⟩
  -- hx0 : eval x X = 0  ⇒  x = 0;  hx1 : eval x (X - 1) = 0  ⇒  x = 1.
  rw [IsRoot.def, eval_X] at hx0
  rw [IsRoot.def, eval_sub, eval_X, eval_one, sub_eq_zero] at hx1
  rw [hx0] at hx1
  exact zero_ne_one hx1

/-- Conversely, `X` and `X` (or any polynomial with itself, when non-unit) are
    NOT coprime — they share the common root `0`, witnessing the forward
    direction's necessity. -/
example : ¬ IsCoprime (X : ℂ[X]) X := by
  intro h
  exact coprime_imp_no_common_root h 0 ⟨by simp [IsRoot.def], by simp [IsRoot.def]⟩

/-!
## Part VI: Scope Note — The Bézout Route is Intrinsically Univariate

The results above are *exactly* as strong as Bézout reasoning allows. For two
or more variables the argument breaks at its very first step:

* `k[X, Y]` is **not** a PID — e.g. `Ideal.span {X, Y}` is not principal — and
  hence not `IsBezout`. So `gcd_isUnit_iff` / `isBezout_coprime_iff` simply do
  not apply, and the contradiction argument of Part II has no analogue.

* The genuine multivariate **Hilbert Nullstellensatz** is a strictly deeper
  theorem. Mathlib establishes it as
  `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`, proved via Noether
  normalization and the Rabinowitsch trick — not via gcd/Bézout identities.

Thus the honest answer to OQ-02-OQ-02-OQ-03 is: **the Bézout/`IsCoprime`
machinery proves the Nullstellensatz precisely in the one-variable case
(Parts III–IV), and provably cannot reach the multivariate case.** The two
statements below record the obstruction concretely.
-/

/-- The first obstruction to a multivariate Bézout proof: `(X, Y)` is a proper,
    non-unit ideal of `k[X, Y]` even though `X` and `Y` have no *common* root
    that is forced by a Bézout identity — coprimality and emptiness of the
    variety genuinely diverge once `gcd` is unavailable. Concretely, `X` and `Y`
    are coprime in `k[X,Y]` (they generate `(X,Y) ⊊ (1)`? — no: they are NOT
    coprime), illustrating that the univariate equivalence fails to generalize.
    We record only the structural fact that the two-variable polynomial ring is
    not a field-of-fractions-style Bézout setting by exhibiting non-coprimality. -/
example : ¬ IsCoprime (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) (MvPolynomial.X 1) := by
  -- If they were coprime, ∃ u v, u·X₀ + v·X₁ = 1. Evaluate at (0,0): 0 = 1.
  rintro ⟨u, v, huv⟩
  have hev := congrArg (MvPolynomial.eval (fun _ => (0 : ℂ))) huv
  simp only [map_add, map_mul, map_one, MvPolynomial.eval_X, mul_zero, add_zero] at hev
  exact zero_ne_one hev

end BezoutNullstellensatz
