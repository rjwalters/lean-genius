import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

/-!
# The Eisenstein integers ℤ[ω] — ring, norm, and Euclidean structure

This file is the S2 + S3 ACT deliverable for `zsqrtd-neg-two-oq-03`. It
builds the algebraic infrastructure for the long-term target

  `sq_add_three_sq_of_prime_one_mod_three :`
  `  ∀ {p : ℕ}, p.Prime → p % 3 = 1 → ∃ a b : ℤ, (p : ℤ) = a ^ 2 + 3 * b ^ 2`

which generalises the parent file `Proofs/ZsqrtdNegTwo.lean` (the case
`n = 2`) to the next non-trivial Heegner-number case `n = 3`. Unlike
`n = 2`, the maximal order of `ℚ(√-3)` is **not** `ℤ[√-3]` but the
**Eisenstein integers** `ℤ[ω] = ℤ[exp(2πi/3)]`, with `ω² + ω + 1 = 0`.
Mathlib's `Zsqrtd` therefore does **not** apply directly; we build a
fresh concrete structure on `re, im : ℤ` representing `re + im · ω`.

## Contents of this file

S2 ACT — bare ring + norm (lines ≈ 56–207):

* `Eisenstein` — the underlying type, two integer coordinates `re, im`.
* `Zero`, `One`, `Add`, `Neg`, `Mul` — primitive instances together with
  `@[simp] rfl` projection lemmas, derived from the rule
  `ω² = -1 - ω` so that
  `(a + bω)(c + dω) = (ac - bd) + (ad + bc - bd) · ω`.
* `AddCommGroup`, `AddGroupWithOne`, `CommRing` — built via the same
  `refine ... <;> intros <;> ext <;> simp <;> ring` template that
  Mathlib uses for `Zsqrtd.commRing` (see
  `Mathlib/NumberTheory/Zsqrtd/Basic.lean` ≈ line 164).
* `norm` — the algebraic norm `N(a + bω) = a² - ab + b²`, with
  `norm_nonneg` (via `4 · N(z) = (2re - im)² + 3 im²`), `norm_mul`,
  `norm_eq_zero_iff`, `norm_pos_of_ne_zero`.

S3 ACT — Euclidean structure (lines ≈ 209 onward):

* `conj` — the Eisenstein conjugate `(a + bω) ↦ (a - b) + (-b)ω`,
  satisfying `z · conj z = N(z)` and `N(conj z) = N(z)`.
* `instDiv`, `instMod`, `mod_def` — division by rounding the rational
  quotient `(x · conj y) / N(y)` to the nearest lattice point.
* `sq_rounding_error_lt_one` — the geometric core: the worst-case
  rounding error satisfies `ε_re² - ε_re · ε_im + ε_im² ≤ 3/4 < 1`,
  using the algebraic identity `4(a² - ab + b²) = (2a - b)² + 3b²`.
* `norm_mod_lt` — `N(x % y) < N(y)` for `y ≠ 0`, the central
  decreasing-norm inequality.
* `instEuclideanDomain` — assembled from the above via
  `EuclideanDomain.r = (norm ·).natAbs <`.

S4 ACT (incremental — Step 1 + `mul_conj` projections):

* `mul_conj_re`, `mul_conj_im` — `@[simp]` projection lemmas for
  `z · conj z` (absorbed from the stranded
  `research/zsqrtd-neg-two-oq03-s3-act-1778799640` branch per S8 PREP §1
  and S12 PREP §6).
* `legendreSym_neg_three` — Step 1 of the splitting argument:
  `(-3/p) = (-1/p) · (3/p)` via `legendreSym.mul`.

## What is **not** in this file

Steps 2 (`(-3/p) = 1 ↔ p ≡ 1 mod 3` via QR + `at_neg_one`) and 3
(extract `α, β ∈ Eisenstein` with `p = α · β` and neither a unit) are
deferred to a later iteration; the paste-ready skeleton lives in
`research/problems/zsqrtd-neg-two-oq-03/sessions/2026-05-16-s12-prep-json-drift-fix-bearer-respotcheck-s4-act-paste-ready.md`
§5 (with 1 acknowledged sorry on the `exists_sq_eq_neg_three_iff`
derivation step).

The Euclidean structure is the foundation for the splitting argument:
once `Eisenstein` is a Euclidean domain it is automatically a UFD, so
non-irreducibility of `(p : Eisenstein)` (which S4 will derive from
quadratic reciprocity) yields a non-trivial factorisation
`p = α · β`, hence `N(α) · N(β) = p²` with both norms strictly between
`1` and `p²`, forcing `N(α) = p`.

This file has 0 axioms, 0 sorries.
-/

/-- Closed `decide` helper hoisted outside `namespace Proofs`: `(2 : ZMod 3) ≠ 0`.
    Used inside `legendreSym_three_eq_one_iff_p_mod_three_eq_one`; the in-namespace
    `by decide` failed with a "free variables" error due to the surrounding
    universe-polymorphic context. -/
private lemma two_ne_zero_zmod_three : (2 : ZMod 3) ≠ 0 := by decide

/-- Closed `decide` helper hoisted outside `namespace Proofs`: `2` is not a square
    in `ZMod 3`. Used inside `legendreSym_three_eq_one_iff_p_mod_three_eq_one`. -/
private lemma not_isSquare_two_zmod_three : ¬ IsSquare (2 : ZMod 3) := by
  rintro ⟨r, hr⟩
  have : ∀ x : ZMod 3, x * x ≠ 2 := by decide
  exact this r hr.symm

namespace Proofs

/-- The Eisenstein integers `ℤ[ω]`, where `ω = exp(2πi/3)` is a
primitive cube root of unity satisfying `ω² + ω + 1 = 0`. An element
`re + im · ω` is represented by its two integer coordinates. -/
@[ext]
structure Eisenstein where
  /-- The "rational" (real) coordinate of `re + im · ω`. -/
  re : ℤ
  /-- The "`ω`" coordinate of `re + im · ω`. -/
  im : ℤ
  deriving DecidableEq

namespace Eisenstein

/-- Convert an integer to an Eisenstein integer. -/
def ofInt (n : ℤ) : Eisenstein := ⟨n, 0⟩

theorem re_ofInt (n : ℤ) : (ofInt n).re = n := rfl
theorem im_ofInt (n : ℤ) : (ofInt n).im = 0 := rfl

instance : Zero Eisenstein := ⟨ofInt 0⟩
instance : One  Eisenstein := ⟨ofInt 1⟩

instance : Add Eisenstein :=
  ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩

instance : Neg Eisenstein :=
  ⟨fun x => ⟨-x.re, -x.im⟩⟩

/-- The Eisenstein product. From `ω² = -1 - ω`:
`(a + bω)(c + dω) = ac + (ad + bc) ω + bd · ω²`
`               = ac + (ad + bc) ω + bd · (-1 - ω)`
`               = (ac - bd) + (ad + bc - bd) · ω`. -/
instance : Mul Eisenstein :=
  ⟨fun x y => ⟨x.re * y.re - x.im * y.im,
               x.re * y.im + x.im * y.re - x.im * y.im⟩⟩

@[simp] theorem zero_re : (0 : Eisenstein).re = 0 := rfl
@[simp] theorem zero_im : (0 : Eisenstein).im = 0 := rfl
@[simp] theorem one_re  : (1 : Eisenstein).re = 1 := rfl
@[simp] theorem one_im  : (1 : Eisenstein).im = 0 := rfl

@[simp] theorem add_re (x y : Eisenstein) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : Eisenstein) : (x + y).im = x.im + y.im := rfl

@[simp] theorem neg_re (x : Eisenstein) : (-x).re = -x.re := rfl
@[simp] theorem neg_im (x : Eisenstein) : (-x).im = -x.im := rfl

@[simp] theorem mul_re (x y : Eisenstein) :
    (x * y).re = x.re * y.re - x.im * y.im := rfl

@[simp] theorem mul_im (x y : Eisenstein) :
    (x * y).im = x.re * y.im + x.im * y.re - x.im * y.im := rfl

instance addCommGroup : AddCommGroup Eisenstein := by
  refine
  { sub := fun a b => a + -b
    nsmul := @nsmulRec Eisenstein ⟨0⟩ ⟨(· + ·)⟩
    zsmul := @zsmulRec Eisenstein ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩
             (@nsmulRec Eisenstein ⟨0⟩ ⟨(· + ·)⟩)
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    neg_add_cancel := ?_
    add_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp [add_comm, add_left_comm]

@[simp] theorem sub_re (x y : Eisenstein) : (x - y).re = x.re - y.re := by
  show (x + -y).re = x.re - y.re
  simp [sub_eq_add_neg]

@[simp] theorem sub_im (x y : Eisenstein) : (x - y).im = x.im - y.im := by
  show (x + -y).im = x.im - y.im
  simp [sub_eq_add_neg]

instance addGroupWithOne : AddGroupWithOne Eisenstein :=
  { Eisenstein.addCommGroup with
    natCast := fun n => ofInt (n : ℤ)
    intCast := ofInt }

instance commRing : CommRing Eisenstein := by
  refine
  { Eisenstein.addGroupWithOne with
    npow := @npowRec Eisenstein ⟨1⟩ ⟨(· * ·)⟩
    add_comm := ?_
    left_distrib := ?_
    right_distrib := ?_
    zero_mul := ?_
    mul_zero := ?_
    mul_assoc := ?_
    one_mul := ?_
    mul_one := ?_
    mul_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp <;>
  ring

/-! ## The Eisenstein norm `N(a + bω) = a² - ab + b²` -/

/-- The Eisenstein norm: `N(a + bω) = a² - ab + b²`. -/
def norm (z : Eisenstein) : ℤ := z.re ^ 2 - z.re * z.im + z.im ^ 2

@[simp] theorem norm_zero : norm (0 : Eisenstein) = 0 := by
  simp [norm]

@[simp] theorem norm_one : norm (1 : Eisenstein) = 1 := by
  simp [norm]

/-- The Eisenstein norm is non-negative, via the algebraic identity
`4 · N(z) = (2 re - im)² + 3 · im²`. -/
theorem norm_nonneg (z : Eisenstein) : 0 ≤ norm z := by
  have h4 : (4 : ℤ) * norm z = (2 * z.re - z.im) ^ 2 + 3 * z.im ^ 2 := by
    simp only [norm]; ring
  nlinarith [sq_nonneg (2 * z.re - z.im), sq_nonneg z.im]

/-- The Eisenstein norm is multiplicative:
`N((a + bω)(c + dω)) = N(a + bω) · N(c + dω)`. -/
theorem norm_mul (x y : Eisenstein) : norm (x * y) = norm x * norm y := by
  simp only [norm, mul_re, mul_im]
  ring

/-- The Eisenstein norm vanishes only on zero. -/
theorem norm_eq_zero_iff (z : Eisenstein) : norm z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    -- `4 · 0 = (2 re - im)² + 3 · im²`, so both squares vanish.
    have h4 : (4 : ℤ) * norm z = (2 * z.re - z.im) ^ 2 + 3 * z.im ^ 2 := by
      simp only [norm]; ring
    rw [hz, mul_zero] at h4
    have him_sq : (3 : ℤ) * z.im ^ 2 = 0 := by
      nlinarith [sq_nonneg (2 * z.re - z.im), sq_nonneg z.im]
    have him_sq' : z.im ^ 2 = 0 := by linarith [sq_nonneg z.im]
    have him : z.im = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp him_sq'
    have hre_sq : (2 * z.re - z.im) ^ 2 = 0 := by linarith
    have hre' : 2 * z.re - z.im = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hre_sq
    have hre : z.re = 0 := by
      have : 2 * z.re = z.im := by linarith
      rw [him] at this
      linarith
    ext <;> simp [hre, him]
  · rintro rfl
    simp

/-- The Eisenstein norm of a nonzero element is strictly positive. -/
theorem norm_pos_of_ne_zero {z : Eisenstein} (hz : z ≠ 0) : 0 < norm z := by
  have hnn := norm_nonneg z
  rcases lt_or_eq_of_le hnn with hpos | hzero
  · exact hpos
  · exfalso; exact hz ((norm_eq_zero_iff z).mp hzero.symm)

/-! ## The Eisenstein conjugate and division by rounding (S3) -/

/-- The Eisenstein conjugate. For a primitive cube root of unity `ω`,
complex conjugation acts as `ω̄ = ω² = -1 - ω`, giving
`(a + bω)̄ = a + b·(-1 - ω) = (a - b) + (-b)·ω`. -/
def conj (z : Eisenstein) : Eisenstein := ⟨z.re - z.im, -z.im⟩

@[simp] theorem conj_re (z : Eisenstein) : (conj z).re = z.re - z.im := rfl
@[simp] theorem conj_im (z : Eisenstein) : (conj z).im = -z.im := rfl

/-- The Eisenstein conjugate preserves the norm:
`N(conj z) = (a - b)² - (a - b)·(-b) + (-b)² = a² - ab + b² = N(z)`. -/
theorem norm_conj (z : Eisenstein) : norm (conj z) = norm z := by
  simp only [norm, conj_re, conj_im]; ring

/-- `z · conj z` collapses to the constant integer `N(z)` (no `ω` part). -/
theorem mul_conj (z : Eisenstein) : z * conj z = ⟨norm z, 0⟩ := by
  ext
  · simp only [mul_re, conj_re, conj_im, norm]; ring
  · simp only [mul_im, conj_re, conj_im]; ring

/-- `re`-projection of `z · conj z`: the lattice-projection identity. -/
@[simp] theorem mul_conj_re (z : Eisenstein) : (z * conj z).re = norm z := by
  rw [mul_conj]

/-- `im`-projection of `z · conj z`: the conjugate-product is real. -/
@[simp] theorem mul_conj_im (z : Eisenstein) : (z * conj z).im = 0 := by
  rw [mul_conj]

/-- Division in `ℤ[ω]` by rounding the rational quotient
`(x · conj y) / N(y)` componentwise to the nearest integer. -/
noncomputable instance instDiv : Div Eisenstein :=
  ⟨fun x y =>
    let n : ℚ := (norm y : ℚ)⁻¹
    let c := conj y
    ⟨round ((x * c).re * n), round ((x * c).im * n)⟩⟩

/-- Modulo derived from division: `x % y := x - y · (x / y)`. -/
noncomputable instance instMod : Mod Eisenstein :=
  ⟨fun x y => x - y * (x / y)⟩

theorem mod_def (x y : Eisenstein) : x % y = x - y * (x / y) := rfl

/-- The squared rounding error for the Eisenstein lattice is strictly
less than one. The algebraic identity
`4 · (a² - ab + b²) = (2a - b)² + 3 b²`
plus the per-coordinate bound `|a|, |b| ≤ 1/2` give
`(2a - b)² ≤ 9/4` and `3 b² ≤ 3/4`, so
`a² - ab + b² ≤ 3/4 < 1`. -/
theorem sq_rounding_error_lt_one (r₁ r₂ : ℚ) :
    (r₁ - round r₁) ^ 2 - (r₁ - round r₁) * (r₂ - round r₂)
      + (r₂ - round r₂) ^ 2 < 1 := by
  have h1 : |r₁ - round r₁| ≤ 1 / 2 := abs_sub_round r₁
  have h2 : |r₂ - round r₂| ≤ 1 / 2 := abs_sub_round r₂
  have habs1 := abs_le.mp h1
  have habs2 := abs_le.mp h2
  have hid : 4 * ((r₁ - round r₁) ^ 2
                  - (r₁ - round r₁) * (r₂ - round r₂)
                  + (r₂ - round r₂) ^ 2)
           = (2 * (r₁ - round r₁) - (r₂ - round r₂)) ^ 2
             + 3 * (r₂ - round r₂) ^ 2 := by ring
  have hbound1 : (2 * (r₁ - round r₁) - (r₂ - round r₂)) ^ 2 ≤ 9 / 4 := by
    nlinarith [habs1.1, habs1.2, habs2.1, habs2.2,
               sq_nonneg (2 * (r₁ - round r₁) - (r₂ - round r₂))]
  have hbound2 : 3 * (r₂ - round r₂) ^ 2 ≤ 3 / 4 := by
    nlinarith [habs2.1, habs2.2, sq_nonneg (r₂ - round r₂)]
  linarith

/-- The norm of the remainder is strictly less than the norm of the
divisor. This is the central Euclidean inequality:
`N(x - y · (x / y)) < N(y)`. -/
theorem norm_mod_lt (x : Eisenstein) {y : Eisenstein} (hy : y ≠ 0) :
    norm (x % y) < norm y := by
  -- Setup: rational reciprocal of `n := N(y)`, conjugate product, errors.
  let n : ℤ := norm y
  have hn_pos : 0 < n := norm_pos_of_ne_zero hy
  have hn_rat_pos : (0 : ℚ) < n := by exact_mod_cast hn_pos
  let A := x * conj y
  let q := x / y
  let r := x % y
  have hq_re : q.re = round ((A.re : ℚ) / n) := rfl
  have hq_im : q.im = round ((A.im : ℚ) / n) := rfl
  -- Rounding errors in ℚ.
  let ε_re : ℚ := (A.re : ℚ) / n - q.re
  let ε_im : ℚ := (A.im : ℚ) / n - q.im
  -- `y · conj y = ⟨n, 0⟩` (the lattice-projection identity).
  have hy_conj : y * conj y = ⟨n, 0⟩ := mul_conj y
  -- `r · conj y = A - ⟨n, 0⟩ · q`.
  have hr_conj : r * conj y = A - ⟨n, 0⟩ * q := by
    show (x - y * q) * conj y = x * conj y - ⟨n, 0⟩ * q
    calc (x - y * q) * conj y
        = x * conj y - y * q * conj y := by ring
      _ = x * conj y - y * conj y * q := by ring
      _ = x * conj y - ⟨n, 0⟩ * q := by rw [hy_conj]
  -- Component-wise: `(r · conj y).re = A.re - n · q.re`, ditto `.im`.
  have hr_conj_re : (r * conj y).re = A.re - n * q.re := by
    rw [hr_conj]
    show A.re - (⟨n, 0⟩ * q).re = A.re - n * q.re
    simp [mul_re]
  have hr_conj_im : (r * conj y).im = A.im - n * q.im := by
    rw [hr_conj]
    show A.im - (⟨n, 0⟩ * q).im = A.im - n * q.im
    simp [mul_im]
  -- Cast to ℚ: `((r · conj y).re : ℚ) = n · ε_re`, ditto `.im`.
  have hn_rat_ne : (n : ℚ) ≠ 0 := hn_rat_pos.ne'
  have hr_conj_re_rat : ((r * conj y).re : ℚ) = n * ε_re := by
    rw [hr_conj_re]
    show ((A.re - n * q.re : ℤ) : ℚ) = (n : ℚ) * ((A.re : ℚ) / n - q.re)
    push_cast
    field_simp
  have hr_conj_im_rat : ((r * conj y).im : ℚ) = n * ε_im := by
    rw [hr_conj_im]
    show ((A.im - n * q.im : ℤ) : ℚ) = (n : ℚ) * ((A.im : ℚ) / n - q.im)
    push_cast
    field_simp
  -- The Eisenstein-lattice rounding-error bound: `ε_re² - ε_re·ε_im + ε_im² < 1`.
  have hbound : ε_re ^ 2 - ε_re * ε_im + ε_im ^ 2 < 1 := by
    have h := sq_rounding_error_lt_one ((A.re : ℚ) / n) ((A.im : ℚ) / n)
    -- ε_re = (A.re : ℚ) / n - q.re = (A.re : ℚ) / n - round((A.re : ℚ) / n)
    show ((A.re : ℚ) / n - q.re) ^ 2 - ((A.re : ℚ) / n - q.re) * ((A.im : ℚ) / n - q.im)
         + ((A.im : ℚ) / n - q.im) ^ 2 < 1
    rw [hq_re, hq_im]
    exact h
  -- Multiplicativity of `norm`: `N(r · conj y) = N(r) · N(conj y) = N(r) · n`.
  have hnorm_mul_eq : norm (r * conj y) = norm r * n := by
    rw [norm_mul, norm_conj]
  -- Compute `N(r · conj y) : ℚ` algebraically in terms of `n` and `ε_re, ε_im`.
  have hnorm_r_conj_rat :
      (norm (r * conj y) : ℚ) = n ^ 2 * (ε_re ^ 2 - ε_re * ε_im + ε_im ^ 2) := by
    have hre := hr_conj_re_rat
    have him := hr_conj_im_rat
    unfold norm
    push_cast
    calc ((r * conj y).re : ℚ) ^ 2
            - ((r * conj y).re : ℚ) * ((r * conj y).im : ℚ)
            + ((r * conj y).im : ℚ) ^ 2
        = (n * ε_re) ^ 2 - (n * ε_re) * (n * ε_im) + (n * ε_im) ^ 2 := by
              rw [hre, him]
      _ = (n : ℚ) ^ 2 * (ε_re ^ 2 - ε_re * ε_im + ε_im ^ 2) := by ring
  -- Conclude `(N(r) : ℚ) < n`, hence `N(r) < n` in ℤ.
  have hlt : (norm r : ℚ) * n < (n : ℚ) ^ 2 := by
    have hcast : (norm r : ℚ) * n = (norm (r * conj y) : ℚ) := by
      have step : ((norm r * n : ℤ) : ℚ) = (norm (r * conj y) : ℚ) := by
        rw [hnorm_mul_eq]
      push_cast at step
      exact step
    have hbound' : (n : ℚ) ^ 2 * (ε_re ^ 2 - ε_re * ε_im + ε_im ^ 2) < (n : ℚ) ^ 2 * 1 := by
      have hn_sq_pos : 0 < (n : ℚ) ^ 2 := by positivity
      nlinarith [hbound, hn_sq_pos]
    rw [hcast, hnorm_r_conj_rat]
    linarith
  have hfinal : (norm r : ℚ) < n := by
    have hr_nn : (0 : ℚ) ≤ norm r := by exact_mod_cast norm_nonneg r
    -- `(norm r : ℚ) · n < n²` with `0 < n` gives `(norm r : ℚ) < n`.
    nlinarith [hlt, hn_rat_pos, hr_nn]
  exact_mod_cast hfinal

/-- The natural-absolute-value version of `norm_mod_lt`, packaged as the
strict-decrease witness for the `EuclideanDomain` instance. -/
theorem natAbs_norm_mod_lt (x : Eisenstein) {y : Eisenstein} (hy : y ≠ 0) :
    (norm (x % y)).natAbs < (norm y).natAbs := by
  have h := norm_mod_lt x hy
  have h1 := norm_nonneg (x % y)
  have h2 := norm_nonneg y
  exact Int.natAbs_lt_natAbs_of_nonneg_of_lt h1 h

/-- Multiplying on the right by a non-zero element does not decrease
the `.natAbs` of the norm. (Used to discharge the
`mul_left_not_lt` field of `EuclideanDomain`.) -/
theorem norm_le_norm_mul_left (x : Eisenstein) {y : Eisenstein} (hy : y ≠ 0) :
    (norm x).natAbs ≤ (norm (x * y)).natAbs := by
  rw [norm_mul, Int.natAbs_mul]
  have hy_pos : 0 < norm y := norm_pos_of_ne_zero hy
  have h : 1 ≤ (norm y).natAbs := by
    have : 1 ≤ norm y := hy_pos
    omega
  exact Nat.le_mul_of_pos_right _ (by omega)

noncomputable instance instNontrivial : Nontrivial Eisenstein :=
  ⟨⟨0, 1, by decide⟩⟩

/-- Strict ordering on Eisenstein integers via the `.natAbs` of the norm.
Used to instantiate the well-founded relation `r` in `EuclideanDomain`. -/
noncomputable instance instLT : LT Eisenstein :=
  ⟨fun x y => (norm x).natAbs < (norm y).natAbs⟩

/-- `Eisenstein = ℤ[ω]` is a Euclidean domain, with Euclidean function
`(norm ·).natAbs` and division by rounding. -/
noncomputable instance instEuclideanDomain : EuclideanDomain Eisenstein :=
  { inferInstanceAs (CommRing Eisenstein) with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := by
      intro a
      show (a / 0 : Eisenstein) = 0
      have hzero : (norm (0 : Eisenstein) : ℚ)⁻¹ = 0 := by
        rw [norm_zero]; simp
      ext
      · show round ((a * conj 0).re * (norm (0 : Eisenstein) : ℚ)⁻¹)
              = (0 : Eisenstein).re
        rw [hzero, mul_zero, round_zero, zero_re]
      · show round ((a * conj 0).im * (norm (0 : Eisenstein) : ℚ)⁻¹)
              = (0 : Eisenstein).im
        rw [hzero, mul_zero, round_zero, zero_im]
    quotient_mul_add_remainder_eq := fun x y => by simp only [mod_def]; ring
    r := (· < ·)
    r_wellFounded := (measure fun z : Eisenstein => (norm z).natAbs).wf
    remainder_lt := fun x y hy => natAbs_norm_mod_lt x hy
    mul_left_not_lt := fun a b hb0 => not_lt_of_ge (norm_le_norm_mul_left a hb0) }

end Eisenstein

/-! ## S4 splitting argument — Step 1: `(-3/p) = (-1/p) · (3/p)`

This is the first ingredient of the splitting argument toward
`sq_add_three_sq_of_prime_one_mod_three`: the Legendre-symbol identity
`(-3/p) = (-1/p) · (3/p)`, derived from the multiplicativity of the
Legendre symbol (`legendreSym.mul`). Steps 2 (`(-3/p) = 1 ↔ p ≡ 1 mod 3`)
and 3 (extract `α, β ∈ Eisenstein` with `p = α · β` and neither a unit)
are deferred to a later iteration; see
`research/problems/zsqrtd-neg-two-oq-03/sessions/2026-05-16-s12-prep-json-drift-fix-bearer-respotcheck-s4-act-paste-ready.md`
§5 for the full paste-ready S4 ACT skeleton. -/

/-- Multiplicativity step: `(-3/p) = (-1/p) · (3/p)`. First lemma of the
S4 splitting argument. The hypothesis `[Fact p.Prime]` is required by
`legendreSym`; no other primality hypothesis (e.g. `p ≠ 2`, `p ≠ 3`) is
needed at this step. -/
lemma legendreSym_neg_three (p : ℕ) [Fact p.Prime] :
    legendreSym p (-3) = legendreSym p (-1) * legendreSym p 3 := by
  rw [show ((-3 : ℤ) = (-1) * 3) by norm_num, legendreSym.mul]

/-- Helper: `(p/3) = 1 ↔ p ≡ 1 mod 3` for primes `p ≠ 3`.

    Reduces to `IsSquare ((p : ℕ) : ZMod 3)` via `legendreSym.eq_one_iff'`,
    then case-splits on `p % 3 ∈ {1, 2}` (forced by `p ≠ 3` so `p % 3 ≠ 0`).
    Branch `p % 3 = 1`: `(1 : ZMod 3)` is a square (`1 = 1 * 1`).
    Branch `p % 3 = 2`: `(2 : ZMod 3)` is not a square (`decide` on
    the finite codomain). -/
private lemma legendreSym_three_eq_one_iff_p_mod_three_eq_one
    (p : ℕ) [hp_fact : Fact p.Prime] (hp_ne_three : p ≠ 3) :
    legendreSym 3 p = 1 ↔ p % 3 = 1 := by
  haveI : Fact (3 : ℕ).Prime := ⟨by decide⟩
  have hp_prime := hp_fact.out
  have hp_mod_3 : p % 3 = 1 ∨ p % 3 = 2 := by
    have h0 : p % 3 ≠ 0 := by
      intro h
      have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
      rcases hp_prime.eq_one_or_self_of_dvd 3 hdvd with h1 | h3
      · exact absurd h1 (by decide)
      · exact hp_ne_three h3.symm
    have := Nat.mod_lt p (by norm_num : 0 < 3)
    omega
  have hp_cast : (p : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod p 3).symm
  rcases hp_mod_3 with hmod | hmod
  · -- p % 3 = 1: both sides true.
    have hpZ : (p : ZMod 3) = 1 := by rw [hp_cast, hmod]; rfl
    have ha0 : (p : ZMod 3) ≠ 0 := by rw [hpZ]; exact one_ne_zero
    refine ⟨fun _ => hmod, fun _ => ?_⟩
    rw [legendreSym.eq_one_iff' (3 : ℕ) ha0, hpZ]
    exact ⟨1, by ring⟩
  · -- p % 3 = 2: both sides false.
    have hpZ : (p : ZMod 3) = 2 := by rw [hp_cast, hmod]; rfl
    have ha0 : (p : ZMod 3) ≠ 0 := by
      rw [hpZ]; exact two_ne_zero_zmod_three
    refine ⟨fun hLS => ?_, fun h => ?_⟩
    · rw [legendreSym.eq_one_iff' (3 : ℕ) ha0, hpZ] at hLS
      exact (not_isSquare_two_zmod_three hLS).elim
    · exact absurd (h.symm.trans hmod) (by decide)

/-- Step 2 of the splitting argument: for an odd prime `p ≠ 3`,
    `(-3/p) = 1 ↔ p ≡ 1 mod 3`. The classical Heegner-number
    characterization of the primes representable as `x² + 3y²`.

    Proof strategy:
    1. Decompose via `legendreSym_neg_three`: `(-3/p) = (-1/p) · (3/p)`.
    2. Compute `(-1/p) = χ₄ p` via `legendreSym.at_neg_one`.
    3. Case-split on `p % 4 ∈ {1, 3}`:
       - `p % 4 = 1`: `χ₄ p = 1`; QR_one_mod_four gives `(3/p) = (p/3)`.
       - `p % 4 = 3`: `χ₄ p = -1`; QR_three_mod_four gives
         `(3/p) = -(p/3)`. The two `-1`s cancel.
    4. Both branches reduce to `(p/3) = 1 ↔ p ≡ 1 mod 3`
       via `legendreSym_three_eq_one_iff_p_mod_three_eq_one`. -/
lemma legendreSym_neg_three_eq_one_iff
    (p : ℕ) [hp_fact : Fact p.Prime]
    (hp_ne_two : p ≠ 2) (hp_ne_three : p ≠ 3) :
    legendreSym p (-3) = 1 ↔ p % 3 = 1 := by
  rw [legendreSym_neg_three p, legendreSym.at_neg_one (p := p) hp_ne_two]
  haveI : Fact (3 : ℕ).Prime := ⟨by decide⟩
  have hp_prime := hp_fact.out
  have hp_mod_4 : p % 4 = 1 ∨ p % 4 = 3 := by
    have hp_odd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp_prime).mpr hp_ne_two
    have := Nat.mod_lt p (by norm_num : 0 < 4)
    omega
  -- Normalize `(3 : ℤ)` to `((3 : ℕ) : ℤ)` so QR's RHS pattern matches.
  have h3cast : (3 : ℤ) = ((3 : ℕ) : ℤ) := by norm_cast
  rcases hp_mod_4 with hp4 | hp4
  · -- p % 4 = 1: χ₄ p = 1; QR gives (3/p) = (p/3).
    rw [ZMod.χ₄_nat_one_mod_four hp4, one_mul, h3cast,
        ← legendreSym.quadratic_reciprocity_one_mod_four hp4
          (by decide : (3 : ℕ) ≠ 2)]
    exact legendreSym_three_eq_one_iff_p_mod_three_eq_one p hp_ne_three
  · -- p % 4 = 3: χ₄ p = -1; QR gives (3/p) = -(p/3).
    rw [ZMod.χ₄_nat_three_mod_four hp4]
    have hQR : legendreSym 3 p = -legendreSym p ((3 : ℕ) : ℤ) :=
      legendreSym.quadratic_reciprocity_three_mod_four hp4
        (by decide : (3 : ℕ) % 4 = 3)
    -- From hQR: legendreSym p 3 = -legendreSym 3 p.
    have hQR' : legendreSym p ((3 : ℕ) : ℤ) = -legendreSym 3 p := by linarith [hQR]
    rw [h3cast, hQR']
    rw [show ((-1 : ℤ) * -legendreSym 3 p = legendreSym 3 p) from by ring]
    exact legendreSym_three_eq_one_iff_p_mod_three_eq_one p hp_ne_three

end Proofs
