/-
  Bézout Identity OQ-02·OQ-01·OQ-01·OQ-01·OQ-02:
  The Nullstellensatz in the multivariate UFD context — the arithmetic obstruction

  Parent `BezoutIdentityOQ02OQ01OQ01OQ01` proves that ℤ[X,Y] (and `MvPolynomial σ R`
  for a UFD `R` and `Fintype σ`) is a UNIQUE FACTORIZATION DOMAIN.  Its open question
  #2 asks: *can we formalize the Nullstellensatz in this multivariate UFD context?*

  The honest answer is **no**, and this file pins down exactly why.  Hilbert's
  Nullstellensatz needs an **algebraically closed FIELD** of coefficients.  Being a
  UFD — even the most arithmetically perfect UFD, `ℤ` — is not enough, and the failure
  is already visible at the level of *constants*.

  The obstruction here is of a DIFFERENT character from the real one studied in
  `FactorRemainderNullstellensatzOQ01OQ02` (where `X² + 1` over ℝ fails for lack of the
  root `i`).  That is a *not-algebraically-closed* obstruction at degree 2.  Here the
  obstruction is *not-a-field*: the prime constant `2 ∈ ℤ` is a nonzero non-unit, so
  the ideal `(2)` is proper, yet `2` never vanishes — its zero locus over ℤ is empty.
  The very same prime `2` is the witness that `(2, X)` is non-principal in the sibling
  proof `BezoutIdentityOQ02OQ01OQ01OQ01OQ01` (ℤ[X,Y] is not a PIR).

  Because Mathlib's `MvPolynomial.zeroLocus` / `vanishingIdeal` are *defined only over
  a field*, we work with elementary ring-level versions `zeroSet` / `vanishingId` valid
  over any commutative ring; the fact that the standard definitions do not even apply
  over `ℤ` is itself part of the answer to the open question.

  Results:
    * `weakNSS_fails_of_nonunit`              — general: a nonzero non-unit constant
                                                `C p` gives a proper ideal `(C p)` with
                                                empty zero locus (weak NSS fails).
    * `not_isUnit_C_two`                      — `C 2` is not a unit in `ℤ[X,…]`.
    * `weak_nullstellensatz_fails_over_int`   — instantiation `R = ℤ`, `p = 2`, any `σ`.
    * `weak_nullstellensatz_fails_over_ZXY`   — the headline `ℤ[X,Y]` case.
    * `strong_nullstellensatz_fails_over_int` — `I(V(2)) = ⊤ ≠ (2).radical`.

  Siblings:
    * `BezoutIdentityOQ02OQ01OQ01OQ01`         — ℤ[X,Y] is a UFD (parent)
    * `BezoutIdentityOQ02OQ01OQ01OQ01OQ01`     — ℤ[X,Y] is not a PIR (prime-2 witness)
    * `FactorRemainderNullstellensatzOQ01OQ02` — failure over ℝ (not-closed obstruction)
-/

import Mathlib

namespace BezoutIdentityOQ02OQ01OQ01OQ01OQ02

open MvPolynomial Ideal

noncomputable section

variable {R : Type*} [CommRing R] {σ : Type*}

-- ============================================================
-- PART I: Ring-level zero locus and vanishing ideal
-- ============================================================

/-- Ring-level zero locus: points of `σ → R` where every polynomial of `I` vanishes
    under evaluation `MvPolynomial.eval`.  Mathlib's `MvPolynomial.zeroLocus` is only
    defined over a field; this elementary version is valid over any commutative ring,
    which is what the UFD `ℤ` requires. -/
def zeroSet (I : Ideal (MvPolynomial σ R)) : Set (σ → R) :=
  {x | ∀ p ∈ I, eval x p = 0}

/-- Ring-level vanishing ideal of a set of points (mirrors Mathlib's `vanishingIdeal`
    with `eval` in place of `aeval`). -/
def vanishingId (V : Set (σ → R)) : Ideal (MvPolynomial σ R) where
  carrier := {p | ∀ x ∈ V, eval x p = 0}
  zero_mem' _ _ := map_zero _
  add_mem' {p q} hp hq x hx := by simp only [hp x hx, hq x hx, add_zero, map_add]
  smul_mem' c q hq x hx := by simp only [hq x hx, smul_eq_mul, mul_zero, map_mul]

@[simp] theorem mem_zeroSet {I : Ideal (MvPolynomial σ R)} {x : σ → R} :
    x ∈ zeroSet I ↔ ∀ p ∈ I, eval x p = 0 := Iff.rfl

@[simp] theorem mem_vanishingId {V : Set (σ → R)} {p : MvPolynomial σ R} :
    p ∈ vanishingId V ↔ ∀ x ∈ V, eval x p = 0 := Iff.rfl

/-- The vanishing ideal of the empty set is everything. -/
theorem vanishingId_empty : vanishingId (∅ : Set (σ → R)) = ⊤ := by
  ext p
  simp only [mem_vanishingId, Submodule.mem_top, iff_true]
  intro x hx
  exact absurd hx (Set.notMem_empty x)

-- ============================================================
-- PART II: The general arithmetic obstruction
-- ============================================================

/-- **Weak Nullstellensatz, general arithmetic obstruction.** A nonzero non-unit
    *constant* `C p` generates a proper ideal whose zero locus is empty: it vanishes
    nowhere (its value is the nonzero constant `p`), yet `(C p) ≠ ⊤` because `C p` is
    not a unit.  So over any commutative ring carrying a nonzero non-unit, the weak
    Nullstellensatz fails.  (Over a field there are no nonzero non-units — that is the
    point.) -/
theorem weakNSS_fails_of_nonunit (p : R) (hp0 : p ≠ 0)
    (hpu : ¬ IsUnit (C p : MvPolynomial σ R)) :
    (Ideal.span {C p} : Ideal (MvPolynomial σ R)) ≠ ⊤ ∧
      zeroSet (Ideal.span {C p}) = (∅ : Set (σ → R)) := by
  refine ⟨?_, ?_⟩
  · intro htop
    rw [Ideal.span_singleton_eq_top] at htop
    exact hpu htop
  · rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    rw [mem_zeroSet] at hx
    have hval : eval x (C p) = 0 := hx (C p) (Ideal.mem_span_singleton_self _)
    rw [eval_C] at hval
    exact hp0 hval

-- ============================================================
-- PART III: The UFD case — failure over ℤ and over ℤ[X,Y]
-- ============================================================

/-- `C 2` is not a unit in `ℤ[X,…]`: applying the ring homomorphism `constantCoeff`
    sends `C 2 ↦ 2`, and `2` is not a unit in `ℤ`. -/
theorem not_isUnit_C_two : ¬ IsUnit (C (2 : ℤ) : MvPolynomial σ ℤ) := by
  intro h
  have h2 : IsUnit (2 : ℤ) := by
    have hm := h.map (constantCoeff (σ := σ) (R := ℤ))
    rwa [constantCoeff_C] at hm
  rw [Int.isUnit_iff] at h2
  rcases h2 with h2 | h2 <;> norm_num at h2

/-- **Weak Nullstellensatz fails over ℤ.** For any index set `σ`, the proper ideal
    `(2) ⊆ ℤ[Xₛ]` has an empty zero locus — the constant `2` never evaluates to `0`,
    yet `(2) ≠ ⊤`.  Over an algebraically closed field a proper ideal always has a
    common zero, so the field hypothesis is essential. -/
theorem weak_nullstellensatz_fails_over_int (σ : Type*) :
    (Ideal.span {C (2 : ℤ)} : Ideal (MvPolynomial σ ℤ)) ≠ ⊤ ∧
      zeroSet (Ideal.span {C (2 : ℤ)}) = (∅ : Set (σ → ℤ)) :=
  weakNSS_fails_of_nonunit (2 : ℤ) (by norm_num) not_isUnit_C_two

/-- **The Nullstellensatz fails over `ℤ[X,Y]`.** Specialization to
    `MvPolynomial (Fin 2) ℤ`, the very ring the parent proves is a UFD: it is a UFD,
    but the Nullstellensatz still fails on it. -/
theorem weak_nullstellensatz_fails_over_ZXY :
    (Ideal.span {C (2 : ℤ)} : Ideal (MvPolynomial (Fin 2) ℤ)) ≠ ⊤ ∧
      zeroSet (Ideal.span {C (2 : ℤ)}) = (∅ : Set (Fin 2 → ℤ)) :=
  weak_nullstellensatz_fails_over_int (Fin 2)

/-- **Strong Nullstellensatz fails over ℤ.** The zero locus of `(2)` is empty, so
    `vanishingId (zeroSet (2)) = ⊤`, while `(2).radical ≠ ⊤` (because `(2) ≠ ⊤`).  The
    identity `I(V(J)) = √J` therefore breaks over the UFD `ℤ`. -/
theorem strong_nullstellensatz_fails_over_int (σ : Type*) :
    vanishingId (zeroSet (Ideal.span {C (2 : ℤ)} : Ideal (MvPolynomial σ ℤ)))
      ≠ (Ideal.span {C (2 : ℤ)}).radical := by
  obtain ⟨hne, hempty⟩ := weak_nullstellensatz_fails_over_int σ
  rw [hempty, vanishingId_empty]
  intro h
  rw [eq_comm, Ideal.radical_eq_top] at h
  exact hne h

end

end BezoutIdentityOQ02OQ01OQ01OQ01OQ02
