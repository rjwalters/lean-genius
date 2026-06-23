/-
  Newton–Girard k=4 Closed Form:  p₄ = e₁⁴ − 4·e₁²·e₂ + 2·e₂² + 4·e₁·e₃ − 4·e₄

  Open Question (amgm-inequality-oq-02-oq-01-oq-03-oq-01), the next rung after the
  k=3 closed form `amgm-inequality-oq-02-oq-01-oq-03`.

  Establish the fully reduced k=4 Newton–Girard identity expressing the fourth power
  sum p₄ purely in terms of the elementary symmetric polynomials e₁, e₂, e₃, e₄:
      p₄ = e₁⁴ − 4·e₁²·e₂ + 2·e₂² + 4·e₁·e₃ − 4·e₄.
  For concrete values (a Finset) this is the symmetric-function form of
      a⁴+b⁴+c⁴+d⁴
        = (a+b+c+d)⁴ − 4(a+b+c+d)²·e₂ + 2·e₂² + 4(a+b+c+d)·e₃ − 4·e₄.

  Lineage:
  • Parent    amgm-inequality-oq-02-oq-01             : k=2 identity p₂ = e₁² − 2e₂.
  • Recurrence amgm-inequality-oq-02-oq-01-oq-02-oq-01: p₃ = e₁p₂ − e₂p₁ + 3e₃ and the
                                                        k=1,2 corollaries, all from
                                                        Mathlib's `psum_eq_mul_esymm_sub_sum`.
  • k=3 closed amgm-inequality-oq-02-oq-01-oq-03      : `psum_three_closed`
                                                        (universal) + the concrete
                                                        general-Finset form and the
                                                        char-2-safe `aeval` bridge.

  This file adds the next rung.  Two complementary forms, each 0-sorry / 0-axiom:

  (1) UNIVERSAL (MvPolynomial).  `psum_four_recurrence` extracts the k=4 Newton
      recurrence  p₄ = e₁p₃ − e₂p₂ + e₃p₁ − 4e₄  directly from
      `MvPolynomial.psum_eq_mul_esymm_sub_sum` (antidiagonal filter {(1,3),(2,2),(3,1)},
      lead term (−1)⁵·4·e₄).  Substituting the proven closed forms for p₃, p₂, p₁ and
      ring-normalising yields `psum_four_closed`.

  (2) CONCRETE general-Finset, over an ARBITRARY CommRing (characteristic 2 included).
      Reusing the already-built, n-general `aeval` bridge from the k=3 Finset file
      (`aeval_psum_subtype`, `aeval_esymm_subtype`), the universal closed form transports
      onto the subtype {x // x ∈ s} to give `newton_girard_four_finset` with the e₄/p₄
      bridge lemmas instantiated at n=4.  No characteristic hypothesis is required — the
      same transport that bypassed the char-2 obstruction at k=3 works verbatim here.

  Every coefficient is independently checked over ℚ for n ≤ 5 variables in
  `research/problems/.../lean/verify_newton_girard_k4.py` (residual 0 ⟹ universal).

  Status: PROVED — 0 sorries, 0 axioms.  Holds over any `CommRing`.
  Tags: algebra, symmetric-functions, newton-girard, power-sums, finset, characteristic-two
-/

import Mathlib
import Proofs.AmgmInequalityOQ02OQ01OQ02OQ01
import Proofs.AmgmInequalityOQ02OQ01OQ03
import Proofs.AmgmInequalityOQ02OQ01OQ03Finset

namespace AMGMInequalityOQ02OQ01OQ03OQ01

open MvPolynomial Finset BigOperators Set

-- ============================================================
-- Universal closed form (MvPolynomial setting)
-- ============================================================

section Universal

variable (σ : Type*) (R : Type*) [CommRing R] [Fintype σ]

/-- **Newton–Girard k=4, recurrence form** (universal / MvPolynomial setting):
      p₄ = e₁·p₃ − e₂·p₂ + e₃·p₁ − 4·e₄.

    Proof: apply `psum_eq_mul_esymm_sub_sum` at n = 4.  The antidiagonal
    {a : a.1 + a.2 = 4, 0 < a.1 < 4} = {(1,3), (2,2), (3,1)}, and the lead term is
    (−1)⁵·4·e₄ = −4·e₄, so
      p₄ = −4e₄ − ((−1)¹e₁p₃ + (−1)²e₂p₂ + (−1)³e₃p₁)
         = e₁p₃ − e₂p₂ + e₃p₁ − 4e₄. -/
theorem psum_four_recurrence :
    psum σ R 4 =
      esymm σ R 1 * psum σ R 3 - esymm σ R 2 * psum σ R 2
        + esymm σ R 3 * psum σ R 1 - 4 * esymm σ R 4 := by
  rw [MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 4 (by norm_num)]
  have hfilt : (Finset.antidiagonal 4).filter (fun a : ℕ × ℕ => a.1 ∈ Set.Ioo 0 4) =
               {(1, 3), (2, 2), (3, 1)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_Ioo,
               Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega
  simp only [hfilt,
    Finset.sum_insert (by decide : (1, 3) ∉ ({(2, 2), (3, 1)} : Finset (ℕ × ℕ))),
    Finset.sum_insert (by decide : (2, 2) ∉ ({(3, 1)} : Finset (ℕ × ℕ))),
    Finset.sum_singleton]
  ring

/-- **Newton–Girard k=4, closed form** (universal / MvPolynomial setting):
      p₄ = e₁⁴ − 4·e₁²·e₂ + 2·e₂² + 4·e₁·e₃ − 4·e₄.
    Substitute the proven closed forms `psum_three_closed` (p₃ = e₁³ − 3e₁e₂ + 3e₃),
    `psum_two_eq` (p₂ = e₁² − 2e₂) and `psum_one_eq_esymm_one` (p₁ = e₁) into the
    recurrence `psum_four_recurrence`, then ring-normalise. -/
theorem psum_four_closed :
    psum σ R 4 =
      esymm σ R 1 ^ 4 - 4 * (esymm σ R 1 ^ 2 * esymm σ R 2) + 2 * esymm σ R 2 ^ 2
        + 4 * (esymm σ R 1 * esymm σ R 3) - 4 * esymm σ R 4 := by
  have h4 := psum_four_recurrence σ R
  have h3 := AMGMInequalityOQ02OQ01OQ03.psum_three_closed σ R
  have h2 := AMGMInequalityOQ02OQ01OQ02OQ01.psum_two_eq σ R
  have h1 := AMGMInequalityOQ02OQ01OQ02OQ01.psum_one_eq_esymm_one σ R
  rw [h4, h3, h2, h1]; ring

end Universal

-- ============================================================
-- Concrete general-Finset form, over ANY CommRing (char 2 included)
-- ============================================================

section Concrete

open AMGMInequalityOQ02OQ01OQ03Finset

variable {ι R : Type*} [CommRing R] [DecidableEq ι]

/-- e₄ = Σ over 4-subsets of the product (concrete `powersetCard` form). -/
def e4 (s : Finset ι) (f : ι → R) : R := ∑ t ∈ s.powersetCard 4, ∏ i ∈ t, f i
/-- p₄ = Σ fᵢ⁴. -/
def p4 (s : Finset ι) (f : ι → R) : R := ∑ i ∈ s, f i ^ 4

omit [DecidableEq ι] in
/-- Bridge at degree 4:  `aeval (esymm … 4) = e₄`  (definitional, from the n-general
    `aeval_esymm_subtype`). -/
theorem e4_bridge (s : Finset ι) (f : ι → R) :
    aeval (fun i : {x // x ∈ s} => f i.1) (MvPolynomial.esymm {x // x ∈ s} R 4) = e4 s f :=
  aeval_esymm_subtype s f 4

omit [DecidableEq ι] in
/-- Bridge for the fourth power sum:  `aeval (psum … 4) = p₄`  (definitional, from the
    n-general `aeval_psum_subtype`). -/
theorem p4_bridge (s : Finset ι) (f : ι → R) :
    aeval (fun i : {x // x ∈ s} => f i.1) (MvPolynomial.psum {x // x ∈ s} R 4) = p4 s f :=
  aeval_psum_subtype s f 4

omit [DecidableEq ι] in
/-- **Concrete general-Finset Newton–Girard k=4** over an arbitrary `CommRing`:
      p₄ = e₁⁴ − 4·e₁²·e₂ + 2·e₂² + 4·e₁·e₃ − 4·e₄.
    Transport of the universal `psum_four_closed` across the (char-2-safe) aeval bridge
    onto the subtype {x // x ∈ s}.  No characteristic hypothesis is required. -/
theorem newton_girard_four_finset (s : Finset ι) (f : ι → R) :
    p4 s f =
      e1 s f ^ 4 - 4 * (e1 s f ^ 2 * e2 s f) + 2 * e2 s f ^ 2
        + 4 * (e1 s f * e3 s f) - 4 * e4 s f := by
  have H := congrArg (aeval (fun i : {x // x ∈ s} => f i.1))
    (psum_four_closed {x // x ∈ s} R)
  simpa only [map_add, map_sub, map_mul, map_pow, map_ofNat,
    p4_bridge, e1_bridge, e2_bridge, e3_bridge, e4_bridge] using H

end Concrete

-- ============================================================
-- Concrete 4-variable instance (smallest nondegenerate case)
-- ============================================================

section Explicit

variable {R : Type*} [CommRing R]

/-- **Concrete 4-variable instance** — sum of fourth powers:
      a⁴ + b⁴ + c⁴ + d⁴
        = e₁⁴ − 4·e₁²·e₂ + 2·e₂² + 4·e₁·e₃ − 4·e₄,
    where e₁ = a+b+c+d, e₂ = Σ pairs, e₃ = Σ triples, e₄ = abcd.
    This is the n = 4 Finset case of `psum_four_closed`. -/
theorem fourth_power_sum_four (a b c d : R) :
    a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 =
      (a + b + c + d) ^ 4
        - 4 * ((a + b + c + d) ^ 2 * (a*b + a*c + a*d + b*c + b*d + c*d))
        + 2 * (a*b + a*c + a*d + b*c + b*d + c*d) ^ 2
        + 4 * ((a + b + c + d) * (a*b*c + a*b*d + a*c*d + b*c*d))
        - 4 * (a*b*c*d) := by
  ring

end Explicit

end AMGMInequalityOQ02OQ01OQ03OQ01
