/-
  Newton–Girard k=5 Closed Form:
      p₅ = e₁⁵ − 5·e₁³·e₂ + 5·e₁·e₂² + 5·e₁²·e₃ − 5·e₂·e₃ − 5·e₁·e₄ + 5·e₅.

  Open Question (amgm-inequality-oq-02-oq-01-oq-03-oq-01-oq-01), the next rung after the
  k=4 closed form `amgm-inequality-oq-02-oq-01-oq-03-oq-01`.

  Establish the fully reduced k=5 Newton–Girard identity expressing the fifth power sum
  p₅ purely in terms of the elementary symmetric polynomials e₁, e₂, e₃, e₄, e₅:
      p₅ = e₁⁵ − 5·e₁³·e₂ + 5·e₁·e₂² + 5·e₁²·e₃ − 5·e₂·e₃ − 5·e₁·e₄ + 5·e₅.
  For concrete values (a Finset) this is the symmetric-function form of
      a⁵+b⁵+c⁵+d⁵+e⁵
        = e₁⁵ − 5·e₁³·e₂ + 5·e₁·e₂² + 5·e₁²·e₃ − 5·e₂·e₃ − 5·e₁·e₄ + 5·e₅.

  Lineage:
  • Parent     amgm-inequality-oq-02-oq-01             : k=2 identity p₂ = e₁² − 2e₂.
  • Recurrence amgm-inequality-oq-02-oq-01-oq-02-oq-01 : p₃ = e₁p₂ − e₂p₁ + 3e₃ and the
                                                         k=1,2 corollaries.
  • k=3 closed amgm-inequality-oq-02-oq-01-oq-03       : `psum_three_closed`.
  • k=4 closed amgm-inequality-oq-02-oq-01-oq-03-oq-01 : `psum_four_closed` + the concrete
                                                         general-Finset form `newton_girard_four_finset`
                                                         and the e₄/p₄ aeval bridges.

  This file adds the next rung.  Two complementary forms, each 0-sorry / 0-axiom:

  (1) UNIVERSAL (MvPolynomial).  `psum_five_recurrence` extracts the k=5 Newton
      recurrence  p₅ = e₁p₄ − e₂p₃ + e₃p₂ − e₄p₁ + 5e₅  directly from
      `MvPolynomial.psum_eq_mul_esymm_sub_sum` (antidiagonal filter {(1,4),(2,3),(3,2),(4,1)},
      lead term (−1)⁶·5·e₅ = +5·e₅).  Substituting the proven closed forms for p₄, p₃, p₂, p₁
      and ring-normalising yields `psum_five_closed`.

  (2) CONCRETE general-Finset, over an ARBITRARY CommRing (characteristic 2 and 5 included).
      Reusing the already-built, n-general `aeval` bridge from the k=3 Finset file
      (`aeval_psum_subtype`, `aeval_esymm_subtype`) and the e₁..e₄ bridges from the
      parent files, the universal closed form transports onto the subtype {x // x ∈ s} to
      give `newton_girard_five_finset` with the e₅/p₅ bridge lemmas instantiated at n=5.
      No characteristic hypothesis is required — the same transport that bypassed the
      char-2 obstruction at k=3 works verbatim here.

  Every coefficient is independently checked over ℚ for n ≤ 6 variables (residual 0 ⟹
  universal).

  Status: PROVED — 0 sorries, 0 axioms.  Holds over any `CommRing`.
  Tags: algebra, symmetric-functions, newton-girard, power-sums, finset, characteristic-two
-/

import Mathlib
import Proofs.AmgmInequalityOQ02OQ01OQ02OQ01
import Proofs.AmgmInequalityOQ02OQ01OQ03
import Proofs.AmgmInequalityOQ02OQ01OQ03Finset
import Proofs.AmgmInequalityOQ02OQ01OQ03OQ01

namespace AMGMInequalityOQ02OQ01OQ03OQ01OQ01

open MvPolynomial Finset BigOperators Set

-- ============================================================
-- Universal closed form (MvPolynomial setting)
-- ============================================================

section Universal

variable (σ : Type*) (R : Type*) [CommRing R] [Fintype σ]

/-- **Newton–Girard k=5, recurrence form** (universal / MvPolynomial setting):
      p₅ = e₁·p₄ − e₂·p₃ + e₃·p₂ − e₄·p₁ + 5·e₅.

    Proof: apply `psum_eq_mul_esymm_sub_sum` at n = 5.  The antidiagonal
    {a : a.1 + a.2 = 5, 0 < a.1 < 5} = {(1,4), (2,3), (3,2), (4,1)}, and the lead term is
    (−1)⁶·5·e₅ = 5·e₅, so
      p₅ = 5e₅ − ((−1)¹e₁p₄ + (−1)²e₂p₃ + (−1)³e₃p₂ + (−1)⁴e₄p₁)
         = e₁p₄ − e₂p₃ + e₃p₂ − e₄p₁ + 5e₅. -/
theorem psum_five_recurrence :
    psum σ R 5 =
      esymm σ R 1 * psum σ R 4 - esymm σ R 2 * psum σ R 3
        + esymm σ R 3 * psum σ R 2 - esymm σ R 4 * psum σ R 1 + 5 * esymm σ R 5 := by
  rw [MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 5 (by norm_num)]
  have hfilt : (Finset.antidiagonal 5).filter (fun a : ℕ × ℕ => a.1 ∈ Set.Ioo 0 5) =
               {(1, 4), (2, 3), (3, 2), (4, 1)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_Ioo,
               Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega
  simp only [hfilt,
    Finset.sum_insert (by decide : (1, 4) ∉ ({(2, 3), (3, 2), (4, 1)} : Finset (ℕ × ℕ))),
    Finset.sum_insert (by decide : (2, 3) ∉ ({(3, 2), (4, 1)} : Finset (ℕ × ℕ))),
    Finset.sum_insert (by decide : (3, 2) ∉ ({(4, 1)} : Finset (ℕ × ℕ))),
    Finset.sum_singleton]
  ring

/-- **Newton–Girard k=5, closed form** (universal / MvPolynomial setting):
      p₅ = e₁⁵ − 5·e₁³·e₂ + 5·e₁·e₂² + 5·e₁²·e₃ − 5·e₂·e₃ − 5·e₁·e₄ + 5·e₅.
    Substitute the proven closed forms `psum_four_closed` (p₄), `psum_three_closed` (p₃),
    `psum_two_eq` (p₂ = e₁² − 2e₂) and `psum_one_eq_esymm_one` (p₁ = e₁) into the
    recurrence `psum_five_recurrence`, then ring-normalise. -/
theorem psum_five_closed :
    psum σ R 5 =
      esymm σ R 1 ^ 5 - 5 * (esymm σ R 1 ^ 3 * esymm σ R 2)
        + 5 * (esymm σ R 1 * esymm σ R 2 ^ 2) + 5 * (esymm σ R 1 ^ 2 * esymm σ R 3)
        - 5 * (esymm σ R 2 * esymm σ R 3) - 5 * (esymm σ R 1 * esymm σ R 4)
        + 5 * esymm σ R 5 := by
  have h5 := psum_five_recurrence σ R
  have h4 := AMGMInequalityOQ02OQ01OQ03OQ01.psum_four_closed σ R
  have h3 := AMGMInequalityOQ02OQ01OQ03.psum_three_closed σ R
  have h2 := AMGMInequalityOQ02OQ01OQ02OQ01.psum_two_eq σ R
  have h1 := AMGMInequalityOQ02OQ01OQ02OQ01.psum_one_eq_esymm_one σ R
  rw [h5, h4, h3, h2, h1]; ring

end Universal

-- ============================================================
-- Concrete general-Finset form, over ANY CommRing (char 2, 5 included)
-- ============================================================

section Concrete

open AMGMInequalityOQ02OQ01OQ03Finset
open AMGMInequalityOQ02OQ01OQ03OQ01

variable {ι R : Type*} [CommRing R] [DecidableEq ι]

/-- e₅ = Σ over 5-subsets of the product (concrete `powersetCard` form). -/
def e5 (s : Finset ι) (f : ι → R) : R := ∑ t ∈ s.powersetCard 5, ∏ i ∈ t, f i
/-- p₅ = Σ fᵢ⁵. -/
def p5 (s : Finset ι) (f : ι → R) : R := ∑ i ∈ s, f i ^ 5

omit [DecidableEq ι] in
/-- Bridge at degree 5:  `aeval (esymm … 5) = e₅`  (definitional, from the n-general
    `aeval_esymm_subtype`). -/
theorem e5_bridge (s : Finset ι) (f : ι → R) :
    aeval (fun i : {x // x ∈ s} => f i.1) (MvPolynomial.esymm {x // x ∈ s} R 5) = e5 s f :=
  aeval_esymm_subtype s f 5

omit [DecidableEq ι] in
/-- Bridge for the fifth power sum:  `aeval (psum … 5) = p₅`  (definitional, from the
    n-general `aeval_psum_subtype`). -/
theorem p5_bridge (s : Finset ι) (f : ι → R) :
    aeval (fun i : {x // x ∈ s} => f i.1) (MvPolynomial.psum {x // x ∈ s} R 5) = p5 s f :=
  aeval_psum_subtype s f 5

omit [DecidableEq ι] in
/-- **Concrete general-Finset Newton–Girard k=5** over an arbitrary `CommRing`:
      p₅ = e₁⁵ − 5·e₁³·e₂ + 5·e₁·e₂² + 5·e₁²·e₃ − 5·e₂·e₃ − 5·e₁·e₄ + 5·e₅.
    Transport of the universal `psum_five_closed` across the (char-2/5-safe) aeval bridge
    onto the subtype {x // x ∈ s}.  No characteristic hypothesis is required. -/
theorem newton_girard_five_finset (s : Finset ι) (f : ι → R) :
    p5 s f =
      e1 s f ^ 5 - 5 * (e1 s f ^ 3 * e2 s f) + 5 * (e1 s f * e2 s f ^ 2)
        + 5 * (e1 s f ^ 2 * e3 s f) - 5 * (e2 s f * e3 s f) - 5 * (e1 s f * e4 s f)
        + 5 * e5 s f := by
  have H := congrArg (aeval (fun i : {x // x ∈ s} => f i.1))
    (psum_five_closed {x // x ∈ s} R)
  simpa only [map_add, map_sub, map_mul, map_pow, map_ofNat,
    p5_bridge, e1_bridge, e2_bridge, e3_bridge, e4_bridge, e5_bridge] using H

end Concrete

-- ============================================================
-- Concrete 5-variable instance (smallest nondegenerate case)
-- ============================================================

section Explicit

variable {R : Type*} [CommRing R]

/-- **Concrete 5-variable instance** — sum of fifth powers:
      a⁵ + b⁵ + c⁵ + d⁵ + e⁵
        = e₁⁵ − 5·e₁³·e₂ + 5·e₁·e₂² + 5·e₁²·e₃ − 5·e₂·e₃ − 5·e₁·e₄ + 5·e₅,
    where e₁ = a+b+c+d+e, e₂ = Σ pairs, e₃ = Σ triples, e₄ = Σ quadruples, e₅ = abcde.
    This is the n = 5 Finset case of `psum_five_closed`. -/
theorem fifth_power_sum_five (a b c d e : R) :
    a ^ 5 + b ^ 5 + c ^ 5 + d ^ 5 + e ^ 5 =
      (a + b + c + d + e) ^ 5
        - 5 * ((a + b + c + d + e) ^ 3 *
            (a*b + a*c + a*d + a*e + b*c + b*d + b*e + c*d + c*e + d*e))
        + 5 * ((a + b + c + d + e) *
            (a*b + a*c + a*d + a*e + b*c + b*d + b*e + c*d + c*e + d*e) ^ 2)
        + 5 * ((a + b + c + d + e) ^ 2 *
            (a*b*c + a*b*d + a*b*e + a*c*d + a*c*e + a*d*e + b*c*d + b*c*e + b*d*e + c*d*e))
        - 5 * ((a*b + a*c + a*d + a*e + b*c + b*d + b*e + c*d + c*e + d*e) *
            (a*b*c + a*b*d + a*b*e + a*c*d + a*c*e + a*d*e + b*c*d + b*c*e + b*d*e + c*d*e))
        - 5 * ((a + b + c + d + e) *
            (a*b*c*d + a*b*c*e + a*b*d*e + a*c*d*e + b*c*d*e))
        + 5 * (a*b*c*d*e) := by
  ring

end Explicit

end AMGMInequalityOQ02OQ01OQ03OQ01OQ01
