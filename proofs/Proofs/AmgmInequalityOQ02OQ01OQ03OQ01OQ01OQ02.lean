/-
  Newton–Girard k=6 Closed Form:
      p₆ = e₁⁶ − 6·e₁⁴·e₂ + 9·e₁²·e₂² − 2·e₂³ + 6·e₁³·e₃ − 12·e₁·e₂·e₃ + 3·e₃²
             − 6·e₁²·e₄ + 6·e₂·e₄ + 6·e₁·e₅ − 6·e₆.

  Open Question (amgm-inequality-oq-02-oq-01-oq-03-oq-01-oq-01-oq-02), the next rung after
  the k=5 closed form `amgm-inequality-oq-02-oq-01-oq-03-oq-01-oq-01`.

  Establish the fully reduced k=6 Newton–Girard identity expressing the sixth power sum
  p₆ purely in terms of the elementary symmetric polynomials e₁, …, e₆:
      p₆ = e₁⁶ − 6·e₁⁴·e₂ + 9·e₁²·e₂² − 2·e₂³ + 6·e₁³·e₃ − 12·e₁·e₂·e₃ + 3·e₃²
             − 6·e₁²·e₄ + 6·e₂·e₄ + 6·e₁·e₅ − 6·e₆.
  For concrete values (a Finset) this is the symmetric-function form of
      a⁶+b⁶+c⁶+d⁶+e⁶+g⁶
        = e₁⁶ − 6·e₁⁴·e₂ + 9·e₁²·e₂² − 2·e₂³ + 6·e₁³·e₃ − 12·e₁·e₂·e₃ + 3·e₃²
             − 6·e₁²·e₄ + 6·e₂·e₄ + 6·e₁·e₅ − 6·e₆.

  Lineage:
  • Parent     amgm-inequality-oq-02-oq-01             : k=2 identity p₂ = e₁² − 2e₂.
  • Recurrence amgm-inequality-oq-02-oq-01-oq-02-oq-01 : p₃ recurrence and the k=1,2 corollaries.
  • k=3 closed amgm-inequality-oq-02-oq-01-oq-03       : `psum_three_closed`.
  • k=4 closed amgm-inequality-oq-02-oq-01-oq-03-oq-01 : `psum_four_closed`.
  • k=5 closed amgm-inequality-oq-02-oq-01-oq-03-oq-01-oq-01 : `psum_five_closed` + the concrete
                                                         general-Finset form `newton_girard_five_finset`
                                                         and the e₅/p₅ aeval bridges.

  This file adds the next rung.  Two complementary forms, each 0-sorry / 0-axiom:

  (1) UNIVERSAL (MvPolynomial).  `psum_six_recurrence` extracts the k=6 Newton recurrence
        p₆ = e₁p₅ − e₂p₄ + e₃p₃ − e₄p₂ + e₅p₁ − 6e₆
      directly from `MvPolynomial.psum_eq_mul_esymm_sub_sum` (antidiagonal filter
      {(1,5),(2,4),(3,3),(4,2),(5,1)}, lead term (−1)⁷·6·e₆ = −6·e₆).  Substituting the proven
      closed forms for p₅, p₄, p₃, p₂, p₁ and ring-normalising yields `psum_six_closed`.

  (2) CONCRETE general-Finset, over an ARBITRARY CommRing (every characteristic included).
      Reusing the already-built, n-general `aeval` bridges (`aeval_psum_subtype`,
      `aeval_esymm_subtype`) and the e₁..e₅ bridges from the ancestor files, the universal
      closed form transports onto the subtype {x // x ∈ s} to give `newton_girard_six_finset`
      with the e₆/p₆ bridge lemmas instantiated at n=6.  No characteristic hypothesis is
      required — the same transport that bypassed the char-2 obstruction at k=3 works verbatim.

  The closed-form coefficients are cross-checked here against the recurrence (the `ring`
  closing `psum_six_closed`) and independently against an explicit 6-variable instance
  (`sixth_power_sum_six`, closed by `ring`).

  Status: PROVED — 0 sorries, 0 axioms.  Holds over any `CommRing`.
  Tags: algebra, symmetric-functions, newton-girard, power-sums, finset, characteristic-two
-/

import Mathlib
import Proofs.AmgmInequalityOQ02OQ01OQ02OQ01
import Proofs.AmgmInequalityOQ02OQ01OQ03
import Proofs.AmgmInequalityOQ02OQ01OQ03Finset
import Proofs.AmgmInequalityOQ02OQ01OQ03OQ01
import Proofs.AmgmInequalityOQ02OQ01OQ03OQ01OQ01

namespace AMGMInequalityOQ02OQ01OQ03OQ01OQ01OQ02

open MvPolynomial Finset BigOperators Set

-- ============================================================
-- Universal closed form (MvPolynomial setting)
-- ============================================================

section Universal

variable (σ : Type*) (R : Type*) [CommRing R] [Fintype σ]

/-- **Newton–Girard k=6, recurrence form** (universal / MvPolynomial setting):
      p₆ = e₁·p₅ − e₂·p₄ + e₃·p₃ − e₄·p₂ + e₅·p₁ − 6·e₆.

    Proof: apply `psum_eq_mul_esymm_sub_sum` at n = 6.  The antidiagonal
    {a : a.1 + a.2 = 6, 0 < a.1 < 6} = {(1,5), (2,4), (3,3), (4,2), (5,1)}, and the lead term is
    (−1)⁷·6·e₆ = −6·e₆, so
      p₆ = −6e₆ − ((−1)¹e₁p₅ + (−1)²e₂p₄ + (−1)³e₃p₃ + (−1)⁴e₄p₂ + (−1)⁵e₅p₁)
         = e₁p₅ − e₂p₄ + e₃p₃ − e₄p₂ + e₅p₁ − 6e₆. -/
theorem psum_six_recurrence :
    psum σ R 6 =
      esymm σ R 1 * psum σ R 5 - esymm σ R 2 * psum σ R 4
        + esymm σ R 3 * psum σ R 3 - esymm σ R 4 * psum σ R 2
        + esymm σ R 5 * psum σ R 1 - 6 * esymm σ R 6 := by
  rw [MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 6 (by norm_num)]
  have hfilt : (Finset.antidiagonal 6).filter (fun a : ℕ × ℕ => a.1 ∈ Set.Ioo 0 6) =
               {(1, 5), (2, 4), (3, 3), (4, 2), (5, 1)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_Ioo,
               Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega
  simp only [hfilt,
    Finset.sum_insert (by decide : (1, 5) ∉ ({(2, 4), (3, 3), (4, 2), (5, 1)} : Finset (ℕ × ℕ))),
    Finset.sum_insert (by decide : (2, 4) ∉ ({(3, 3), (4, 2), (5, 1)} : Finset (ℕ × ℕ))),
    Finset.sum_insert (by decide : (3, 3) ∉ ({(4, 2), (5, 1)} : Finset (ℕ × ℕ))),
    Finset.sum_insert (by decide : (4, 2) ∉ ({(5, 1)} : Finset (ℕ × ℕ))),
    Finset.sum_singleton]
  ring

/-- **Newton–Girard k=6, closed form** (universal / MvPolynomial setting):
      p₆ = e₁⁶ − 6·e₁⁴·e₂ + 9·e₁²·e₂² − 2·e₂³ + 6·e₁³·e₃ − 12·e₁·e₂·e₃ + 3·e₃²
             − 6·e₁²·e₄ + 6·e₂·e₄ + 6·e₁·e₅ − 6·e₆.
    Substitute the proven closed forms `psum_five_closed` (p₅), `psum_four_closed` (p₄),
    `psum_three_closed` (p₃), `psum_two_eq` (p₂ = e₁² − 2e₂) and `psum_one_eq_esymm_one`
    (p₁ = e₁) into the recurrence `psum_six_recurrence`, then ring-normalise. -/
theorem psum_six_closed :
    psum σ R 6 =
      esymm σ R 1 ^ 6 - 6 * (esymm σ R 1 ^ 4 * esymm σ R 2)
        + 9 * (esymm σ R 1 ^ 2 * esymm σ R 2 ^ 2) - 2 * esymm σ R 2 ^ 3
        + 6 * (esymm σ R 1 ^ 3 * esymm σ R 3) - 12 * (esymm σ R 1 * esymm σ R 2 * esymm σ R 3)
        + 3 * esymm σ R 3 ^ 2 - 6 * (esymm σ R 1 ^ 2 * esymm σ R 4)
        + 6 * (esymm σ R 2 * esymm σ R 4) + 6 * (esymm σ R 1 * esymm σ R 5)
        - 6 * esymm σ R 6 := by
  have h6 := psum_six_recurrence σ R
  have h5 := AMGMInequalityOQ02OQ01OQ03OQ01OQ01.psum_five_closed σ R
  have h4 := AMGMInequalityOQ02OQ01OQ03OQ01.psum_four_closed σ R
  have h3 := AMGMInequalityOQ02OQ01OQ03.psum_three_closed σ R
  have h2 := AMGMInequalityOQ02OQ01OQ02OQ01.psum_two_eq σ R
  have h1 := AMGMInequalityOQ02OQ01OQ02OQ01.psum_one_eq_esymm_one σ R
  rw [h6, h5, h4, h3, h2, h1]; ring

end Universal

-- ============================================================
-- Concrete general-Finset form, over ANY CommRing (every characteristic)
-- ============================================================

section Concrete

open AMGMInequalityOQ02OQ01OQ03Finset
open AMGMInequalityOQ02OQ01OQ03OQ01
open AMGMInequalityOQ02OQ01OQ03OQ01OQ01

variable {ι R : Type*} [CommRing R] [DecidableEq ι]

/-- e₆ = Σ over 6-subsets of the product (concrete `powersetCard` form). -/
def e6 (s : Finset ι) (f : ι → R) : R := ∑ t ∈ s.powersetCard 6, ∏ i ∈ t, f i
/-- p₆ = Σ fᵢ⁶. -/
def p6 (s : Finset ι) (f : ι → R) : R := ∑ i ∈ s, f i ^ 6

omit [DecidableEq ι] in
/-- Bridge at degree 6:  `aeval (esymm … 6) = e₆`  (definitional, from the n-general
    `aeval_esymm_subtype`). -/
theorem e6_bridge (s : Finset ι) (f : ι → R) :
    aeval (fun i : {x // x ∈ s} => f i.1) (MvPolynomial.esymm {x // x ∈ s} R 6) = e6 s f :=
  aeval_esymm_subtype s f 6

omit [DecidableEq ι] in
/-- Bridge for the sixth power sum:  `aeval (psum … 6) = p₆`  (definitional, from the
    n-general `aeval_psum_subtype`). -/
theorem p6_bridge (s : Finset ι) (f : ι → R) :
    aeval (fun i : {x // x ∈ s} => f i.1) (MvPolynomial.psum {x // x ∈ s} R 6) = p6 s f :=
  aeval_psum_subtype s f 6

omit [DecidableEq ι] in
/-- **Concrete general-Finset Newton–Girard k=6** over an arbitrary `CommRing`:
      p₆ = e₁⁶ − 6·e₁⁴·e₂ + 9·e₁²·e₂² − 2·e₂³ + 6·e₁³·e₃ − 12·e₁·e₂·e₃ + 3·e₃²
             − 6·e₁²·e₄ + 6·e₂·e₄ + 6·e₁·e₅ − 6·e₆.
    Transport of the universal `psum_six_closed` across the (characteristic-safe) aeval
    bridges onto the subtype {x // x ∈ s}.  No characteristic hypothesis is required. -/
theorem newton_girard_six_finset (s : Finset ι) (f : ι → R) :
    p6 s f =
      e1 s f ^ 6 - 6 * (e1 s f ^ 4 * e2 s f) + 9 * (e1 s f ^ 2 * e2 s f ^ 2)
        - 2 * e2 s f ^ 3 + 6 * (e1 s f ^ 3 * e3 s f)
        - 12 * (e1 s f * e2 s f * e3 s f) + 3 * e3 s f ^ 2
        - 6 * (e1 s f ^ 2 * e4 s f) + 6 * (e2 s f * e4 s f)
        + 6 * (e1 s f * e5 s f) - 6 * e6 s f := by
  have H := congrArg (aeval (fun i : {x // x ∈ s} => f i.1))
    (psum_six_closed {x // x ∈ s} R)
  simpa only [map_add, map_sub, map_mul, map_pow, map_ofNat,
    p6_bridge, e1_bridge, e2_bridge, e3_bridge, e4_bridge, e5_bridge, e6_bridge] using H

end Concrete

-- ============================================================
-- Concrete 6-variable instance (smallest nondegenerate case)
-- ============================================================

section Explicit

variable {R : Type*} [CommRing R]

/-- **Concrete 6-variable instance** — sum of sixth powers:
      a⁶ + b⁶ + c⁶ + d⁶ + e⁶ + g⁶
        = e₁⁶ − 6·e₁⁴·e₂ + 9·e₁²·e₂² − 2·e₂³ + 6·e₁³·e₃ − 12·e₁·e₂·e₃ + 3·e₃²
             − 6·e₁²·e₄ + 6·e₂·e₄ + 6·e₁·e₅ − 6·e₆,
    where e₁ = Σ, e₂ = Σ pairs, e₃ = Σ triples, e₄ = Σ quadruples, e₅ = Σ quintuples,
    e₆ = abcdeg.  This is the n = 6 Finset case of `psum_six_closed`. -/
theorem sixth_power_sum_six (a b c d e g : R) :
    a ^ 6 + b ^ 6 + c ^ 6 + d ^ 6 + e ^ 6 + g ^ 6 =
      (a + b + c + d + e + g) ^ 6
        - 6 * ((a + b + c + d + e + g) ^ 4 *
            (a*b + a*c + a*d + a*e + a*g + b*c + b*d + b*e + b*g + c*d + c*e + c*g
              + d*e + d*g + e*g))
        + 9 * ((a + b + c + d + e + g) ^ 2 *
            (a*b + a*c + a*d + a*e + a*g + b*c + b*d + b*e + b*g + c*d + c*e + c*g
              + d*e + d*g + e*g) ^ 2)
        - 2 * (a*b + a*c + a*d + a*e + a*g + b*c + b*d + b*e + b*g + c*d + c*e + c*g
              + d*e + d*g + e*g) ^ 3
        + 6 * ((a + b + c + d + e + g) ^ 3 *
            (a*b*c + a*b*d + a*b*e + a*b*g + a*c*d + a*c*e + a*c*g + a*d*e + a*d*g + a*e*g
              + b*c*d + b*c*e + b*c*g + b*d*e + b*d*g + b*e*g + c*d*e + c*d*g + c*e*g + d*e*g))
        - 12 * ((a + b + c + d + e + g) *
            (a*b + a*c + a*d + a*e + a*g + b*c + b*d + b*e + b*g + c*d + c*e + c*g
              + d*e + d*g + e*g) *
            (a*b*c + a*b*d + a*b*e + a*b*g + a*c*d + a*c*e + a*c*g + a*d*e + a*d*g + a*e*g
              + b*c*d + b*c*e + b*c*g + b*d*e + b*d*g + b*e*g + c*d*e + c*d*g + c*e*g + d*e*g))
        + 3 * (a*b*c + a*b*d + a*b*e + a*b*g + a*c*d + a*c*e + a*c*g + a*d*e + a*d*g + a*e*g
              + b*c*d + b*c*e + b*c*g + b*d*e + b*d*g + b*e*g + c*d*e + c*d*g + c*e*g + d*e*g) ^ 2
        - 6 * ((a + b + c + d + e + g) ^ 2 *
            (a*b*c*d + a*b*c*e + a*b*c*g + a*b*d*e + a*b*d*g + a*b*e*g + a*c*d*e + a*c*d*g
              + a*c*e*g + a*d*e*g + b*c*d*e + b*c*d*g + b*c*e*g + b*d*e*g + c*d*e*g))
        + 6 * ((a*b + a*c + a*d + a*e + a*g + b*c + b*d + b*e + b*g + c*d + c*e + c*g
              + d*e + d*g + e*g) *
            (a*b*c*d + a*b*c*e + a*b*c*g + a*b*d*e + a*b*d*g + a*b*e*g + a*c*d*e + a*c*d*g
              + a*c*e*g + a*d*e*g + b*c*d*e + b*c*d*g + b*c*e*g + b*d*e*g + c*d*e*g))
        + 6 * ((a + b + c + d + e + g) *
            (a*b*c*d*e + a*b*c*d*g + a*b*c*e*g + a*b*d*e*g + a*c*d*e*g + b*c*d*e*g))
        - 6 * (a*b*c*d*e*g) := by
  ring

end Explicit

end AMGMInequalityOQ02OQ01OQ03OQ01OQ01OQ02
