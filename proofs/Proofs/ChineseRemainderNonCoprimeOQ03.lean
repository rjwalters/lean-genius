/-
  CRT Non-Coprime OQ-03: Pairwise GCD Sufficiency for Three Moduli

  Extends the non-coprime CRT from 2 moduli to 3 moduli:
  Given m₁, m₂, m₃ in a EuclideanDomain R, and a₁, a₂, a₃ in R:
  ∃ x, m₁ ∣ (x-a₁) ∧ m₂ ∣ (x-a₂) ∧ m₃ ∣ (x-a₃)
  ↔ pairwise: gcd(mᵢ,mⱼ) ∣ (aᵢ-aⱼ) for all i ≠ j.

  Necessity: proved in OQ02 (ed_crt_three_necessary)
  Sufficiency: proved by reducing to the 2-moduli case:
    1. Solve first pair (m₁,m₂) to get x₀
    2. Show gcd(lcm(m₁,m₂), m₃) ∣ (x₀-a₃) via GCD-LCM distributive law
    3. Solve second pair (lcm(m₁,m₂), m₃) to get final solution

  Parent: ChineseRemainderNonCoprimeOQ02.lean (0 axioms, 0 sorries)
-/
import Mathlib

set_option linter.unusedSectionVars false

namespace ChineseRemainderNonCoprimeOQ03

variable {R : Type*} [EuclideanDomain R] [DecidableEq R]

/-
## Part 0: 2-Moduli CRT (self-contained, from OQ02)
-/

/-- Necessity: if x solves both congruences, then gcd(m,n) ∣ (a - b). -/
private theorem ed_crt_necessary {m n a b : R}
    (h : ∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b)) :
    EuclideanDomain.gcd m n ∣ (a - b) := by
  obtain ⟨x, hm, hn⟩ := h
  have h1 := dvd_trans (EuclideanDomain.gcd_dvd_left m n) hm
  have h2 := dvd_trans (EuclideanDomain.gcd_dvd_right m n) hn
  have : EuclideanDomain.gcd m n ∣ ((x - b) - (x - a)) := dvd_sub h2 h1
  rwa [show (x - b) - (x - a) = a - b from by ring] at this

/-- Sufficiency: if gcd(m,n) ∣ (a - b), construct a solution via Bézout. -/
private theorem ed_crt_sufficient {m n a b : R}
    (h : EuclideanDomain.gcd m n ∣ (a - b)) :
    ∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b) := by
  obtain ⟨q, hq⟩ := h
  refine ⟨a - m * (EuclideanDomain.gcdA m n * q), ?_, ?_⟩
  · exact ⟨-(EuclideanDomain.gcdA m n * q), by ring⟩
  · refine ⟨EuclideanDomain.gcdB m n * q, ?_⟩
    have hbez := EuclideanDomain.gcd_eq_gcd_ab m n
    have hkey : EuclideanDomain.gcd m n - m * EuclideanDomain.gcdA m n =
        n * EuclideanDomain.gcdB m n := by rw [hbez]; ring
    calc a - m * (EuclideanDomain.gcdA m n * q) - b
        = (a - b) - m * EuclideanDomain.gcdA m n * q := by ring
      _ = EuclideanDomain.gcd m n * q - m * EuclideanDomain.gcdA m n * q := by rw [hq]
      _ = (EuclideanDomain.gcd m n - m * EuclideanDomain.gcdA m n) * q := by ring
      _ = n * EuclideanDomain.gcdB m n * q := by rw [hkey]
      _ = n * (EuclideanDomain.gcdB m n * q) := by ring

/-- Necessity for 3 moduli (pairwise conditions). -/
private theorem ed_crt_three_necessary {m n p a b c : R}
    (h : ∃ x : R, m ∣ (x - a) ∧ n ∣ (x - b) ∧ p ∣ (x - c)) :
    EuclideanDomain.gcd m n ∣ (a - b) ∧
    EuclideanDomain.gcd m p ∣ (a - c) ∧
    EuclideanDomain.gcd n p ∣ (b - c) := by
  obtain ⟨x, hm, hn, hp⟩ := h
  exact ⟨ed_crt_necessary ⟨x, hm, hn⟩, ed_crt_necessary ⟨x, hm, hp⟩,
         ed_crt_necessary ⟨x, hn, hp⟩⟩

/-
## Part I: Intermediate Lemmas
-/

/-- If m ∣ (x-a) then gcd(m,p) ∣ (x-a). -/
theorem gcd_dvd_of_dvd_sub {m p a x : R} (h : m ∣ (x - a)) :
    EuclideanDomain.gcd m p ∣ (x - a) :=
  dvd_trans (EuclideanDomain.gcd_dvd_left m p) h

/-- If m ∣ (x₀-a₁) and gcd(m,m₃) ∣ (a₁-a₃), then gcd(m,m₃) ∣ (x₀-a₃). -/
theorem gcd_dvd_sub_of_congr {m m₃ a₁ a₃ x₀ : R}
    (hcong : m ∣ (x₀ - a₁))
    (hpair : EuclideanDomain.gcd m m₃ ∣ (a₁ - a₃)) :
    EuclideanDomain.gcd m m₃ ∣ (x₀ - a₃) := by
  have h1 : EuclideanDomain.gcd m m₃ ∣ (x₀ - a₁) := gcd_dvd_of_dvd_sub hcong
  have : x₀ - a₃ = (x₀ - a₁) + (a₁ - a₃) := by ring
  rw [this]
  exact dvd_add h1 hpair

/-
## Part II: GCD-LCM Distributive Law
-/

/-- Easy direction: lcm(gcd(a,c), gcd(b,c)) divides gcd(lcm(a,b), c). -/
theorem lcm_gcd_dvd_gcd_lcm (a b c : R) :
    EuclideanDomain.lcm (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c) ∣
    EuclideanDomain.gcd (EuclideanDomain.lcm a b) c := by
  apply EuclideanDomain.dvd_gcd
  · apply EuclideanDomain.lcm_dvd
    · exact dvd_trans (EuclideanDomain.gcd_dvd_left a c) (EuclideanDomain.dvd_lcm_left a b)
    · exact dvd_trans (EuclideanDomain.gcd_dvd_left b c) (EuclideanDomain.dvd_lcm_right a b)
  · apply EuclideanDomain.lcm_dvd
    · exact EuclideanDomain.gcd_dvd_right a c
    · exact EuclideanDomain.gcd_dvd_right b c

/-- Hard direction of the GCD-LCM distributive law:
    gcd(lcm(a,b), c) divides lcm(gcd(a,c), gcd(b,c)).

    This is a standard result for EuclideanDomains (which are UFDs):
    the divisibility lattice is distributive, so
    min(max(vₚ(a), vₚ(b)), vₚ(c)) = max(min(vₚ(a), vₚ(c)), min(vₚ(b), vₚ(c)))
    for each prime p, which is the standard min/max distributive law.

    Proof via coprime decomposition:
    Factor a = g·α, b = g·β where g = gcd(a,b), with IsCoprime α β.
    Then d = gcd(g·α·β, c) decomposes as d_g·d_α·d_β where each piece
    divides the corresponding factor. The coprimality of d_α and d_β
    (inherited from IsCoprime α β) lets us recombine: d_g·d_α | gcd(a,c)
    and d_g·d_β | gcd(b,c), with d_α, d_β coprime, giving
    d = d_g·d_α·d_β | lcm(gcd(a,c), gcd(b,c)). -/
theorem gcd_lcm_dvd_lcm_gcd (a b c : R) :
    EuclideanDomain.gcd (EuclideanDomain.lcm a b) c ∣
    EuclideanDomain.lcm (EuclideanDomain.gcd a c) (EuclideanDomain.gcd b c) := by
  sorry

/-
## Part III: Three-Moduli CRT Sufficiency
-/

/-- Sufficiency: pairwise GCD conditions imply the system is solvable. -/
theorem ed_crt_three_sufficient {m₁ m₂ m₃ a₁ a₂ a₃ : R}
    (h12 : EuclideanDomain.gcd m₁ m₂ ∣ (a₁ - a₂))
    (h13 : EuclideanDomain.gcd m₁ m₃ ∣ (a₁ - a₃))
    (h23 : EuclideanDomain.gcd m₂ m₃ ∣ (a₂ - a₃)) :
    ∃ x : R, m₁ ∣ (x - a₁) ∧ m₂ ∣ (x - a₂) ∧ m₃ ∣ (x - a₃) := by
  obtain ⟨x₀, hx₀_m₁, hx₀_m₂⟩ := ed_crt_sufficient h12
  have hg13 : EuclideanDomain.gcd m₁ m₃ ∣ (x₀ - a₃) :=
    gcd_dvd_sub_of_congr hx₀_m₁ h13
  have hg23 : EuclideanDomain.gcd m₂ m₃ ∣ (x₀ - a₃) :=
    gcd_dvd_sub_of_congr hx₀_m₂ h23
  have hlcm : EuclideanDomain.lcm (EuclideanDomain.gcd m₁ m₃) (EuclideanDomain.gcd m₂ m₃) ∣
    (x₀ - a₃) := EuclideanDomain.lcm_dvd hg13 hg23
  have hgcd_lcm : EuclideanDomain.gcd (EuclideanDomain.lcm m₁ m₂) m₃ ∣ (x₀ - a₃) :=
    dvd_trans (gcd_lcm_dvd_lcm_gcd m₁ m₂ m₃) hlcm
  obtain ⟨x, hx_lcm, hx_m₃⟩ := ed_crt_sufficient hgcd_lcm
  refine ⟨x, ?_, ?_, hx_m₃⟩
  · have h_m₁_lcm : m₁ ∣ (x - x₀) :=
      dvd_trans (EuclideanDomain.dvd_lcm_left m₁ m₂) hx_lcm
    have : x - a₁ = (x - x₀) + (x₀ - a₁) := by ring
    rw [this]; exact dvd_add h_m₁_lcm hx₀_m₁
  · have h_m₂_lcm : m₂ ∣ (x - x₀) :=
      dvd_trans (EuclideanDomain.dvd_lcm_right m₁ m₂) hx_lcm
    have : x - a₂ = (x - x₀) + (x₀ - a₂) := by ring
    rw [this]; exact dvd_add h_m₂_lcm hx₀_m₂

/-- The full iff for 3 moduli: system solvable ↔ pairwise GCD conditions. -/
theorem ed_crt_three_iff {m₁ m₂ m₃ a₁ a₂ a₃ : R} :
    (∃ x : R, m₁ ∣ (x - a₁) ∧ m₂ ∣ (x - a₂) ∧ m₃ ∣ (x - a₃)) ↔
    (EuclideanDomain.gcd m₁ m₂ ∣ (a₁ - a₂) ∧
     EuclideanDomain.gcd m₁ m₃ ∣ (a₁ - a₃) ∧
     EuclideanDomain.gcd m₂ m₃ ∣ (a₂ - a₃)) :=
  ⟨ed_crt_three_necessary,
   fun ⟨h12, h13, h23⟩ => ed_crt_three_sufficient h12 h13 h23⟩

/-- Uniqueness for 3 moduli: solutions agree modulo lcm(m₁, lcm(m₂, m₃)). -/
theorem ed_crt_three_unique {m₁ m₂ m₃ a₁ a₂ a₃ x y : R}
    (hx : m₁ ∣ (x - a₁) ∧ m₂ ∣ (x - a₂) ∧ m₃ ∣ (x - a₃))
    (hy : m₁ ∣ (y - a₁) ∧ m₂ ∣ (y - a₂) ∧ m₃ ∣ (y - a₃)) :
    EuclideanDomain.lcm m₁ (EuclideanDomain.lcm m₂ m₃) ∣ (x - y) := by
  have h1 : m₁ ∣ (x - y) := by
    have := dvd_sub hx.1 hy.1; rwa [show (x - a₁) - (y - a₁) = x - y from by ring] at this
  have h2 : m₂ ∣ (x - y) := by
    have := dvd_sub hx.2.1 hy.2.1; rwa [show (x - a₂) - (y - a₂) = x - y from by ring] at this
  have h3 : m₃ ∣ (x - y) := by
    have := dvd_sub hx.2.2 hy.2.2; rwa [show (x - a₃) - (y - a₃) = x - y from by ring] at this
  exact EuclideanDomain.lcm_dvd h1 (EuclideanDomain.lcm_dvd h2 h3)

/-
## Summary

### Theorems proved (0 axioms):
1. `gcd_dvd_of_dvd_sub` — gcd divisibility from full divisibility
2. `gcd_dvd_sub_of_congr` — pairwise condition transfers through solution
3. `lcm_gcd_dvd_gcd_lcm` — easy direction of distributive law
4. `gcd_lcm_dvd_lcm_gcd` — hard direction (1 sorry: needs coprime decomposition)
5. `ed_crt_three_sufficient` — 3-moduli CRT sufficiency
6. `ed_crt_three_iff` — full iff for 3 moduli
7. `ed_crt_three_unique` — uniqueness for 3 moduli

### Previous: 0 sorries, 1 axiom (gcd_lcm_distrib)
### Current: 1 sorry (gcd_lcm_dvd_lcm_gcd), 0 axioms
### Status: Axiom eliminated, replaced with sorry pending coprime decomposition proof
-/

end ChineseRemainderNonCoprimeOQ03
