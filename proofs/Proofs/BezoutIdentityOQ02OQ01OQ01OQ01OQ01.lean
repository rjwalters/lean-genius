/-
# ℤ[X,Y] is NOT a Principal Ideal Ring

Problem: bezout-identity-oq-02-oq-01-oq-01-oq-01-oq-01

The parent proof (BezoutIdentityOQ02OQ01OQ01OQ01.lean) established that ℤ[X,Y] is a UFD.
This file proves the complementary fact: ℤ[X,Y] is NOT a principal ideal ring (PID).

## Proof Strategy

The ideal I = (2, X₀) ⊆ ℤ[X,Y] is not principal:
1. I is a proper ideal: 1 ∉ I (proved via constantCoeff: 2*a + X₀*b has even constant term)
2. I is not principal: if I = ⟨f⟩, then f ∣ 2 and f ∣ X₀.
   - f ∣ 2: using totalDegree_mul_of_isDomain (exact equality in domains), totalDegree(f)=0,
     so f = C c for some integer c with c ∣ 2.
   - C c ∣ X₀: coeff of X₀ shows c ∣ 1 in ℤ, so c = ±1 and C c is a unit.
   - But then I = ⟨C c⟩ = ⊤, contradicting I being proper.

## Main Result

`not_isPrincipalIdealRing : ¬IsPrincipalIdealRing (MvPolynomial (Fin 2) ℤ)`

## Tags

algebra, polynomial-rings, not-PID, multivariate, ideal-theory, Bezout
-/

import Mathlib
import Proofs.BezoutIdentityOQ02OQ01OQ01OQ01

set_option maxHeartbeats 800000

namespace NotPID

open MvPolynomial

-- Type abbreviation for convenience
abbrev ZXY := MvPolynomial (Fin 2) ℤ

/-!
## The ideal I = (2, X₀) ⊆ ℤ[X,Y]
-/

/-- The constant polynomial 2 in ℤ[X,Y]. -/
def gen2 : ZXY := C 2

/-- The variable X₀ in ℤ[X,Y]. -/
def genX : ZXY := X (0 : Fin 2)

/-- The ideal I = (2, X₀) ⊆ ℤ[X,Y]. -/
def I : Ideal ZXY := Ideal.span {gen2, genX}

/-!
## Step 1: The ideal I is proper — it does not contain 1.
-/

/-- 1 ∉ I = (2, X₀) in ℤ[X,Y].
    Proof: constantCoeff is a ring hom and constantCoeff(X₀) = 0, so any element
    2*a + X₀*b ∈ I maps to 2*(constantCoeff a) in ℤ, which cannot equal 1. -/
theorem one_not_mem_I : (1 : ZXY) ∉ I := by
  intro h
  -- I = Ideal.span {gen2, genX} = Ideal.span {C 2, X₀}
  -- Any element: a * (C 2) + b * X₀ for some a, b : ZXY
  rw [I, Ideal.mem_span_pair] at h
  obtain ⟨a, b, hab⟩ := h
  -- Apply constantCoeff (the ring hom ZXY → ℤ evaluating all variables at 0)
  have hcc := congr_arg MvPolynomial.constantCoeff hab
  simp only [map_add, map_mul, map_one, map_ofNat,
             MvPolynomial.constantCoeff_X, mul_zero, add_zero] at hcc
  -- hcc : 2 * constantCoeff a = 1 in ℤ — impossible by parity
  omega

/-- I is a proper ideal (not equal to ⊤). -/
theorem I_ne_top : I ≠ ⊤ := by
  rwa [Ne, Ideal.eq_top_iff_one]

/-!
## Step 2: If f ∣ (C 2 : ZXY), then f has total degree 0.
   Key: use totalDegree_mul_of_isDomain (exact equality for nonzero polynomials over a domain).
-/

/-- If f ∣ gen2 in ZXY, then f has totalDegree 0.
    Uses the exact equality totalDegree(f*g) = totalDegree(f) + totalDegree(g) for
    nonzero polynomials over ℤ (NoZeroDivisors), hence both degrees must be 0. -/
private lemma dvd_gen2_totalDeg_zero {f : ZXY} (hf : f ∣ gen2) :
    f.totalDegree = 0 := by
  obtain ⟨g, hg⟩ := hf
  -- f ≠ 0: from gen2 = f * g and gen2 ≠ 0
  have hf_ne : f ≠ 0 := by
    rintro rfl; simp [gen2] at hg
  -- g ≠ 0: similarly
  have hg_ne : g ≠ 0 := by
    rintro rfl; simp [gen2] at hg
  -- Exact equality of total degrees (NoZeroDivisors on ZXY ← ℤ is a domain)
  have hmul_eq := MvPolynomial.totalDegree_mul_of_isDomain hf_ne hg_ne
  -- gen2 = C 2 has totalDegree 0
  have hC2deg : (gen2 : ZXY).totalDegree = 0 := MvPolynomial.totalDegree_C
  rw [← hg] at hC2deg
  -- hC2deg : totalDegree (f * g) = 0
  -- hmul_eq : totalDegree (f * g) = totalDegree f + totalDegree g
  -- Since both are ℕ and sum to 0: totalDegree f = 0
  omega

/-- If f ∣ gen2 in ZXY, then f is a constant polynomial C c with c ∣ 2 in ℤ. -/
theorem dvd_gen2_is_const {f : ZXY} (hf : f ∣ gen2) :
    ∃ c : ℤ, f = C c ∧ c ∣ 2 := by
  have hdeg : f.totalDegree = 0 := dvd_gen2_totalDeg_zero hf
  -- totalDegree 0 ↔ f = C (constantCoeff f)
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hdeg
  -- hdeg : f = C (constantCoeff f)
  refine ⟨MvPolynomial.constantCoeff f, hdeg, ?_⟩
  -- Extract constant-term divisibility from gen2 = f * g
  obtain ⟨g, hg⟩ := hf
  -- Apply constantCoeff to gen2 = f * g
  have hcoeff := congr_arg MvPolynomial.constantCoeff hg
  simp only [gen2, MvPolynomial.constantCoeff_C, map_mul] at hcoeff
  -- hcoeff : 2 = constantCoeff f * constantCoeff g
  exact ⟨MvPolynomial.constantCoeff g, hcoeff⟩

/-!
## Step 3: If (C c : ZXY) ∣ X₀, then c is a unit in ℤ.
-/

/-- If (C c : ZXY) ∣ genX, then c ∣ 1 in ℤ, so c is a unit.
    Proof: extract the coefficient of X₀ from C c * g = X₀. -/
theorem isUnit_of_C_dvd_genX {c : ℤ} (h : (C c : ZXY) ∣ genX) : IsUnit c := by
  obtain ⟨g, hg⟩ := h
  -- The coefficient of X₀ (monomial with single variable X₀) in C c * g is c * coeff[X₀] g
  have hcoeff := congr_arg (MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 1)) hg
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X] at hcoeff
  -- hcoeff : 1 = c * coeff[X₀] g  (since coeff[X₀](X₀) = 1)
  exact Int.isUnit_of_dvd_one ⟨MvPolynomial.coeff (Finsupp.single 0 1) g, hcoeff.symm⟩

/-!
## Step 4: C c is a unit in ZXY iff c is a unit in ℤ.
-/

/-- If c is a unit in ℤ, then C c is a unit in ℤ[X,Y] (ring hom preserves units). -/
private lemma isUnit_C_of_isUnit {c : ℤ} (hc : IsUnit c) : IsUnit (C c : ZXY) :=
  hc.map (MvPolynomial.C : ℤ →+* ZXY)

/-!
## Main Theorem: I = (2, X₀) is not principal.
-/

/-- The ideal I = (2, X₀) is NOT a principal ideal in ℤ[X,Y].
    If I = ⟨f⟩, then f ∣ (C 2) and f ∣ X₀.
    Step 2 gives f = C c with c ∣ 2.
    Step 3 gives IsUnit c from C c ∣ X₀.
    Step 4 gives IsUnit (C c), so ⟨C c⟩ = ⊤, contradicting I being proper. -/
theorem I_not_principal : ¬(Submodule.IsPrincipal I) := by
  intro hprin
  obtain ⟨f, hf⟩ := hprin.principal
  -- I = R ∙ f = Ideal.span {f}
  -- gen2 ∈ I gives f ∣ gen2
  have h2 : gen2 ∈ I := Ideal.subset_span (Set.mem_insert _ _)
  have hX : genX ∈ I := Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  rw [hf, Submodule.mem_span_singleton] at h2 hX
  -- h2 : f ∣ gen2,  hX : f ∣ genX
  -- f = C c for some c with c ∣ 2
  obtain ⟨c, rfl, _hc2⟩ := dvd_gen2_is_const h2
  -- C c ∣ genX, so c is a unit in ℤ
  have hc_unit : IsUnit c := isUnit_of_C_dvd_genX hX
  -- C c is a unit in ZXY, so ⟨C c⟩ = ⊤
  have hI_top : I = ⊤ := by
    rw [hf, ← Ideal.span_singleton_eq_top]
    exact isUnit_C_of_isUnit hc_unit
  exact I_ne_top hI_top

/-!
## Main Theorems
-/

/-- **ℤ[X,Y] is NOT a principal ideal ring.**

The ideal I = (2, X₀) is a proper non-principal ideal. Since not every ideal is principal,
ℤ[X,Y] is not a PID. Note: ℤ[X,Y] IS a UFD (see parent proof), showing UFD ⊋ PID. -/
theorem not_isPrincipalIdealRing : ¬IsPrincipalIdealRing ZXY := fun h_pir =>
  I_not_principal (IsPrincipalIdealRing.principal I)

/-- Corollary: There exists a proper non-principal ideal in ℤ[X,Y]. -/
theorem exists_non_principal_ideal :
    ∃ J : Ideal ZXY, J ≠ ⊤ ∧ ¬(Submodule.IsPrincipal J) :=
  ⟨I, I_ne_top, I_not_principal⟩

/-- **Distinction**: ℤ[X,Y] is a UFD but NOT a principal ideal ring.
    UFD and PID are different: every PID is a UFD, but not conversely. -/
theorem ufd_not_pir_distinction :
    UniqueFactorizationMonoid ZXY ∧ ¬IsPrincipalIdealRing ZXY :=
  ⟨inferInstance, not_isPrincipalIdealRing⟩

end NotPID
