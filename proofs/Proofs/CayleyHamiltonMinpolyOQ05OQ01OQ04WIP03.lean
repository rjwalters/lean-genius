/-
  Nonderogatory → Cyclic Vector: Prime Power Case (All Fields)

  This file proves the cyclic vector theorem for nonderogatory matrices whose
  characteristic polynomial is a PRIME POWER p^e (p irreducible, e ≥ 1), over
  ANY field K. This covers the non-squarefree case left open by WIP02.

  ## Status: axiom-free (0 axioms, 0 sorries — see build verification)

  ## Key New Lemma

  `pow_irred_dvd_of_annihilated` (proved by induction on e):
  If p irred, p^e(M)v ≠ 0, p^(e+1)(M)v = 0, r(M)v = 0, then p^(e+1) | r.

  Proof by induction on e:
  - e=0: v ≠ 0, p(M)v = 0, r(M)v = 0 → p | r. From `irreducible_dvd_of_annihilated`.
  - e+1: Given p^(e+1)(M)v ≠ 0, p^(e+2)(M)v = 0, r(M)v = 0.
    1. Let w = p^(e+1)(M)v. Then p(M)w = 0, r(M)w = 0, w ≠ 0 → p | r.
    2. Write r = p*r₁. Let u = p(M)v. Then:
       p^e(M)u = p^(e+1)(M)v ≠ 0, p^(e+1)(M)u = p^(e+2)(M)v = 0.
       r₁(M)u = r₁(M)p(M)v = p(M)r₁(M)v = 0 (since r = p*r₁, r(M)v = 0).
    3. IH gives p^(e+1) | r₁. So r = p*r₁ and p^(e+1) | r₁ → p^(e+2) | r.

  ## Coverage

  - WIP02: minpoly squarefree → cyclic vector (axiom-free)
  - WIP03: minpoly = p^e → cyclic vector (axiom-free, this file)
  - WIP01: general nonderogatory → cyclic vector (1 axiom: similar to companion)

  The general case (arbitrary minpoly) reduces to combining prime power components
  via CRT (as in WIP02's squarefree induction), which is left as future work.
-/
import Mathlib

noncomputable section

namespace PrimePowerCyclicVector

open Matrix Polynomial

attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K] {n : ℕ}

-- ============================================================
-- SECTION I: Definitions (same as WIP02)
-- ============================================================

/-- A vector v is cyclic for M if no nonzero polynomial of degree < n annihilates v. -/
def IsCyclicVector (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : Prop :=
  ∀ p : K[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0

/-- M is nonderogatory if minpoly = charpoly. -/
def IsNonderogatory (M : Matrix (Fin n) (Fin n) K) : Prop :=
  minpoly K M = M.charpoly

-- ============================================================
-- SECTION II: Utility Lemmas
-- ============================================================

/-- If p irred, v ≠ 0, p(M)v = 0, r(M)v = 0, then p | r. (Bezout argument.) -/
private lemma irreducible_dvd_of_annihilated {M : Matrix (Fin n) (Fin n) K}
    {p r : K[X]} {v : Fin n → K}
    (hp_irr : Irreducible p) (hv_ne : v ≠ 0)
    (hpv : (aeval M p).mulVec v = 0)
    (hrv : (aeval M r).mulVec v = 0) :
    p ∣ r := by
  by_contra h_ndvd
  have hp_prime : Prime p :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hp_irr
  have hcop : IsCoprime p r := hp_prime.coprime_iff_not_dvd.mpr h_ndvd
  obtain ⟨a, b, hab⟩ := hcop
  have hmat : aeval M a * aeval M p + aeval M b * aeval M r = 1 := by
    have h := congr_arg (aeval M) hab
    simp only [map_add, map_mul, map_one] at h; exact h
  have hv_zero : v = 0 := by
    have h := congr_arg (· *ᵥ v) hmat
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hpv, hrv,
               Matrix.mulVec_zero, Matrix.one_mulVec, add_zero] at h
    exact h.symm
  exact hv_ne hv_zero

/-- A nonzero matrix has a vector outside its kernel. -/
private lemma exists_mulVec_ne_zero {M : Matrix (Fin n) (Fin n) K} (hM : M ≠ 0) :
    ∃ v : Fin n → K, M.mulVec v ≠ 0 := by
  by_contra hall
  push_neg at hall
  apply hM
  funext i j
  have h2 : (M.mulVec (Pi.single j 1)) i = 0 := congr_fun (hall (Pi.single j 1)) i
  simp only [mulVec, dotProduct, Pi.single_apply] at h2
  simpa using h2

/-- Minimality of minpoly: natDegree < minpoly natDegree → polynomial ≠ 0 as matrix. -/
private lemma aeval_ne_zero_of_lt_minpoly {M : Matrix (Fin n) (Fin n) K}
    {p : K[X]} (hp_ne : p ≠ 0)
    (hp_deg : p.natDegree < (minpoly K M).natDegree) :
    (aeval M p : Matrix (Fin n) (Fin n) K) ≠ 0 := by
  intro h
  exact absurd (Polynomial.natDegree_le_of_dvd (minpoly.dvd K M h) hp_ne) (by omega)

-- ============================================================
-- SECTION III: Core Lemma — Prime Power Divisibility
-- ============================================================

/-- **Prime power divisibility from annihilation** (induction on e):
    If p irred, p^e(M)v ≠ 0, p^(e+1)(M)v = 0, r(M)v = 0, then p^(e+1) | r.

    Proof by induction on e:
    - Base (e=0): v ≠ 0, p(M)v = 0, r(M)v = 0 → p | r.
    - Step: Let w = p^(e+1)(M)v ≠ 0. Then p(M)w = 0, r(M)w = 0 → p | r.
      Write r = p*r₁. Let u = p(M)v. Then p^e(M)u ≠ 0, p^(e+1)(M)u = 0,
      r₁(M)u = 0. IH gives p^(e+1) | r₁, so p^(e+2) | r. -/
private lemma pow_irred_dvd_of_annihilated
    {M : Matrix (Fin n) (Fin n) K} {p : K[X]}
    (hp_irr : Irreducible p) :
    ∀ (e : ℕ) (v : Fin n → K),
      (aeval M (p ^ e)).mulVec v ≠ 0 →
      (aeval M (p ^ (e + 1))).mulVec v = 0 →
      ∀ (r : K[X]), (aeval M r).mulVec v = 0 → p ^ (e + 1) ∣ r := by
  intro e
  induction e with
  | zero =>
    -- Base: p^0(M)v = v ≠ 0, p^1(M)v = p(M)v = 0, r(M)v = 0 → p | r
    intro v hne hzero r hrv
    have hv_ne : v ≠ 0 := by simpa using hne
    have hpv_zero : (aeval M p).mulVec v = 0 := by simpa using hzero
    simpa using irreducible_dvd_of_annihilated hp_irr hv_ne hpv_zero hrv
  | succ e ih =>
    -- Inductive step: p^(e+1)(M)v ≠ 0, p^(e+2)(M)v = 0, r(M)v = 0. Want p^(e+2) | r.
    intro v hne hzero r hrv
    -- Step 1: p | r via w = p^(e+1)(M)v
    have hw_ne : (aeval M (p ^ (e + 1))).mulVec v ≠ 0 := hne
    -- p(M)w = p(M)*p^(e+1)(M)*v = p^(e+1+1)(M)*v = 0
    have hpw : (aeval M p).mulVec ((aeval M (p ^ (e + 1))).mulVec v) = 0 := by
      have : (aeval M p).mulVec ((aeval M (p ^ (e + 1))).mulVec v) =
             (aeval M (p ^ (e + 1 + 1))).mulVec v := by
        rw [Matrix.mulVec_mulVec, ← map_mul]
        congr 2; ring
      rw [this]; exact hzero
    -- r(M)w = p^(e+1)(M)(r(M)v) = 0 (polynomials in M commute)
    have hrw : (aeval M r).mulVec ((aeval M (p ^ (e + 1))).mulVec v) = 0 := by
      rw [Matrix.mulVec_mulVec, ← map_mul (aeval M),
          show r * p ^ (e + 1) = p ^ (e + 1) * r from mul_comm _ _,
          map_mul (aeval M), ← Matrix.mulVec_mulVec, hrv, Matrix.mulVec_zero]
    have hp_r : p ∣ r := irreducible_dvd_of_annihilated hp_irr hw_ne hpw hrw
    obtain ⟨r₁, hr₁_eq⟩ := hp_r  -- r = p * r₁
    -- Step 2: Apply IH to u = p(M)v, polynomial r₁
    -- p^(e+1)(M)u = p^(e+1)(M)*p(M)*v = p^(e+1+1)(M)*v = 0
    have hu_zero : (aeval M (p ^ (e + 1))).mulVec ((aeval M p).mulVec v) = 0 := by
      have : (aeval M (p ^ (e + 1))).mulVec ((aeval M p).mulVec v) =
             (aeval M (p ^ (e + 1 + 1))).mulVec v := by
        rw [Matrix.mulVec_mulVec, ← map_mul]
        congr 2; ring
      rw [this]; exact hzero
    -- p^e(M)u = p^e(M)*p(M)*v = p^(e+1)(M)*v ≠ 0
    have hu_ne : (aeval M (p ^ e)).mulVec ((aeval M p).mulVec v) ≠ 0 := by
      have : (aeval M (p ^ e)).mulVec ((aeval M p).mulVec v) =
             (aeval M (p ^ (e + 1))).mulVec v := by
        rw [Matrix.mulVec_mulVec, ← map_mul]
        congr 2; ring
      rw [this]; exact hne
    -- r₁(M)u = r₁(M)*p(M)*v = (r₁*p)(M)*v = r(M)*v = 0
    have hr₁u : (aeval M r₁).mulVec ((aeval M p).mulVec v) = 0 := by
      have : (aeval M r₁).mulVec ((aeval M p).mulVec v) =
             (aeval M r).mulVec v := by
        rw [Matrix.mulVec_mulVec, ← map_mul]
        congr 2; rw [mul_comm r₁ p, ← hr₁_eq]
      rw [this]; exact hrv
    -- IH gives p^(e+1) | r₁
    have hp_e_r₁ : p ^ (e + 1) ∣ r₁ := ih ((aeval M p).mulVec v) hu_ne hu_zero r₁ hr₁u
    -- Conclude p^(e+2) | r = p * r₁
    obtain ⟨r₂, hr₂_eq⟩ := hp_e_r₁
    exact ⟨r₂, by rw [hr₁_eq, hr₂_eq]; ring⟩

-- ============================================================
-- SECTION IV: Main Theorem — Prime Power Case
-- ============================================================

/-- **Main Theorem (Prime Power Case)**:
    For nonderogatory M with minpoly = p^e (p monic irreducible, e ≥ 1),
    M has a cyclic vector over any field K.

    **Axiom-free proof** (no PID structure theorem needed):
    1. p^(e-1)(M) ≠ 0 (by minimality of minpoly, since deg(p^(e-1)) < n).
    2. ∃ v with p^(e-1)(M)v ≠ 0. Also p^e(M)v = 0 (minpoly kills all vectors).
    3. `pow_irred_dvd_of_annihilated`: r(M)v = 0 → p^e | r.
    4. If r ≠ 0: deg(p^e) ≤ deg(r) < n = deg(p^e). Contradiction → r = 0. -/
theorem nonderogatory_pw_has_cyclic_vector
    (M : Matrix (Fin n) (Fin n) K)
    (h_nd : IsNonderogatory M)
    (p : K[X]) (e : ℕ)
    (hp_irr : Irreducible p) (hp_monic : p.Monic)
    (he_pos : 0 < e)
    (h_min : minpoly K M = p ^ e) :
    ∃ v, IsCyclicVector M v := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨Fin.elim0, fun r hr _ => by omega⟩
  -- Degree of minpoly = n
  have h_deg : (minpoly K M).natDegree = n := by
    rw [h_nd, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  -- p ≠ 0 and p.natDegree > 0 (p irreducible over a field → not a unit → degree > 0)
  have hp_ne : p ≠ 0 := hp_monic.ne_zero
  have hp_deg_pos : 0 < p.natDegree := by
    by_contra h; push_neg at h
    exact hp_irr.not_isUnit
      ((Polynomial.eq_one_of_monic_natDegree_zero hp_monic (Nat.le_zero.mp h)) ▸ isUnit_one)
  -- natDegree(p^e) = e * natDegree(p) = n
  have h_pe_deg : (p ^ e).natDegree = n := by rw [← h_deg, h_min]
  have h_e_deg : e * p.natDegree = n := by rw [← h_pe_deg, Polynomial.natDegree_pow]
  -- p^(e-1)(M) ≠ 0 since natDegree(p^(e-1)) = (e-1)*deg(p) < e*deg(p) = n
  have hprev_deg : (p ^ (e - 1)).natDegree < (minpoly K M).natDegree := by
    rw [h_deg, Polynomial.natDegree_pow, ← h_e_deg]
    apply Nat.mul_lt_mul_of_pos_right _ hp_deg_pos
    omega
  have hprev_mat_ne : (aeval M (p ^ (e - 1)) : Matrix (Fin n) (Fin n) K) ≠ 0 :=
    aeval_ne_zero_of_lt_minpoly (pow_ne_zero _ hp_ne) hprev_deg
  -- Find v with p^(e-1)(M)v ≠ 0
  obtain ⟨v, hv_ne⟩ := exists_mulVec_ne_zero hprev_mat_ne
  -- p^e(M)v = minpoly(M)v = 0 (minpoly annihilates all vectors)
  have hpe_v : (aeval M (p ^ e)).mulVec v = 0 := by
    have hmat : (aeval M (p ^ e) : Matrix (Fin n) (Fin n) K) = 0 := by
      rw [← h_min]; exact minpoly.aeval K M
    simp [hmat]
  -- Apply pow_irred_dvd_of_annihilated: need exponent in form (e-1+1) = e
  have he1 : e - 1 + 1 = e := Nat.sub_add_cancel he_pos
  have hprev'_v : (aeval M (p ^ (e - 1 + 1))).mulVec v = 0 := by rwa [he1]
  -- v is a cyclic vector
  refine ⟨v, fun r hr_deg hann => ?_⟩
  by_contra hr_ne
  -- r(M)v = 0 → p^e | r
  have h_strong : p ^ e ∣ r := by
    have := pow_irred_dvd_of_annihilated hp_irr (e - 1) v hv_ne hprev'_v r hann
    rwa [he1] at this
  -- deg(p^e) = n ≤ deg(r) < n. Contradiction.
  have h_le : n ≤ r.natDegree :=
    h_pe_deg ▸ Polynomial.natDegree_le_of_dvd h_strong hr_ne
  omega

/-- Corollary: Prime power case works over finite fields of any size. -/
theorem nonderogatory_pw_has_cyclic_vector_finite [Fintype K]
    (M : Matrix (Fin n) (Fin n) K)
    (h_nd : IsNonderogatory M)
    (p : K[X]) (e : ℕ)
    (hp_irr : Irreducible p) (hp_monic : p.Monic)
    (he_pos : 0 < e)
    (h_min : minpoly K M = p ^ e) :
    ∃ v, IsCyclicVector M v :=
  nonderogatory_pw_has_cyclic_vector M h_nd p e hp_irr hp_monic he_pos h_min

end PrimePowerCyclicVector

end
