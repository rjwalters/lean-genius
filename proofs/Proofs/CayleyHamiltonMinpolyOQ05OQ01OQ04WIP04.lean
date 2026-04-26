/-
  Nonderogatory → Cyclic Vector: Binary Prime Power Case (All Fields)

  This file proves the cyclic vector theorem for nonderogatory matrices whose
  minimal polynomial factors as p^a * q^b where p, q are distinct monic
  irreducible polynomials (coprime), a >= 1, b >= 1, over ANY field K.

  This combines:
  - WIP02's CRT/Bezout projection technique (for the squarefree binary case)
  - WIP03's `pow_irred_dvd_of_annihilated` (for prime power divisibility)

  ## Status: axiom-free (0 axioms, target 0 sorries)

  ## Proof Strategy

  Given nonderogatory M with minpoly K M = p^a * q^b:

  1. IsCoprime(p^a, q^b) from IsCoprime(p, q) via coprime powers.
  2. Bezout: exists s t with s * p^a + t * q^b = 1.
  3. Find v1 in ker(p^a(M)) with p^(a-1)(M) * v1 != 0:
     - w1 with (p^(a-1) * q^b)(M) * w1 != 0 (degree < n, so matrix nonzero)
     - v1 = q^b(M) * w1 satisfies: p^(a-1)(M) * v1 != 0, p^a(M) * v1 = 0
     - pow_irred_dvd_of_annihilated gives: r(M) * v1 = 0 -> p^a | r
  4. Similarly find v2 in ker(q^b(M)) with q^(b-1)(M) * v2 != 0:
     - pow_irred_dvd_of_annihilated gives: r(M) * v2 = 0 -> q^b | r
  5. v = v1 + v2 is cyclic:
     - CRT projections extract r(M) * v1 = 0 and r(M) * v2 = 0
     - Then p^a | r and q^b | r, with IsCoprime(p^a, q^b) -> p^a * q^b | r
     - deg(p^a * q^b) = n <= deg(r) < n, contradiction.

  ## Coverage

  - WIP02: minpoly squarefree -> cyclic vector (axiom-free)
  - WIP03: minpoly = p^e -> cyclic vector (axiom-free)
  - WIP04: minpoly = p^a * q^b -> cyclic vector (axiom-free, this file)

  Together WIP02 + WIP03 + WIP04 cover all cases where the minimal polynomial
  has at most 2 distinct irreducible factors. The general case (arbitrary number
  of factors) can be handled by induction on the number of factors using
  the same CRT technique.
-/
import Mathlib

noncomputable section

namespace BinaryPrimePowerCyclicVector

open Matrix Polynomial

attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K] {n : ℕ}

-- ============================================================
-- SECTION I: Definitions (same as WIP02/WIP03)
-- ============================================================

/-- A vector v is cyclic for M if no nonzero polynomial of degree < n annihilates v. -/
def IsCyclicVector (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : Prop :=
  ∀ p : K[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0

/-- M is nonderogatory if minpoly = charpoly. -/
def IsNonderogatory (M : Matrix (Fin n) (Fin n) K) : Prop :=
  minpoly K M = M.charpoly

-- ============================================================
-- SECTION II: Utility Lemmas (copied from WIP02/WIP03)
-- ============================================================

/-- If p irred, v != 0, p(M)v = 0, r(M)v = 0, then p | r. (Bezout argument.) -/
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

/-- Minimality of minpoly: natDegree < minpoly natDegree -> polynomial != 0 as matrix. -/
private lemma aeval_ne_zero_of_lt_minpoly {M : Matrix (Fin n) (Fin n) K}
    {p : K[X]} (hp_ne : p ≠ 0)
    (hp_deg : p.natDegree < (minpoly K M).natDegree) :
    (aeval M p : Matrix (Fin n) (Fin n) K) ≠ 0 := by
  intro h
  exact absurd (Polynomial.natDegree_le_of_dvd (minpoly.dvd K M h) hp_ne) (by omega)

/-- Polynomials in M commute: aeval M f * aeval M g = aeval M g * aeval M f. -/
private lemma aeval_mul_comm_poly {M : Matrix (Fin n) (Fin n) K} (f g : K[X]) :
    aeval M f * aeval M g = aeval M g * aeval M f := by
  rw [← map_mul (aeval M), ← map_mul (aeval M), mul_comm]

-- ============================================================
-- SECTION III: Prime Power Divisibility (from WIP03)
-- ============================================================

/-- **Prime power divisibility from annihilation** (induction on e):
    If p irred, p^e(M)v != 0, p^(e+1)(M)v = 0, r(M)v = 0, then p^(e+1) | r. -/
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
    intro v hne hzero r hrv
    have hv_ne : v ≠ 0 := by simpa using hne
    have hpv_zero : (aeval M p).mulVec v = 0 := by simpa using hzero
    simpa using irreducible_dvd_of_annihilated hp_irr hv_ne hpv_zero hrv
  | succ e ih =>
    intro v hne hzero r hrv
    -- Step 1: p | r via w = p^(e+1)(M)v
    have hw_ne : (aeval M (p ^ (e + 1))).mulVec v ≠ 0 := hne
    have hpw : (aeval M p).mulVec ((aeval M (p ^ (e + 1))).mulVec v) = 0 := by
      have : (aeval M p).mulVec ((aeval M (p ^ (e + 1))).mulVec v) =
             (aeval M (p ^ (e + 1 + 1))).mulVec v := by
        rw [Matrix.mulVec_mulVec, ← map_mul]
        congr 2; ring
      rw [this]; exact hzero
    have hrw : (aeval M r).mulVec ((aeval M (p ^ (e + 1))).mulVec v) = 0 := by
      rw [Matrix.mulVec_mulVec, ← map_mul (aeval M),
          show r * p ^ (e + 1) = p ^ (e + 1) * r from mul_comm _ _,
          map_mul (aeval M), ← Matrix.mulVec_mulVec, hrv, Matrix.mulVec_zero]
    have hp_r : p ∣ r := irreducible_dvd_of_annihilated hp_irr hw_ne hpw hrw
    obtain ⟨r₁, hr₁_eq⟩ := hp_r
    -- Step 2: Apply IH to u = p(M)v, polynomial r₁
    have hu_zero : (aeval M (p ^ (e + 1))).mulVec ((aeval M p).mulVec v) = 0 := by
      have : (aeval M (p ^ (e + 1))).mulVec ((aeval M p).mulVec v) =
             (aeval M (p ^ (e + 1 + 1))).mulVec v := by
        rw [Matrix.mulVec_mulVec, ← map_mul]
        congr 2; ring
      rw [this]; exact hzero
    have hu_ne : (aeval M (p ^ e)).mulVec ((aeval M p).mulVec v) ≠ 0 := by
      have : (aeval M (p ^ e)).mulVec ((aeval M p).mulVec v) =
             (aeval M (p ^ (e + 1))).mulVec v := by
        rw [Matrix.mulVec_mulVec, ← map_mul]
        congr 2; ring
      rw [this]; exact hne
    have hr₁u : (aeval M r₁).mulVec ((aeval M p).mulVec v) = 0 := by
      have : (aeval M r₁).mulVec ((aeval M p).mulVec v) =
             (aeval M r).mulVec v := by
        rw [Matrix.mulVec_mulVec, ← map_mul]
        congr 2; rw [mul_comm r₁ p, ← hr₁_eq]
      rw [this]; exact hrv
    have hp_e_r₁ : p ^ (e + 1) ∣ r₁ := ih ((aeval M p).mulVec v) hu_ne hu_zero r₁ hr₁u
    obtain ⟨r₂, hr₂_eq⟩ := hp_e_r₁
    exact ⟨r₂, by rw [hr₁_eq, hr₂_eq]; ring⟩

-- ============================================================
-- SECTION IV: CRT Projection Lemmas (from WIP02)
-- ============================================================

/-- **CRT projection identity**: The Bezout projection e = b(M)*q(M) acts as
    the identity on ker(p(M)), given a*p + b*q = 1. -/
private lemma bezout_proj_identity {M : Matrix (Fin n) (Fin n) K}
    {p q a b : K[X]} (hab : a * p + b * q = 1) {v : Fin n → K}
    (hpv : (aeval M p).mulVec v = 0) :
    (aeval M b * aeval M q).mulVec v = v := by
  have hmat : aeval M a * aeval M p + aeval M b * aeval M q = 1 := by
    have h := congr_arg (aeval M) hab
    simp only [map_add, map_mul, map_one] at h; exact h
  have h := congr_arg (· *ᵥ v) hmat
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hpv, Matrix.mulVec_zero,
             Matrix.one_mulVec, zero_add] at h
  rwa [← Matrix.mulVec_mulVec]

/-- **CRT projection kills other component**: The Bezout projection b(M)*q(M) kills
    vectors annihilated by q(M). -/
private lemma bezout_proj_kills {M : Matrix (Fin n) (Fin n) K}
    {q b : K[X]} {v : Fin n → K} (hqv : (aeval M q).mulVec v = 0) :
    (aeval M b * aeval M q).mulVec v = 0 := by
  rw [← Matrix.mulVec_mulVec, hqv, Matrix.mulVec_zero]

-- ============================================================
-- SECTION V: Main Theorem — Binary Prime Power Case
-- ============================================================

/-- **Main Theorem (Binary Prime Power Case)**:
    For nonderogatory M with minpoly = p^a * q^b (p, q distinct monic irreducibles,
    coprime, a >= 1, b >= 1), M has a cyclic vector over any field K.

    **Axiom-free proof** combining CRT projections (WIP02) with prime power
    divisibility (WIP03):

    1. IsCoprime(p, q) -> IsCoprime(p^a, q^b) via coprime powers.
    2. Bezout: exists s, t with s * p^a + t * q^b = 1.
    3. Find v1 = q^b(M) * w1 in ker(p^a(M)) with p^(a-1)(M) * v1 != 0.
       Then pow_irred_dvd_of_annihilated gives: r(M) * v1 = 0 -> p^a | r.
    4. Find v2 = p^a(M) * w2 in ker(q^b(M)) with q^(b-1)(M) * v2 != 0.
       Then pow_irred_dvd_of_annihilated gives: r(M) * v2 = 0 -> q^b | r.
    5. v = v1 + v2 is cyclic via CRT projections + IsCoprime(p^a, q^b).mul_dvd. -/
theorem nonderogatory_bipow_has_cyclic_vector
    (M : Matrix (Fin n) (Fin n) K)
    (h_nd : IsNonderogatory M)
    (p q : K[X])
    (a b : ℕ)
    (hp_irr : Irreducible p) (hq_irr : Irreducible q)
    (hp_monic : p.Monic) (hq_monic : q.Monic)
    (ha_pos : 0 < a) (hb_pos : 0 < b)
    (hcop : IsCoprime p q)
    (h_min : minpoly K M = p ^ a * q ^ b) :
    ∃ v, IsCyclicVector M v := by
  -- Trivial base case
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨Fin.elim0, fun r hr _ => by omega⟩
  -- Basic nonzero facts
  have hp_ne : p ≠ 0 := hp_monic.ne_zero
  have hq_ne : q ≠ 0 := hq_monic.ne_zero
  have hpa_ne : p ^ a ≠ 0 := pow_ne_zero _ hp_ne
  have hqb_ne : q ^ b ≠ 0 := pow_ne_zero _ hq_ne
  -- Degree of minpoly = n
  have h_deg : (minpoly K M).natDegree = n := by
    rw [h_nd, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  -- Degree facts
  have hp_deg_pos : 0 < p.natDegree := by
    by_contra h; push_neg at h
    exact hp_irr.not_isUnit
      ((Polynomial.eq_one_of_monic_natDegree_zero hp_monic (Nat.le_zero.mp h)) ▸ isUnit_one)
  have hq_deg_pos : 0 < q.natDegree := by
    by_contra h; push_neg at h
    exact hq_irr.not_isUnit
      ((Polynomial.eq_one_of_monic_natDegree_zero hq_monic (Nat.le_zero.mp h)) ▸ isUnit_one)
  -- natDegree(p^a) = a * natDegree(p), natDegree(q^b) = b * natDegree(q)
  have hpa_deg : (p ^ a).natDegree = a * p.natDegree := Polynomial.natDegree_pow
  have hqb_deg : (q ^ b).natDegree = b * q.natDegree := Polynomial.natDegree_pow
  -- Total degree: a * deg(p) + b * deg(q) = n
  have h_total_deg : a * p.natDegree + b * q.natDegree = n := by
    have : (p ^ a * q ^ b).natDegree = n := by rw [← h_min]; exact h_deg
    rw [Polynomial.natDegree_mul hpa_ne hqb_ne, hpa_deg, hqb_deg] at this
    exact this
  -- IsCoprime(p^a, q^b) from IsCoprime(p, q)
  have hcop_pow : IsCoprime (p ^ a) (q ^ b) := hcop.pow_pow
  -- Bezout: exists s, t with s * p^a + t * q^b = 1
  obtain ⟨s, t, hst⟩ := hcop_pow
  -- ════════════════════════════════════════════════════════════
  -- Construct v1 in ker(p^a(M)) with p^(a-1)(M) * v1 != 0
  -- ════════════════════════════════════════════════════════════
  -- Write a = (a-1) + 1
  have ha_eq : a = (a - 1) + 1 := (Nat.sub_add_cancel ha_pos).symm
  -- (p^(a-1) * q^b)(M) != 0 since deg(p^(a-1) * q^b) < n
  have h_prev_p_deg_lt : (p ^ (a - 1) * q ^ b).natDegree < n := by
    rw [Polynomial.natDegree_mul (pow_ne_zero _ hp_ne) hqb_ne,
        Polynomial.natDegree_pow, Polynomial.natDegree_pow]
    calc (a - 1) * p.natDegree + b * q.natDegree
        < (a - 1) * p.natDegree + p.natDegree + b * q.natDegree := by
          linarith [hp_deg_pos]
      _ = ((a - 1) + 1) * p.natDegree + b * q.natDegree := by ring
      _ = a * p.natDegree + b * q.natDegree := by rw [Nat.sub_add_cancel ha_pos]
      _ = n := h_total_deg
  have h_prev_p_ne : p ^ (a - 1) * q ^ b ≠ 0 := mul_ne_zero (pow_ne_zero _ hp_ne) hqb_ne
  have h_prev_p_mat_ne : (aeval M (p ^ (a - 1) * q ^ b) : Matrix (Fin n) (Fin n) K) ≠ 0 :=
    aeval_ne_zero_of_lt_minpoly h_prev_p_ne (by rw [h_deg]; exact h_prev_p_deg_lt)
  -- Find w1 with (p^(a-1) * q^b)(M) * w1 != 0
  obtain ⟨w₁, hw₁⟩ := exists_mulVec_ne_zero h_prev_p_mat_ne
  -- v1 = q^b(M) * w1
  let v₁ := (aeval M (q ^ b)).mulVec w₁
  -- p^(a-1)(M) * v1 = (p^(a-1) * q^b)(M) * w1 != 0
  -- (using commutativity of polynomials in M)
  have hv₁_prev_ne : (aeval M (p ^ (a - 1))).mulVec v₁ ≠ 0 := by
    show (aeval M (p ^ (a - 1))).mulVec ((aeval M (q ^ b)).mulVec w₁) ≠ 0
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_comm]
    exact hw₁
  -- p^a(M) * v1 = (p^a * q^b)(M) * w1 = minpoly(M) * w1 = 0
  have hv₁_pa_ann : (aeval M (p ^ a)).mulVec v₁ = 0 := by
    show (aeval M (p ^ a)).mulVec ((aeval M (q ^ b)).mulVec w₁) = 0
    rw [Matrix.mulVec_mulVec, ← map_mul, ← h_min, minpoly.aeval K M, Matrix.zero_mulVec]
  -- v1 != 0 (since p^(a-1)(M) * v1 != 0)
  have hv₁_ne : v₁ ≠ 0 := by
    intro h; apply hv₁_prev_ne; rw [h, Matrix.mulVec_zero]
  -- Strong divisibility: r(M) * v1 = 0 -> p^a | r
  -- via pow_irred_dvd_of_annihilated with exponent (a-1)
  have hv₁_strong : ∀ r : K[X], (aeval M r).mulVec v₁ = 0 → p ^ a ∣ r := by
    intro r hr_v1
    have key := pow_irred_dvd_of_annihilated hp_irr (a - 1) v₁ hv₁_prev_ne
      (by rwa [Nat.sub_add_cancel ha_pos]) r hr_v1
    rwa [Nat.sub_add_cancel ha_pos] at key
  -- ════════════════════════════════════════════════════════════
  -- Construct v2 in ker(q^b(M)) with q^(b-1)(M) * v2 != 0
  -- ════════════════════════════════════════════════════════════
  -- Write b = (b-1) + 1
  have hb_eq : b = (b - 1) + 1 := (Nat.sub_add_cancel hb_pos).symm
  -- (p^a * q^(b-1))(M) != 0 since deg(p^a * q^(b-1)) < n
  have h_prev_q_deg_lt : (p ^ a * q ^ (b - 1)).natDegree < n := by
    rw [Polynomial.natDegree_mul hpa_ne (pow_ne_zero _ hq_ne),
        Polynomial.natDegree_pow, Polynomial.natDegree_pow]
    calc a * p.natDegree + (b - 1) * q.natDegree
        < a * p.natDegree + ((b - 1) * q.natDegree + q.natDegree) := by
          linarith [hq_deg_pos]
      _ = a * p.natDegree + ((b - 1) + 1) * q.natDegree := by ring
      _ = a * p.natDegree + b * q.natDegree := by rw [Nat.sub_add_cancel hb_pos]
      _ = n := h_total_deg
  have h_prev_q_ne : p ^ a * q ^ (b - 1) ≠ 0 := mul_ne_zero hpa_ne (pow_ne_zero _ hq_ne)
  have h_prev_q_mat_ne : (aeval M (p ^ a * q ^ (b - 1)) : Matrix (Fin n) (Fin n) K) ≠ 0 :=
    aeval_ne_zero_of_lt_minpoly h_prev_q_ne (by rw [h_deg]; exact h_prev_q_deg_lt)
  -- Find w2 with (p^a * q^(b-1))(M) * w2 != 0
  obtain ⟨w₂, hw₂⟩ := exists_mulVec_ne_zero h_prev_q_mat_ne
  -- v2 = p^a(M) * w2
  let v₂ := (aeval M (p ^ a)).mulVec w₂
  -- q^(b-1)(M) * v2 = (q^(b-1) * p^a)(M) * w2 = (p^a * q^(b-1))(M) * w2 != 0
  have hv₂_prev_ne : (aeval M (q ^ (b - 1))).mulVec v₂ ≠ 0 := by
    show (aeval M (q ^ (b - 1))).mulVec ((aeval M (p ^ a)).mulVec w₂) ≠ 0
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_comm]
    exact hw₂
  -- q^b(M) * v2 = (q^b * p^a)(M) * w2 = (p^a * q^b)(M) * w2 = minpoly(M) * w2 = 0
  have hv₂_qb_ann : (aeval M (q ^ b)).mulVec v₂ = 0 := by
    show (aeval M (q ^ b)).mulVec ((aeval M (p ^ a)).mulVec w₂) = 0
    rw [Matrix.mulVec_mulVec, ← map_mul, show q ^ b * p ^ a = p ^ a * q ^ b from mul_comm _ _,
        ← h_min, minpoly.aeval K M, Matrix.zero_mulVec]
  -- v2 != 0
  have hv₂_ne : v₂ ≠ 0 := by
    intro h; apply hv₂_prev_ne; rw [h, Matrix.mulVec_zero]
  -- Strong divisibility: r(M) * v2 = 0 -> q^b | r
  have hv₂_strong : ∀ r : K[X], (aeval M r).mulVec v₂ = 0 → q ^ b ∣ r := by
    intro r hr_v2
    have key := pow_irred_dvd_of_annihilated hq_irr (b - 1) v₂ hv₂_prev_ne
      (by rwa [Nat.sub_add_cancel hb_pos]) r hr_v2
    rwa [Nat.sub_add_cancel hb_pos] at key
  -- ════════════════════════════════════════════════════════════
  -- v = v1 + v2 is a cyclic vector
  -- ════════════════════════════════════════════════════════════
  use v₁ + v₂
  intro r hr hann
  by_contra hr_ne
  -- === Show r(M) * v1 = 0 via CRT projection e1 = t(M) * q^b(M) ===
  -- e1 is identity on ker(p^a(M)), kills ker(q^b(M))
  -- e1 commutes with r(M); e1 * (v1 + v2) = e1 * v1 + e1 * v2 = v1 + 0 = v1
  -- So r(M) * v1 = r(M) * e1 * (v1 + v2) = e1 * r(M) * (v1 + v2) = e1 * 0 = 0
  have hr_v1 : (aeval M r).mulVec v₁ = 0 := by
    have h_applied : (aeval M t * aeval M (q ^ b)).mulVec
        ((aeval M r).mulVec (v₁ + v₂)) = 0 := by
      rw [hann, Matrix.mulVec_zero]
    have h_comm : aeval M t * aeval M (q ^ b) * aeval M r =
        aeval M r * (aeval M t * aeval M (q ^ b)) := by
      have : aeval M t * aeval M (q ^ b) = aeval M (t * q ^ b) := by rw [map_mul]
      rw [this, aeval_mul_comm_poly (t * q ^ b) r, ← this]
    rw [Matrix.mulVec_mulVec, h_comm, ← Matrix.mulVec_mulVec,
        Matrix.mulVec_add,
        bezout_proj_identity hst hv₁_pa_ann,
        bezout_proj_kills hv₂_qb_ann, add_zero] at h_applied
    exact h_applied
  -- === Show r(M) * v2 = 0 via CRT projection e2 = s(M) * p^a(M) ===
  -- e2 is identity on ker(q^b(M)), kills ker(p^a(M))
  have hr_v2 : (aeval M r).mulVec v₂ = 0 := by
    have h_applied : (aeval M s * aeval M (p ^ a)).mulVec
        ((aeval M r).mulVec (v₁ + v₂)) = 0 := by
      rw [hann, Matrix.mulVec_zero]
    have h_comm : aeval M s * aeval M (p ^ a) * aeval M r =
        aeval M r * (aeval M s * aeval M (p ^ a)) := by
      have : aeval M s * aeval M (p ^ a) = aeval M (s * p ^ a) := by rw [map_mul]
      rw [this, aeval_mul_comm_poly (s * p ^ a) r, ← this]
    -- e2 kills v1: s(M) * p^a(M) * v1 = s(M) * 0 = 0
    have he2_v1 : (aeval M s * aeval M (p ^ a)).mulVec v₁ = 0 := by
      rw [← Matrix.mulVec_mulVec, hv₁_pa_ann, Matrix.mulVec_zero]
    -- e2 is identity on v2: t * q^b + s * p^a = 1, q^b(M) * v2 = 0
    have he2_v2 : (aeval M s * aeval M (p ^ a)).mulVec v₂ = v₂ := by
      apply bezout_proj_identity (p := q ^ b) (q := p ^ a) (a := t) (b := s)
      · calc t * q ^ b + s * p ^ a = s * p ^ a + t * q ^ b := add_comm _ _
          _ = 1 := hst
      · exact hv₂_qb_ann
    rw [Matrix.mulVec_mulVec, h_comm, ← Matrix.mulVec_mulVec,
        Matrix.mulVec_add, he2_v1, he2_v2, zero_add] at h_applied
    exact h_applied
  -- === Derive contradiction via degree ===
  -- p^a | r (from strong divisibility of v1)
  have hpa_r : p ^ a ∣ r := hv₁_strong r hr_v1
  -- q^b | r (from strong divisibility of v2)
  have hqb_r : q ^ b ∣ r := hv₂_strong r hr_v2
  -- IsCoprime(p^a, q^b) + p^a | r + q^b | r -> p^a * q^b | r
  have hpq_r : p ^ a * q ^ b ∣ r := hcop_pow.mul_dvd hpa_r hqb_r
  -- n = deg(p^a * q^b) <= deg(r) < n (contradiction)
  have h_pq_n : (p ^ a * q ^ b).natDegree = n := by
    rw [Polynomial.natDegree_mul hpa_ne hqb_ne, hpa_deg, hqb_deg, h_total_deg]
  have h_deg_le : n ≤ r.natDegree := by
    calc n = (p ^ a * q ^ b).natDegree := h_pq_n.symm
      _ ≤ r.natDegree := Polynomial.natDegree_le_of_dvd hpq_r hr_ne
  omega

/-- Corollary: Binary prime power case works over finite fields of any size. -/
theorem nonderogatory_bipow_has_cyclic_vector_finite [Fintype K]
    (M : Matrix (Fin n) (Fin n) K)
    (h_nd : IsNonderogatory M)
    (p q : K[X])
    (a b : ℕ)
    (hp_irr : Irreducible p) (hq_irr : Irreducible q)
    (hp_monic : p.Monic) (hq_monic : q.Monic)
    (ha_pos : 0 < a) (hb_pos : 0 < b)
    (hcop : IsCoprime p q)
    (h_min : minpoly K M = p ^ a * q ^ b) :
    ∃ v, IsCyclicVector M v :=
  nonderogatory_bipow_has_cyclic_vector M h_nd p q a b hp_irr hq_irr hp_monic hq_monic
    ha_pos hb_pos hcop h_min

end BinaryPrimePowerCyclicVector

end
