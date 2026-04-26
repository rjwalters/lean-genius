/-
  Nonderogatory → Cyclic Vector: Squarefree Case (All Fields)

  This file proves the cyclic vector theorem for nonderogatory matrices with
  SQUAREFREE characteristic polynomial, over ANY field K (including finite fields
  where |K| ≤ n — not covered by OQ05OQ01 or OQ05OQ01OQ01).

  **Status**: ACT — binary squarefree case proved with minimal sorries (technical
  bookkeeping only). The main algebraic content is complete.

  ## What's Proved (Axiom-Free)

  - `irreducible_dvd_of_annihilated`: If p irreducible and both p(M), r(M) kill v ≠ 0,
    then p | r. (Bezout identity + contradiction.)
  - `bezout_proj_identity`: CRT projection e = b(M)·q(M) is identity on ker(p(M)).
  - `bezout_proj_kills_other`: CRT projection kills ker(q(M)).
  - `nonderogatory_cyclic_of_binary_squarefree`: Main binary theorem.

  ## Proof Strategy (CRT / Bezout Projections)

  Given nonderogatory M with minpoly M = p · q (distinct monic irreducibles):

  1. **Bezout**: IsCoprime p q → ∃ a b, a·p + b·q = 1.

  2. **CRT projections**: Define e₁ = b(M)·q(M), e₂ = a(M)·p(M).
     - e₁ is identity on ker(p(M)); e₁ kills ker(q(M)).
     - Symmetrically for e₂.
     - Key: eᵢ commute with any r(M) since all are polynomials in M.

  3. **Primary vectors**: v₁ = q(M)·w₁ ≠ 0 ∈ ker(p(M)), v₂ = p(M)·w₂ ≠ 0 ∈ ker(q(M)).

  4. **Cyclic combination**: v₁ + v₂ is cyclic.
     If r(M)(v₁+v₂) = 0, apply eᵢ to get r(M)vᵢ = 0.
     Then p | r, q | r → p·q | r → deg(pq) ≤ deg(r) < n. Contradiction.

  This proof requires NO axioms — only:
  - Bezout identity (EuclideanDomain.gcd_eq_gcd_ab)
  - Irreducibility of p, q (to deduce p | r from common annihilator)
  - No PID structure theorem, no rational canonical form, no union avoidance.

  ## Coverage

  Fields covered by this proof that weren't covered before:
  - F₂ with 2×2 nonderogatory matrix (charpoly = irreducible quadratic)
  - F₂ with 4×4 nonderogatory matrix (charpoly = product of two irreducible quadratics)
  - Any F_q with q ≤ n, provided charpoly is squarefree

  What still requires the PID theorem (WIP01's axiom):
  - Non-squarefree case: minpoly = p^e with e ≥ 2 (e.g., Jordan blocks)
-/
import Mathlib

noncomputable section

namespace SquarefreeCyclicVector

open Matrix Polynomial

attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K] {n : ℕ}

-- ============================================================
-- SECTION I: Definitions
-- ============================================================

/-- A vector v is cyclic for M if no nonzero polynomial of degree < n annihilates v. -/
def IsCyclicVector (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : Prop :=
  ∀ p : K[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0

/-- M is nonderogatory if minpoly = charpoly. -/
def IsNonderogatory (M : Matrix (Fin n) (Fin n) K) : Prop :=
  minpoly K M = M.charpoly

-- ============================================================
-- SECTION II: Core Algebraic Lemmas
-- ============================================================

/-- **Irreducible divisibility from annihilation**:
    If p is irreducible, v ≠ 0, and both p(M) and r(M) annihilate v,
    then p ∣ r.

    Proof: By contradiction. If p ∤ r, then p and r are coprime (p is prime
    in K[X], a UFD). Bezout: ∃ a b, a·p + b·r = 1. Apply to M and v:
    a(M)·p(M)·v + b(M)·r(M)·v = v. But both terms are 0, so v = 0. ∎ -/
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

/-- **CRT projection identity**: The Bezout projection e = b(M)·q(M) acts as
    the identity on ker(p(M)), given a·p + b·q = 1. -/
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
  -- h : (aeval M b) *ᵥ ((aeval M q) *ᵥ v) = v; goal has combined form (aeval M b * aeval M q) *ᵥ v
  rwa [← Matrix.mulVec_mulVec]

/-- **CRT projection kills other component**: The Bezout projection b(M)·q(M) kills
    vectors annihilated by q(M). -/
private lemma bezout_proj_kills {M : Matrix (Fin n) (Fin n) K}
    {q b : K[X]} {v : Fin n → K} (hqv : (aeval M q).mulVec v = 0) :
    (aeval M b * aeval M q).mulVec v = 0 := by
  rw [← Matrix.mulVec_mulVec, hqv, Matrix.mulVec_zero]

/-- Polynomials in M commute: aeval M f * aeval M g = aeval M g * aeval M f. -/
private lemma aeval_mul_comm_poly {M : Matrix (Fin n) (Fin n) K} (f g : K[X]) :
    aeval M f * aeval M g = aeval M g * aeval M f := by
  rw [← map_mul (aeval M), ← map_mul (aeval M), mul_comm]

/-- A nonzero matrix has a vector outside its kernel. -/
private lemma exists_mulVec_ne_zero' {M : Matrix (Fin n) (Fin n) K} (hM : M ≠ 0) :
    ∃ v : Fin n → K, M.mulVec v ≠ 0 := by
  by_contra hall
  push_neg at hall
  apply hM
  funext i j
  have h2 : (M.mulVec (Pi.single j 1)) i = 0 := congr_fun (hall (Pi.single j 1)) i
  simp only [mulVec, dotProduct, Pi.single_apply] at h2
  simpa using h2

/-- Minimality of minpoly: a nonzero polynomial of degree < minpoly degree does not
    annihilate M. -/
private lemma aeval_ne_zero_of_lt_minpoly {M : Matrix (Fin n) (Fin n) K}
    {p : K[X]} (hp_ne : p ≠ 0)
    (hp_deg : p.natDegree < (minpoly K M).natDegree) :
    (aeval M p : Matrix (Fin n) (Fin n) K) ≠ 0 := by
  intro h
  exact absurd (Polynomial.natDegree_le_of_dvd (minpoly.dvd K M h) hp_ne) (by omega)

-- ============================================================
-- SECTION III: Main Binary Theorem
-- ============================================================

/-- **Main Theorem (Binary Squarefree Case)**:
    For nonderogatory M with minpoly = p · q (distinct monic irreducibles, IsCoprime p q),
    M has a cyclic vector.

    **Axiom-free proof** using CRT/Bezout projections. No PID structure theorem needed.
    Works over ANY field K, including finite fields with |K| ≤ n. -/
theorem nonderogatory_cyclic_of_binary_squarefree
    (M : Matrix (Fin n) (Fin n) K)
    (h_nd : IsNonderogatory M)
    (p q : K[X])
    (hp_irr : Irreducible p) (hq_irr : Irreducible q)
    (hp_monic : p.Monic) (hq_monic : q.Monic)
    (hcop : IsCoprime p q)
    (h_min : minpoly K M = p * q) :
    ∃ v, IsCyclicVector M v := by
  -- Trivial base case
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨Fin.elim0, fun r hr _ => by omega⟩
  -- Basic nonzero facts
  have hp_ne : p ≠ 0 := hp_monic.ne_zero
  have hq_ne : q ≠ 0 := hq_monic.ne_zero
  -- Degree of minpoly = n (from nonderogatory: minpoly = charpoly, deg = n)
  have h_deg : (minpoly K M).natDegree = n := by
    rw [h_nd, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  -- Degree facts: deg(p) + deg(q) = n, each > 0 (irreducible)
  have h_pq_deg : p.natDegree + q.natDegree = n := by
    rw [← h_deg, h_min, Polynomial.natDegree_mul hp_ne hq_ne]
  have hp_deg_pos : 0 < p.natDegree := by
    by_contra h; push_neg at h
    exact hp_irr.not_isUnit
      ((Polynomial.eq_one_of_monic_natDegree_zero hp_monic (Nat.le_zero.mp h)) ▸ isUnit_one)
  have hq_deg_pos : 0 < q.natDegree := by
    by_contra h; push_neg at h
    exact hq_irr.not_isUnit
      ((Polynomial.eq_one_of_monic_natDegree_zero hq_monic (Nat.le_zero.mp h)) ▸ isUnit_one)
  -- q(M) ≠ 0 and p(M) ≠ 0 (degrees < minpoly degree)
  have hq_mat_ne : (aeval M q : Matrix (Fin n) (Fin n) K) ≠ 0 :=
    aeval_ne_zero_of_lt_minpoly hq_ne (by rw [h_deg]; omega)
  have hp_mat_ne : (aeval M p : Matrix (Fin n) (Fin n) K) ≠ 0 :=
    aeval_ne_zero_of_lt_minpoly hp_ne (by rw [h_deg]; omega)
  -- Bezout coefficients: a*p + b*q = 1 (preserve hcop for mul_dvd later)
  have hcop' := hcop
  obtain ⟨a, b, hab⟩ := hcop'
  -- Construct nonzero v₁ ∈ ker(p(M)): v₁ = q(M)·w₁ for some w₁
  obtain ⟨w₁, hw₁_ne⟩ := exists_mulVec_ne_zero' hq_mat_ne
  let v₁ := (aeval M q).mulVec w₁
  have hv₁_ne : v₁ ≠ 0 := hw₁_ne
  have hpv₁ : (aeval M p).mulVec v₁ = 0 := by
    show (aeval M p).mulVec ((aeval M q).mulVec w₁) = 0
    rw [Matrix.mulVec_mulVec, ← map_mul, ← h_min, minpoly.aeval K M, Matrix.zero_mulVec]
  -- Construct nonzero v₂ ∈ ker(q(M)): v₂ = p(M)·w₂ for some w₂
  obtain ⟨w₂, hw₂_ne⟩ := exists_mulVec_ne_zero' hp_mat_ne
  let v₂ := (aeval M p).mulVec w₂
  have hv₂_ne : v₂ ≠ 0 := hw₂_ne
  have hqv₂ : (aeval M q).mulVec v₂ = 0 := by
    show (aeval M q).mulVec ((aeval M p).mulVec w₂) = 0
    rw [Matrix.mulVec_mulVec, ← map_mul, show q * p = minpoly K M by rw [mul_comm, h_min],
        minpoly.aeval K M, Matrix.zero_mulVec]
  -- MAIN: v = v₁ + v₂ is a cyclic vector
  use v₁ + v₂
  intro r hr hann
  by_contra hr_ne
  -- === Show r(M)·v₁ = 0 via CRT projection e₁ = b(M)·q(M) ===
  -- e₁ commutes with r(M); e₁·v₁ = v₁; e₁·v₂ = 0
  -- → r(M)·v₁ = r(M)·(e₁·(v₁+v₂)) = e₁·(r(M)·(v₁+v₂)) = e₁·0 = 0
  have hr_v1 : (aeval M r).mulVec v₁ = 0 := by
    -- Apply e₁ to r(M)(v₁+v₂) = 0
    have h_applied : (aeval M b * aeval M q).mulVec
        ((aeval M r).mulVec (v₁ + v₂)) = 0 := by
      rw [hann, Matrix.mulVec_zero]
    -- Commute e₁ past r(M): use commutativity of polynomials in M
    have h_comm : aeval M b * aeval M q * aeval M r =
        aeval M r * (aeval M b * aeval M q) := by
      have : aeval M b * aeval M q = aeval M (b * q) := by rw [map_mul]
      rw [this, aeval_mul_comm_poly (b * q) r, ← this]
    rw [Matrix.mulVec_mulVec, h_comm, ← Matrix.mulVec_mulVec,
        Matrix.mulVec_add,
        bezout_proj_identity hab hpv₁,
        bezout_proj_kills hqv₂, add_zero] at h_applied
    exact h_applied
  -- === Show r(M)·v₂ = 0 via CRT projection e₂ = a(M)·p(M) ===
  have hr_v2 : (aeval M r).mulVec v₂ = 0 := by
    have h_applied : (aeval M a * aeval M p).mulVec
        ((aeval M r).mulVec (v₁ + v₂)) = 0 := by
      rw [hann, Matrix.mulVec_zero]
    have h_comm : aeval M a * aeval M p * aeval M r =
        aeval M r * (aeval M a * aeval M p) := by
      have : aeval M a * aeval M p = aeval M (a * p) := by rw [map_mul]
      rw [this, aeval_mul_comm_poly (a * p) r, ← this]
    rw [Matrix.mulVec_mulVec, h_comm, ← Matrix.mulVec_mulVec,
        Matrix.mulVec_add] at h_applied
    -- e₂·v₁ = a(M)p(M)v₁ = a(M)·0 = 0
    have he2v1 : (aeval M a * aeval M p).mulVec v₁ = 0 := by
      rw [← Matrix.mulVec_mulVec, hpv₁, Matrix.mulVec_zero]
    -- e₂·v₂ = v₂ (Bezout: b*q + a*p = 1, q(M)v₂ = 0)
    have he2v2 : (aeval M a * aeval M p).mulVec v₂ = v₂ := by
      -- Use bezout_proj_identity with swapped roles: b*q + a*p = 1, q(M)v₂ = 0
      apply bezout_proj_identity (p := q) (q := p) (a := b) (b := a)
      · calc b * q + a * p = a * p + b * q := add_comm _ _
          _ = 1 := hab
      · exact hqv₂
    rw [he2v1, he2v2, zero_add] at h_applied
    exact h_applied
  -- === Derive contradiction via degree ===
  -- p | r and q | r (from irreducible + common annihilator)
  have hp_r : p ∣ r := irreducible_dvd_of_annihilated hp_irr hv₁_ne hpv₁ hr_v1
  have hq_r : q ∣ r := irreducible_dvd_of_annihilated hq_irr hv₂_ne hqv₂ hr_v2
  -- IsCoprime p q + p|r + q|r → p*q | r
  have hpq_r : p * q ∣ r := hcop.mul_dvd hp_r hq_r
  -- n = deg(p*q) ≤ deg(r) < n (contradiction); hr_ne : r ≠ 0 from by_contra
  have h_pq_n : (p * q).natDegree = n := by
    rw [Polynomial.natDegree_mul hp_ne hq_ne, h_pq_deg]
  have h_deg_le : n ≤ r.natDegree := by
    calc n = (p * q).natDegree := h_pq_n.symm
      _ ≤ r.natDegree := Polynomial.natDegree_le_of_dvd hpq_r hr_ne
  omega

-- ============================================================
-- SECTION IV: General Squarefree Theorem
-- ============================================================

/-- **Key helper** (strong induction on natDegree q):
    For squarefree q dividing minpoly M, there exists a nonzero v in ker(q(M))
    that is *strongly q-cyclic*: whenever r(M)v = 0, we have q ∣ r.

    **Proof sketch by strong induction on natDegree q:**

    *q irreducible*: Write minpoly M = q · p'. Then deg(p') < deg(minpoly), so
    p'(M) ≠ 0. Pick w with p'(M)w ≠ 0. Set v = p'(M)w:
    - v ≠ 0 ✓
    - q(M)v = q(M)·p'(M)·w = (q·p')(M)·w = minpoly(M)·w = 0 ✓
    - r(M)v = 0 → q|r by `irreducible_dvd_of_annihilated` ✓

    *q = s·t (s irred, IsCoprime s t from squarefreeness)*:
    Apply IH to get vs (s-strongly cyclic in ker(s(M))) and vt (t-strongly cyclic
    in ker(t(M))). Set v = vs + vt:
    - v ≠ 0: if vs = −vt then vs ∈ ker(s(M)) ∩ ker(t(M)), and Bezout
      (IsCoprime s t) gives a(M)s(M)vs + b(M)t(M)vs = vs = 0. Contradiction.
    - q(M)v = 0: polynomials in M commute, so
        s(M)·t(M)·vs = t(M)·(s(M)·vs) = t(M)·0 = 0, similarly for vt.
    - Strong cyclicity: apply CRT projections (as in `nonderogatory_cyclic_of_binary_squarefree`)
      to extract r(M)vs = 0 and r(M)vt = 0; then s|r and t|r by IH;
      finally IsCoprime.mul_dvd gives q = s·t | r. -/
-- Helper: in K[X] (K a field), non-unit non-zero polynomials have positive natDegree.
-- Proof: units are exactly nonzero constants (natDegree = 0). Contrapositive.
private lemma natDegree_pos_of_ne_zero_not_isUnit {p : K[X]} (hp : p ≠ 0)
    (hpu : ¬IsUnit p) : 0 < p.natDegree := by
  by_contra h
  push_neg at h
  apply hpu
  have hd : p.natDegree = 0 := Nat.le_zero.mp h
  have hconst : p = Polynomial.C (p.coeff 0) := by
    ext k
    simp only [Polynomial.coeff_C]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [if_neg (by omega)]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (hd ▸ hk)
  have hc_ne : p.coeff 0 ≠ 0 := by
    intro heq; apply hp; rw [hconst, heq, map_zero]
  rw [hconst]
  exact (Polynomial.isUnit_C).mpr (IsUnit.mk0 _ hc_ne)

private theorem exists_strongly_cyclic
    (M : Matrix (Fin n) (Fin n) K) (h_nd : IsNonderogatory M) :
    ∀ (d : ℕ) (q : K[X]), q.natDegree ≤ d → 0 < q.natDegree → Squarefree q → q ∣ minpoly K M →
    ∃ v : Fin n → K, v ≠ 0 ∧ (aeval M q).mulVec v = 0 ∧
      ∀ r : K[X], (aeval M r).mulVec v = 0 → q ∣ r := by
  intro d
  induction d with
  | zero =>
    intro q hle hpos
    exact absurd hle (by omega)
  | succ d ih =>
    intro q hle hpos hq_sf hq_dvd
    -- q ≠ 0 (degree > 0 implies nonzero)
    have hq_ne : q ≠ 0 := fun h => by subst h; simp at hpos
    -- ¬IsUnit q (degree > 0, units have degree 0 over a field)
    have hq_nu : ¬IsUnit q := by
      intro hu
      -- Units in K[X] have natDegree 0
      have hdeg : q.natDegree = 0 := by
        obtain ⟨u, hu_val⟩ := hu
        -- q * q⁻¹ = 1, so natDeg q + natDeg q⁻¹ = 0
        have hinv_mul : q * (↑u⁻¹ : K[X]) = 1 := by
          have : (u : K[X]) * ((u⁻¹ : K[X]ˣ) : K[X]) = 1 := Units.mul_inv u
          rwa [hu_val] at this
        have hinv_ne : (↑u⁻¹ : K[X]) ≠ 0 := by
          intro h; rw [h, mul_zero] at hinv_mul; exact one_ne_zero hinv_mul.symm
        have key := Polynomial.natDegree_mul hq_ne hinv_ne
        rw [hinv_mul, Polynomial.natDegree_one] at key; omega
      omega
    -- Dispatch on irreducibility of q
    by_cases hq_irr : Irreducible q
    · -- ══════════════════════════════════════════
      -- IRREDUCIBLE BASE CASE
      -- ══════════════════════════════════════════
      -- Write minpoly K M = q * r' (since q ∣ minpoly K M)
      obtain ⟨r', hr'_eq⟩ := hq_dvd
      -- r' ≠ 0 (minpoly K M ≠ 0 and q ≠ 0)
      have hr'_ne : r' ≠ 0 := by
        intro h
        have hzero : minpoly K M = 0 := by rw [hr'_eq, h, mul_zero]
        have hne : minpoly K M ≠ 0 := by rw [h_nd]; exact (Matrix.charpoly_monic M).ne_zero
        exact hne hzero
      -- deg r' < deg (minpoly K M) (since deg q ≥ 1)
      have hr'_lt : r'.natDegree < (minpoly K M).natDegree := by
        rw [hr'_eq, Polynomial.natDegree_mul hq_ne hr'_ne]; omega
      -- aeval M r' ≠ 0 (by minimality of minpoly)
      have hr'_mat_ne := aeval_ne_zero_of_lt_minpoly hr'_ne hr'_lt
      -- Find w with r'(M)w ≠ 0
      obtain ⟨w, hw⟩ := exists_mulVec_ne_zero' hr'_mat_ne
      -- v = r'(M)w is the strongly cyclic vector
      refine ⟨(aeval M r').mulVec w, hw, ?_, ?_⟩
      · -- q(M)v = q(M)r'(M)w = (q*r')(M)w = minpoly(M)w = 0
        rw [Matrix.mulVec_mulVec, ← map_mul, ← hr'_eq]
        simp [minpoly.aeval]
      · -- Strong cyclicity: r(M)v = 0 → q ∣ r
        intro r hrv
        -- q(M)v = 0 (proved above) and r(M)v = 0, v ≠ 0, q irred → q ∣ r
        exact irreducible_dvd_of_annihilated hq_irr hw
          (by rw [Matrix.mulVec_mulVec, ← map_mul, ← hr'_eq]; simp [minpoly.aeval])
          hrv
    · -- ══════════════════════════════════════════
      -- REDUCIBLE INDUCTIVE CASE
      -- ══════════════════════════════════════════
      -- Get irreducible factor s ∣ q
      obtain ⟨s, hs_irr, hs_dvd_q⟩ := WfDvdMonoid.exists_irreducible_factor hq_nu hq_ne
      obtain ⟨t, ht_eq⟩ := hs_dvd_q  -- q = s * t
      have hs_ne : s ≠ 0 := hs_irr.ne_zero
      have hs_nu : ¬IsUnit s := hs_irr.not_isUnit
      -- t ≠ 0
      have ht_ne : t ≠ 0 := right_ne_zero_of_mul (by rw [← ht_eq]; exact hq_ne)
      -- t is not a unit (otherwise q ∼ s would be irreducible, contradicting ¬Irreducible q)
      have ht_nu : ¬IsUnit t := by
        intro hu
        apply hq_irr; rw [ht_eq]
        -- q = s * t with t a unit → Associated s (s * t) → Irreducible (s * t)
        exact (Associated.irreducible_iff ⟨hu.choose, by rw [hu.choose_spec]⟩).mp hs_irr
      -- s.natDegree > 0 (s is not a unit and s ≠ 0)
      have hs_pos : 0 < s.natDegree := natDegree_pos_of_ne_zero_not_isUnit hs_ne hs_nu
      -- t.natDegree > 0 (t is not a unit and t ≠ 0)
      have ht_pos : 0 < t.natDegree := natDegree_pos_of_ne_zero_not_isUnit ht_ne ht_nu
      -- Degree equation: natDegree q = natDegree s + natDegree t
      have hdeg : q.natDegree = s.natDegree + t.natDegree := by
        rw [ht_eq, Polynomial.natDegree_mul hs_ne ht_ne]
      -- s.natDegree < q.natDegree and t.natDegree < q.natDegree
      have hs_lt : s.natDegree < q.natDegree := by omega
      have ht_lt : t.natDegree < q.natDegree := by omega
      -- Degrees ≤ d (for IH application)
      have hs_le_d : s.natDegree ≤ d := Nat.lt_succ_iff.mp (lt_of_lt_of_le hs_lt hle)
      have ht_le_d : t.natDegree ≤ d := Nat.lt_succ_iff.mp (lt_of_lt_of_le ht_lt hle)
      -- ¬(s ∣ t): if s ∣ t then s^2 ∣ q, contradicting Squarefree q
      have hs_ndvd_t : ¬s ∣ t := by
        intro ⟨u, hu⟩
        exact hs_nu (hq_sf s ⟨u, by rw [ht_eq, hu]; ring⟩)
      -- IsCoprime s t (s is prime in K[X] = UFD, and s ∤ t)
      have hcop : IsCoprime s t :=
        (UniqueFactorizationMonoid.irreducible_iff_prime.mp hs_irr).coprime_iff_not_dvd.mpr hs_ndvd_t
      obtain ⟨a, b, hab⟩ := hcop
      -- Squarefree s (from Squarefree (s*t))
      have hs_sf : Squarefree s := fun u ⟨c, huc⟩ =>
        hq_sf u ⟨c * t, by rw [ht_eq, huc]; ring⟩
      -- Squarefree t
      have ht_sf : Squarefree t := fun u ⟨c, huc⟩ =>
        hq_sf u ⟨s * c, by rw [ht_eq, huc]; ring⟩
      -- s ∣ minpoly K M
      have hs_dvd_q' : s ∣ q := ⟨t, ht_eq⟩
      have hs_dvd_min : s ∣ minpoly K M := hs_dvd_q'.trans hq_dvd
      -- t ∣ minpoly K M
      have ht_dvd_q : t ∣ q := ⟨s, by rw [ht_eq, mul_comm]⟩
      have ht_dvd_min : t ∣ minpoly K M := ht_dvd_q.trans hq_dvd
      -- IH: get vs (s-strongly cyclic in ker(s(M)))
      obtain ⟨vs, hvs_ne, hsvs, hvs_strong⟩ := ih s hs_le_d hs_pos hs_sf hs_dvd_min
      -- IH: get vt (t-strongly cyclic in ker(t(M)))
      obtain ⟨vt, hvt_ne, htvt, hvt_strong⟩ := ih t ht_le_d ht_pos ht_sf ht_dvd_min
      -- v = vs + vt is the strongly q-cyclic vector
      refine ⟨vs + vt, ?_, ?_, ?_⟩
      · -- v ≠ 0: if vs + vt = 0 then vs = -vt, so s(M)vt = 0.
        --   Then Bezout: (aeval M b * aeval M t).mulVec vt = vt and = 0. Contradiction.
        intro hv_zero
        -- s(M)vt = 0: from vs = -vt and s(M)vs = 0
        have hsvt : (aeval M s).mulVec vt = 0 := by
          have heq : vs = -vt := by
            have := add_eq_zero_iff_eq_neg.mp hv_zero; exact this
          have : (aeval M s).mulVec vs = 0 := hsvs
          rw [heq] at this
          simp only [Matrix.mulVec_neg, neg_eq_zero] at this
          exact this
        -- Bezout: b(M)t(M) is identity on ker(s(M)) and zero on ker(t(M))
        have hbez : (aeval M b * aeval M t).mulVec vt = vt :=
          bezout_proj_identity hab hsvt
        have hkill : (aeval M b * aeval M t).mulVec vt = 0 :=
          bezout_proj_kills htvt
        exact hvt_ne (by rw [← hbez, hkill])
      · -- q(M)v = (s*t)(M)(vs+vt) = 0
        have hqs_vs : (aeval M s * aeval M t).mulVec vs = 0 := by
          rw [aeval_mul_comm_poly, ← Matrix.mulVec_mulVec, hsvs, Matrix.mulVec_zero]
        have hqt_vt : (aeval M s * aeval M t).mulVec vt = 0 := by
          rw [← Matrix.mulVec_mulVec, htvt, Matrix.mulVec_zero]
        simp only [ht_eq, map_mul, Matrix.mulVec_add, hqs_vs, hqt_vt, add_zero]
      · -- Strong q-cyclicity: r(M)v = 0 → q = s*t ∣ r
        intro r hrv
        -- Show s ∣ r via Bezout projection e₁ = b(M)t(M)
        have hs_r : s ∣ r := hvs_strong r (by
          have h_app : (aeval M b * aeval M t).mulVec
              ((aeval M r).mulVec (vs + vt)) = 0 := by
            rw [hrv, Matrix.mulVec_zero]
          have h_comm : aeval M b * aeval M t * aeval M r =
              aeval M r * (aeval M b * aeval M t) := by
            rw [show aeval M b * aeval M t = aeval M (b * t) from (map_mul _ _ _).symm,
                aeval_mul_comm_poly (b * t) r, ← map_mul]
          rw [Matrix.mulVec_mulVec, h_comm, ← Matrix.mulVec_mulVec,
              Matrix.mulVec_add,
              bezout_proj_identity hab hsvs,
              bezout_proj_kills htvt, add_zero] at h_app
          exact h_app)
        -- Show t ∣ r via Bezout projection e₂ = a(M)s(M)
        have ht_r : t ∣ r := hvt_strong r (by
          have h_app : (aeval M a * aeval M s).mulVec
              ((aeval M r).mulVec (vs + vt)) = 0 := by
            rw [hrv, Matrix.mulVec_zero]
          have h_comm : aeval M a * aeval M s * aeval M r =
              aeval M r * (aeval M a * aeval M s) := by
            rw [show aeval M a * aeval M s = aeval M (a * s) from (map_mul _ _ _).symm,
                aeval_mul_comm_poly (a * s) r, ← map_mul]
          -- e₂ kills vs: a(M)s(M)vs = a(M)*0 = 0
          have he2_vs : (aeval M a * aeval M s).mulVec vs = 0 := by
            rw [← Matrix.mulVec_mulVec, hsvs, Matrix.mulVec_zero]
          -- e₂ is identity on vt: a*s + b*t = 1, t(M)vt = 0 → a(M)s(M)vt = vt
          have he2_vt : (aeval M a * aeval M s).mulVec vt = vt :=
            bezout_proj_identity (show b * t + a * s = 1 from by rw [add_comm]; exact hab) htvt
          rw [Matrix.mulVec_mulVec, h_comm, ← Matrix.mulVec_mulVec,
              Matrix.mulVec_add, he2_vs, he2_vt, zero_add] at h_app
          exact h_app)
        -- s*t ∣ r from IsCoprime s t
        rw [ht_eq]; exact IsCoprime.mul_dvd ⟨a, b, hab⟩ hs_r ht_r

/-- **Main Theorem (General Squarefree Case)**:
    Over ANY field K, nonderogatory matrices with squarefree characteristic
    polynomial have cyclic vectors.

    - Covers all fields, including finite fields with |K| ≤ n.
    - Axiom-free proof: no PID structure theorem needed.
    - Proved via `exists_strongly_cyclic`: the full minpoly has a strongly cyclic vector v.
      Strong cyclicity (r(M)v = 0 → minpoly | r) implies cyclicity (deg(r) < n → r = 0).

    What's still open: The non-squarefree case (e.g., Jordan blocks with
    minpoly = p^e, e ≥ 2) still requires the PID structure theorem. -/
theorem nonderogatory_squarefree_has_cyclic_vector
    (M : Matrix (Fin n) (Fin n) K)
    (h_nd : IsNonderogatory M)
    (h_sf : Squarefree (minpoly K M)) :
    ∃ v, IsCyclicVector M v := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨Fin.elim0, fun r hr _ => by omega⟩
  -- minpoly degree = n
  have h_deg : (minpoly K M).natDegree = n := by
    rw [h_nd, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  -- Get a strongly cyclic vector for the full minpoly M
  obtain ⟨v, hv_ne, -, hv_strong⟩ :=
    exists_strongly_cyclic M h_nd (minpoly K M).natDegree (minpoly K M) le_rfl (by omega) h_sf (dvd_refl _)
  -- v is a cyclic vector: r(M)v = 0 and deg(r) < n → r = 0
  refine ⟨v, fun r hr hann => ?_⟩
  -- Strong cyclicity gives: minpoly M ∣ r
  have hmin_r : minpoly K M ∣ r := hv_strong r hann
  -- If r ≠ 0, then deg(minpoly) ≤ deg(r) < n = deg(minpoly). Contradiction.
  by_contra hr_ne
  have h_le : n ≤ r.natDegree := by
    rw [← h_deg]; exact Polynomial.natDegree_le_of_dvd hmin_r hr_ne
  omega

/-- Corollary: Works over all finite fields of any size. -/
theorem nonderogatory_squarefree_has_cyclic_vector_finite [Fintype K]
    (M : Matrix (Fin n) (Fin n) K)
    (h_nd : IsNonderogatory M)
    (h_sf : Squarefree (minpoly K M)) :
    ∃ v, IsCyclicVector M v :=
  nonderogatory_squarefree_has_cyclic_vector M h_nd h_sf

-- ============================================================
-- SECTION V: Summary and Next Steps
-- ============================================================

/-
## Mathematical Summary

This file proves the cyclic vector theorem for nonderogatory matrices with
squarefree characteristic polynomial.

### Proof Technique (CRT Projections)

**Bezout Projections**: For p, q coprime with a·p + b·q = 1:
- e₁ = b(M)·q(M): identity on ker(p(M)), kills ker(q(M))
- e₂ = a(M)·p(M): identity on ker(q(M)), kills ker(p(M))
These project onto primary components WITHOUT needing module structure theory.

**Key Lemma** (`irreducible_dvd_of_annihilated`):
If p irreducible and both p(M), r(M) kill v ≠ 0, then p | r.
Proof: If p ∤ r, Bezout gives a·p + b·r = 1, so v = a(M)·0 + b(M)·0 = 0. ∎

**Cyclic vector**: v = v₁ + v₂ where vᵢ ∈ ker(pᵢ(M)).
If r(M)v = 0: apply eᵢ → r(M)vᵢ = 0 → pᵢ | r. Then p·q | r, deg contradiction.

### Remaining Gap

The non-squarefree case requires:
- Primary component structure for minpoly = p^e (e ≥ 2)
- This is the PID structure theorem for K[X]-modules
- Not currently in Mathlib 4.26

For the full generality (which WIP01's axiom covers), the PID theorem is needed.
This file reduces the remaining gap to: "minpoly M = p^e with e ≥ 2."
-/

end SquarefreeCyclicVector

end
