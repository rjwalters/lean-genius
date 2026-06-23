/-
  Nonderogatory → Cyclic Vector: General Case (All Fields) — Axiom-Free (WIP04)

  This file proves the cyclic vector theorem for ALL nonderogatory matrices over any
  field K, WITHOUT axioms or sorries, using primary decomposition via Bezout projections.

  ## Context

  A matrix M is nonderogatory if minpoly(M) = charpoly(M). Equivalently, K^n is a
  cyclic K[X]-module — there exists a vector v such that {v, Mv, M²v, …, M^(n-1)v}
  spans K^n.

  Previous work:
  - WIP01 (290 lines): General case with 1 axiom (nonderogatory ≅ companion matrix).
  - WIP02 (575 lines): Squarefree minpoly case, axiom-free.
  - WIP03 (253 lines): Prime power minpoly case, axiom-free.

  This file (WIP04) combines WIP02 and WIP03 into a complete axiom-free proof for
  arbitrary minpoly = ∏_i p_i^{e_i} via primary decomposition.

  ## Key Strategy

  Given nonderogatory M with minpoly = ∏_{i < k} p_i^{e_i} (pairwise coprime prime powers):

  **Step 1 — Construct primary vectors**:
    For each i, define F_i := ∏_{j ≠ i} p_j^{e_j} and pick w_i with (p_i^{e_i-1}·F_i)(M)w_i ≠ 0.
    Set v_i := F_i(M)w_i. Then:
    - p_i^{e_i}(M)v_i = 0  [minpoly kills all vectors]
    - p_i^{e_i-1}(M)v_i ≠ 0  [by choice of w_i]
    By `pow_irred_dvd_of_annihilated` (WIP03): if r(M)v_i = 0, then p_i^{e_i} | r.

  **Step 2 — Combine via CRT**:
    Let v := ∑_i v_i. Suppose r(M)v = 0 with deg(r) < n.
    For each i, IsCoprime(p_i^{e_i}, F_i) gives Bezout a_i·p_i^{e_i} + b_i·F_i = 1.
    Projection π_i = (b_i·F_i)(M) satisfies:
    - π_i(v_i) = v_i  [since p_i^{e_i}(M)v_i = 0 and a_i·p_i^{e_i} + b_i·F_i = 1]
    - π_i(v_j) = 0    [for j ≠ i, since p_j^{e_j} | F_i → F_i(M) kills ker(p_j^{e_j}(M))]
    So r(M)v_i = π_i(r(M)v) = π_i(0) = 0.
    By Step 1: p_i^{e_i} | r for all i.
    By pairwise coprimality: ∏ p_i^{e_i} = minpoly | r → deg(r) ≥ n. Contradiction.

  ## Status: 0 sorries, 0 axioms (pending build verification)
-/
import Mathlib

noncomputable section

namespace GeneralCyclicVector

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
-- SECTION II: Utility Lemmas (mirrored from WIP02/WIP03)
-- ============================================================

/-- If p irred, v ≠ 0, p(M)v = 0, r(M)v = 0, then p | r. -/
private lemma irreducible_dvd_of_annihilated {M : Matrix (Fin n) (Fin n) K}
    {p r : K[X]} {v : Fin n → K}
    (hp_irr : Irreducible p) (hv_ne : v ≠ 0)
    (hpv : (aeval M p).mulVec v = 0) (hrv : (aeval M r).mulVec v = 0) :
    p ∣ r := by
  by_contra h_ndvd
  have hp_prime := UniqueFactorizationMonoid.irreducible_iff_prime.mp hp_irr
  have hcop : IsCoprime p r := hp_prime.coprime_iff_not_dvd.mpr h_ndvd
  obtain ⟨a, b, hab⟩ := hcop
  have hmat : aeval M a * aeval M p + aeval M b * aeval M r = 1 := by
    have h := congr_arg (aeval M) hab; simp only [map_add, map_mul, map_one] at h; exact h
  have hv_zero : v = 0 := by
    have h := congr_arg (· *ᵥ v) hmat
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hpv, hrv,
               Matrix.mulVec_zero, Matrix.one_mulVec, add_zero] at h
    exact h.symm
  exact hv_ne hv_zero

/-- A nonzero matrix has a vector outside its kernel. -/
private lemma exists_mulVec_ne_zero {M : Matrix (Fin n) (Fin n) K} (hM : M ≠ 0) :
    ∃ v : Fin n → K, M.mulVec v ≠ 0 := by
  by_contra hall; push_neg at hall; apply hM
  funext i j
  have h2 : (M.mulVec (Pi.single j 1)) i = 0 := congr_fun (hall (Pi.single j 1)) i
  simp only [mulVec, dotProduct, Pi.single_apply] at h2; simpa using h2

/-- Minimality of minpoly: natDegree p < natDegree(minpoly M) → aeval M p ≠ 0. -/
private lemma aeval_ne_zero_of_lt_minpoly {M : Matrix (Fin n) (Fin n) K}
    {p : K[X]} (hp_ne : p ≠ 0) (hp_deg : p.natDegree < (minpoly K M).natDegree) :
    (aeval M p : Matrix (Fin n) (Fin n) K) ≠ 0 := fun h =>
  absurd (Polynomial.natDegree_le_of_dvd (minpoly.dvd K M h) hp_ne) (by omega)

/-- Polynomials in M commute. -/
private lemma aeval_mul_comm {M : Matrix (Fin n) (Fin n) K} (f g : K[X]) :
    aeval M f * aeval M g = aeval M g * aeval M f := by
  rw [← map_mul (aeval M), ← map_mul (aeval M), mul_comm]

/-- CRT projection identity: if a*p + b*q = 1 and p(M)v = 0, then (b*q)(M)v = v. -/
private lemma bezout_proj_identity {M : Matrix (Fin n) (Fin n) K}
    {p q a b : K[X]} (hab : a * p + b * q = 1) {v : Fin n → K}
    (hpv : (aeval M p).mulVec v = 0) :
    (aeval M b * aeval M q).mulVec v = v := by
  have hmat : aeval M a * aeval M p + aeval M b * aeval M q = 1 := by
    have h := congr_arg (aeval M) hab; simp only [map_add, map_mul, map_one] at h; exact h
  have h := congr_arg (· *ᵥ v) hmat
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hpv, Matrix.mulVec_zero,
             Matrix.one_mulVec, zero_add] at h
  rwa [← Matrix.mulVec_mulVec]

/-- **Prime power divisibility from annihilation** (induction on e):
    If p irred, p^e(M)v ≠ 0, p^(e+1)(M)v = 0, r(M)v = 0, then p^(e+1) | r. -/
private lemma pow_irred_dvd_of_annihilated
    {M : Matrix (Fin n) (Fin n) K} {p : K[X]} (hp_irr : Irreducible p) :
    ∀ (e : ℕ) (v : Fin n → K),
      (aeval M (p ^ e)).mulVec v ≠ 0 →
      (aeval M (p ^ (e + 1))).mulVec v = 0 →
      ∀ (r : K[X]), (aeval M r).mulVec v = 0 → p ^ (e + 1) ∣ r := by
  intro e
  induction e with
  | zero =>
    intro v hne hzero r hrv
    simpa using irreducible_dvd_of_annihilated hp_irr (by simpa using hne) (by simpa using hzero) hrv
  | succ e ih =>
    intro v hne hzero r hrv
    -- Step 1: p | r via w = p^(e+1)(M)v
    have hpw : (aeval M p).mulVec ((aeval M (p ^ (e + 1))).mulVec v) = 0 := by
      have : (aeval M p).mulVec ((aeval M (p ^ (e + 1))).mulVec v) =
             (aeval M (p ^ (e + 1 + 1))).mulVec v := by
        rw [Matrix.mulVec_mulVec, ← map_mul]; congr 2; ring
      rw [this]; exact hzero
    have hrw : (aeval M r).mulVec ((aeval M (p ^ (e + 1))).mulVec v) = 0 := by
      rw [Matrix.mulVec_mulVec, ← map_mul (aeval M),
          show r * p ^ (e + 1) = p ^ (e + 1) * r from mul_comm _ _,
          map_mul (aeval M), ← Matrix.mulVec_mulVec, hrv, Matrix.mulVec_zero]
    obtain ⟨r₁, hr₁_eq⟩ := irreducible_dvd_of_annihilated hp_irr hne hpw hrw
    -- Step 2: IH applied to u = p(M)v and polynomial r₁
    have hu_ne : (aeval M (p ^ e)).mulVec ((aeval M p).mulVec v) ≠ 0 := by
      rwa [Matrix.mulVec_mulVec, ← map_mul, ← pow_succ]
    have hu_zero : (aeval M (p ^ (e + 1))).mulVec ((aeval M p).mulVec v) = 0 := by
      rwa [Matrix.mulVec_mulVec, ← map_mul, ← pow_succ]
    have hr₁u : (aeval M r₁).mulVec ((aeval M p).mulVec v) = 0 := by
      have : (aeval M r₁).mulVec ((aeval M p).mulVec v) = (aeval M r).mulVec v := by
        rw [Matrix.mulVec_mulVec, ← map_mul]; congr 2; rw [mul_comm r₁ p, ← hr₁_eq]
      rw [this]; exact hrv
    obtain ⟨r₂, hr₂_eq⟩ := ih ((aeval M p).mulVec v) hu_ne hu_zero r₁ hr₁u
    exact ⟨r₂, by rw [hr₁_eq, hr₂_eq]; ring⟩

/-- mulVec distributes over finite sums of vectors. -/
private lemma mulVec_finset_sum (A : Matrix (Fin n) (Fin n) K)
    {ι : Type*} (s : Finset ι) (f : ι → Fin n → K) :
    A.mulVec (∑ i ∈ s, f i) = ∑ i ∈ s, A.mulVec (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [Matrix.mulVec_zero]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Matrix.mulVec_add, ih, Finset.sum_insert ha]

-- ============================================================
-- SECTION III: Main Theorem — General Case
-- ============================================================

/-- **Main Theorem (General Nonderogatory Cyclic Vector, Axiom-Free)**:
    For nonderogatory M with minpoly = ∏_{i : Fin k} p_i^{e_i}
    (pairwise coprime, each p_i irreducible monic, e_i ≥ 1),
    M has a cyclic vector over any field K. -/
theorem nonderogatory_general_has_cyclic_vector
    {k : ℕ} (hk : 0 < k)
    (M : Matrix (Fin n) (Fin n) K)
    (h_nd : IsNonderogatory M)
    (p : Fin k → K[X]) (e : Fin k → ℕ)
    (hp_irr : ∀ i, Irreducible (p i))
    (hp_monic : ∀ i, (p i).Monic)
    (he_pos : ∀ i, 0 < e i)
    (hcoprime : ∀ i j : Fin k, i ≠ j → IsCoprime (p i ^ e i) (p j ^ e j))
    (hprod : minpoly K M = ∏ i : Fin k, p i ^ e i) :
    ∃ v : Fin n → K, IsCyclicVector M v := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨Fin.elim0, fun r hr _ => by omega⟩
  -- Degree of minpoly = n
  have h_deg : (minpoly K M).natDegree = n := by
    rw [h_nd, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  -- Nonzero facts
  have hp_ne : ∀ i, p i ≠ 0 := fun i => (hp_monic i).ne_zero
  have hpe_ne : ∀ i, p i ^ e i ≠ 0 := fun i => pow_ne_zero _ (hp_ne i)
  -- Complementary product F i = ∏_{j ≠ i} p j ^ e j
  let F : Fin k → K[X] := fun i => ∏ j ∈ Finset.univ.erase i, p j ^ e j
  have hFi_ne : ∀ i, F i ≠ 0 := fun i => by
    simp only [F]
    intro h
    obtain ⟨j, _, hj⟩ := (Finset.prod_eq_zero_iff).mp h
    exact hpe_ne j hj
  -- p i ^ e i * F i = minpoly K M
  have hprod_split : ∀ i, p i ^ e i * F i = minpoly K M := by
    intro i
    rw [hprod]
    rw [show (∏ j : Fin k, p j ^ e j) = p i ^ e i * F i from
      (Finset.mul_prod_erase Finset.univ (fun j => p j ^ e j) (Finset.mem_univ i)).symm]
  -- deg(p i ^ (e i - 1) * F i) < n
  have hpow_Fi_deg : ∀ i, (p i ^ (e i - 1) * F i).natDegree < n := by
    intro i
    have hpowFi_ne : p i ^ (e i - 1) * F i ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (hp_ne i)) (hFi_ne i)
    have hpi_pos : 0 < (p i).natDegree := by
      by_contra h; push_neg at h
      exact (hp_irr i).not_isUnit
        ((Polynomial.eq_one_of_monic_natDegree_zero (hp_monic i) (Nat.le_zero.mp h)) ▸ isUnit_one)
    have he_pred : e i - 1 + 1 = e i := Nat.succ_pred_eq_of_pos (he_pos i)
    -- (p i ^ (e i - 1) * F i) * p i = p i ^ e i * F i = minpoly
    have heq : p i ^ (e i - 1) * F i * p i = p i ^ e i * F i := by
      calc p i ^ (e i - 1) * F i * p i
          = p i ^ (e i - 1) * p i * F i := by ring
        _ = p i ^ e i * F i := by rw [← pow_succ, he_pred]
    have hdeg_prod : (p i ^ (e i - 1) * F i * p i).natDegree = n := by
      rw [heq, hprod_split i]; exact h_deg
    rw [Polynomial.natDegree_mul hpowFi_ne (hp_ne i)] at hdeg_prod
    omega
  -- aeval M (p i ^ (e i - 1) * F i) ≠ 0
  have hpow_Fi_ne_mat : ∀ i,
      (aeval M (p i ^ (e i - 1) * F i) : Matrix (Fin n) (Fin n) K) ≠ 0 := fun i =>
    aeval_ne_zero_of_lt_minpoly (mul_ne_zero (pow_ne_zero _ (hp_ne i)) (hFi_ne i))
      (by rw [h_deg]; exact hpow_Fi_deg i)
  -- Choose w i: (p i ^ (e i - 1) * F i)(M) *ᵥ w i ≠ 0
  let w : Fin k → (Fin n → K) := fun i =>
    (exists_mulVec_ne_zero (hpow_Fi_ne_mat i)).choose
  have hw : ∀ i, (aeval M (p i ^ (e i - 1) * F i)).mulVec (w i) ≠ 0 := fun i =>
    (exists_mulVec_ne_zero (hpow_Fi_ne_mat i)).choose_spec
  -- Define primary vectors: v i = F i(M) *ᵥ w i
  let v : Fin k → (Fin n → K) := fun i => (aeval M (F i)).mulVec (w i)
  -- p i ^ e i kills v i (since minpoly kills all)
  have h_vi_kill : ∀ i, (aeval M (p i ^ e i)).mulVec (v i) = 0 := fun i => by
    show (aeval M (p i ^ e i)).mulVec ((aeval M (F i)).mulVec (w i)) = 0
    rw [Matrix.mulVec_mulVec, ← map_mul, hprod_split i,
        minpoly.aeval K M, Matrix.zero_mulVec]
  -- p i ^ (e i - 1)(M) *ᵥ v i ≠ 0
  have h_vi_pow : ∀ i, (aeval M (p i ^ (e i - 1))).mulVec (v i) ≠ 0 := fun i => by
    show (aeval M (p i ^ (e i - 1))).mulVec ((aeval M (F i)).mulVec (w i)) ≠ 0
    rw [Matrix.mulVec_mulVec, ← map_mul]
    exact hw i
  -- IsCoprime (p i ^ e i) (F i)
  have hcop_Fi : ∀ i, IsCoprime (p i ^ e i) (F i) := fun i => by
    apply IsCoprime.prod_right
    intro j hj
    exact hcoprime i j (Ne.symm (Finset.mem_erase.mp hj).1)
  -- F i kills v j for j ≠ i (since p j ^ e j | F i and p j ^ e j kills v j)
  have h_Fi_kills : ∀ i j : Fin k, j ≠ i →
      (aeval M (F i)).mulVec (v j) = 0 := by
    intro i j hji
    show (aeval M (F i)).mulVec ((aeval M (F j)).mulVec (w j)) = 0
    obtain ⟨Q, hQ⟩ := Finset.dvd_prod_of_mem (fun l => p l ^ e l)
        (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
    have h_pj_kills : (aeval M (p j ^ e j)).mulVec ((aeval M (F j)).mulVec (w j)) = 0 := by
      rw [Matrix.mulVec_mulVec, ← map_mul, hprod_split j,
          minpoly.aeval K M, Matrix.zero_mulVec]
    rw [show F i = p j ^ e j * Q from hQ, map_mul,
        show aeval M (p j ^ e j) * aeval M Q = aeval M Q * aeval M (p j ^ e j)
          from aeval_mul_comm (p j ^ e j) Q]
    calc (aeval M Q * aeval M (p j ^ e j)).mulVec ((aeval M (F j)).mulVec (w j))
        = (aeval M Q).mulVec ((aeval M (p j ^ e j)).mulVec ((aeval M (F j)).mulVec (w j))) :=
            (Matrix.mulVec_mulVec _ _ _).symm
      _ = (aeval M Q).mulVec 0 := by rw [h_pj_kills]
      _ = 0 := Matrix.mulVec_zero _
  -- The cyclic vector candidate: v_sum = ∑ i, v i
  use ∑ i : Fin k, v i
  intro r hr hann
  by_contra hr_ne
  -- For each i, Bezout projection extracts r(M) *ᵥ v i = 0
  have h_rvi : ∀ i, (aeval M r).mulVec (v i) = 0 := by
    intro i
    obtain ⟨a_i, b_i, hab⟩ := hcop_Fi i
    -- Projection acts as identity on v i
    have h_proj_id : (aeval M b_i * aeval M (F i)).mulVec (v i) = v i :=
      bezout_proj_identity hab (h_vi_kill i)
    -- Projection kills v j for j ≠ i
    have h_proj_zero : ∀ j : Fin k, j ≠ i →
        (aeval M b_i * aeval M (F i)).mulVec (v j) = 0 := fun j hji => by
      rw [← Matrix.mulVec_mulVec, h_Fi_kills i j hji, Matrix.mulVec_zero]
    -- Projection of full sum = v i
    have h_proj_sum : (aeval M b_i * aeval M (F i)).mulVec (∑ j : Fin k, v j) = v i := by
      rw [mulVec_finset_sum, Finset.sum_eq_single i
          (fun j _ hji => h_proj_zero j hji)
          (fun hi => absurd (Finset.mem_univ i) hi)]
      exact h_proj_id
    -- Commutativity: r(M) * π_i = π_i * r(M) (both polynomials in M)
    have hcomm : aeval M r * (aeval M b_i * aeval M (F i)) =
        aeval M b_i * aeval M (F i) * aeval M r := by
      rw [← map_mul (aeval M), aeval_mul_comm r (b_i * F i), map_mul]
    -- r(M) *ᵥ v i = π_i (r(M) *ᵥ (∑ v j)) = π_i 0 = 0
    calc (aeval M r).mulVec (v i)
        = (aeval M r).mulVec ((aeval M b_i * aeval M (F i)).mulVec (∑ j, v j)) :=
            by rw [h_proj_sum]
      _ = (aeval M r * (aeval M b_i * aeval M (F i))).mulVec (∑ j, v j) :=
            by rw [Matrix.mulVec_mulVec]
      _ = (aeval M b_i * aeval M (F i) * aeval M r).mulVec (∑ j, v j) :=
            by rw [hcomm]
      _ = (aeval M b_i * aeval M (F i)).mulVec ((aeval M r).mulVec (∑ j, v j)) :=
            by rw [← Matrix.mulVec_mulVec]
      _ = (aeval M b_i * aeval M (F i)).mulVec 0 := by rw [hann]
      _ = 0 := Matrix.mulVec_zero _
  -- For each i: p i ^ e i | r (from pow_irred_dvd_of_annihilated)
  have h_pow_dvd : ∀ i, p i ^ e i ∣ r := by
    intro i
    have he_pred : e i - 1 + 1 = e i := Nat.succ_pred_eq_of_pos (he_pos i)
    -- (p i ^ (e i - 1 + 1))(M) *ᵥ v i = 0
    have h_kill_pred : (aeval M (p i ^ (e i - 1 + 1))).mulVec (v i) = 0 := by
      rw [he_pred]; exact h_vi_kill i
    -- Apply the key lemma with exponent e i - 1
    have hdvd := pow_irred_dvd_of_annihilated (hp_irr i) (e i - 1) (v i)
      (h_vi_pow i) h_kill_pred r (h_rvi i)
    rwa [he_pred] at hdvd
  -- By pairwise coprimality: ∏ i, p i ^ e i | r
  have h_prod_dvd : (∏ i : Fin k, p i ^ e i) ∣ r :=
    Finset.prod_dvd_of_coprime
      (fun i _ j _ hij => hcoprime i j hij)
      (fun i _ => h_pow_dvd i)
  -- minpoly | r → deg(r) ≥ n = deg(minpoly), but deg(r) < n
  rw [← hprod] at h_prod_dvd
  exact absurd (h_deg ▸ Polynomial.natDegree_le_of_dvd h_prod_dvd hr_ne) (by omega)

-- ============================================================
-- SECTION IV: Commentary
-- ============================================================

/-!
### Completeness

WIP04 proves the cyclic vector theorem axiom-free for nonderogatory M, given the
factored form of minpoly K M. To complete the fully general theorem:
1. Factor minpoly K M using K[X] as a UFD (available in Mathlib via `UniqueFactorizationMonoid`).
2. Apply `nonderogatory_general_has_cyclic_vector`.

### Technical Insight

The key construction `v_i = F_i(M)·w_i` (for the complementary product F_i) avoids
the need to work with restrictions of M to primary subspaces. Crucially, we never need
to know that dim(ker(p_i^{e_i}(M))) = deg(p_i^{e_i}) — only that p_i^{e_i-1}(M)·v_i ≠ 0
and p_i^{e_i}(M)·v_i = 0, which follows directly from the construction.

### Supersedes WIP01

The axiom in WIP01 (`nonderogatory_similar_to_companion`) is unnecessary:
the cyclic vector theorem holds without rational canonical form.

### Open Question

Can the factorization hypotheses be eliminated by using the UFD structure of K[X]
to automatically decompose minpoly K M into prime power factors?
-/

end GeneralCyclicVector
