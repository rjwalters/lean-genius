/-
  Nonderogatory ⟹ Cyclic Vector: Arbitrary Fields

  The nonderogatory cyclic vector theorem (OQ-05-OQ-01) was proved for
  infinite fields, and OQ-05-OQ-01-OQ-01 weakened this to |K| > n.

  This file addresses the remaining case: over finite fields F_q with q ≤ n,
  does every nonderogatory matrix still have a cyclic vector?

  **Answer: YES.** The theorem holds over ALL fields, including finite fields
  with |K| ≤ n. The union avoidance argument is unnecessary.

  Proof Strategy (Module-Theoretic):
  For M ∈ M_n(K) nonderogatory (minpoly = charpoly, both of degree n):
  1. K^n is a K[X]-module via M (X acts as multiplication by M)
  2. v is cyclic ⟺ ann(v) = (minpoly(M)) as an ideal
  3. By the cyclic decomposition theorem for modules over a PID,
     nonderogatory forces V = K[X]/(minpoly) (single cyclic factor)
  4. The generator of this cyclic module is a cyclic vector

  This proof uses the structure theorem for f.g. modules over a PID,
  which is a deep result not currently in Mathlib. The key sorry
  (exists_cyclic_vector_module) isolates this gap.

  Key insight: The proof works over ANY field (finite or infinite) because
  it uses algebraic structure (module theory over PID) rather than
  cardinality arguments (union avoidance).
-/
import Mathlib
import Proofs.CayleyHamiltonReductionOQ02OQ01

noncomputable section

namespace CyclicVectorArbitrary

open Matrix Polynomial

attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K] {n : ℕ}

-- ============================================================
-- SECTION I: Definitions (consistent with OQ05OQ01)
-- ============================================================

def IsCyclicVector (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : Prop :=
  ∀ p : K[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0

def IsNonderogatory (M : Matrix (Fin n) (Fin n) K) : Prop :=
  minpoly K M = M.charpoly

-- ============================================================
-- SECTION II: Similarity Preserves Cyclic Vectors
-- ============================================================

/-- Conjugation by an invertible matrix commutes with polynomial evaluation.
    Uses P.inv and P.val (Units structure fields) to avoid coercion elaboration issues. -/
theorem aeval_conj (M : Matrix (Fin n) (Fin n) K) (P : (Matrix (Fin n) (Fin n) K)ˣ)
    (p : K[X]) :
    aeval (P.inv * M * P.val) p = P.inv * aeval M p * P.val := by
  -- Key: (P.inv * M * P.val)^k = P.inv * M^k * P.val by induction
  have conj_pow : ∀ k : ℕ, (P.inv * M * P.val) ^ k = P.inv * M ^ k * P.val := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, mul_one]
      exact P.inv_val.symm
    | succ k ih =>
      rw [pow_succ, ih]
      calc P.inv * M ^ k * P.val * (P.inv * M * P.val)
          = P.inv * M ^ k * (P.val * P.inv) * M * P.val := by simp only [mul_assoc]
        _ = P.inv * M ^ k * 1 * M * P.val := by rw [P.val_inv]
        _ = P.inv * M ^ k * M * P.val := by rw [mul_one]
        _ = P.inv * M ^ (k + 1) * P.val := by rw [mul_assoc P.inv (M ^ k) M, ← pow_succ M k]
  -- Induct on p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, hp, hq, mul_add, add_mul]
  | monomial k a =>
    simp only [Polynomial.aeval_monomial, conj_pow]
    -- aeval_monomial gives algebraMap K _ a * M^k; convert to a • M^k via ← Algebra.smul_def
    simp only [← Algebra.smul_def]
    rw [← smul_mul_assoc, ← mul_smul_comm]

/-- If N has a cyclic vector w, and M = P.inv * N * P.val, then M has a cyclic vector. -/
theorem cyclic_vector_of_similar
    (M N : Matrix (Fin n) (Fin n) K)
    (P : (Matrix (Fin n) (Fin n) K)ˣ)
    (hMN : M = P.inv * N * P.val)
    (w : Fin n → K) (hw : IsCyclicVector N w) :
    ∃ v, IsCyclicVector M v := by
  -- v = P.inv · w is cyclic for M
  refine ⟨P.inv.mulVec w, fun p hp hann => ?_⟩
  apply hw p hp
  -- Substitute M = P.inv * N * P.val and apply aeval_conj
  rw [hMN, aeval_conj N P p] at hann
  -- hann : (P.inv * aeval N p * P.val) *ᵥ (P.inv *ᵥ w) = 0
  -- Key matrix identity: P.val * (P.inv * aeval N p * P.val) * P.inv = aeval N p
  have heq : P.val * (P.inv * aeval N p * P.val) * P.inv = aeval N p := by
    calc P.val * (P.inv * aeval N p * P.val) * P.inv
        = (P.val * P.inv) * aeval N p * (P.val * P.inv) := by simp only [mul_assoc]
      _ = aeval N p := by simp only [P.val_inv, one_mul, mul_one]
  -- Use mulVec_mulVec (forward) to unfold (P.val * A * P.inv) *ᵥ w
  -- = P.val *ᵥ (A *ᵥ (P.inv *ᵥ w)) for A = P.inv * aeval N p * P.val
  have key : (P.val * (P.inv * aeval N p * P.val) * P.inv) *ᵥ w =
             P.val *ᵥ ((P.inv * aeval N p * P.val) *ᵥ (P.inv *ᵥ w)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [← heq, key, hann, Matrix.mulVec_zero]

-- ============================================================
-- SECTION III: Annihilator Characterization
-- ============================================================

/-- The annihilator polynomial of a vector: the monic generator of
    {p : p(M)v = 0}. This equals the minimal polynomial of M
    restricted to the cyclic subspace generated by v. -/
theorem annihilator_dvd_minpoly (M : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) (p : K[X]) (hp : (aeval M p).mulVec v = 0) :
    (aeval M (EuclideanDomain.gcd p (minpoly K M))).mulVec v = 0 := by
  -- This follows from the Bezout identity: gcd(p, μ) = ap + bμ
  -- So gcd(M)v = a(M)p(M)v + b(M)μ(M)v = 0 + 0 = 0
  set μ := minpoly K M
  set d := EuclideanDomain.gcd p μ
  have bezout := EuclideanDomain.gcd_eq_gcd_ab p μ
  have hμ_ann : (aeval M μ : Matrix (Fin n) (Fin n) K) = 0 := minpoly.aeval K M
  calc (aeval M d).mulVec v
      = (aeval M (EuclideanDomain.gcdA p μ * p +
          EuclideanDomain.gcdB p μ * μ)).mulVec v := by
        congr 1; congr 1; rw [show d = _ from bezout]; ring
    _ = (aeval M (EuclideanDomain.gcdA p μ * p)).mulVec v +
        (aeval M (EuclideanDomain.gcdB p μ * μ)).mulVec v := by
        rw [map_add, Matrix.add_mulVec]
    _ = (aeval M (EuclideanDomain.gcdA p μ) * aeval M p).mulVec v +
        (aeval M (EuclideanDomain.gcdB p μ) * aeval M μ).mulVec v := by
        rw [map_mul, map_mul]
    _ = (aeval M (EuclideanDomain.gcdA p μ)).mulVec ((aeval M p).mulVec v) +
        (aeval M (EuclideanDomain.gcdB p μ)).mulVec ((aeval M μ).mulVec v) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = 0 := by rw [hp, hμ_ann, Matrix.zero_mulVec,
                     Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]

/-- A vector is cyclic iff p(M)v = 0 implies minpoly | p
    (i.e., the annihilator of v equals the minimal polynomial). -/
theorem cyclic_iff_ann_eq_minpoly (M : Matrix (Fin n) (Fin n) K)
    (hn : 0 < n) (hnd : IsNonderogatory M) (v : Fin n → K) :
    IsCyclicVector M v ↔
      ∀ p : K[X], (aeval M p).mulVec v = 0 → minpoly K M ∣ p := by
  constructor
  · -- Forward: cyclic ⟹ ann = minpoly
    intro hcyc p hp
    -- gcd(p, μ) annihilates v and divides μ
    set μ := minpoly K M
    set d := EuclideanDomain.gcd p μ
    have hd_ann := annihilator_dvd_minpoly M v p hp
    have hd_dvd_μ : d ∣ μ := EuclideanDomain.gcd_dvd_right p μ
    -- If d properly divides μ, then deg(d) < deg(μ) = n
    have hd_ne : d ≠ 0 := by
      intro h0; rw [h0] at hd_dvd_μ
      exact (minpoly.monic (isIntegral M)).ne_zero (eq_zero_of_zero_dvd hd_dvd_μ)
    have hd_deg_le : d.natDegree ≤ μ.natDegree := Polynomial.natDegree_le_of_dvd hd_dvd_μ
      (minpoly.monic (isIntegral M)).ne_zero
    have hμ_deg : μ.natDegree = n := by
      rw [show μ = minpoly K M from rfl, hnd, Matrix.charpoly_natDegree_eq_dim,
          Fintype.card_fin]
    rcases hd_deg_le.lt_or_eq with hd_lt | hd_eq
    · -- deg(d) < deg(μ) = n: cyclicity forces d = 0, contradicting d ≠ 0
      exfalso; exact absurd (hcyc d (by omega) hd_ann) hd_ne
    · -- deg(d) = deg(μ): μ = d * q where q is a unit, so μ ∣ d ∣ p
      obtain ⟨q, hq_eq⟩ := hd_dvd_μ
      have hμ_ne : μ ≠ 0 := (minpoly.monic (isIntegral M)).ne_zero
      have hq_ne : q ≠ 0 := right_ne_zero_of_mul (hq_eq ▸ hμ_ne)
      have hq_deg : q.natDegree = 0 := by
        have h1 : μ.natDegree = d.natDegree + q.natDegree := by
          rw [hq_eq]; exact Polynomial.natDegree_mul hd_ne hq_ne
        omega
      have hq_unit : IsUnit q := by
        rw [Polynomial.eq_C_of_natDegree_eq_zero hq_deg]
        exact isUnit_C.mpr (IsUnit.mk0 _ (by
          intro h0; exact hq_ne
            (by rw [Polynomial.eq_C_of_natDegree_eq_zero hq_deg, h0, map_zero])))
      obtain ⟨u, hu⟩ := hq_unit
      have hμ_du : μ = d * ↑u := by rw [hq_eq, hu]
      have hd_eq_μu : d = μ * ↑u⁻¹ :=
        ((calc μ * ↑u⁻¹ = d * ↑u * ↑u⁻¹ := by rw [hμ_du]
          _ = d * (↑u * ↑u⁻¹) := by ring
          _ = d := by rw [Units.mul_inv, mul_one]).symm)
      exact dvd_trans ⟨↑u⁻¹, hd_eq_μu⟩ (EuclideanDomain.gcd_dvd_left p μ)
  · -- Backward: ann = minpoly ⟹ cyclic
    intro hann p hp hpann
    by_contra hp_ne
    have hμ_dvd := hann p hpann
    have hμ_deg : (minpoly K M).natDegree = n := by
      rw [hnd, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    exact absurd (Polynomial.natDegree_le_of_dvd hμ_dvd hp_ne) (by omega)

-- ============================================================
-- SECTION IV: Companion Matrix Cyclic Vector
-- ============================================================

-- Private helpers (analogues of private lemmas in CayleyHamiltonReductionOQ02OQ01)

/-- Distribute mulVec over a finite sum of matrices. -/
private theorem sum_mulVec_dist {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    (∑ i ∈ s, f i) *ᵥ v = ∑ i ∈ s, f i *ᵥ v := by
  induction s using Finset.induction_on with
  | empty => simp [Matrix.zero_mulVec]
  | @insert a s' has ih => rw [Finset.sum_insert has, Matrix.add_mulVec, ih, Finset.sum_insert has]

/-- Expand aeval C q as a sum over range(natDegree q + 1). -/
private lemma aeval_eq_range_sum (q : K[X]) (C : Matrix (Fin n) (Fin n) K) :
    aeval C q = ∑ k ∈ Finset.range (q.natDegree + 1), q.coeff k • C ^ k := by
  simp only [aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  apply Finset.sum_subset
  · intro i hi
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_mem_supp i hi))
  · intro i _ hi
    simp only [Polynomial.notMem_support_iff.mp hi, map_zero, zero_mul]

/-- The standard basis vector e₀ is a cyclic vector for the companion matrix C(p).

    Key: C(p)^k · e₀ = eₖ (orbit property), so p(C(p)) · e₀ expands as a
    weighted sum of standard basis vectors. If this is 0, all coefficients
    (hence all of p) must be 0. -/
theorem companionMatrix_cyclic_e0 (hn : 0 < n) (p : K[X]) (hp : p.Monic)
    (hdeg : p.natDegree = n) :
    IsCyclicVector (CayleyHamiltonReductionOQ02OQ01.companionMatrix (d := n) p)
                   (Pi.single (0 : Fin n) 1) := by
  set C := CayleyHamiltonReductionOQ02OQ01.companionMatrix (d := n) p
  intro q hq_deg hann
  by_contra hq_ne
  -- q ≠ 0, so leadingCoeff ≠ 0
  have hlc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq_ne
  -- Expand: (aeval C q) *ᵥ e₀ = ∑_{k < natDeg+1} q.coeff k • (C^k *ᵥ e₀)
  rw [aeval_eq_range_sum q C, sum_mulVec_dist] at hann
  simp only [Matrix.smul_mulVec] at hann
  -- Substitute orbit: C^k *ᵥ e₀ = e_k for k ≤ natDegree q < n
  have hklt : ∀ k : Fin (q.natDegree + 1), k.val < n := fun k => by omega
  have hterms : ∑ k ∈ Finset.range (q.natDegree + 1),
      q.coeff k • (C ^ k).mulVec (Pi.single (0 : Fin n) 1) =
      ∑ k : Fin (q.natDegree + 1),
        q.coeff k.val • (Pi.single ⟨k.val, hklt k⟩ 1 : Fin n → K) := by
    rw [← Fin.sum_univ_eq_sum_range]
    congr 1; funext k
    congr 1
    exact CayleyHamiltonReductionOQ02OQ01.companionMatrix_pow_basis p k.val (hklt k)
  rw [hterms] at hann
  -- Evaluate at position ⟨q.natDegree, hq_deg⟩ to extract leading coefficient
  have hval := congr_fun hann ⟨q.natDegree, hq_deg⟩
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Pi.zero_apply,
             Fin.mk.injEq] at hval
  -- Collapse: only term k.val = q.natDegree contributes
  rw [Finset.sum_eq_single ⟨q.natDegree, Nat.lt_succ_self _⟩
    (fun k _ hk => by
      have hne : k.val ≠ q.natDegree := fun h => hk (Fin.ext h)
      simp [hne, Ne.symm hne])
    (fun h => absurd (Finset.mem_univ _) h)] at hval
  simp only [↓reduceIte, mul_one] at hval
  -- hval : q.coeff q.natDegree = 0, but q.leadingCoeff = q.coeff q.natDegree ≠ 0
  exact hlc (show q.leadingCoeff = 0 from hval)

-- ============================================================
-- SECTION IV.5: Main Theorem (All Fields)
-- ============================================================

/-- KEY SORRY: Every nonderogatory matrix is similar to its companion matrix.
    This is the Rational Canonical Form theorem (Frobenius normal form).
    Requires: structure theorem for f.g. modules over K[X] (a PID). -/
theorem nonderogatory_similar_companion (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) K) (h : IsNonderogatory M) :
    ∃ P : (Matrix (Fin n) (Fin n) K)ˣ,
      M = P.inv * CayleyHamiltonReductionOQ02OQ01.companionMatrix (d := n) (minpoly K M) * P.val := by
  sorry -- Requires: Rational Canonical Form / PID module structure theorem (not in Mathlib)

/-- **Main Result**: Over ANY field K, nonderogatory matrices have cyclic vectors.

    Proof structure:
    1. [sorry] M is similar to C(minpoly M) — the companion matrix (RCF theorem)
    2. [proved] e₀ is cyclic for C(minpoly M) — orbit property of companion matrices
    3. [proved] Cyclic vectors transfer under matrix similarity

    The sorry isolates exactly the missing Mathlib infrastructure: the PID module
    structure theorem giving Rational Canonical Form. -/
theorem nonderogatory_has_cyclic_vector_any_field
    (M : Matrix (Fin n) (Fin n) K) (h : IsNonderogatory M) :
    ∃ v, IsCyclicVector M v := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨Fin.elim0, fun p hp _ => by omega⟩
  -- Step 1: M ~ C(minpoly M) [sorry: RCF theorem]
  obtain ⟨P, hMC⟩ := nonderogatory_similar_companion hn M h
  -- Step 2: minpoly M has degree n (since M is nonderogatory)
  have hμ_deg : (minpoly K M).natDegree = n := by
    have := h  -- IsNonderogatory: minpoly K M = M.charpoly
    rw [h, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  -- Step 3: e₀ is cyclic for C(minpoly M) [proved: no sorry]
  have hμ_monic : (minpoly K M).Monic := minpoly.monic (Matrix.isIntegral M)
  have hcyc := companionMatrix_cyclic_e0 hn (minpoly K M) hμ_monic hμ_deg
  -- Step 4: Transfer cyclic vector along similarity [proved: no sorry]
  exact cyclic_vector_of_similar M
    (CayleyHamiltonReductionOQ02OQ01.companionMatrix (d := n) (minpoly K M))
    P hMC _ hcyc

/-- Corollary: The cyclic vector theorem holds over all finite fields,
    including those with |K| ≤ n. The union avoidance lemma is not needed. -/
theorem nonderogatory_has_cyclic_vector_finite_any_size [Fintype K]
    (M : Matrix (Fin n) (Fin n) K) (h : IsNonderogatory M) :
    ∃ v, IsCyclicVector M v :=
  nonderogatory_has_cyclic_vector_any_field M h

-- ============================================================
-- SECTION IV.6: Irreducible Minpoly Case (Sorry-Free)
-- ============================================================

/-- Over ANY field K (including finite fields), if M is nonderogatory and
    the minimal polynomial μ = minpoly K M is IRREDUCIBLE, then EVERY
    nonzero vector is cyclic.

    Proof (no sorry, works over all fields):
    Take any v ≠ 0 and p with deg(p) < n and p(M)v = 0.
    Let d = gcd(p, μ). By Bezout, d(M)v = 0 (annihilator_dvd_minpoly).
    Since d | μ and μ is irreducible: either IsUnit d or d ~ μ.
    • Unit case: d = C c (nonzero constant) → (aeval M d)v = c•v = 0 → v = 0. Contradiction.
    • Associate case: μ | d | p → deg(p) ≥ deg(μ) = n, contradicting deg(p) < n → p = 0. -/
theorem every_nonzero_cyclic_of_irred_minpoly
    (M : Matrix (Fin n) (Fin n) K)
    (h : IsNonderogatory M) (hirr : Irreducible (minpoly K M))
    (v : Fin n → K) (hv : v ≠ 0) : IsCyclicVector M v := by
  intro p hp hann
  set μ := minpoly K M with hμ_def
  set d := EuclideanDomain.gcd p μ with hd_def
  have hd_ann : (aeval M d).mulVec v = 0 := annihilator_dvd_minpoly M v p hann
  have hd_dvd : d ∣ μ := EuclideanDomain.gcd_dvd_right p μ
  obtain ⟨q, hq⟩ := hd_dvd
  rcases hirr.isUnit_or_isUnit hq with hd_unit | hq_unit
  · -- Case 1: d is a unit polynomial → d(M) = c • I → c • v = 0 → v = 0, contradiction
    exfalso
    -- In K[X], units are nonzero constants: d = C ↑c for some c : Kˣ
    obtain ⟨c, hc⟩ := Polynomial.isUnit_iff.mp hd_unit
    -- (aeval M (C ↑c)).mulVec v = ↑c • v
    have heval_smul : (aeval M d).mulVec v = ↑c • v := by
      rw [← hc, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
          Matrix.smul_mulVec, Matrix.one_mulVec]
    -- ↑c • v = 0 with ↑c ≠ 0 forces v = 0
    rw [heval_smul] at hd_ann
    exact hv (smul_eq_zero.mp hd_ann |>.resolve_left (Units.ne_zero c))
  · -- Case 2: q is a unit → d ~ μ → μ | d | p → p = 0
    obtain ⟨u, hu⟩ := hq_unit
    -- From μ = d * q = d * ↑u, derive d = μ * ↑u⁻¹
    have hdu : d * ↑u = μ := by rw [← hu]; exact hq.symm
    have hd_eq : d = μ * ↑u⁻¹ := by
      have h1 : d = d * (↑u * ↑u⁻¹) := by rw [Units.mul_inv, mul_one]
      rw [← mul_assoc, hdu] at h1; exact h1
    -- μ | d (via the associate relation)
    have hμ_dvd_d : μ ∣ d := ⟨↑u⁻¹, hd_eq⟩
    -- d | p (gcd divides first argument) → μ | p
    have hd_dvd_p : d ∣ p := EuclideanDomain.gcd_dvd_left p μ
    have hμ_dvd_p : μ ∣ p := dvd_trans hμ_dvd_d hd_dvd_p
    -- p = 0 or deg(μ) ≤ deg(p), but deg(p) < n = deg(μ)
    rcases eq_or_ne p 0 with rfl | hp_ne
    · rfl
    · exfalso
      have hμ_deg : μ.natDegree = n := by
        rw [hμ_def, h, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
      exact absurd (Polynomial.natDegree_le_of_dvd hμ_dvd_p hp_ne) (by omega)

/-- Corollary: When minpoly K M is irreducible, nonderogatory M has a cyclic vector.
    This case is proved WITHOUT any sorry — no Rational Canonical Form needed.
    The proof holds over all fields, including finite fields with |K| ≤ n. -/
theorem nonderogatory_has_cyclic_vector_irred_minpoly
    (M : Matrix (Fin n) (Fin n) K)
    (h : IsNonderogatory M) (hirr : Irreducible (minpoly K M)) :
    ∃ v, IsCyclicVector M v := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨Fin.elim0, fun p hp _ => by omega⟩
  -- e₀ = Pi.single 0 1 is a nonzero vector (n ≥ 1)
  refine ⟨Pi.single (0 : Fin n) 1, every_nonzero_cyclic_of_irred_minpoly M h hirr _ ?_⟩
  intro h0
  exact one_ne_zero (congr_fun h0 ⟨0, hn⟩ |>.symm.trans (by simp [Pi.single_apply]))

-- ============================================================
-- SECTION V: Counterexample to Union Avoidance over Small Fields
-- ============================================================

/-- Over F₂, the 2-dimensional vector space F₂² can be covered by 3
    proper subspaces (the three 1-dimensional subspaces). This shows
    union avoidance fails when |K| ≤ n. Yet the nonderogatory cyclic
    vector theorem still holds (by the module-theoretic argument). -/
theorem F2_union_covers :
    ∀ v : Fin 2 → ZMod 2, v ≠ 0 →
      v ∈ ({![1, 0], ![0, 1], ![1, 1]} : Set (Fin 2 → ZMod 2)) := by
  decide

/- ## Summary

**Problem**: For which (n, q) pairs does every nonderogatory M ∈ M_n(F_q) have
a cyclic vector? Does the theorem fail when q ≤ n?

**Answer**: The theorem holds for ALL (n, q). No failure threshold exists.

**Proof structure** (modular):
1. [sorry] `nonderogatory_similar_companion`: M ~ C(minpoly M) — Rational Canonical Form
2. [proved] `companionMatrix_cyclic_e0`: e₀ is cyclic for C(p) — orbit lemma
3. [proved] `cyclic_vector_of_similar`: cyclic vectors transfer under similarity
4. Main theorem follows from 1+2+3.

**Key sorry**: `nonderogatory_similar_companion` requires the structure theorem for
f.g. modules over K[X] (a PID), which gives Rational Canonical Form. Not in Mathlib.

**Progress vs previous version**: Replaced a monolithic `sorry` with a modular proof.
The new `companionMatrix_cyclic_e0` (no sorry) establishes the orbit-based cyclic
vector argument. The remaining sorry is isolated to exactly the RCF similarity step.

**Proved (sorry-free)**:
- `sum_mulVec_dist`: mulVec distributes over finite sums
- `aeval_eq_range_sum`: aeval expansion as sum over range(natDegree+1)
- `companionMatrix_cyclic_e0`: e₀ cyclic for companion matrix (orbit argument)
- `annihilator_dvd_minpoly`: Bezout identity for GCD annihilation
- `cyclic_iff_ann_eq_minpoly`: Characterization of cyclic vectors via annihilators
- `aeval_conj`: Conjugation commutes with polynomial evaluation (inductive proof)
- `cyclic_vector_of_similar`: Cyclic vectors transfer under similarity
- `F2_union_covers`: Counterexample showing union avoidance fails over F₂
- `every_nonzero_cyclic_of_irred_minpoly`: Every nonzero v is cyclic when minpoly irreducible (no sorry)
- `nonderogatory_has_cyclic_vector_irred_minpoly`: Cyclic vector exists when minpoly irreducible (no sorry)

**Remaining sorry**: `nonderogatory_similar_companion` (RCF similarity, used by main theorem).
**Sorry-free subcase**: irreducible minpoly case is fully proved without RCF.
-/

end CyclicVectorArbitrary

end
