/-
  Nonderogatory ⟹ Cyclic Vector: All Fields (Primary Decomposition)

  Every nonderogatory matrix over ANY field K (finite or infinite, any size)
  has a cyclic vector. This formalization uses the primary decomposition approach
  from WIP04, avoiding the Rational Canonical Form axiom entirely.

  ## Proof Structure (V2: Axiom-Free)

  V1 axiomatized the RCF similarity theorem (nonderogatory_similar_companion).
  V2 eliminates that axiom using direct algebraic arguments:

  1. **[Proved, WIP04]** Primary decomposition: Given the factored form of
     minpoly K M = ∏ p_i^{e_i}, construct primary vectors v_i in
     ker(p_i^{e_i}(M)) \ ker(p_i^{e_i-1}(M)) via minimality of minpoly.

  2. **[Proved, WIP04]** CRT combination: v = ∑ v_i is cyclic. For any r with
     r(M)v = 0, Bezout projections extract r(M)v_i = 0 for each i, giving
     p_i^{e_i} | r by pow_irred_dvd_of_annihilated. Then ∏ p_i^{e_i} | r by
     pairwise coprimality, so deg(r) ≥ n — contradiction with deg(r) < n.

  3. **[Sorry: routine]** Factorization bridge: Every monic polynomial of positive
     degree over a field factors into coprime monic irreducible prime powers.
     This is a standard consequence of K[X] being a UFD. The sorry is strictly
     routine Mathlib API work, NOT a mathematical assumption.

  ## Status: 0 axioms, 1 sorry (polynomial factorization bridge)

  The mathematical content is fully verified. The single sorry is a routine
  application of UniqueFactorizationMonoid.normalizedFactors in Mathlib.

  ## Why V2 is Stronger than V1

  V1's axiom (RCF similarity) required the structure theorem for finitely
  generated modules over a PID — ~800 lines to formalize, fundamentally deep.
  V2's sorry is ~50 lines of Mathlib API navigation — routine and Aristotle-suitable.

  ## Related Gallery Entries

  - `cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-04`: Full proof (WIP04)
  - `cayley-hamilton-minpoly-oq-05-oq-01-oq-04`: Module-theory approach
  - `cayley-hamilton-reduction-oq-02-oq-01`: Companion matrix properties
-/
import Mathlib
import Proofs.CayleyHamiltonMinpolyOQ05OQ01OQ04WIP04

noncomputable section

namespace CayleyHamiltonCyclicVectorAllFields

open Matrix Polynomial UniqueFactorizationMonoid

-- ============================================================
-- SECTION I: Definitions
-- ============================================================

/-- A vector v ∈ Kⁿ is **cyclic** for M if no nonzero polynomial of degree < n
    annihilates both M and v. Equivalently, {v, Mv, ..., M^{n-1}v} is a basis. -/
abbrev IsCyclicVector {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : Prop :=
  GeneralCyclicVector.IsCyclicVector M v

/-- A matrix M is **nonderogatory** if its minimal polynomial equals its
    characteristic polynomial (both monic, both of degree n). -/
abbrev IsNonderogatory {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) : Prop :=
  GeneralCyclicVector.IsNonderogatory M

-- ============================================================
-- SECTION II: Factorization Bridge
-- ============================================================

private theorem monic_irreducible_multiset_factorization {K : Type*} [Field K]
    (μ : K[X]) (hμ_monic : μ.Monic) (hμ_deg : 0 < μ.natDegree) :
    ∃ (f : Multiset K[X]),
      (∀ p ∈ f, Irreducible p ∧ p.Monic) ∧
      f ≠ 0 ∧
      f.prod = μ := by
  obtain ⟨f, hf⟩ : ∃ f : Multiset (Polynomial K), (∀ p ∈ f, Irreducible p) ∧ f.prod = μ := by
    have := UniqueFactorizationMonoid.exists_prime_factors μ;
    obtain ⟨ f, hf₁, hf₂ ⟩ := this ( Polynomial.Monic.ne_zero hμ_monic );
    obtain ⟨ u, hu ⟩ := hf₂;
    rcases f with ⟨ ⟨ p, hp ⟩ ⟩ <;> simp_all +decide [ Polynomial.Monic.def ];
    · exact absurd ( Polynomial.natDegree_eq_zero_of_isUnit u.isUnit ) ( by aesop );
    · refine' ⟨ Multiset.cons ( ‹_› * ↑u ) ( Multiset.ofList ‹_› ), _, _ ⟩ <;> simp_all +decide [ irreducible_mul_iff ];
      · exact ⟨ Or.inl hf₁.1.irreducible, fun a ha => hf₁.2 a ha |> Prime.irreducible ⟩;
      · rw [ mul_right_comm, hu ];
  refine' ⟨ f.map fun p => Polynomial.C ( p.leadingCoeff ) ⁻¹ * p, _, _, _ ⟩ <;> simp_all +decide [ Polynomial.Monic.def ];
  · intro p hp; have := hf.1 p hp; simp_all +decide [ irreducible_mul_iff ] ;
    exact ⟨ Or.inr ( by specialize hf; have := hf.1 p hp; exact this.ne_zero ), inv_mul_cancel₀ ( by specialize hf; have := hf.1 p hp; exact this.ne_zero |> fun h => by aesop ) ⟩;
  · aesop;
  · replace hf := congr_arg Polynomial.leadingCoeff hf.2; simp_all +decide [ Polynomial.leadingCoeff_multiset_prod ] ;
    have h_inv_prod : (Multiset.map (fun f => C (f.leadingCoeff)⁻¹) f).prod = C ((Multiset.map (fun f => f.leadingCoeff) f).prod)⁻¹ := by
      have h_inv_prod : ∀ (s : Multiset K), (Multiset.map (fun x => C x⁻¹) s).prod = C ((Multiset.map (fun x => x) s).prod)⁻¹ := by
        intro s; induction s using Multiset.induction <;> simp_all +decide [ mul_comm ] ;
      convert h_inv_prod ( Multiset.map ( fun f => f.leadingCoeff ) f ) using 1 ; simp +decide [ Multiset.map_map ];
      rw [ Multiset.map_id' ];
    aesop

private theorem coprime_of_distinct_monic_irreducible {K : Type*} [Field K]
    (p q : K[X]) (hp : Irreducible p) (hq : Irreducible q)
    (hp_monic : p.Monic) (hq_monic : q.Monic) (hne : p ≠ q) :
    IsCoprime p q := by
  refine' hp.coprime_iff_not_dvd.mpr fun h => hne _;
  obtain ⟨ a, rfl ⟩ := h;
  rw [ irreducible_mul_iff ] at hq;
  cases hq <;> simp_all +decide [ Polynomial.Monic.def, Polynomial.leadingCoeff_mul ];
  · rw [ Polynomial.isUnit_iff ] at * ; aesop;
  · exact hp.not_isUnit ( by tauto )

private theorem coprime_pow_of_coprime_irreducible {K : Type*} [Field K]
    (p q : K[X]) (m n : ℕ) (_hp : Irreducible p) (_hq : Irreducible q)
    (hcop : IsCoprime p q) :
    IsCoprime (p ^ m) (q ^ n) :=
  hcop.pow

private theorem finset_factorization_from_multiset {K : Type*} [Field K]
    (f : Multiset K[X])
    (hf : ∀ p ∈ f, Irreducible p ∧ p.Monic)
    (hf_ne : f ≠ 0) :
    ∃ (k : ℕ) (_ : 0 < k) (p : Fin k → K[X]) (e : Fin k → ℕ),
      (∀ i, Irreducible (p i)) ∧
      (∀ i, (p i).Monic) ∧
      (∀ i, 0 < e i) ∧
      (∀ i j : Fin k, i ≠ j → p i ≠ p j) ∧
      f.prod = ∏ i : Fin k, p i ^ e i := by
  revert f;
  intro f hf hf_ne
  obtain ⟨k, p, e, hp, he⟩ : ∃ (k : ℕ) (p : Fin k → K[X]) (e : Fin k → ℕ), (∀ i, p i ∈ f) ∧ (∀ i, Irreducible (p i)) ∧ (∀ i, (p i).Monic) ∧ (∀ i, 0 < e i) ∧ (∀ i j, i ≠ j → p i ≠ p j) ∧ Multiset.prod f = ∏ i, p i ^ e i := by
    have h_factorization : ∀ (f : Multiset K[X]), (∀ p ∈ f, Irreducible p ∧ p.Monic) → f ≠ 0 → ∃ (k : ℕ) (p : Fin k → K[X]) (e : Fin k → ℕ), (∀ i, p i ∈ f) ∧ (∀ i, Irreducible (p i)) ∧ (∀ i, (p i).Monic) ∧ (∀ i, 0 < e i) ∧ (∀ i j, i ≠ j → p i ≠ p j) ∧ Multiset.prod f = ∏ i, p i ^ e i := by
      intro f hf hf_ne
      induction' f using Multiset.induction with p f ih;
      · contradiction;
      · by_cases hf_zero : f = 0;
        · use 1, ![p], ![1]
          simp [hf_zero];
          exact hf p ( Multiset.mem_cons_self _ _ );
        · obtain ⟨ k, p', e', hp', he', he'', he''', he'''' ⟩ := ih ( fun q hq => hf q ( Multiset.mem_cons_of_mem hq ) ) hf_zero;
          by_cases h : ∃ i, p' i = p;
          · obtain ⟨ i, rfl ⟩ := h;
            refine' ⟨ k, p', fun j => if j = i then e' j + 1 else e' j, _, _, _, _, _ ⟩ <;> simp +decide [ *, Finset.prod_ite, Finset.filter_eq', Finset.filter_ne' ];
            · exact fun j => by split_ifs <;> linarith [ he''' j ] ;
            · exact ⟨ he'''' |>.1, by rw [ ← Finset.mul_prod_erase _ _ ( Finset.mem_univ i ) ] ; ring ⟩;
          · refine' ⟨ k + 1, Fin.cons p p', Fin.cons 1 e', _, _, _, _, _ ⟩ <;> simp +decide [ Fin.forall_fin_succ, * ];
            simp +decide [ Fin.prod_univ_succ, Fin.cons ];
            exact ⟨ fun i hi => Ne.symm ( by rintro rfl; exact h ⟨ i, rfl ⟩ ), fun i => ⟨ fun hi => h ⟨ i, hi ⟩, fun j hj => he'''' |>.1 i j hj ⟩ ⟩;
    exact h_factorization f hf hf_ne;
  rcases k with ( _ | k ) <;> simp_all +decide;
  · induction f using Multiset.induction <;> simp_all +decide;
    exact absurd ( hf.1.1.not_isUnit ( isUnit_of_dvd_one ( dvd_of_mul_right_eq _ he ) ) ) ( by simp +decide );
  · exact ⟨ k + 1, Nat.succ_pos _, p, fun i => hf _ ( hp i ) |>.1, fun i => hf _ ( hp i ) |>.2, e, he.1, he.2.1, rfl ⟩

/-- Every monic polynomial of positive degree over a field factors into a
    finite product of coprime monic irreducible prime powers. -/
private theorem monic_factored_form {K : Type*} [Field K]
    (μ : K[X]) (hμ_monic : μ.Monic) (hμ_deg : 0 < μ.natDegree) :
    ∃ (k : ℕ) (_ : 0 < k) (p : Fin k → K[X]) (e : Fin k → ℕ),
      (∀ i, Irreducible (p i)) ∧
      (∀ i, (p i).Monic) ∧
      (∀ i, 0 < e i) ∧
      (∀ i j : Fin k, i ≠ j → IsCoprime (p i ^ e i) (p j ^ e j)) ∧
      μ = ∏ i : Fin k, p i ^ e i := by
  obtain ⟨f, hf_irr, hf_ne, hf_prod⟩ := monic_irreducible_multiset_factorization μ hμ_monic hμ_deg
  obtain ⟨k, hk, p, e, hirr, hmon, hpos, hdist, hprod⟩ :=
    finset_factorization_from_multiset f hf_irr hf_ne
  exact ⟨k, hk, p, e, hirr, hmon, hpos, fun i j hij =>
    coprime_pow_of_coprime_irreducible (p i) (p j) (e i) (e j) (hirr i) (hirr j)
      (coprime_of_distinct_monic_irreducible (p i) (p j) (hirr i) (hirr j) (hmon i) (hmon j)
        (hdist i j hij)),
    hf_prod ▸ hprod⟩

-- ============================================================
-- SECTION III: Main Theorem
-- ============================================================

/-- **Main Theorem**: Over ANY field K (including finite fields F_q with q ≤ n),
    every nonderogatory matrix has a cyclic vector.

    **Proof**:
    - Case n = 0: trivial (Fin 0 → K is empty, the empty function works).
    - Case n > 0:
      1. Factor minpoly K M = ∏ p_i^{e_i} via `monic_factored_form`.
      2. Apply WIP04's primary decomposition theorem
         (`GeneralCyclicVector.nonderogatory_general_has_cyclic_vector`).

    **Why this works over finite fields**: The proof never invokes |K| > n.
    The key insight is that primary decomposition + CRT provides a cyclic vector
    purely from the annihilator structure, bypassing union avoidance entirely. -/
theorem nonderogatory_has_cyclic_vector
    {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (h : IsNonderogatory M) :
    ∃ v, IsCyclicVector M v := by
  -- Dispatch trivial n = 0 case
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨Fin.elim0, fun p hp _ => by omega⟩
  -- minpoly facts
  have hμ_monic : (minpoly K M).Monic := minpoly.monic (Matrix.isIntegral M)
  have hμ_deg : (minpoly K M).natDegree = n := by
    rw [h, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  -- Factor minpoly into coprime prime powers
  obtain ⟨k, hk, p, e, hp_irr, hp_monic, he_pos, hcop, hprod⟩ :=
    monic_factored_form (minpoly K M) hμ_monic (by omega)
  -- Apply WIP04's axiom-free primary decomposition theorem
  exact GeneralCyclicVector.nonderogatory_general_has_cyclic_vector
    hk M h p e hp_irr hp_monic he_pos hcop hprod

-- ============================================================
-- SECTION IV: Corollaries
-- ============================================================

/-- **Corollary (Finite Fields)**: The cyclic vector theorem holds over any
    finite field, including F_q with q ≤ n (where union avoidance fails). -/
theorem nonderogatory_has_cyclic_vector_finite
    {K : Type*} [Field K] [Fintype K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (h : IsNonderogatory M) :
    ∃ v, IsCyclicVector M v :=
  nonderogatory_has_cyclic_vector M h

/-- **Corollary (Uniqueness condition)**: If M is nonderogatory, a vector v is
    cyclic iff it is not annihilated by any polynomial of degree < n. -/
theorem cyclic_iff_not_killed_below_degree
    {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (h : IsNonderogatory M) (v : Fin n → K) :
    IsCyclicVector M v ↔ ∀ p : K[X], p ≠ 0 → p.natDegree < n → ¬(aeval M p).mulVec v = 0 := by
  constructor
  · intro hcyc p hne hdeg hann
    exact hne (hcyc p hdeg hann)
  · intro h' p hdeg hann
    by_contra hne
    exact h' p hne hdeg hann

-- ============================================================
-- SECTION V: Summary
-- ============================================================

/-!
## Summary

This formalization proves the cyclic vector theorem for nonderogatory matrices
over arbitrary fields using primary decomposition (WIP04).

**V2 Upgrade**: Eliminated the RCF similarity axiom from V1. The proof no longer
depends on the Rational Canonical Form theorem or the structure theorem for
finitely generated modules over PIDs.

**What is fully proved (sorry-free, axiom-free)**:
- Primary decomposition construction (GeneralCyclicVector, WIP04)
- Bezout projections and CRT-based cyclic vector construction (WIP04)
- `nonderogatory_has_cyclic_vector`: main theorem (modulo factorization bridge)
- `nonderogatory_has_cyclic_vector_finite`: finite field corollary
- `cyclic_iff_not_killed_below_degree`: characterization corollary

**The one sorry**:
- `monic_factored_form`: monic polynomial factors into coprime prime powers
  This is a routine consequence of K[X] being a UFD (UniqueFactorizationMonoid).
  NOT a mathematical assumption — purely Mathlib API navigation.
  Estimated: ~50 lines using normalizedFactors + Finset.equivFin.
  Suitable for Aristotle submission.

**V1 → V2 delta**:
- Removed: `axiom nonderogatory_similar_companion` (RCF similarity, ~800 lines to prove)
- Added: `sorry` in `monic_factored_form` (routine Mathlib API, ~50 lines to prove)
- Net: Deep mathematical axiom → routine API sorry
-/

end CayleyHamiltonCyclicVectorAllFields

end
