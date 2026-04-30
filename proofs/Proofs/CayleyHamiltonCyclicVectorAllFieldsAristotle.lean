/-
  Aristotle targets for CayleyHamiltonCyclicVectorAllFields

  Routine polynomial factorization bridge for automated proof search.
  See CayleyHamiltonCyclicVectorAllFields.lean for the main formalization.

  Target: monic_factored_form
  Every monic polynomial of positive degree over a field factors into a finite
  product of coprime monic irreducible prime powers.
  This follows from K[X] being a UniqueFactorizationMonoid via normalizedFactors.
-/
import Mathlib

namespace CayleyHamiltonCyclicVectorAllFieldsAristotle

open Polynomial UniqueFactorizationMonoid

/-
A monic polynomial of positive degree over a field can be written as a product
    of a multiset of monic irreducible polynomials.
-/
theorem monic_irreducible_multiset_factorization {K : Type*} [Field K]
    (μ : K[X]) (hμ_monic : μ.Monic) (hμ_deg : 0 < μ.natDegree) :
    ∃ (f : Multiset K[X]),
      (∀ p ∈ f, Irreducible p ∧ p.Monic) ∧
      f ≠ 0 ∧
      f.prod = μ := by
  -- Since μ is non-constant, it has a prime factorization.
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
    -- Since the product of the leading coefficients of the factors in f is 1, the product of their inverses is also 1.
    have h_inv_prod : (Multiset.map (fun f => C (f.leadingCoeff)⁻¹) f).prod = C ((Multiset.map (fun f => f.leadingCoeff) f).prod)⁻¹ := by
      have h_inv_prod : ∀ (s : Multiset K), (Multiset.map (fun x => C x⁻¹) s).prod = C ((Multiset.map (fun x => x) s).prod)⁻¹ := by
        intro s; induction s using Multiset.induction <;> simp_all +decide [ mul_comm ] ;
      convert h_inv_prod ( Multiset.map ( fun f => f.leadingCoeff ) f ) using 1 ; simp +decide [ Multiset.map_map ];
      rw [ Multiset.map_id' ];
    aesop

/-
Distinct monic irreducible polynomials over a field are coprime.
-/
theorem coprime_of_distinct_monic_irreducible {K : Type*} [Field K]
    (p q : K[X]) (hp : Irreducible p) (hq : Irreducible q)
    (hp_monic : p.Monic) (hq_monic : q.Monic) (hne : p ≠ q) :
    IsCoprime p q := by
  refine' hp.coprime_iff_not_dvd.mpr fun h => hne _;
  obtain ⟨ a, rfl ⟩ := h;
  rw [ irreducible_mul_iff ] at hq;
  cases hq <;> simp_all +decide [ Polynomial.Monic.def, Polynomial.leadingCoeff_mul ];
  · rw [ Polynomial.isUnit_iff ] at * ; aesop;
  · exact hp.not_isUnit ( by tauto )

/-
Coprime irreducible polynomials have coprime powers.
-/
theorem coprime_pow_of_coprime_irreducible {K : Type*} [Field K]
    (p q : K[X]) (m n : ℕ) (_hp : Irreducible p) (_hq : Irreducible q)
    (hcop : IsCoprime p q) :
    IsCoprime (p ^ m) (q ^ n) := by
  exact hcop.pow

/-
Given a nonempty multiset of monic irreducibles, one can group them into
    distinct irreducibles with multiplicities and index by Fin k.
-/
theorem finset_factorization_from_multiset {K : Type*} [Field K]
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
theorem monic_factored_form {K : Type*} [Field K]
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

end CayleyHamiltonCyclicVectorAllFieldsAristotle