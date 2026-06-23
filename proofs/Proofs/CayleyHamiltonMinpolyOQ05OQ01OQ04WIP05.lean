/-
  Nonderogatory → Cyclic Vector: Final Wrapper (All Fields, No Factored-Form Hypothesis)

  This file completes the cyclic vector theorem by eliminating the factored-form
  hypothesis from WIP04. We use the UFD structure of `K[X]` (where K is a field) to
  automatically factor `minpoly K M` into prime power factors, then apply WIP04's
  general theorem.

  ## Context

  WIP04 proves: nonderogatory M with minpoly = ∏_{i : Fin k} p_i^{e_i}
  (pairwise coprime, p_i monic irreducible) has a cyclic vector.

  This file proves: nonderogatory M has a cyclic vector — without taking the
  factorization as input. The factorization is constructed from
  `UniqueFactorizationMonoid.normalizedFactors (minpoly K M)`.

  ## Strategy

  1. f := minpoly K M is monic (since M.charpoly is monic and minpoly = charpoly).
  2. Let s := normalizedFactors f. Each q ∈ s is irreducible, monic, and
     prime-divides f.
  3. Let D := s.toFinset (the distinct prime factors). For each q ∈ D, the
     multiplicity is s.count q ≥ 1. Since deg f ≥ 1, D is nonempty.
  4. Distinct monic irreducibles p, q over a field are coprime: if p ∣ q then
     p ~ᵤ q (by `Irreducible.associated_of_dvd`), and `eq_of_monic_of_associated`
     forces p = q.
  5. The product identity f = ∏_{q ∈ D} q^(s.count q) follows from
     `prod_normalizedFactors_eq` (s.prod = normalize f),
     `Polynomial.Monic.normalize_eq_self` (normalize f = f for monic f), and
     `Finset.prod_multiset_count` (s.prod = ∏ q ∈ D, q^(s.count q)).
  6. Convert the Finset-indexed family to a Fin-indexed family using
     `Fintype.equivFin` and apply WIP04's theorem.

  ## Status: 0 sorries, 0 axioms (pending build verification)
-/
import Proofs.CayleyHamiltonMinpolyOQ05OQ01OQ04WIP04

noncomputable section

namespace GeneralCyclicVectorComplete

open Matrix Polynomial UniqueFactorizationMonoid GeneralCyclicVector

attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K] {n : ℕ}

-- ============================================================
-- SECTION I: Index Conversion (Fintype version of WIP04)
-- ============================================================

/-- Fintype-indexed version of WIP04's theorem. Reduces to the `Fin k` case via
    `Fintype.equivFin`. -/
private theorem nonderogatory_general_has_cyclic_vector_fintype
    {σ : Type*} [Fintype σ] [Nonempty σ]
    (M : Matrix (Fin n) (Fin n) K)
    (h_nd : IsNonderogatory M)
    (p : σ → K[X]) (e : σ → ℕ)
    (hp_irr : ∀ i, Irreducible (p i))
    (hp_monic : ∀ i, (p i).Monic)
    (he_pos : ∀ i, 0 < e i)
    (hcoprime : ∀ i j : σ, i ≠ j → IsCoprime (p i ^ e i) (p j ^ e j))
    (hprod : minpoly K M = ∏ i : σ, p i ^ e i) :
    ∃ v : Fin n → K, IsCyclicVector M v := by
  let k := Fintype.card σ
  have hk : 0 < k := Fintype.card_pos
  let φ : Fin k ≃ σ := (Fintype.equivFin σ).symm
  -- Reindex everything through φ
  have hprod' : minpoly K M = ∏ i : Fin k, p (φ i) ^ e (φ i) := by
    rw [hprod]
    exact (Equiv.prod_comp φ (fun i => p i ^ e i)).symm
  have hcop' : ∀ i j : Fin k, i ≠ j →
      IsCoprime (p (φ i) ^ e (φ i)) (p (φ j) ^ e (φ j)) := fun i j hij =>
    hcoprime (φ i) (φ j) (fun heq => hij (φ.injective heq))
  exact nonderogatory_general_has_cyclic_vector hk M h_nd
    (fun i => p (φ i)) (fun i => e (φ i))
    (fun i => hp_irr (φ i)) (fun i => hp_monic (φ i)) (fun i => he_pos (φ i))
    hcop' hprod'

-- ============================================================
-- SECTION II: Final Wrapper — Any-Field Cyclic Vector Theorem
-- ============================================================

/-- **Main Theorem (Nonderogatory ⇒ Cyclic Vector, All Fields, Axiom-Free)**:
    Any nonderogatory matrix M ∈ Mₙ(K) over any field K has a cyclic vector.

    This eliminates the factored-form hypothesis from WIP04 by automatically
    factoring `minpoly K M` using `UniqueFactorizationMonoid.normalizedFactors`. -/
theorem nonderogatory_has_cyclic_vector_any_field
    (M : Matrix (Fin n) (Fin n) K) (h : IsNonderogatory M) :
    ∃ v : Fin n → K, IsCyclicVector M v := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨Fin.elim0, fun r hr _ => by omega⟩
  -- Step 1: Set up f := minpoly K M and basic facts
  set f : K[X] := minpoly K M with hf_def
  have hf_eq_charpoly : f = M.charpoly := h
  have hf_monic : f.Monic := by rw [hf_eq_charpoly]; exact M.charpoly_monic
  have hf_ne : f ≠ 0 := hf_monic.ne_zero
  have hf_deg : f.natDegree = n := by
    rw [hf_eq_charpoly, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hf_not_unit : ¬IsUnit f := by
    intro hu
    have h1 : f = 1 := hf_monic.eq_one_of_isUnit hu
    have : f.natDegree = 0 := by rw [h1]; simp
    omega
  -- Step 2: Build distinct prime factors and Fintype structure
  let s : Multiset K[X] := normalizedFactors f
  let D : Finset K[X] := s.toFinset
  have hD_nonempty : D.Nonempty := by
    obtain ⟨q, hq⟩ := exists_mem_normalizedFactors hf_ne hf_not_unit
    exact ⟨q, Multiset.mem_toFinset.mpr hq⟩
  obtain ⟨q₀, hq₀⟩ := hD_nonempty
  haveI : Nonempty (↥D) := ⟨⟨q₀, hq₀⟩⟩
  -- Step 3: Define the family p, e indexed by ↥D
  let p_fn : ↥D → K[X] := fun x => x.val
  let e_fn : ↥D → ℕ := fun x => s.count x.val
  -- Membership facts
  have hp_in_s : ∀ x : ↥D, p_fn x ∈ s := fun x =>
    Multiset.mem_toFinset.mp x.property
  -- Irreducibility, monicity, positive multiplicity
  have hp_irr : ∀ x, Irreducible (p_fn x) := fun x =>
    irreducible_of_normalized_factor _ (hp_in_s x)
  have hp_mem_factors : ∀ x : ↥D, Irreducible (p_fn x) ∧ (p_fn x).Monic ∧ p_fn x ∣ f := fun x =>
    (Polynomial.mem_normalizedFactors_iff hf_ne).mp (hp_in_s x)
  have hp_monic : ∀ x, (p_fn x).Monic := fun x => (hp_mem_factors x).2.1
  have he_pos : ∀ x, 0 < e_fn x := fun x =>
    Multiset.count_pos.mpr (hp_in_s x)
  -- Coprimality: distinct monic irreducibles are coprime, then so are their powers
  have hcoprime : ∀ i j : ↥D, i ≠ j →
      IsCoprime (p_fn i ^ e_fn i) (p_fn j ^ e_fn j) := by
    intro i j hij
    have hpij_ne : p_fn i ≠ p_fn j := fun heq => hij (Subtype.ext heq)
    have h_base : IsCoprime (p_fn i) (p_fn j) := by
      rw [(hp_irr i).coprime_iff_not_dvd]
      intro hdvd
      have h_assoc : Associated (p_fn i) (p_fn j) :=
        Irreducible.associated_of_dvd (hp_irr i) (hp_irr j) hdvd
      exact hpij_ne (eq_of_monic_of_associated (hp_monic i) (hp_monic j) h_assoc)
    exact h_base.pow
  -- Product identity: f = ∏ x : ↥D, p_fn x ^ e_fn x
  have hprod : minpoly K M = ∏ x : ↥D, p_fn x ^ e_fn x := by
    show f = ∏ x : ↥D, p_fn x ^ e_fn x
    have h1 : f = s.prod := by
      rw [← hf_monic.normalize_eq_self, ← prod_normalizedFactors_eq hf_ne]
    have h2 : s.prod = ∏ m ∈ D, m ^ s.count m := Finset.prod_multiset_count s
    have h3 : (∏ m ∈ D, m ^ s.count m) = ∏ x : ↥D, p_fn x ^ e_fn x :=
      (Finset.prod_coe_sort D (fun m => m ^ s.count m)).symm
    rw [h1, h2, h3]
  -- Apply the Fintype-indexed version
  exact nonderogatory_general_has_cyclic_vector_fintype M h
    p_fn e_fn hp_irr hp_monic he_pos hcoprime hprod

-- ============================================================
-- SECTION III: Commentary
-- ============================================================

/-
### Significance

This eliminates the last hypothesis (factored form of `minpoly K M`) from WIP04,
yielding the fully general nonderogatory ⇒ cyclic vector theorem over any field K.

Combined with WIP04, this is the complete axiom-free formalization of the theorem
that prior versions (WIP01) stated using the `nonderogatory_similar_to_companion`
axiom (a stand-in for the rational canonical form structure theorem).

### Proof Architecture

- **WIP02**: squarefree minpoly case (CRT projections, no module theory).
- **WIP03**: prime-power minpoly case (induction on exponent, no dimension args).
- **WIP04**: general factored case (combines WIP02/WIP03 via primary decomposition
  using Bezout projections).
- **WIP05** (this file): wraps WIP04 by extracting the factorization from
  `UniqueFactorizationMonoid.normalizedFactors`.

### Mathlib Facts Used

- `Polynomial.Monic.normalize_eq_self`: monic ⇒ `normalize p = p`.
- `Polynomial.mem_normalizedFactors_iff`: characterizes membership in
  `normalizedFactors q` for a field.
- `prod_normalizedFactors_eq`: `(normalizedFactors a).prod = normalize a`.
- `Finset.prod_multiset_count`: `s.prod = ∏ m ∈ s.toFinset, m ^ s.count m`.
- `Polynomial.eq_of_monic_of_associated`: monic + associated ⇒ equal.
- `Irreducible.coprime_iff_not_dvd` (over PID): irreducible + ¬ dvd ⇒ coprime.
- `IsCoprime.pow_pow`: coprime ⇒ powers coprime.
- `Matrix.charpoly_monic`, `Matrix.charpoly_natDegree_eq_dim`: charpoly facts.
-/

end GeneralCyclicVectorComplete
