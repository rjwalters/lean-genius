import Mathlib

/-
# Galois Group of x⁵ - 4x + 2 is S₅ (Abel-Ruffini OQ-04 Extension)

## What This Proves

We show that the polynomial p(x) = x⁵ - 4x + 2 over ℚ has Galois group S₅,
completing the Abel-Ruffini proof chain. This gives a concrete polynomial
whose roots CANNOT be expressed using radicals.

## The Proof Chain (now complete)

1. A₅ is simple (Mathlib: `alternatingGroup.isSimpleGroup_five`)
2. Sₙ (n ≥ 5) is not solvable (AbelRuffiniOQ04.lean)
3. Solvable by radicals ⟹ solvable Galois group (AbelRuffini.lean)
4. **Gal(x⁵ - 4x + 2 / ℚ) ≅ S₅ (THIS FILE)**
5. Therefore: the roots of x⁵ - 4x + 2 are not solvable by radicals

## Why x⁵ - 4x + 2?

- **Irreducible**: Eisenstein's criterion at p = 2 (PROVED)
- **Separable**: automatic over ℚ (characteristic 0) (PROVED)
- **Gal = S₅**: |Gal| = 120 = 5! (PROVED — axiom-free)

### Proof that |Gal| = 120 (Axiom-Free)

All axioms have been eliminated. The proof proceeds in two stages:

**Stage 1 — Gal ⊄ A₅ (odd permutation exists):**
  Δ² = -212144 (via derivative product identity + Vieta's formulas).
  Δ ∉ ℚ (since Δ² < 0). By FTGT, some σ has sign(σ) = -1.

**Stage 2 — Complex conjugation gives a transposition:**
  Embed SF → ℂ via IsAlgClosed.lift. Complex conjugation is an involution
  with sign -1 (since Δ² < 0 forces non-real Δ). So Gal has a transposition.

**Stage 3 — Eliminate all non-120 orders via Sylow theory:**
  5 | |Gal| (prime degree), |Gal| | 120 (embeds in S₅).
  - |Gal| ≠ 5: order-5 perms are even, but Gal has odd perm
  - |Gal| ∉ {10,20,40}: unique normal Sylow 5-subgroup, but transpositions
    don't normalize 5-cycles (native_decide)
  - |Gal| ≠ 15,30: no such subgroups in S₅ (Sylow/A₅ simplicity)
  - |Gal| ≠ 60: unique order-60 subgroup is A₅, but Gal ⊄ A₅
  Therefore |Gal| = 120.

## Extends

- AbelRuffini.lean: Galois bridge and contrapositive form
- AbelRuffiniOQ04.lean: A₅ simplicity and S₅ non-solvability
- AbelRuffiniGaloisExtensions.lean: Solvability classifications

## Wiedijk's 100 Theorems: #83 (Extension)
-/

set_option linter.unusedVariables false

-- ============================================================================
-- Computational Lemmas (BEFORE `open scoped Classical` for native_decide)
-- Namespaced to avoid collisions with InverseGaloisA5 which shares some lemmas.
-- ============================================================================

namespace AbelRuffiniOQ04OQ01

/-- No element of order 5 commutes with any element of order 3 in S₅.
    Used to prove no subgroup of S₅ has order 15. -/
theorem perm_fin5_order5_order3_not_commute :
    ∀ (σ τ : Equiv.Perm (Fin 5)),
      σ ^ 5 = 1 → σ ≠ 1 → τ ^ 3 = 1 → τ ≠ 1 → σ * τ ≠ τ * σ := by
  native_decide


/-- Every σ ∈ S₅ with σ^5 = 1 has sign 1.
    (Elements of order dividing 5 in S₅ are 5-cycles or identity; all even.)
    Useful for eliminating |Gal| = 5 in future axiom elimination work. -/
theorem perm_fin5_order_dvd5_sign_one :
    ∀ σ : Equiv.Perm (Fin 5), σ ^ 5 = 1 → Equiv.Perm.sign σ = 1 := by
  native_decide

/-- No transposition in S₅ normalizes any 5-cycle.
    The normalizer of ⟨5-cycle⟩ in S₅ is F₂₀, whose involutions are double
    transpositions (even), not transpositions (odd).
    Used for eliminating |Gal| = 20 in the axiom elimination proof. -/
theorem transposition_not_normalizing_5cycle :
    ∀ (σ τ : Equiv.Perm (Fin 5)),
      σ ^ 5 = 1 → σ ≠ 1 →
      Equiv.Perm.sign τ = -1 → τ ^ 2 = 1 →
      τ * σ * τ ≠ σ ∧ τ * σ * τ ≠ σ ^ 2 ∧ τ * σ * τ ≠ σ ^ 3 ∧ τ * σ * τ ≠ σ ^ 4 := by
  native_decide

end AbelRuffiniOQ04OQ01

open scoped Classical

namespace AbelRuffiniOQ04OQ01

open Polynomial

-- ============================================================================
-- Part I: The Polynomial p = X⁵ - 4X + 2
-- ============================================================================

/-- The polynomial p = X⁵ - 4X + 2 over ℚ. -/
noncomputable def p : ℚ[X] := X ^ 5 - C 4 * X + C 2

/-- The ℤ[X] version of p for Eisenstein criterion application. -/
private noncomputable def p_int : ℤ[X] := X ^ 5 - C 4 * X + C 2

-- ============================================================================
-- Part II: Irreducibility via Eisenstein at p = 2
-- ============================================================================

/-
## Eisenstein's Criterion at p = 2

p(x) = x⁵ - 4x + 2 satisfies Eisenstein at (2) ⊂ ℤ:

| Condition                        | Check         |
|----------------------------------|---------------|
| Leading coeff 1 ∉ (2)           | 2 ∤ 1 ✓      |
| coeff x⁴ = 0 ∈ (2)             | 2 ∣ 0 ✓      |
| coeff x³ = 0 ∈ (2)             | 2 ∣ 0 ✓      |
| coeff x² = 0 ∈ (2)             | 2 ∣ 0 ✓      |
| coeff x¹ = -4 ∈ (2)            | 2 ∣ -4 ✓     |
| coeff x⁰ = 2 ∈ (2)            | 2 ∣ 2 ✓      |
| coeff x⁰ = 2 ∉ (4)            | 4 ∤ 2 ✓      |
-/

/-- p_int has degree 5. -/
private theorem p_int_degree : p_int.degree = 5 := by
  unfold p_int; compute_degree!

/-- p_int has natDegree 5. -/
private theorem p_int_natDegree : p_int.natDegree = 5 := by
  unfold p_int; compute_degree!

/-- p_int is monic (leading coefficient = 1). -/
private theorem p_int_monic : p_int.Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, p_int_natDegree]
  unfold p_int
  simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

/-- p_int is irreducible over ℤ, by Eisenstein's criterion at p = 2. -/
private theorem p_int_irreducible : Irreducible p_int := by
  apply Polynomial.irreducible_of_eisenstein_criterion (P := Ideal.span {(2 : ℤ)})
  · -- (2) is a prime ideal in ℤ
    rw [Ideal.span_singleton_prime (show (2 : ℤ) ≠ 0 from by norm_num)]
    exact Int.prime_iff_natAbs_prime.mpr (by norm_num)
  · -- leadingCoeff ∉ (2)
    rw [show p_int.leadingCoeff = 1 from p_int_monic, Ideal.mem_span_singleton]
    norm_num
  · -- ∀ k < degree, coeff k ∈ (2)
    intro k hk
    rw [p_int_degree] at hk
    have hkn : k < 5 := WithBot.coe_lt_coe.mp hk
    simp only [Ideal.mem_span_singleton]
    unfold p_int
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    interval_cases k <;> norm_num
  · -- 0 < degree
    rw [p_int_degree]; exact_mod_cast Nat.zero_lt_succ 4
  · -- coeff 0 ∉ (2)²
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    unfold p_int
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    norm_num
  · -- isPrimitive: monic → primitive
    exact p_int_monic.isPrimitive

/-- p is irreducible over ℚ.

    Proof: Eisenstein's criterion at p = 2 gives ℤ-irreducibility.
    Gauss's lemma (monic → primitive) transfers to ℚ. -/
theorem p_irreducible : Irreducible p := by
  have hprim := p_int_monic.isPrimitive
  have hirr := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp p_int_irreducible
  convert hirr using 1
  unfold p p_int
  simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow]
  norm_cast

-- ============================================================================
-- Part III: Basic Structural Properties
-- ============================================================================

/-- p has natDegree 5. -/
theorem p_natDegree : p.natDegree = 5 := by
  unfold p; compute_degree!

/-- p is monic (leading coefficient = 1). -/
theorem p_monic : p.Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, p_natDegree]
  unfold p
  simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

/-- p is separable (irreducible in characteristic 0). -/
theorem p_separable : p.Separable := p_irreducible.separable

/-- The root set of p in its splitting field has exactly 5 elements. -/
theorem p_rootSet_card :
    Fintype.card (p.rootSet p.SplittingField) = 5 :=
  (Polynomial.card_rootSet_eq_natDegree p_separable
    (Polynomial.SplittingField.splits p)).trans p_natDegree

-- ============================================================================
-- Part IV: Galois Group Structure
-- ============================================================================

/-- 5 divides |Gal(p/ℚ)| (since p is irreducible of prime degree 5). -/
theorem five_dvd_gal_card :
    5 ∣ Fintype.card p.Gal := by
  have h := Polynomial.Gal.prime_degree_dvd_card p_irreducible
    (by rw [p_natDegree]; decide : Nat.Prime p.natDegree)
  rw [p_natDegree, Nat.card_eq_fintype_card] at h
  exact h

/-- |Gal(p/ℚ)| divides 120 = 5! (Gal embeds into S₅ via action on roots). -/
theorem gal_card_dvd_120 :
    Fintype.card p.Gal ∣ 120 := by
  haveI : Fact (map (algebraMap ℚ p.SplittingField) p).Splits :=
    ⟨Polynomial.SplittingField.splits p⟩
  have hinj := Polynomial.Gal.galActionHom_injective p p.SplittingField
  have hdvd : Nat.card p.Gal ∣ Nat.card (Equiv.Perm (p.rootSet p.SplittingField)) :=
    Subgroup.card_dvd_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hdvd
  rw [Fintype.card_perm, p_rootSet_card] at hdvd
  simpa using hdvd

-- ============================================================================
-- Part V: Polynomial Evaluation (toward eliminating gal_card_eq_120)
-- ============================================================================

/-- p(-2) = -22 (negative). -/
theorem p_eval_neg2 : p.eval (-2 : ℚ) = -22 := by unfold p; simp [eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X]; try ring

/-- p(-1) = 5 (positive). -/
theorem p_eval_neg1 : p.eval (-1 : ℚ) = 5 := by unfold p; simp [eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X]; try ring

/-- p(0) = 2 (positive). -/
theorem p_eval_0 : p.eval (0 : ℚ) = 2 := by unfold p; simp [eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X]; try ring

/-- p(1) = -1 (negative). -/
theorem p_eval_1 : p.eval (1 : ℚ) = -1 := by unfold p; simp [eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X]; try ring

/-- p(2) = 26 (positive). -/
theorem p_eval_2 : p.eval (2 : ℚ) = 26 := by unfold p; simp [eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X]; try ring

/-
These evaluations show 3 sign changes: p has at least 3 real roots.
  p(-2) = -22 < 0,  p(-1) = 5 > 0   → root in (-2, -1)
  p(0)  = 2 > 0,    p(1) = -1 < 0   → root in (0, 1)
  p(1)  = -1 < 0,   p(2) = 26 > 0   → root in (1, 2)

Combined with p' = 5x⁴ - 4 having exactly 2 real roots (hence p has
at most 3 real roots by Rolle's theorem), p has EXACTLY 3 real roots.

This means 2 roots are complex conjugate. Complex conjugation induces
a transposition in the Galois group. A transitive subgroup of S₅
(5 prime) containing a transposition is S₅ itself. Hence |Gal| = 120.
-/

-- ============================================================================
-- Part V(b): Group Theory — 5-Cycle + Transposition Generates S₅
-- ============================================================================

/-
## Key Group Theory Lemma

A transitive subgroup of S₅ containing a transposition is S₅.

**Proof**: By conjugating the transposition with the 5-cycle (guaranteed by
transitivity + prime degree), we generate all 10 transpositions. Since every
permutation is a product of transpositions, the subgroup is S₅.

The chain:
  1. swap(k, k+1) = c₅ᵏ · swap(0,1) · c₅⁻ᵏ          (adjacent swaps)
  2. swap(0, k+1) = swap(0,k) · swap(k,k+1) · swap(0,k)  (star swaps)
  3. swap(a, b) = swap(0,a) · swap(0,b) · swap(0,a)       (all swaps)
-/

-- The standard 5-cycle (0 1 2 3 4)
private def c5 : Equiv.Perm (Fin 5) where
  toFun := fun i => ⟨(i.val + 1) % 5, Nat.mod_lt _ (by omega)⟩
  invFun := fun i => ⟨(i.val + 4) % 5, Nat.mod_lt _ (by omega)⟩
  left_inv := by intro ⟨i, hi⟩; simp [Fin.ext_iff]; omega
  right_inv := by intro ⟨i, hi⟩; simp [Fin.ext_iff]; omega

-- ============================================================================
-- Part V(c): Galois Group Infrastructure
-- ============================================================================

/-- The splitting field is a Galois extension. -/
instance : Normal ℚ p.SplittingField := inferInstance
instance : Algebra.IsSeparable ℚ p.SplittingField := inferInstance

/-- The map (algebraMap ...) p splits in the splitting field. -/
instance p_splits_fact : Fact (map (algebraMap ℚ p.SplittingField) p).Splits :=
  ⟨Polynomial.SplittingField.splits p⟩

/-- Permutation homomorphism from Gal(p) to Perm(rootSet) using galActionAux.
    Uses galActionAux (direct action) to avoid an instance diamond between
    galActionAux and galAction when E = SplittingField. -/
private noncomputable def galPermHomAux : p.Gal →* Equiv.Perm (p.rootSet p.SplittingField) :=
  @MulAction.toPermHom _ _ _ (@Polynomial.Gal.galActionAux ℚ _ p)

/-- galPermHomAux is injective — the Galois group acts faithfully on roots. -/
private theorem galPermHomAux_injective : Function.Injective galPermHomAux := by
  rw [injective_iff_map_eq_one]
  intro ϕ hϕ
  ext (x hx)
  exact congrArg Subtype.val (Equiv.Perm.ext_iff.mp hϕ ⟨x, hx⟩)

/-- Composite injection Gal(p) →* Perm(Fin 5) via root enumeration. -/
noncomputable def galToPerm5 : p.Gal →* Equiv.Perm (Fin 5) :=
  let rootEquiv : p.rootSet p.SplittingField ≃ Fin 5 :=
    Fintype.equivOfCardEq (by rw [p_rootSet_card, Fintype.card_fin])
  let permEquiv : Equiv.Perm (p.rootSet p.SplittingField) ≃* Equiv.Perm (Fin 5) :=
    { toEquiv := Equiv.permCongr rootEquiv
      map_mul' := fun σ τ => by
        ext x; simp [Equiv.permCongr_apply, Equiv.Perm.mul_apply] }
  permEquiv.toMonoidHom.comp galPermHomAux

/-- galToPerm5 is injective. -/
theorem galToPerm5_injective : Function.Injective galToPerm5 := by
  unfold galToPerm5
  exact (Equiv.permCongr
    (Fintype.equivOfCardEq (by rw [p_rootSet_card, Fintype.card_fin]))).injective.comp
    galPermHomAux_injective

/-- The sign of a Galois element in S₅. -/
noncomputable def galSign (σ : p.Gal) : ℤˣ :=
  Equiv.Perm.sign (galToPerm5 σ)

-- ============================================================================
-- Part V(d): Structural Lemmas — No Subgroups of Order 15 or 30 in S₅
-- ============================================================================

/-- No subgroup of S₅ has order 15.

    Proof: In any group of order 15 = 3·5, Sylow theory gives unique
    normal P₅ and P₃. Their elements commute. But no order-5 element
    commutes with any order-3 element in S₅ (native_decide). -/
theorem no_subgroup_order_15 (H : Subgroup (Equiv.Perm (Fin 5)))
    (hcard : Nat.card H = 15) : False := by
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI hft : Fintype H := Fintype.ofFinite H
  have hcard_ft : Fintype.card H = 15 := by rwa [Nat.card_eq_fintype_card] at hcard
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card (p := 5)
    (show 5 ∣ Fintype.card H by rw [hcard_ft]; norm_num)
  obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card (p := 3)
    (show 3 ∣ Fintype.card H by rw [hcard_ft]; norm_num)
  have hσ5 : (σ : Equiv.Perm (Fin 5)) ^ 5 = 1 := by
    have : σ ^ 5 = (1 : ↥H) :=
      calc σ ^ 5 = σ ^ orderOf σ := by congr 1; exact hσ.symm
        _ = 1 := pow_orderOf_eq_one σ
    simpa using congr_arg Subtype.val this
  have hσ_ne : (σ : Equiv.Perm (Fin 5)) ≠ 1 := by
    intro heq
    exact absurd hσ (by rw [show σ = (1 : ↥H) from Subtype.ext heq, orderOf_one]; norm_num)
  have hτ3 : (τ : Equiv.Perm (Fin 5)) ^ 3 = 1 := by
    have : τ ^ 3 = (1 : ↥H) :=
      calc τ ^ 3 = τ ^ orderOf τ := by congr 1; exact hτ.symm
        _ = 1 := pow_orderOf_eq_one τ
    simpa using congr_arg Subtype.val this
  have hτ_ne : (τ : Equiv.Perm (Fin 5)) ≠ 1 := by
    intro heq
    exact absurd hτ (by rw [show τ = (1 : ↥H) from Subtype.ext heq, orderOf_one]; norm_num)
  exact perm_fin5_order5_order3_not_commute _ _ hσ5 hσ_ne hτ3 hτ_ne (by
    suffices hsuff : (σ : ↥H) * τ = τ * σ by
      have h1 := congr_arg Subtype.val hsuff
      simp only [Subgroup.coe_mul] at h1; exact h1
    have hn₅ : Nat.card (Sylow 5 ↥H) = 1 := by
      have h_mod := card_sylow_modEq_one 5 ↥H
      obtain ⟨P⟩ := Sylow.nonempty (p := 5) (G := ↥H)
      have h_P_card : Nat.card (↑P : Subgroup ↥H) = 5 := by
        rw [P.card_eq_multiplicity, hcard]; native_decide
      have h_idx : (↑P : Subgroup ↥H).index = 3 := by
        have := (↑P : Subgroup ↥H).index_mul_card; rw [h_P_card, hcard] at this; omega
      have h_dvd := Sylow.card_dvd_index P; rw [h_idx] at h_dvd
      rcases (by norm_num : Nat.Prime 3).eq_one_or_self_of_dvd _ h_dvd with h | h
      · exact h
      · exfalso; rw [h] at h_mod; simp [Nat.ModEq] at h_mod
    haveI : Subsingleton (Sylow 5 ↥H) := by
      haveI := Fintype.ofFinite (Sylow 5 ↥H)
      rw [← Fintype.card_le_one_iff_subsingleton, ← Nat.card_eq_fintype_card]; omega
    have hn₃ : Nat.card (Sylow 3 ↥H) = 1 := by
      have h_mod := card_sylow_modEq_one 3 ↥H
      obtain ⟨P⟩ := Sylow.nonempty (p := 3) (G := ↥H)
      have h_P_card : Nat.card (↑P : Subgroup ↥H) = 3 := by
        rw [P.card_eq_multiplicity, hcard]; native_decide
      have h_idx : (↑P : Subgroup ↥H).index = 5 := by
        have := (↑P : Subgroup ↥H).index_mul_card; rw [h_P_card, hcard] at this; omega
      have h_dvd := Sylow.card_dvd_index P; rw [h_idx] at h_dvd
      rcases (by norm_num : Nat.Prime 5).eq_one_or_self_of_dvd _ h_dvd with h | h
      · exact h
      · exfalso; rw [h] at h_mod; simp [Nat.ModEq] at h_mod
    haveI : Subsingleton (Sylow 3 ↥H) := by
      haveI := Fintype.ofFinite (Sylow 3 ↥H)
      rw [← Fintype.card_le_one_iff_subsingleton, ← Nat.card_eq_fintype_card]; omega
    obtain ⟨P₅⟩ := Sylow.nonempty (p := 5) (G := ↥H)
    obtain ⟨P₃⟩ := Sylow.nonempty (p := 3) (G := ↥H)
    haveI hN₅ : (↑P₅ : Subgroup ↥H).Normal := by
      apply Subgroup.Normal.mk; intro n hn g
      have : g • P₅ = P₅ := Subsingleton.elim _ _
      rw [Sylow.smul_eq_iff_mem_normalizer] at this
      exact ((Subgroup.mem_normalizer_iff.mp this) n).mp hn
    haveI hN₃ : (↑P₃ : Subgroup ↥H).Normal := by
      apply Subgroup.Normal.mk; intro n hn g
      have : g • P₃ = P₃ := Subsingleton.elim _ _
      rw [Sylow.smul_eq_iff_mem_normalizer] at this
      exact ((Subgroup.mem_normalizer_iff.mp this) n).mp hn
    have hσ_mem : σ ∈ (↑P₅ : Subgroup ↥H) := by
      have h_pg : IsPGroup 5 (Subgroup.zpowers σ) :=
        IsPGroup.iff_card.mpr ⟨1, by rw [pow_one, Nat.card_zpowers, hσ]⟩
      obtain ⟨Q, hQ⟩ := h_pg.exists_le_sylow
      exact (show Q = P₅ from Subsingleton.elim Q P₅) ▸ hQ (Subgroup.mem_zpowers σ)
    have hτ_mem : τ ∈ (↑P₃ : Subgroup ↥H) := by
      have h_pg : IsPGroup 3 (Subgroup.zpowers τ) :=
        IsPGroup.iff_card.mpr ⟨1, by rw [pow_one, Nat.card_zpowers, hτ]⟩
      obtain ⟨Q, hQ⟩ := h_pg.exists_le_sylow
      exact (show Q = P₃ from Subsingleton.elim Q P₃) ▸ hQ (Subgroup.mem_zpowers τ)
    set c := σ * τ * σ⁻¹ * τ⁻¹ with hc_def
    have hc₅ : c ∈ (↑P₅ : Subgroup ↥H) := by
      rw [hc_def]; show σ * τ * σ⁻¹ * τ⁻¹ ∈ ↑P₅
      have := hN₅.conj_mem σ⁻¹ ((↑P₅ : Subgroup ↥H).inv_mem hσ_mem) τ
      have hprod := (↑P₅ : Subgroup ↥H).mul_mem hσ_mem this
      convert hprod using 1
    have hc₃ : c ∈ (↑P₃ : Subgroup ↥H) := by
      rw [hc_def]; show σ * τ * σ⁻¹ * τ⁻¹ ∈ ↑P₃
      have := hN₃.conj_mem τ hτ_mem σ
      exact (↑P₃ : Subgroup ↥H).mul_mem this ((↑P₃ : Subgroup ↥H).inv_mem hτ_mem)
    have hc_one : c = 1 := by
      have ⟨k₅, hk₅⟩ := P₅.isPGroup' ⟨c, hc₅⟩
      have ⟨k₃, hk₃⟩ := P₃.isPGroup' ⟨c, hc₃⟩
      have h5 : orderOf c ∣ 5 ^ k₅ := orderOf_dvd_of_pow_eq_one (by
        simpa using congr_arg Subtype.val hk₅)
      have h3 : orderOf c ∣ 3 ^ k₃ := orderOf_dvd_of_pow_eq_one (by
        simpa using congr_arg Subtype.val hk₃)
      have hcop : Nat.Coprime (5 ^ k₅) (3 ^ k₃) := (by norm_num : Nat.Coprime 5 3).pow k₅ k₃
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h5 h3))
    rw [show σ * τ = c * (τ * σ) from by simp only [hc_def]; group, hc_one, one_mul])

/-- A₅ has 60 elements. -/
theorem a5_card : Fintype.card (alternatingGroup (Fin 5)) = 60 := by
  native_decide

/-- No subgroup of S₅ has order 30.

    Proof: If H ≤ S₅ has |H| = 30, then H ∩ A₅ has order 15 or 30.
    Order 30 → H ⊆ A₅, index 2, normal, contradicts A₅ simple.
    Order 15 → contradicts no_subgroup_order_15. -/
theorem no_subgroup_order_30 (H : Subgroup (Equiv.Perm (Fin 5)))
    (hcard : Nat.card H = 30) : False := by
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype H := Fintype.ofFinite H
  by_cases hle : H ≤ alternatingGroup (Fin 5)
  · let H' := H.subgroupOf (alternatingGroup (Fin 5))
    have hH'_card : Nat.card ↥H' = 30 := by
      rw [show Nat.card ↥H' = Nat.card ↥H from
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard]
    have hA5_card : Nat.card (alternatingGroup (Fin 5) : Type _) = 60 := by
      rw [Nat.card_eq_fintype_card]; decide
    have hindex : H'.index = 2 := by
      have := Subgroup.card_mul_index H'
      rw [hA5_card, hH'_card] at this; omega
    haveI : H'.Normal := Subgroup.normal_of_index_eq_two hindex
    rcases alternatingGroup.isSimpleGroup_five.eq_bot_or_eq_top_of_normal H' inferInstance
      with h | h
    · rw [h] at hH'_card; simp at hH'_card
    · rw [h, Nat.card_congr Subgroup.topEquiv.toEquiv, hA5_card] at hH'_card
      norm_num at hH'_card
  · obtain ⟨x, hxH, hxA⟩ : ∃ x ∈ H, x ∉ alternatingGroup (Fin 5) := by
      by_contra h; push_neg at h; exact hle h
    let signH : ↥H →* ℤˣ := Equiv.Perm.sign.comp H.subtype
    let K := signH.ker.map H.subtype
    have hK_card : Nat.card ↥K = 15 := by
      have h_eq : Nat.card ↥K = Nat.card ↥signH.ker :=
        (Nat.card_congr
          (signH.ker.equivMapOfInjective H.subtype Subtype.val_injective).toEquiv).symm
      rw [h_eq]
      have h_mul := Subgroup.card_mul_index signH.ker
      have h_idx_dvd : signH.ker.index ∣ 2 := by
        have h_iso : signH.ker.index = Nat.card ↥signH.range := by
          rw [Subgroup.index]
          exact Nat.card_congr (QuotientGroup.quotientKerEquivRange signH).toEquiv
        rw [h_iso]
        calc Nat.card ↥signH.range
            ∣ Nat.card ℤˣ := Subgroup.card_subgroup_dvd_card signH.range
          _ = 2 := by rw [Nat.card_eq_fintype_card]; decide
      have h_idx_ne : signH.ker.index ≠ 1 := by
        intro heq
        have hker_top : signH.ker = ⊤ := Subgroup.index_eq_one.mp heq
        have : (⟨x, hxH⟩ : ↥H) ∈ signH.ker := hker_top ▸ Subgroup.mem_top _
        rw [MonoidHom.mem_ker] at this
        simp only [signH, MonoidHom.comp_apply, Subgroup.coe_subtype] at this
        exact hxA (Equiv.Perm.mem_alternatingGroup.mpr this)
      have h_idx : signH.ker.index = 2 :=
        (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) _ h_idx_dvd).resolve_left h_idx_ne
      rw [hcard, h_idx] at h_mul; omega
    exact no_subgroup_order_15 K hK_card

-- ============================================================================
-- Part V(e): Vandermonde Product and Discriminant → Odd Permutation
-- ============================================================================

/-
## Vandermonde Product Approach

The Vandermonde product Δ = det(vandermonde(rootEnum)) satisfies:
  σ(Δ) = sign(σ) · Δ for every σ ∈ Gal(p/ℚ).

If Δ² ∈ ℚ is not a perfect square, then Δ ∉ ℚ, so some σ has sign(σ) = -1.

For p = x⁵ - 4x + 2: disc(p) = Δ² = -212144 < 0 (not a perfect square in ℚ),
so Gal(p) contains an odd permutation (Gal ⊄ A₅).

The approach follows InverseGaloisA5.lean's Vandermonde infrastructure.
-/

-- Abbreviation for the splitting field
private abbrev SF := p.SplittingField

-- Section E1: Root Enumeration
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/-- Canonical enumeration of the 5 roots of p in its splitting field. -/
noncomputable def rootEnum : Fin 5 → SF :=
  fun i => ((Fintype.equivOfCardEq (by rw [p_rootSet_card, Fintype.card_fin]) :
    p.rootSet p.SplittingField ≃ Fin 5).symm i : SF)

/-- Each value of rootEnum is a root of p. -/
theorem rootEnum_is_root (i : Fin 5) :
    Polynomial.aeval (rootEnum i) p = 0 := by
  unfold rootEnum
  have hmem := ((Fintype.equivOfCardEq (by rw [p_rootSet_card, Fintype.card_fin]) :
    p.rootSet p.SplittingField ≃ Fin 5).symm i).prop
  rw [Polynomial.mem_rootSet] at hmem
  exact hmem.2

/-- The roots are distinct (p is separable). -/
theorem rootEnum_injective : Function.Injective rootEnum := by
  intro i j hij
  unfold rootEnum at hij
  have hsub : (Fintype.equivOfCardEq (by rw [p_rootSet_card, Fintype.card_fin]) :
    p.rootSet p.SplittingField ≃ Fin 5).symm i =
    (Fintype.equivOfCardEq (by rw [p_rootSet_card, Fintype.card_fin]) :
    p.rootSet p.SplittingField ≃ Fin 5).symm j := Subtype.ext hij
  exact (Fintype.equivOfCardEq (by rw [p_rootSet_card, Fintype.card_fin]) :
    p.rootSet p.SplittingField ≃ Fin 5).symm.injective hsub

-- Section E2: Vandermonde Product
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/-- The Vandermonde product of p's roots:
    Δ = det(vandermonde(rootEnum)) = ∏_{i<j} (rootEnum j - rootEnum i). -/
noncomputable def vandermondeProduct : SF :=
  Matrix.det (Matrix.vandermonde rootEnum)

/-- The Vandermonde product is nonzero (since p is separable, all roots are distinct). -/
theorem vandermondeProduct_ne_zero : vandermondeProduct ≠ 0 := by
  unfold vandermondeProduct
  rw [Matrix.det_vandermonde]
  intro h
  rw [Finset.prod_eq_zero_iff] at h
  obtain ⟨i, _, hi⟩ := h
  rw [Finset.prod_eq_zero_iff] at hi
  obtain ⟨j, hj, hij⟩ := hi
  have hne : j ≠ i := by simp [Finset.mem_Iio] at hj; omega
  exact hne (rootEnum_injective (sub_eq_zero.mp hij))

-- Section E3: Galois Action on Vandermonde Product
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/-- The Galois group permutes roots according to galToPerm5. -/
theorem gal_permutes_roots (σ : p.Gal) (i : Fin 5) :
    σ (rootEnum i) = rootEnum (galToPerm5 σ i) := by
  unfold rootEnum galToPerm5 galPermHomAux
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.coe_mk,
    Equiv.toFun_as_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    MulAction.toPermHom_apply]
  rfl

/-- Vandermonde with permuted input = row-permuted Vandermonde. -/
private theorem vandermonde_comp_eq_submatrix
    (v : Fin 5 → SF) (π : Equiv.Perm (Fin 5)) :
    Matrix.vandermonde (v ∘ π) = (Matrix.vandermonde v).submatrix π id := by
  ext i j; simp [Matrix.vandermonde, Matrix.submatrix, Function.comp]

/-- Vandermonde permutation: det(V(v ∘ π)) = sign(π) · det(V(v)). -/
private theorem vandermonde_perm_det
    (v : Fin 5 → SF) (π : Equiv.Perm (Fin 5)) :
    (Matrix.vandermonde (v ∘ π)).det =
    ↑↑(Equiv.Perm.sign π) * (Matrix.vandermonde v).det := by
  rw [vandermonde_comp_eq_submatrix]
  exact Matrix.det_permute π (Matrix.vandermonde v)

/-- σ maps the Vandermonde matrix entry-wise according to root permutation. -/
private theorem gal_map_vandermonde_entry (σ : p.Gal) (i j : Fin 5) :
    σ ((Matrix.vandermonde rootEnum) i j) =
    (Matrix.vandermonde (rootEnum ∘ galToPerm5 σ)) i j := by
  simp only [Matrix.vandermonde, Matrix.of_apply, Function.comp]
  rw [map_pow]
  congr 1
  exact gal_permutes_roots σ i

/-- **σ(Δ) = galSign(σ) · Δ** — the Galois action on the Vandermonde determinant
    equals the sign of the induced permutation times the determinant. -/
theorem gal_acts_on_vandermondeProduct (σ : p.Gal) :
    σ vandermondeProduct = ↑↑(galSign σ) * vandermondeProduct := by
  unfold vandermondeProduct galSign
  trans (Matrix.vandermonde (rootEnum ∘ galToPerm5 σ)).det
  · change σ.toAlgHom.toRingHom (Matrix.vandermonde rootEnum).det =
      (Matrix.vandermonde (rootEnum ∘ galToPerm5 σ)).det
    rw [RingHom.map_det]
    congr 1; ext i j
    simp only [RingHom.mapMatrix_apply]
    change σ ((Matrix.vandermonde rootEnum) i j) =
      (Matrix.vandermonde (rootEnum ∘ galToPerm5 σ)) i j
    exact gal_map_vandermonde_entry σ i j
  · exact vandermonde_perm_det rootEnum (galToPerm5 σ)

-- Section E4: Discriminant Value (Axiom)
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/-- **Axiom (discriminant computation)**: Δ² = -212144 in the splitting field.

    This is a verifiable computation: disc(x⁵-4x+2) = 256(-4)⁵+3125·2⁴ = -212144.
    The Sylvester matrix of p and p' = 5x⁴-4 is a 9×9 integer matrix whose
    determinant equals -212144.

    Axiomatized because computing resultants of explicit polynomials requires
    API that is not yet available in Lean4/Mathlib v4.26.0. -/
-- vandermondeProduct_sq_val: NOW A THEOREM (proved below)
private noncomputable def p_SF : Polynomial SF := Polynomial.map (algebraMap ℚ SF) p
set_option maxHeartbeats 800000 in
private theorem p_SF_eq_prod_linear : p_SF = ∏ i : Fin 5, (X - C (rootEnum i)) := by
  set P := ∏ i : Fin 5, (X - C (rootEnum i))
  have hq_monic : p_SF.Monic := p_monic.map (algebraMap ℚ SF)
  have hq_ne : p_SF ≠ 0 := hq_monic.ne_zero
  have hP_monic : P.Monic := Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)
  have hP_deg : P.natDegree = 5 := by rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)]; simp [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_fin]
  have hroot : ∀ i, Polynomial.IsRoot p_SF (rootEnum i) := fun i => by have := rootEnum_is_root i; rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at this
  have hcoprime : ∀ i j : Fin 5, i ≠ j → IsCoprime (X - C (rootEnum i) : Polynomial SF) (X - C (rootEnum j)) := by
    intro i j hij; have hne : rootEnum i ≠ rootEnum j := fun h => hij (rootEnum_injective h); have hne' : rootEnum j - rootEnum i ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    exact ⟨C ((rootEnum j - rootEnum i)⁻¹), -C ((rootEnum j - rootEnum i)⁻¹), by
      calc C ((rootEnum j - rootEnum i)⁻¹) * (X - C (rootEnum i)) + -C ((rootEnum j - rootEnum i)⁻¹) * (X - C (rootEnum j))
        _ = C ((rootEnum j - rootEnum i)⁻¹) * ((X - C (rootEnum i)) - (X - C (rootEnum j))) := by ring
        _ = C ((rootEnum j - rootEnum i)⁻¹) * C (rootEnum j - rootEnum i) := by
            congr 1; have : (X : Polynomial SF) - C (rootEnum i) - (X - C (rootEnum j)) = C (rootEnum j) - C (rootEnum i) := by ring
            rw [this, ← map_sub]
        _ = C ((rootEnum j - rootEnum i)⁻¹ * (rootEnum j - rootEnum i)) := by rw [← map_mul]
        _ = C 1 := by rw [inv_mul_cancel₀ hne']
        _ = 1 := map_one _⟩
  obtain ⟨r, hr⟩ := Finset.prod_dvd_of_coprime (fun i _ j _ hij => hcoprime i j hij) (fun i _ => Polynomial.dvd_iff_isRoot.mpr (hroot i))
  have r_ne : r ≠ 0 := right_ne_zero_of_mul (hr ▸ hq_ne)
  have hr_deg : r.natDegree = 0 := by have h1 := Polynomial.natDegree_mul hP_monic.ne_zero r_ne; rw [← hr, show p_SF.natDegree = 5 from by show (Polynomial.map (algebraMap ℚ SF) p).natDegree = 5; rw [Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ SF).injective, p_natDegree], hP_deg] at h1; omega
  have hr_one : r = 1 := by
    have h := Polynomial.eq_C_of_natDegree_eq_zero hr_deg
    have hrc : r.leadingCoeff = 1 := by
      have hm := hq_monic; rw [hr, Polynomial.Monic] at hm
      rw [Polynomial.leadingCoeff_mul, hP_monic.leadingCoeff, one_mul] at hm; exact hm
    rw [h, Polynomial.leadingCoeff_C] at hrc; rw [h, hrc, map_one]
  rw [hr, hr_one, mul_one]
private theorem eval_deriv_factor {K : Type*} [Field K] (f r : Polynomial K) (α : K) (hf : f = (X - C α) * r) : Polynomial.eval α (Polynomial.derivative f) = Polynomial.eval α r := by rw [hf, Polynomial.derivative_mul]; simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C, sub_zero, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, sub_self, zero_mul, add_zero, one_mul]
private theorem eval_deriv_at_root (i : Fin 5) : Polynomial.eval (rootEnum i) (Polynomial.derivative p_SF) = ∏ j ∈ Finset.univ.erase i, (rootEnum i - rootEnum j) := by
  rw [eval_deriv_factor p_SF _ (rootEnum i) (by rw [p_SF_eq_prod_linear]; exact (Finset.mul_prod_erase Finset.univ (fun j => X - C (rootEnum j)) (Finset.mem_univ i)).symm), Polynomial.eval_prod]; congr 1; ext j; simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
private theorem vp_sq_eq_ordered_diff : (∏ i : Fin 5, ∏ j ∈ Finset.univ.erase i, (rootEnum i - rootEnum j)) = vandermondeProduct ^ 2 := by
  have hsplit : ∀ i : Fin 5, ∏ j ∈ Finset.univ.erase i, (rootEnum i - rootEnum j) = (∏ j ∈ Finset.Iio i, (rootEnum i - rootEnum j)) * (∏ j ∈ Finset.Ioi i, (rootEnum i - rootEnum j)) := by
    intro i; rw [← Finset.prod_union (Finset.disjoint_left.mpr (fun x hx1 hx2 => by rw [Finset.mem_Iio] at hx1; rw [Finset.mem_Ioi] at hx2; omega))]; congr 1; ext j; constructor
    · intro hj; rw [Finset.mem_erase] at hj; rw [Finset.mem_union, Finset.mem_Iio, Finset.mem_Ioi]; exact (hj.1).lt_or_gt
    · intro hj; rw [Finset.mem_union, Finset.mem_Iio, Finset.mem_Ioi] at hj; rw [Finset.mem_erase]; refine ⟨?_, Finset.mem_univ _⟩; rcases hj with h | h; exact Fin.ne_of_lt h; exact Fin.ne_of_gt h
  simp_rw [hsplit, Finset.prod_mul_distrib]; unfold vandermondeProduct; rw [Matrix.det_vandermonde, sq]; congr 1
  · exact Finset.prod_comm' (fun i j => by simp only [Finset.mem_univ, Finset.mem_Iio, Finset.mem_Ioi, true_and, and_true])
  · have key : ∀ i : Fin 5, ∏ j ∈ Finset.Ioi i, (rootEnum i - rootEnum j) = (-1 : SF) ^ (Finset.Ioi i).card * ∏ j ∈ Finset.Ioi i, (rootEnum j - rootEnum i) := by
      intro i
      have hmul : ∀ j ∈ Finset.Ioi i, rootEnum i - rootEnum j = (-1 : SF) * (rootEnum j - rootEnum i) := fun _ _ => by ring
      rw [Finset.prod_congr rfl hmul, Finset.prod_mul_distrib, Finset.prod_const]
    simp_rw [key, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have : ∑ i : Fin 5, (Finset.Ioi i).card = 10 := by decide
    rw [this]; norm_num
private theorem root_poly_zero (i : Fin 5) : rootEnum i ^ 5 - algebraMap ℚ SF 4 * rootEnum i + algebraMap ℚ SF 2 = 0 := by
  have h := rootEnum_is_root i; change Polynomial.aeval (rootEnum i) (X ^ 5 - C 4 * X + C 2) = 0 at h
  simp only [map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at h; exact h
private theorem deriv_times_root (i : Fin 5) : (algebraMap ℚ SF 5 * rootEnum i ^ 4 - algebraMap ℚ SF 4) * rootEnum i = algebraMap ℚ SF 16 * rootEnum i - algebraMap ℚ SF 10 := by
  have h := root_poly_zero i
  -- (5r⁴-4)r - (16r-10) = 5(r⁵-4r+2) = 0 after converting constants
  have h16 : algebraMap ℚ SF 16 = algebraMap ℚ SF 5 * algebraMap ℚ SF 4 - algebraMap ℚ SF 4 := by
    rw [← map_mul, ← map_sub]; norm_num
  have h10 : algebraMap ℚ SF 10 = algebraMap ℚ SF 5 * algebraMap ℚ SF 2 := by
    rw [← map_mul]; norm_num
  have key : (algebraMap ℚ SF 5 * rootEnum i ^ 4 - algebraMap ℚ SF 4) * rootEnum i -
      (algebraMap ℚ SF 16 * rootEnum i - algebraMap ℚ SF 10) =
      algebraMap ℚ SF 5 * (rootEnum i ^ 5 - algebraMap ℚ SF 4 * rootEnum i + algebraMap ℚ SF 2) := by
    rw [h16, h10]; ring
  rw [h, mul_zero] at key
  exact sub_eq_zero.mp key
private theorem eval_deriv_val (i : Fin 5) : Polynomial.eval (rootEnum i) (Polynomial.derivative p_SF) = algebraMap ℚ SF 5 * rootEnum i ^ 4 - algebraMap ℚ SF 4 := by
  show Polynomial.eval (rootEnum i) (Polynomial.derivative (Polynomial.map (algebraMap ℚ SF) p)) = _; rw [Polynomial.derivative_map]
  have hd : Polynomial.derivative p = C 5 * X ^ 4 - C 4 := by ext n; unfold p; simp only [Polynomial.coeff_derivative, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X]; rcases n with _ | _ | _ | _ | _ | n <;> simp <;> ring
  rw [hd]; simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
private theorem vp_sq_times_prod : vandermondeProduct ^ 2 * (∏ i : Fin 5, rootEnum i) = ∏ i : Fin 5, (algebraMap ℚ SF 16 * rootEnum i - algebraMap ℚ SF 10) := by
  rw [show vandermondeProduct ^ 2 = ∏ i : Fin 5, Polynomial.eval (rootEnum i) (Polynomial.derivative p_SF) from by rw [← vp_sq_eq_ordered_diff]; congr 1; ext i; exact (eval_deriv_at_root i).symm, ← Finset.prod_mul_distrib]; congr 1; ext i; rw [eval_deriv_val]; exact deriv_times_root i
private theorem prod_roots_val : ∏ i : Fin 5, rootEnum i = algebraMap ℚ SF (-2) := by
  have heval : Polynomial.eval (0 : SF) p_SF = ∏ i : Fin 5, ((0 : SF) - rootEnum i) := by rw [p_SF_eq_prod_linear, Polynomial.eval_prod]; congr 1; ext i; simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hlhs : Polynomial.eval (0 : SF) p_SF = algebraMap ℚ SF 2 := by
    show Polynomial.eval (0 : SF) (Polynomial.map (algebraMap ℚ SF) p) = _; rw [Polynomial.eval_map, show (0 : SF) = algebraMap ℚ SF 0 from (map_zero _).symm]
    rw [show Polynomial.eval₂ (algebraMap ℚ SF) (algebraMap ℚ SF 0) p = algebraMap ℚ SF (Polynomial.eval 0 p) from Polynomial.aeval_algebraMap_apply SF 0 p, p_eval_0]
  have hrhs : ∏ i : Fin 5, ((0 : SF) - rootEnum i) = -(∏ i : Fin 5, rootEnum i) := by simp_rw [zero_sub]; rw [Finset.prod_neg, Finset.card_fin]; norm_num
  rw [hlhs, hrhs] at heval
  -- heval : algebraMap ℚ SF 2 = -(∏ rootEnum i)
  rw [show algebraMap ℚ SF (-2 : ℚ) = -(algebraMap ℚ SF 2) from map_neg (algebraMap ℚ SF) _]
  -- Goal: ∏ rootEnum i = -(algebraMap ℚ SF 2)
  -- From heval: -(∏ rootEnum i) = algebraMap ℚ SF 2, so ∏ rootEnum i = -(algebraMap ℚ SF 2)
  -- heval : algebraMap 2 = -(∏ r), goal: ∏ r = -(algebraMap 2)
  have h2 : -(algebraMap ℚ SF 2) = ∏ i : Fin 5, rootEnum i := by rw [heval, neg_neg]
  exact h2.symm
private theorem p_eval_5_8' : p.eval (5/8 : ℚ) = -13259/32768 := by unfold p; simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]; ring
/-- **THEOREM** (formerly axiom): Δ² = -212144 in the splitting field. -/
theorem vandermondeProduct_sq_val : vandermondeProduct ^ 2 = algebraMap ℚ SF (-212144) := by
  have hmul := vp_sq_times_prod; rw [prod_roots_val] at hmul
  have heval_sf : Polynomial.eval (algebraMap ℚ SF (5/8)) p_SF = ∏ i : Fin 5, (algebraMap ℚ SF (5/8) - rootEnum i) := by rw [p_SF_eq_prod_linear, Polynomial.eval_prod]; congr 1; ext i; simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have heval_val : Polynomial.eval (algebraMap ℚ SF (5/8)) p_SF = algebraMap ℚ SF (p.eval (5/8)) := by
    show Polynomial.eval _ (Polynomial.map (algebraMap ℚ SF) p) = _; rw [Polynomial.eval_map]
    rw [show Polynomial.eval₂ (algebraMap ℚ SF) (algebraMap ℚ SF (5/8 : ℚ)) p = algebraMap ℚ SF (Polynomial.eval (5/8) p) from Polynomial.aeval_algebraMap_apply SF (5/8 : ℚ) p]
  have h58 : algebraMap ℚ SF 16 * algebraMap ℚ SF (5/8 : ℚ) = algebraMap ℚ SF 10 := by rw [← map_mul]; norm_num
  have hterm : ∀ i : Fin 5, algebraMap ℚ SF 16 * rootEnum i - algebraMap ℚ SF 10 = -(algebraMap ℚ SF 16) * (algebraMap ℚ SF (5/8) - rootEnum i) := by intro i; linear_combination h58
  simp_rw [hterm, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin, ← heval_sf] at hmul
  -- hmul: VP² * algebraMap(-2) = (-(algebraMap 16))^5 * p_SF(5/8)
  have hneg5 : (-(algebraMap ℚ SF 16)) ^ 5 = -(algebraMap ℚ SF 16 ^ 5) := by ring
  rw [hneg5] at hmul
  rw [heval_val, p_eval_5_8'] at hmul
  have hrhs : -(algebraMap ℚ SF 16 ^ 5) * algebraMap ℚ SF (-13259/32768 : ℚ) = algebraMap ℚ SF 424288 := by rw [← map_pow, ← map_neg, ← map_mul]; congr 1; norm_num
  rw [hrhs] at hmul
  have hne : algebraMap ℚ SF (-2 : ℚ) ≠ (0 : SF) := by rw [Ne, ← map_zero (algebraMap ℚ SF)]; exact (algebraMap ℚ SF).injective.ne (by norm_num)
  rw [show algebraMap ℚ SF (-212144 : ℚ) = algebraMap ℚ SF 424288 * (algebraMap ℚ SF (-2 : ℚ))⁻¹ from by rw [← map_inv₀, ← map_mul]; congr 1; norm_num]
  exact (eq_mul_inv_iff_mul_eq₀ hne).mpr hmul

-- Section E5: Negative Discriminant → Odd Permutation
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/-- The Vandermonde product is NOT in the range of algebraMap ℚ SF.

    Proof: Δ² = algebraMap ℤ SF (-212144). If Δ = algebraMap ℚ SF r for some r,
    then r² = -212144 in ℚ. But r² ≥ 0 in ℚ (characteristic 0, ordered field),
    contradiction. -/
theorem vandermondeProduct_not_rational :
    vandermondeProduct ∉ Set.range (algebraMap ℚ SF) := by
  intro ⟨r, hr⟩
  have hinj : Function.Injective (algebraMap ℚ SF) := (algebraMap ℚ SF).injective
  have hr2 : r ^ 2 = (-212144 : ℚ) := hinj (by rw [map_pow, hr]; exact vandermondeProduct_sq_val)
  linarith [sq_nonneg r]

/-- Helper: in the Galois splitting field, elements fixed by ALL automorphisms
    lie in the base field ℚ.

    This is one direction of the Fundamental Theorem of Galois Theory.
    Proof: fixingSubgroup(⊥) = ⊤ (every ℚ-alg. aut. fixes ℚ), and by
    IsGalois.fixedField_fixingSubgroup, fixedField(fixingSubgroup(⊥)) = ⊥. -/
private theorem fixed_by_all_gal_is_rational (x : SF)
    (hfix : ∀ σ : SF ≃ₐ[ℚ] SF, σ x = x) :
    x ∈ Set.range (algebraMap ℚ SF) := by
  haveI : IsGalois ℚ SF := IsGalois.mk
  -- x ∈ fixedField(⊤)
  have hmem : x ∈ IntermediateField.fixedField (⊤ : Subgroup (SF ≃ₐ[ℚ] SF)) := by
    rw [IntermediateField.mem_fixedField_iff]
    exact fun σ _ => hfix σ
  -- fixingSubgroup(⊥) = ⊤: every automorphism fixes ℚ
  have hfix_bot : (⊥ : IntermediateField ℚ SF).fixingSubgroup = ⊤ := by
    rw [eq_top_iff]; intro σ _ y
    obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp y.prop
    show σ • (y : SF) = (y : SF)
    rw [show (y : SF) = algebraMap ℚ SF r from hr.symm]
    exact σ.commutes r
  -- fixedField(fixingSubgroup(⊥)) = ⊥ (FTGT)
  have hftgt : IntermediateField.fixedField (⊤ : Subgroup (SF ≃ₐ[ℚ] SF)) = ⊥ := by
    rw [← hfix_bot]; exact IsGalois.fixedField_fixingSubgroup ⊥
  rw [hftgt] at hmem
  exact IntermediateField.mem_bot.mp hmem

/-- Not all Galois signs are positive: some σ has galSign(σ) = -1.

    Proof: If all signs were +1, then σ(Δ) = Δ for all σ, which would mean
    Δ is fixed by the entire Galois group, hence Δ ∈ ℚ. But Δ ∉ ℚ. -/
theorem exists_odd_galSign :
    ∃ σ : p.Gal, galSign σ = -1 := by
  by_contra hall
  push_neg at hall
  have hall_one : ∀ σ : p.Gal, galSign σ = 1 := fun σ =>
    (Int.units_eq_one_or (galSign σ)).resolve_right (hall σ)
  have hfix : ∀ σ : p.Gal, σ vandermondeProduct = vandermondeProduct := by
    intro σ
    have h := gal_acts_on_vandermondeProduct σ
    rw [hall_one σ] at h; simpa using h
  exact vandermondeProduct_not_rational (fixed_by_all_gal_is_rational vandermondeProduct hfix)

/-- **THEOREM** (formerly Axiom B): The Galois group contains an odd permutation.
    Proved from the Vandermonde product approach and disc(p) = -212144 < 0. -/
theorem gal_has_odd_perm :
  ∃ σ : p.Gal, Equiv.Perm.sign (galToPerm5 σ) = -1 := exists_odd_galSign

-- ============================================================================
-- Part V(e2): Axiom Elimination via Complex Conjugation
-- ============================================================================

/-
## Strategy: Eliminating the three_dvd_gal_card axiom

We prove |Gal(p/ℚ)| ≠ 20 (hence = 120) without Dedekind's theorem.

**The argument:**
1. p has exactly 3 real roots (IVT: sign changes at (-2,-1), (0,1), (1,2);
   disc < 0 rules out 5 real roots)
2. Complex conjugation on the roots gives a transposition σ_conj ∈ Gal
   (fixes 3 real roots, swaps 2 complex conjugate roots)
3. F₂₀ (the only transitive subgroup of S₅ of order 20) contains NO
   transpositions (verified by `transposition_not_normalizing_5cycle`)
4. Therefore |Gal| ≠ 20, so |Gal| = 120

**Key fact used:** `transposition_not_normalizing_5cycle` (proved at top of file
by `native_decide`) shows that no transposition normalizes any 5-cycle in S₅.
The normalizer of a 5-cycle in S₅ is F₂₀, so no transposition lies in F₂₀.
-/

-- Section E6a: The Galois group contains a transposition
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/-- **The Galois group of p contains a transposition** (an odd involution).

    Proof sketch: Embed SF → ℂ via IsAlgClosed.lift. Complex conjugation
    (starRingEnd ℂ) composed with this embedding gives another ℚ-algebra
    hom SF → ℂ, which corresponds to some σ_conj ∈ Gal(SF/ℚ) by the
    normal extension property. Since p has 3 real roots (by IVT) and
    2 complex conjugate roots (disc < 0), σ_conj fixes 3 roots and
    swaps 2, i.e., it acts as a transposition.

    The IVT part: p(-2)=-22 < 0, p(-1)=5 > 0 → root in (-2,-1)
                  p(0)=2 > 0, p(1)=-1 < 0   → root in (0,1)
                  p(1)=-1 < 0, p(2)=26 > 0  → root in (1,2)
    Not all real: vandermondeProduct² = -212144 < 0, impossible if Δ ∈ ℝ.

    Proved via complex conjugation + Vandermonde discriminant. -/

-- Embedding and conjugation infrastructure
private noncomputable def sfEmb : SF →ₐ[ℚ] ℂ := IsAlgClosed.lift (R := ℚ)
private noncomputable scoped instance : Algebra SF ℂ := sfEmb.toRingHom.toAlgebra
private scoped instance : IsScalarTower ℚ SF ℂ :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext fun r => (sfEmb.commutes r).symm)
private noncomputable def conjHom : ℂ →ₐ[ℚ] ℂ where
  toFun := starRingEnd ℂ; map_one' := map_one _; map_mul' := map_mul _
  map_zero' := map_zero _; map_add' := map_add _
  commutes' r := by
    show starRingEnd ℂ (algebraMap ℚ ℂ r) = algebraMap ℚ ℂ r
    rw [IsScalarTower.algebraMap_apply ℚ ℝ ℂ]; exact Complex.conj_ofReal _
private noncomputable def sfConjEmb : SF →ₐ[ℚ] ℂ := conjHom.comp sfEmb
private noncomputable def conjGalAut : SF ≃ₐ[ℚ] SF := sfConjEmb.restrictNormal' SF
private theorem conjGalAut_spec (x : SF) :
    sfEmb (conjGalAut x) = starRingEnd ℂ (sfEmb x) := by
  have h := sfConjEmb.restrictNormal_commutes SF x
  simp only [Algebra.id.map_eq_id, RingHom.id_apply] at h
  exact h
private theorem conjGalAut_sq : conjGalAut ^ 2 = 1 := by
  ext x; apply sfEmb.injective; show sfEmb ((conjGalAut * conjGalAut) x) = sfEmb x
  simp only [AlgEquiv.mul_apply]; rw [conjGalAut_spec, conjGalAut_spec, Complex.conj_conj]
private noncomputable def conjGal : p.Gal := conjGalAut
private theorem galSign_conjGal : galSign conjGal = -1 := by
  by_contra h
  have h1 := (Int.units_eq_one_or (galSign conjGal)).resolve_right h
  have hact := gal_acts_on_vandermondeProduct conjGal; rw [h1] at hact; simp at hact
  have hconj : starRingEnd ℂ (sfEmb vandermondeProduct) = sfEmb vandermondeProduct := by
    rw [← conjGalAut_spec]; exact congrArg sfEmb hact
  have him : (sfEmb vandermondeProduct).im = 0 := Complex.conj_eq_iff_im.mp hconj
  have hval : sfEmb vandermondeProduct ^ 2 = (-212144 : ℂ) := by
    rw [← map_pow sfEmb, vandermondeProduct_sq_val, sfEmb.commutes]; push_cast; norm_num
  have hre : sfEmb vandermondeProduct = ↑(sfEmb vandermondeProduct).re :=
    Complex.ext rfl (by simp [him])
  rw [hre] at hval
  have : ((sfEmb vandermondeProduct).re ^ 2 : ℝ) = -212144 := by
    exact_mod_cast hval
  linarith [sq_nonneg (sfEmb vandermondeProduct).re]

theorem gal_has_transposition :
    ∃ σ : p.Gal, (galToPerm5 σ) ^ 2 = 1 ∧ galToPerm5 σ ≠ 1 ∧
      Equiv.Perm.sign (galToPerm5 σ) = -1 := by
  refine ⟨conjGal, ?_, ?_, ?_⟩
  · rw [← map_pow, show conjGal ^ 2 = 1 from conjGalAut_sq, map_one]
  · intro heq; have : galSign conjGal = 1 := by unfold galSign; rw [heq, Equiv.Perm.sign_one]
    exact absurd galSign_conjGal (by rw [this]; decide)
  · exact galSign_conjGal

-- Section E6b: |Gal| ≠ 20 (from transposition + F₂₀ structure)
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/-- |Gal(p/ℚ)| ≠ 20: The Galois group image in S₅ contains a transposition,
    but the unique transitive order-20 subgroup F₂₀ ⊂ S₅ contains no
    transpositions. This uses `transposition_not_normalizing_5cycle`:
    no transposition normalizes any 5-cycle, hence no transposition
    lies in the normalizer N_{S₅}(⟨5-cycle⟩) = F₂₀. -/
private theorem gal_card_ne_20 : Fintype.card p.Gal ≠ 20 := by
  intro hc
  -- Get the transposition in the Galois group image
  obtain ⟨σ, hσ2, hσ_ne, hσ_sign⟩ := gal_has_transposition
  -- Get the 5-cycle from five_dvd_gal_card + Cauchy's theorem
  -- The image galToPerm5.range has order 20 and is transitive on Fin 5.
  -- It contains a 5-cycle (from 5 | 20 + Cauchy) and a transposition.
  -- But transposition_not_normalizing_5cycle says no transposition normalizes
  -- any 5-cycle. The normalizer of any Sylow 5-subgroup in a transitive
  -- order-20 subgroup of S₅ IS the whole group (since F₂₀ has a unique
  -- Sylow 5-subgroup, which is normal). So every element normalizes the
  -- 5-cycle, contradicting transposition_not_normalizing_5cycle.
  --
  -- More concretely: in a group of order 20 with 5 | |G|, the Sylow
  -- 5-subgroup is unique (by Sylow's theorem: n₅ | 4 and n₅ ≡ 1 mod 5,
  -- so n₅ = 1). So ⟨c⟩ ◁ G where c is a 5-cycle. Then every element
  -- normalizes c, i.e., σ·c·σ⁻¹ ∈ {c, c², c³, c⁴}.
  -- But transposition_not_normalizing_5cycle says this fails for transpositions.
  --
  -- Full Sylow proof: unique normal Sylow 5-subgroup in order-20 group
  set G := galToPerm5.range
  have hG_card : Nat.card G = 20 := by
    rw [show Nat.card G = Nat.card p.Gal from
      Nat.card_congr (Equiv.ofBijective galToPerm5.rangeRestrict
        ⟨fun a b h => galToPerm5_injective (congrArg Subtype.val h),
         galToPerm5.rangeRestrict_surjective⟩).symm, Nat.card_eq_fintype_card, hc]
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG_card]; norm_num)
  haveI : Fintype G := Fintype.ofFinite G
  have hG_ft : Fintype.card G = 20 := by rwa [Nat.card_eq_fintype_card] at hG_card
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨c, hc_ord⟩ := exists_prime_orderOf_dvd_card (p := 5) (by rw [hG_ft]; norm_num)
  have hc5 : (c : Equiv.Perm (Fin 5)) ^ 5 = 1 := by
    have h : c ^ orderOf c = (1 : G) := pow_orderOf_eq_one c
    rw [hc_ord] at h; simpa using congr_arg Subtype.val h
  have hc_ne : (c : Equiv.Perm (Fin 5)) ≠ 1 := fun h =>
    absurd hc_ord (by rw [show c = (1 : G) from Subtype.ext h, orderOf_one]; norm_num)
  set σ' : G := ⟨galToPerm5 σ, ⟨σ, rfl⟩⟩
  obtain ⟨P₅⟩ := Sylow.nonempty (p := 5) (G := G)
  have hP_card : Nat.card (↑P₅ : Subgroup G) = 5 := by
    rw [P₅.card_eq_multiplicity, hG_card]; native_decide
  have : Nat.card (Sylow 5 G) = 1 := by
    have h_mod := card_sylow_modEq_one 5 G
    have h_idx : (↑P₅ : Subgroup G).index = 4 := by
      have := (↑P₅ : Subgroup G).index_mul_card; rw [hP_card, hG_card] at this; omega
    have h_dvd := Sylow.card_dvd_index P₅; rw [h_idx] at h_dvd
    have h_le : Nat.card (Sylow 5 G) ≤ 4 := Nat.le_of_dvd (by norm_num) h_dvd
    have h_pos : 0 < Nat.card (Sylow 5 G) := Nat.card_pos
    rw [Nat.ModEq] at h_mod
    interval_cases (Nat.card (Sylow 5 G)) <;> omega
  haveI : Subsingleton (Sylow 5 G) := by
    haveI := Fintype.ofFinite (Sylow 5 G)
    rw [← Fintype.card_le_one_iff_subsingleton, ← Nat.card_eq_fintype_card]; omega
  haveI hNP : (↑P₅ : Subgroup G).Normal := by
    apply Subgroup.Normal.mk; intro n hn g
    have : g • P₅ = P₅ := Subsingleton.elim _ _; rw [Sylow.smul_eq_iff_mem_normalizer] at this
    exact ((Subgroup.mem_normalizer_iff.mp this) n).mp hn
  have hc_P5 : c ∈ (↑P₅ : Subgroup G) := by
    have h_pg : IsPGroup 5 (Subgroup.zpowers c) :=
      IsPGroup.iff_card.mpr ⟨1, by rw [pow_one, Nat.card_zpowers, hc_ord]⟩
    obtain ⟨Q, hQ⟩ := h_pg.exists_le_sylow
    exact (Subsingleton.elim Q P₅ : Q = P₅) ▸ hQ (Subgroup.mem_zpowers c)
  have hzpow_le : Subgroup.zpowers c ≤ ↑P₅ := fun x hx => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (↑P₅ : Subgroup G).zpow_mem hc_P5 k
  have hP5_eq : (↑P₅ : Subgroup G) = Subgroup.zpowers c := by
    apply le_antisymm _ hzpow_le
    intro x hx
    have hbij : Function.Bijective (Subgroup.inclusion hzpow_le) := by
      haveI := Fintype.ofFinite ↥(↑P₅ : Subgroup G)
      haveI := Fintype.ofFinite ↥(Subgroup.zpowers c)
      exact (Fintype.bijective_iff_injective_and_card _).mpr
        ⟨Subgroup.inclusion_injective _, by
          rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
              Nat.card_zpowers, hc_ord, hP_card]⟩
    obtain ⟨⟨y, hy⟩, hxy⟩ := hbij.surjective ⟨x, hx⟩
    rwa [show y = x from congr_arg Subtype.val hxy] at hy
  have hconj_zpow : σ' * c * σ'⁻¹ ∈ Subgroup.zpowers c :=
    (SetLike.ext_iff.mp hP5_eq _).mp (hNP.conj_mem c hc_P5 σ')
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hconj_zpow
  have hσ_inv : (galToPerm5 σ)⁻¹ = galToPerm5 σ :=
    inv_eq_iff_mul_eq_one.mpr (by rw [← sq]; exact hσ2)
  have hconj_val : galToPerm5 σ * ↑c * galToPerm5 σ = (↑c : Equiv.Perm (Fin 5)) ^ k := by
    have h := congr_arg Subtype.val hk
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow, σ'] at h
    rw [hσ_inv] at h; exact h.symm
  have ⟨hn1, hn2, hn3, hn4⟩ := transposition_not_normalizing_5cycle
    ↑c (galToPerm5 σ) hc5 hc_ne hσ_sign hσ2
  have hck_ne : (↑c : Equiv.Perm (Fin 5)) ^ k ≠ 1 := by
    rw [← hconj_val]; intro h
    have h1 : σ' * c * σ'⁻¹ = (1 : G) :=
      Subtype.ext (by simp only [σ', Subgroup.coe_mul, Subgroup.coe_inv]; rw [hσ_inv]; exact h)
    have hc1 : c = 1 := by have := (by group : c = σ'⁻¹ * (σ' * c * σ'⁻¹) * σ'); rw [h1] at this; simpa using this
    exact hc_ne (congr_arg Subtype.val hc1)
  have hred : (↑c : Equiv.Perm (Fin 5)) ^ k = (↑c) ^ (k % 5).toNat := by
    have hdiv : k = 5 * (k / 5) + k % 5 := by omega
    conv_lhs => rw [hdiv]
    rw [zpow_add, zpow_mul]
    have h5z : (↑c : Equiv.Perm (Fin 5)) ^ (5 : ℤ) = 1 := by
      rw [show (5 : ℤ) = ↑(5 : ℕ) from by norm_cast, zpow_natCast]; exact_mod_cast hc5
    rw [h5z, one_zpow, one_mul]
    conv_lhs => rw [(Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))).symm]
    simp only [zpow_natCast]
  rw [hred] at hconj_val hck_ne
  have hbound : (k % 5).toNat < 5 := by
    rw [Int.toNat_lt (by omega)]; exact Int.emod_lt_of_pos k (by norm_num)
  exfalso; interval_cases (k % 5).toNat <;> simp_all

-- Section E6b2: |Gal| ≠ 10 (same Sylow argument as ne_20)
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/-- |Gal(p/ℚ)| ≠ 10: Same Sylow argument as ne_20. The unique normal
    Sylow 5-subgroup P₅ = ⟨5-cycle⟩ is normalized by every element,
    but transpositions don't normalize 5-cycles. -/
private theorem gal_card_ne_10 : Fintype.card p.Gal ≠ 10 := by
  intro hc
  obtain ⟨σ, hσ2, hσ_ne, hσ_sign⟩ := gal_has_transposition
  set G := galToPerm5.range
  have hG_card : Nat.card G = 10 := by
    rw [show Nat.card G = Nat.card p.Gal from
      Nat.card_congr (Equiv.ofBijective galToPerm5.rangeRestrict
        ⟨fun a b h => galToPerm5_injective (congrArg Subtype.val h),
         galToPerm5.rangeRestrict_surjective⟩).symm, Nat.card_eq_fintype_card, hc]
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG_card]; norm_num)
  haveI : Fintype G := Fintype.ofFinite G
  have hG_ft : Fintype.card G = 10 := by rwa [Nat.card_eq_fintype_card] at hG_card
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨c, hc_ord⟩ := exists_prime_orderOf_dvd_card (p := 5) (by rw [hG_ft]; norm_num)
  have hc5 : (c : Equiv.Perm (Fin 5)) ^ 5 = 1 := by
    have h : c ^ orderOf c = (1 : G) := pow_orderOf_eq_one c
    rw [hc_ord] at h; simpa using congr_arg Subtype.val h
  have hc_ne : (c : Equiv.Perm (Fin 5)) ≠ 1 := fun h =>
    absurd hc_ord (by rw [show c = (1 : G) from Subtype.ext h, orderOf_one]; norm_num)
  set σ' : G := ⟨galToPerm5 σ, ⟨σ, rfl⟩⟩
  obtain ⟨P₅⟩ := Sylow.nonempty (p := 5) (G := G)
  have hP_card : Nat.card (↑P₅ : Subgroup G) = 5 := by
    rw [P₅.card_eq_multiplicity, hG_card]; native_decide
  have : Nat.card (Sylow 5 G) = 1 := by
    have h_mod := card_sylow_modEq_one 5 G
    have h_idx : (↑P₅ : Subgroup G).index = 2 := by
      have := (↑P₅ : Subgroup G).index_mul_card; rw [hP_card, hG_card] at this; omega
    have h_dvd := Sylow.card_dvd_index P₅; rw [h_idx] at h_dvd
    have h_le : Nat.card (Sylow 5 G) ≤ 2 := Nat.le_of_dvd (by norm_num) h_dvd
    have h_pos : 0 < Nat.card (Sylow 5 G) := Nat.card_pos
    rw [Nat.ModEq] at h_mod
    interval_cases (Nat.card (Sylow 5 G)) <;> omega
  haveI : Subsingleton (Sylow 5 G) := by
    haveI := Fintype.ofFinite (Sylow 5 G)
    rw [← Fintype.card_le_one_iff_subsingleton, ← Nat.card_eq_fintype_card]; omega
  haveI hNP : (↑P₅ : Subgroup G).Normal := by
    apply Subgroup.Normal.mk; intro n hn g
    have : g • P₅ = P₅ := Subsingleton.elim _ _; rw [Sylow.smul_eq_iff_mem_normalizer] at this
    exact ((Subgroup.mem_normalizer_iff.mp this) n).mp hn
  have hc_P5 : c ∈ (↑P₅ : Subgroup G) := by
    have h_pg : IsPGroup 5 (Subgroup.zpowers c) :=
      IsPGroup.iff_card.mpr ⟨1, by rw [pow_one, Nat.card_zpowers, hc_ord]⟩
    obtain ⟨Q, hQ⟩ := h_pg.exists_le_sylow
    exact (Subsingleton.elim Q P₅ : Q = P₅) ▸ hQ (Subgroup.mem_zpowers c)
  have hzpow_le : Subgroup.zpowers c ≤ ↑P₅ := fun x hx => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (↑P₅ : Subgroup G).zpow_mem hc_P5 k
  have hP5_eq : (↑P₅ : Subgroup G) = Subgroup.zpowers c := by
    apply le_antisymm _ hzpow_le
    intro x hx
    have hbij : Function.Bijective (Subgroup.inclusion hzpow_le) := by
      haveI := Fintype.ofFinite ↥(↑P₅ : Subgroup G)
      haveI := Fintype.ofFinite ↥(Subgroup.zpowers c)
      exact (Fintype.bijective_iff_injective_and_card _).mpr
        ⟨Subgroup.inclusion_injective _, by
          rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
              Nat.card_zpowers, hc_ord, hP_card]⟩
    obtain ⟨⟨y, hy⟩, hxy⟩ := hbij.surjective ⟨x, hx⟩
    rwa [show y = x from congr_arg Subtype.val hxy] at hy
  have hconj_zpow : σ' * c * σ'⁻¹ ∈ Subgroup.zpowers c :=
    (SetLike.ext_iff.mp hP5_eq _).mp (hNP.conj_mem c hc_P5 σ')
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hconj_zpow
  have hσ_inv : (galToPerm5 σ)⁻¹ = galToPerm5 σ :=
    inv_eq_iff_mul_eq_one.mpr (by rw [← sq]; exact hσ2)
  have hconj_val : galToPerm5 σ * ↑c * galToPerm5 σ = (↑c : Equiv.Perm (Fin 5)) ^ k := by
    have h := congr_arg Subtype.val hk
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow, σ'] at h
    rw [hσ_inv] at h; exact h.symm
  have ⟨hn1, hn2, hn3, hn4⟩ := transposition_not_normalizing_5cycle
    ↑c (galToPerm5 σ) hc5 hc_ne hσ_sign hσ2
  have hck_ne : (↑c : Equiv.Perm (Fin 5)) ^ k ≠ 1 := by
    rw [← hconj_val]; intro h
    have h1 : σ' * c * σ'⁻¹ = (1 : G) :=
      Subtype.ext (by simp only [σ', Subgroup.coe_mul, Subgroup.coe_inv]; rw [hσ_inv]; exact h)
    have hc1 : c = 1 := by have := (by group : c = σ'⁻¹ * (σ' * c * σ'⁻¹) * σ'); rw [h1] at this; simpa using this
    exact hc_ne (congr_arg Subtype.val hc1)
  have hred : (↑c : Equiv.Perm (Fin 5)) ^ k = (↑c) ^ (k % 5).toNat := by
    have hdiv : k = 5 * (k / 5) + k % 5 := by omega
    conv_lhs => rw [hdiv]
    rw [zpow_add, zpow_mul]
    have h5z : (↑c : Equiv.Perm (Fin 5)) ^ (5 : ℤ) = 1 := by
      rw [show (5 : ℤ) = ↑(5 : ℕ) from by norm_cast, zpow_natCast]; exact_mod_cast hc5
    rw [h5z, one_zpow, one_mul]
    conv_lhs => rw [(Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))).symm]
    simp only [zpow_natCast]
  rw [hred] at hconj_val hck_ne
  have hbound : (k % 5).toNat < 5 := by
    rw [Int.toNat_lt (by omega)]; exact Int.emod_lt_of_pos k (by norm_num)
  exfalso; interval_cases (k % 5).toNat <;> simp_all

-- Section E6b3: |Gal| ≠ 40 (same Sylow argument as ne_20)
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/-- |Gal(p/ℚ)| ≠ 40: Same Sylow argument as ne_20. In a subgroup of S₅
    of order 40, n₅ | 8 and n₅ ≡ 1 mod 5, so n₅ = 1 (unique normal
    Sylow 5-subgroup). Transposition normalizes it → contradiction. -/
private theorem gal_card_ne_40 : Fintype.card p.Gal ≠ 40 := by
  intro hc
  obtain ⟨σ, hσ2, hσ_ne, hσ_sign⟩ := gal_has_transposition
  set G := galToPerm5.range
  have hG_card : Nat.card G = 40 := by
    rw [show Nat.card G = Nat.card p.Gal from
      Nat.card_congr (Equiv.ofBijective galToPerm5.rangeRestrict
        ⟨fun a b h => galToPerm5_injective (congrArg Subtype.val h),
         galToPerm5.rangeRestrict_surjective⟩).symm, Nat.card_eq_fintype_card, hc]
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG_card]; norm_num)
  haveI : Fintype G := Fintype.ofFinite G
  have hG_ft : Fintype.card G = 40 := by rwa [Nat.card_eq_fintype_card] at hG_card
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨c, hc_ord⟩ := exists_prime_orderOf_dvd_card (p := 5) (by rw [hG_ft]; norm_num)
  have hc5 : (c : Equiv.Perm (Fin 5)) ^ 5 = 1 := by
    have h : c ^ orderOf c = (1 : G) := pow_orderOf_eq_one c
    rw [hc_ord] at h; simpa using congr_arg Subtype.val h
  have hc_ne : (c : Equiv.Perm (Fin 5)) ≠ 1 := fun h =>
    absurd hc_ord (by rw [show c = (1 : G) from Subtype.ext h, orderOf_one]; norm_num)
  set σ' : G := ⟨galToPerm5 σ, ⟨σ, rfl⟩⟩
  obtain ⟨P₅⟩ := Sylow.nonempty (p := 5) (G := G)
  have hP_card : Nat.card (↑P₅ : Subgroup G) = 5 := by
    rw [P₅.card_eq_multiplicity, hG_card]; native_decide
  have : Nat.card (Sylow 5 G) = 1 := by
    have h_mod := card_sylow_modEq_one 5 G
    have h_idx : (↑P₅ : Subgroup G).index = 8 := by
      have := (↑P₅ : Subgroup G).index_mul_card; rw [hP_card, hG_card] at this; omega
    have h_dvd := Sylow.card_dvd_index P₅; rw [h_idx] at h_dvd
    have h_le : Nat.card (Sylow 5 G) ≤ 8 := Nat.le_of_dvd (by norm_num) h_dvd
    have h_pos : 0 < Nat.card (Sylow 5 G) := Nat.card_pos
    rw [Nat.ModEq] at h_mod
    interval_cases (Nat.card (Sylow 5 G)) <;> omega
  haveI : Subsingleton (Sylow 5 G) := by
    haveI := Fintype.ofFinite (Sylow 5 G)
    rw [← Fintype.card_le_one_iff_subsingleton, ← Nat.card_eq_fintype_card]; omega
  haveI hNP : (↑P₅ : Subgroup G).Normal := by
    apply Subgroup.Normal.mk; intro n hn g
    have : g • P₅ = P₅ := Subsingleton.elim _ _; rw [Sylow.smul_eq_iff_mem_normalizer] at this
    exact ((Subgroup.mem_normalizer_iff.mp this) n).mp hn
  have hc_P5 : c ∈ (↑P₅ : Subgroup G) := by
    have h_pg : IsPGroup 5 (Subgroup.zpowers c) :=
      IsPGroup.iff_card.mpr ⟨1, by rw [pow_one, Nat.card_zpowers, hc_ord]⟩
    obtain ⟨Q, hQ⟩ := h_pg.exists_le_sylow
    exact (Subsingleton.elim Q P₅ : Q = P₅) ▸ hQ (Subgroup.mem_zpowers c)
  have hzpow_le : Subgroup.zpowers c ≤ ↑P₅ := fun x hx => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (↑P₅ : Subgroup G).zpow_mem hc_P5 k
  have hP5_eq : (↑P₅ : Subgroup G) = Subgroup.zpowers c := by
    apply le_antisymm _ hzpow_le
    intro x hx
    have hbij : Function.Bijective (Subgroup.inclusion hzpow_le) := by
      haveI := Fintype.ofFinite ↥(↑P₅ : Subgroup G)
      haveI := Fintype.ofFinite ↥(Subgroup.zpowers c)
      exact (Fintype.bijective_iff_injective_and_card _).mpr
        ⟨Subgroup.inclusion_injective _, by
          rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
              Nat.card_zpowers, hc_ord, hP_card]⟩
    obtain ⟨⟨y, hy⟩, hxy⟩ := hbij.surjective ⟨x, hx⟩
    rwa [show y = x from congr_arg Subtype.val hxy] at hy
  have hconj_zpow : σ' * c * σ'⁻¹ ∈ Subgroup.zpowers c :=
    (SetLike.ext_iff.mp hP5_eq _).mp (hNP.conj_mem c hc_P5 σ')
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hconj_zpow
  have hσ_inv : (galToPerm5 σ)⁻¹ = galToPerm5 σ :=
    inv_eq_iff_mul_eq_one.mpr (by rw [← sq]; exact hσ2)
  have hconj_val : galToPerm5 σ * ↑c * galToPerm5 σ = (↑c : Equiv.Perm (Fin 5)) ^ k := by
    have h := congr_arg Subtype.val hk
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow, σ'] at h
    rw [hσ_inv] at h; exact h.symm
  have ⟨hn1, hn2, hn3, hn4⟩ := transposition_not_normalizing_5cycle
    ↑c (galToPerm5 σ) hc5 hc_ne hσ_sign hσ2
  have hck_ne : (↑c : Equiv.Perm (Fin 5)) ^ k ≠ 1 := by
    rw [← hconj_val]; intro h
    have h1 : σ' * c * σ'⁻¹ = (1 : G) :=
      Subtype.ext (by simp only [σ', Subgroup.coe_mul, Subgroup.coe_inv]; rw [hσ_inv]; exact h)
    have hc1 : c = 1 := by have := (by group : c = σ'⁻¹ * (σ' * c * σ'⁻¹) * σ'); rw [h1] at this; simpa using this
    exact hc_ne (congr_arg Subtype.val hc1)
  have hred : (↑c : Equiv.Perm (Fin 5)) ^ k = (↑c) ^ (k % 5).toNat := by
    have hdiv : k = 5 * (k / 5) + k % 5 := by omega
    conv_lhs => rw [hdiv]
    rw [zpow_add, zpow_mul]
    have h5z : (↑c : Equiv.Perm (Fin 5)) ^ (5 : ℤ) = 1 := by
      rw [show (5 : ℤ) = ↑(5 : ℕ) from by norm_cast, zpow_natCast]; exact_mod_cast hc5
    rw [h5z, one_zpow, one_mul]
    conv_lhs => rw [(Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))).symm]
    simp only [zpow_natCast]
  rw [hred] at hconj_val hck_ne
  have hbound : (k % 5).toNat < 5 := by
    rw [Int.toNat_lt (by omega)]; exact Int.emod_lt_of_pos k (by norm_num)
  exfalso; interval_cases (k % 5).toNat <;> simp_all

-- Section E6c: three_dvd_gal_card as THEOREM
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/-- **THEOREM** (formerly Axiom A): 3 divides |Gal(p)|.
    Proved by eliminating all non-3-divisible options {5,10,20,40}:
    - 5: order-5 elements in S₅ are even, but Gal has an odd permutation
    - 10,20,40: unique normal Sylow 5-subgroup (5-cycle), but Gal has
      a transposition which can't normalize any 5-cycle (native_decide) -/
theorem three_dvd_gal_card : 3 ∣ Fintype.card p.Gal := by
  have h5 := five_dvd_gal_card
  have h120 := gal_card_dvd_120
  obtain ⟨a, ha⟩ := h5
  have hapos : 0 < a := by
    have := Fintype.card_pos (α := p.Gal); omega
  -- a | 24
  have ha24 : a ∣ 24 := by
    have h := (Nat.dvd_div_iff_mul_dvd (by norm_num : 5 ∣ 120)).mpr (ha ▸ h120)
    simpa using h
  -- |Gal| ≠ 5: order-5 perms have sign +1, but Gal has an odd perm
  have hne5 : a ≠ 1 := by
    intro heq; rw [heq, mul_one] at ha
    obtain ⟨σ, hσ⟩ := gal_has_odd_perm
    have h5pow : (galToPerm5 σ) ^ 5 = 1 := by
      rw [← map_pow]; convert map_one galToPerm5
      exact_mod_cast ha ▸ pow_card_eq_one
    exact absurd (perm_fin5_order_dvd5_sign_one (galToPerm5 σ) h5pow) (by rw [hσ]; decide)
  -- |Gal| ≠ 10
  have hne10 : a ≠ 2 := fun h => gal_card_ne_10 (by rw [ha, h])
  -- |Gal| ≠ 20
  have hne20 : a ≠ 4 := fun h => gal_card_ne_20 (by rw [ha, h])
  -- |Gal| ≠ 40
  have hne40 : a ≠ 8 := fun h => gal_card_ne_40 (by rw [ha, h])
  -- 3 | a: remaining options are {3,6,12,24}
  suffices 3 ∣ a from ha ▸ dvd_mul_of_dvd_right this 5
  have ha_le : a ≤ 24 := Nat.le_of_dvd (by norm_num) ha24
  interval_cases a <;> simp_all

-- NOTE: Part V(e2) (Vandermonde _p versions + axioms disc_p_neg/vandermonde_sq_eq_disc_p)
-- has been REMOVED. The axiom-free proofs in Part V(d) via vandermondeProduct_sq_val
-- and in Part V(e2) via complex conjugation now prove everything without axioms.
-- (Duplicate _p infrastructure and axioms removed — see git history.)
-- gal_has_odd_perm is proved axiom-free from exists_odd_galSign above.

-- ============================================================================
-- Part V(f): |Gal(p/ℚ)| = 120 (PROVED — all axioms eliminated)
-- ============================================================================

/-- |Gal(p)| ≠ 15: Gal embeds into S₅ which has no subgroup of order 15. -/
private theorem gal_card_ne_15 : Fintype.card p.Gal ≠ 15 := by
  intro hc
  let rootEquiv : p.rootSet p.SplittingField ≃ Fin 5 :=
    Fintype.equivOfCardEq (by rw [p_rootSet_card, Fintype.card_fin])
  let permEquiv : Equiv.Perm (p.rootSet p.SplittingField) ≃* Equiv.Perm (Fin 5) :=
    { toEquiv := Equiv.permCongr rootEquiv
      map_mul' := fun σ τ => by
        ext x; simp [Equiv.permCongr_apply, Equiv.Perm.mul_apply] }
  let φ := permEquiv.toMonoidHom.comp (Polynomial.Gal.galActionHom p p.SplittingField)
  have hinj : Function.Injective φ :=
    permEquiv.injective.comp (Polynomial.Gal.galActionHom_injective p p.SplittingField)
  exact no_subgroup_order_15 φ.range (by
    rw [show Nat.card φ.range = Nat.card p.Gal from
      Nat.card_congr (Equiv.ofBijective φ.rangeRestrict
        ⟨fun a b h => hinj (congrArg Subtype.val h),
         φ.rangeRestrict_surjective⟩).symm,
      Nat.card_eq_fintype_card, hc])

/-- |Gal(p)| ≠ 30: Gal embeds into S₅ which has no subgroup of order 30. -/
private theorem gal_card_ne_30 : Fintype.card p.Gal ≠ 30 := by
  intro hc
  let rootEquiv : p.rootSet p.SplittingField ≃ Fin 5 :=
    Fintype.equivOfCardEq (by rw [p_rootSet_card, Fintype.card_fin])
  let permEquiv : Equiv.Perm (p.rootSet p.SplittingField) ≃* Equiv.Perm (Fin 5) :=
    { toEquiv := Equiv.permCongr rootEquiv
      map_mul' := fun σ τ => by
        ext x; simp [Equiv.permCongr_apply, Equiv.Perm.mul_apply] }
  let φ := permEquiv.toMonoidHom.comp (Polynomial.Gal.galActionHom p p.SplittingField)
  have hinj : Function.Injective φ :=
    permEquiv.injective.comp (Polynomial.Gal.galActionHom_injective p p.SplittingField)
  exact no_subgroup_order_30 φ.range (by
    rw [show Nat.card φ.range = Nat.card p.Gal from
      Nat.card_congr (Equiv.ofBijective φ.rangeRestrict
        ⟨fun a b h => hinj (congrArg Subtype.val h),
         φ.rangeRestrict_surjective⟩).symm,
      Nat.card_eq_fintype_card, hc])

/-- |Gal(p)| ≠ 60: the unique subgroup of S₅ of order 60 is A₅,
    but Gal(p) ⊄ A₅ (Axiom B). -/
private theorem gal_card_ne_60 : Fintype.card p.Gal ≠ 60 := by
  intro hc
  -- galToPerm5 is an injection into Perm(Fin 5)
  -- Image has cardinality 60, so image ≅ A₅ (unique order-60 subgroup)
  have hrange_card : Nat.card galToPerm5.range = 60 := by
    rw [show Nat.card galToPerm5.range = Nat.card p.Gal from
      Nat.card_congr (Equiv.ofBijective galToPerm5.rangeRestrict
        ⟨fun a b h => galToPerm5_injective (congrArg Subtype.val h),
         galToPerm5.rangeRestrict_surjective⟩).symm,
      Nat.card_eq_fintype_card, hc]
  -- A subgroup of S₅ of order 60 must be ≤ A₅
  -- (A₅ has index 2, so any element of G outside A₅ would create a surjection
  --  G → ℤ/2 with kernel G ∩ A₅ of order 30, contradicting no_subgroup_order_30)
  have hle : galToPerm5.range ≤ alternatingGroup (Fin 5) := by
    by_contra hle_neg
    have ⟨x, hxG, hxA⟩ : ∃ x ∈ galToPerm5.range, x ∉ alternatingGroup (Fin 5) := by
      by_contra h; push_neg at h; exact hle_neg h
    let signG : ↥galToPerm5.range →* ℤˣ := Equiv.Perm.sign.comp galToPerm5.range.subtype
    let K := signG.ker.map galToPerm5.range.subtype
    -- K = galToPerm5.range ∩ A₅, has order 30 (index 2)
    have hK_card : Nat.card ↥K = 30 := by
      have h_eq : Nat.card ↥K = Nat.card ↥signG.ker :=
        (Nat.card_congr
          (signG.ker.equivMapOfInjective galToPerm5.range.subtype
            Subtype.val_injective).toEquiv).symm
      rw [h_eq]
      have h_mul := Subgroup.card_mul_index signG.ker
      have h_idx_dvd : signG.ker.index ∣ 2 := by
        have h_iso : signG.ker.index = Nat.card ↥signG.range := by
          rw [Subgroup.index]
          exact Nat.card_congr (QuotientGroup.quotientKerEquivRange signG).toEquiv
        rw [h_iso]
        calc Nat.card ↥signG.range
            ∣ Nat.card ℤˣ := Subgroup.card_subgroup_dvd_card signG.range
          _ = 2 := by rw [Nat.card_eq_fintype_card]; decide
      have h_idx_ne : signG.ker.index ≠ 1 := by
        intro heq
        have hker_top : signG.ker = ⊤ := Subgroup.index_eq_one.mp heq
        have : (⟨x, hxG⟩ : ↥galToPerm5.range) ∈ signG.ker := hker_top ▸ Subgroup.mem_top _
        rw [MonoidHom.mem_ker] at this
        simp only [signG, MonoidHom.comp_apply, Subgroup.coe_subtype] at this
        exact hxA (Equiv.Perm.mem_alternatingGroup.mpr this)
      have h_idx : signG.ker.index = 2 :=
        (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) _ h_idx_dvd).resolve_left h_idx_ne
      rw [hrange_card, h_idx] at h_mul; omega
    exact no_subgroup_order_30 K hK_card
  -- But Axiom B says Gal has an odd permutation, contradicting Gal ⊆ A₅
  obtain ⟨σ, hσ⟩ := gal_has_odd_perm
  have hmem : galToPerm5 σ ∈ alternatingGroup (Fin 5) :=
    hle (MonoidHom.mem_range.mpr ⟨σ, rfl⟩)
  rw [Equiv.Perm.mem_alternatingGroup] at hmem
  rw [hmem] at hσ
  exact absurd hσ (by decide)

/-- **THEOREM**: |Gal(p/ℚ)| = 120.

    Proof: 5 | |Gal| (five_dvd_gal_card) and 3 | |Gal| (three_dvd_gal_card).
    So 15 | |Gal| and |Gal| | 120, giving |Gal| ∈ {15, 30, 60, 120}.
    |Gal| ≠ 15 (no_subgroup_order_15), ≠ 30 (no_subgroup_order_30),
    ≠ 60 (Gal ⊄ A₅). Therefore |Gal| = 120. -/
theorem gal_card_eq_120 : Fintype.card p.Gal = 120 := by
  have h5 := five_dvd_gal_card
  have h3 := three_dvd_gal_card
  have h120 := gal_card_dvd_120
  -- 15 | |Gal| (from 5 | and 3 |, coprime)
  have h15 : 15 ∣ Fintype.card p.Gal := by
    have : Nat.Coprime 5 3 := by norm_num
    exact this.mul_dvd_of_dvd_of_dvd h5 h3
  -- |Gal| | 120 and 15 | |Gal| → |Gal| ∈ {15, 30, 60, 120}
  have hpos : 0 < Fintype.card p.Gal := Fintype.card_pos
  -- By divisibility, the only options are 15, 30, 60, 120
  have hmem : Fintype.card p.Gal ∈ ({15, 30, 60, 120} : Finset ℕ) := by
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    -- |Gal| = 15a for some a, and 15a | 120
    obtain ⟨a, ha⟩ := h15
    have hapos : 0 < a := Nat.pos_of_ne_zero (by omega)
    have h15a_dvd : 15 * a ∣ 120 := ha ▸ h120
    have hale : a ≤ 8 := by
      have := Nat.le_of_dvd (by norm_num : 0 < 120) h15a_dvd
      omega
    -- a ∈ {1..8} and 15a | 120 → a ∈ {1,2,4,8}
    interval_cases a <;> simp_all
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact absurd h gal_card_ne_15
  · exact absurd h gal_card_ne_30
  · exact absurd h gal_card_ne_60
  · exact h

-- ============================================================================
-- Part VI: Gal(p/ℚ) ≅ S₅
-- ============================================================================

/-- The Galois group of x⁵ - 4x + 2 is isomorphic to S₅ (= Perm(Fin 5)).

    Proof: galActionHom is injective with |Gal| = |Perm(rootSet)| = 120,
    so it is bijective. Transfer via rootSet ≃ Fin 5. -/
theorem gal_iso_s5 :
    Nonempty (p.Gal ≃* Equiv.Perm (Fin 5)) := by
  classical
  haveI : Fact (map (algebraMap ℚ p.SplittingField) p).Splits :=
    ⟨Polynomial.SplittingField.splits p⟩
  -- galActionHom is injective
  have hinj := Polynomial.Gal.galActionHom_injective p p.SplittingField
  -- |rootSet| = 5
  have hcard_root : Fintype.card (p.rootSet p.SplittingField) = 5 := p_rootSet_card
  -- |Gal| = 120 = |Perm(rootSet)| (since 5! = 120)
  have hcard_gal : Fintype.card p.Gal = 120 := gal_card_eq_120
  have hcard_perm : Fintype.card (Equiv.Perm (p.rootSet p.SplittingField)) = 120 := by
    rw [Fintype.card_perm, hcard_root]; norm_num
  -- Injective + equal cardinality → bijective
  have hbij : Function.Bijective (Polynomial.Gal.galActionHom p p.SplittingField) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by rw [hcard_gal, hcard_perm]⟩
  -- Construct isomorphism Gal ≅ Perm(rootSet)
  have hiso : p.Gal ≃* Equiv.Perm (p.rootSet p.SplittingField) :=
    MulEquiv.ofBijective _ hbij
  -- Transfer via rootSet ≃ Fin 5
  have hfin : p.rootSet p.SplittingField ≃ Fin 5 :=
    Fintype.equivFinOfCardEq hcard_root
  have hperm : Equiv.Perm (p.rootSet p.SplittingField) ≃* Equiv.Perm (Fin 5) :=
    { toEquiv := Equiv.permCongr hfin
      map_mul' := fun σ τ => by ext x; simp [Equiv.permCongr_apply, Equiv.Perm.mul_apply] }
  exact ⟨hiso.trans hperm⟩

-- ============================================================================
-- Part VII: S₅ is Not Solvable
-- ============================================================================

/-- S₅ is not solvable: immediate from Mathlib. -/
theorem s5_not_solvable : ¬ IsSolvable (Equiv.Perm (Fin 5)) := by
  have h : 5 ≤ Cardinal.mk (Fin 5) := by
    simp only [Cardinal.mk_fintype, Fintype.card_fin]; norm_cast
  exact Equiv.Perm.not_solvable (Fin 5) h

/-- The Galois group of x⁵ - 4x + 2 is not solvable. -/
theorem gal_not_solvable : ¬ IsSolvable p.Gal := by
  obtain ⟨iso⟩ := gal_iso_s5
  intro hsol
  apply s5_not_solvable
  haveI := hsol
  exact solvable_of_surjective
    (f := iso.toMonoidHom) (fun b => ⟨iso.symm b, iso.apply_symm_apply b⟩)

-- ============================================================================
-- Part VIII: The Abel-Ruffini Conclusion
-- ============================================================================

/-
## The Complete Proof

1. p = x⁵ - 4x + 2 is irreducible over ℚ (Eisenstein at 2) ✓ PROVED
2. Gal(p/ℚ) ≅ S₅ (axiom-free) ✓ PROVED
3. S₅ is not solvable (Mathlib) ✓ PROVED
4. If α is solvable by radicals, Gal(minpoly(α)) is solvable (Mathlib) ✓
5. Contrapositive: Gal not solvable ⟹ α not solvable by radicals ✓ PROVED

Therefore: the roots of x⁵ - 4x + 2 cannot be expressed using radicals.
This gives a CONCRETE witness for the Abel-Ruffini theorem.
-/

/-- **Abel-Ruffini (concrete witness):**
    The roots of x⁵ - 4x + 2 cannot be expressed by radicals.

    Proof: If some root α were solvable by radicals, then Gal(p/ℚ) would be
    solvable (by Galois's theorem). But Gal(p/ℚ) ≅ S₅ which is not solvable.
    Contradiction. -/
theorem roots_not_solvable_by_rad
    {E : Type*} [Field E] [Algebra ℚ E] (α : E)
    (hroot : Polynomial.aeval α p = 0) :
    ¬ IsSolvableByRad ℚ α := by
  intro hrad
  -- If α is solvable by radicals and p(α) = 0 with p irreducible,
  -- then Gal(p) is solvable
  have hsol : IsSolvable p.Gal :=
    solvableByRad.isSolvable' p_irreducible hroot hrad
  -- But Gal(p) is not solvable (it's S₅)
  exact gal_not_solvable hsol

-- ============================================================================
-- Part IX: S₅ Realizability
-- ============================================================================

/-- S₅ is realizable as a Galois group over ℚ, witnessed by x⁵ - 4x + 2. -/
theorem s5_realizable :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : FiniteDimensional ℚ K)
      (_ : IsGalois ℚ K),
      Nonempty (Equiv.Perm (Fin 5) ≃* (K ≃ₐ[ℚ] K)) := by
  have : Normal ℚ p.SplittingField := inferInstance
  have : Algebra.IsSeparable ℚ p.SplittingField := inferInstance
  obtain ⟨iso⟩ := gal_iso_s5
  exact ⟨p.SplittingField,
    inferInstance, inferInstance, inferInstance,
    IsGalois.mk,
    ⟨iso.symm⟩⟩

-- ============================================================================
-- Verification
-- ============================================================================

#check p_irreducible      -- Irreducible over ℚ
#check p_natDegree         -- Degree = 5
#check p_separable         -- Separable
#check five_dvd_gal_card   -- 5 | |Gal|
#check gal_card_dvd_120    -- |Gal| | 120
#check gal_iso_s5          -- Gal ≅ S₅
#check gal_not_solvable    -- Gal is not solvable
#check roots_not_solvable_by_rad  -- Roots not solvable by radicals
#check s5_realizable       -- S₅ realizable over ℚ

end AbelRuffiniOQ04OQ01
