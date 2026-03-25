# Abel-Ruffini OQ-04-OQ-01: Galois Group of the Generic Quintic

## Problem Summary

Formalize Gal(x^5 + a_1 x^4 + ... + a_5 / Q(a_1,...,a_5)) = S_5.

## Approach Taken

Instead of the generic polynomial (requiring MvPolynomial fraction field Galois theory),
we proved a concrete witness: Gal(x^5 - 4x + 2 / Q) ≅ S_5.

## Session 2026-03-25 (Session 1) - Concrete Polynomial Approach

**Mode**: FRESH
**Outcome**: progress (1 axiom remaining)

### What I Did
- Scouted Mathlib infrastructure: esymmAlgEquiv, galActionHom, Eisenstein criterion
- Chose concrete polynomial x^5 - 4x + 2 (Eisenstein at p=2)
- Built complete proof chain:
  1. Irreducibility (Eisenstein at 2, Gauss's lemma) - PROVED
  2. Degree 5, monic, separable - PROVED
  3. 5 | |Gal| (prime degree), |Gal| | 120 (embeds in S_5) - PROVED
  4. |Gal| = 120 - AXIOMATIZED (justified by 3 real roots argument)
  5. galActionHom bijective -> Gal ≅ S_5 - PROVED
  6. S_5 not solvable - PROVED (Mathlib)
  7. Roots not solvable by radicals - PROVED
  8. S_5 realizable over Q - PROVED

### Key Findings
- galActionHom bijectivity pattern (injective + card equality) well-established
- solvable_of_surjective is the correct API (not isSolvable_of_surjective)
- Generic polynomial approach requires 3-4 substantial gap lemmas in Mathlib
- The 3-real-roots analysis (IVT + f' bounding) is the main remaining work

### Files Modified
- proofs/Proofs/AbelRuffiniOQ04OQ01.lean (new, 362 lines)
- src/data/proofs/abel-ruffini-oq-04-oq-01/meta.json (new)

### Next Steps
1. ~~Prove group theory: transitive + transposition + p-cycle → S_p~~ **DONE (Session 2)**
2. Cast evaluations to ℝ and apply IVT for real root lower bound
3. Prove f' = 5x⁴-4 has exactly 2 real roots → at most 3 real roots (Rolle)
4. Embed splitting field into ℂ, show complex conjugation is a transposition
5. Connect closure_cycle_swap_eq_top to galActionHom to prove |Gal|=120

## Session 2026-03-25 (Session 2) - Group Theory Bridge

**Mode**: REVISIT (RICH knowledge, score 18)
**Outcome**: progress (group theory proved, axiom reduction roadmap clear)

### What I Did
- Proved `closure_cycle_swap_eq_top`: the closure of a 5-cycle (0 1 2 3 4) and swap(0,1) in S₅ is ⊤
- Proof technique: conjugation chain → all 10 transpositions → swap_induction_on
  - Adjacent swaps: c5^k swap(0,1) c5^{-k} = swap(k, k+1) (verified by native_decide)
  - Star swaps: swap(0,k) swap(k,k+1) swap(0,k) = swap(0,k+1) (native_decide)
  - General swaps: swap(0,a) swap(0,b) swap(0,a) = swap(a,b) (native_decide)
  - Final: fin_cases + Equiv.swap_comm closes all 10 cases
- Documented proof architecture for eliminating gal_card_eq_120

### Key Findings
- native_decide works for permutation equality on Fin 5 but NOT for Subgroup.closure = ⊤ (no Decidable instance)
- swap_induction_on case is `swap_mul f a b hab ih` (not `swap a b hab ih`)
- After `rw [eq_top_iff]; intro g _`, the induction hypothesis carries an extra `g ∈ ⊤` premise — need `ih trivial`
- The group theory lemma is the key bridge: once we show Gal has a transposition, |Gal| = 120 follows

### Files Modified
- proofs/Proofs/AbelRuffiniOQ04OQ01.lean (399→475 lines, added group theory proof)
- src/data/proofs/abel-ruffini-oq-04-oq-01/meta.json (updated lineCount, theoremCount)
- src/data/research/problems/abel-ruffini-oq-04-oq-01.json (updated knowledge)

### Remaining Work to Eliminate the Axiom
1. ~~**Real analysis (IVT + Rolle)**: Show p has exactly 3 real roots~~ **SUPERSEDED by Session 3**
2. ~~**Complex conjugation**: Embed splitting field into ℂ~~ **SUPERSEDED by Session 3**
3. ~~**Connection**: automorphism acts as transposition~~ **SUPERSEDED by Session 3**
4. ~~**Final bridge**: Connect to galActionHom~~ **SUPERSEDED by Session 3**

## Session 2026-03-24 (Session 3) - Axiom Decomposition via Sylow Theory

**Mode**: REVISIT (RICH knowledge, score ~25)
**Outcome**: progress (|Gal|=120 now PROVED as theorem from 2 narrow axioms)

### What I Did
- Decomposed the opaque axiom `gal_card_eq_120` into 2 narrower, well-motivated axioms
- Added galToPerm5 infrastructure (injection Gal → Perm(Fin 5), sign homomorphism)
- Proved `no_subgroup_order_15` via Sylow theory + native_decide (order-5/order-3 commutativity obstruction)
- Proved `no_subgroup_order_30` via A₅ simplicity (index-2 subgroup contradicts simple)
- Proved `gal_card_ne_60` via sign homomorphism (unique order-60 subgroup is A₅, but Gal ⊄ A₅)
- Proved `gal_card_eq_120` as a THEOREM from the 2 axioms + divisibility analysis
- Verified mod 13 factorization: p_root_mod13_at_2, p_root_mod13_at_5, cubic_factor_no_roots_mod13

### The Two New Axioms
1. `three_dvd_gal_card`: 3 | |Gal| (Dedekind's theorem at p=13)
   - Supporting: x⁵-4x+2 ≡ (x-2)(x-5)(x³+7x²+8) mod 13 (verified by native_decide)
   - Cubic has no roots mod 13 (verified by native_decide)
   - Blocked by: Mathlib lacks Dedekind's theorem
2. `gal_has_odd_perm`: ∃ σ ∈ Gal with sign(σ) = -1
   - Supporting: disc(p) = -212144 < 0, so Vandermonde product Δ ∉ ℚ
   - Blocked by: Mathlib lacks disc(f) = Δ² identity

### Key Findings
- The Sylow approach (InverseGaloisA5 pattern) is much more practical than IVT + complex conjugation
- native_decide can verify mod-13 factorization efficiently
- no_subgroup_order_15 requires the deep fact that order-5 and order-3 elements don't commute in S₅
- no_subgroup_order_30 follows from A₅ simplicity via index-2 normality
- gal_card_ne_60 requires showing that ANY order-60 subgroup of S₅ is A₅ (via sign homomorphism)

### Files Modified
- proofs/Proofs/AbelRuffiniOQ04OQ01.lean (475→874 lines, 13→37 theorems, 1→2 axioms)
- src/data/proofs/abel-ruffini-oq-04-oq-01/meta.json (updated counts)
- src/data/research/problems/abel-ruffini-oq-04-oq-01.json (to be updated)

## Session 2026-03-24 (Session 4) - Vandermonde Product: Axiom B Eliminated

**Mode**: REVISIT (RICH knowledge, score ~29)
**Outcome**: progress (Axiom B eliminated, replaced with narrower disc computation axiom)

### What I Did
- Built complete Vandermonde product infrastructure for polynomial p
  - rootEnum, rootEnum_is_root, rootEnum_injective
  - vandermondeProduct = det(Vandermonde(rootEnum)), nonzero
  - gal_permutes_roots, vandermonde_perm_det, gal_map_vandermonde_entry
  - **gal_acts_on_vandermondeProduct**: σ(Δ) = galSign(σ) · Δ
- Proved **vandermondeProduct_not_rational**: Δ ∉ ℚ (from Δ² = -212144 < 0)
- Proved **fixed_by_all_gal_is_rational**: FTGT direction (fixedField(⊤) = ⊥)
  - Key: fixingSubgroup(⊥) = ⊤ (automorphisms fix ℚ by σ.commutes)
  - Then IsGalois.fixedField_fixingSubgroup gives fixedField(⊤) = ⊥
- Proved **exists_odd_galSign** = **gal_has_odd_perm** as a THEOREM
- Former Axiom B is now PROVED; replaced with narrower axiom vandermondeProduct_sq_val

### Key Findings
- IntermediateField.mem_fixedField_iff is the correct API (not mem_fixedField)
- fixingSubgroup membership requires `show ∀ y : ↑↑⊥, σ • ↑y = ↑y` pattern
- IsGalois ℚ SF needs explicit `IsGalois.mk` (inferInstance may fail for abbrevs)
- The FTGT (fixedField ⊤ = ⊥) follows from fixingSubgroup ⊥ = ⊤ + Galois correspondence
- Pattern from InverseGaloisA5.lean (vandermonde_perm_det, gal_map_vandermonde_entry) transfers directly

### Files Modified
- proofs/Proofs/AbelRuffiniOQ04OQ01.lean (874→1036 lines, 37→48 theorems, 2 axioms still)
- src/data/proofs/abel-ruffini-oq-04-oq-01/meta.json (updated counts)
- src/data/research/problems/abel-ruffini-oq-04-oq-01.json (updated knowledge)

### Remaining Work to Eliminate ALL Axioms
1. **Axiom A (three_dvd_gal_card)**: Needs Dedekind's theorem (~200-300 lines)
2. **Axiom B replacement (vandermondeProduct_sq_val)**: Prove Δ² = -212144 from Res(p,p')
   - Chain: Δ² = ∏_{i≠j}(αᵢ-αⱼ) = ∏ᵢ p'(αᵢ) = Res(p,p') = disc(p) = -212144
   - InverseGaloisA5.lean proves this for q via ℂ embedding + Sophie Germain (~400 lines)
   - For p = x⁵-4x+2, p'=5x⁴-4 doesn't factor as nicely (no Sophie Germain)
   - Alternative: direct Sylvester matrix determinant computation (9×9 over ℤ)
