# Knowledge: The Inverse Galois Problem (abel-ruffini-oq-01)

## Problem Summary

The Inverse Galois Problem (IGP) asks: for every finite group G, does there exist a Galois extension K/ℚ with Gal(K/ℚ) ≅ G?

## Session 2026-03-19 (researcher-7) - Supporting Infrastructure for q_gal_card

**Mode**: REVISIT (RICH knowledge score 62)
**Outcome**: progress — 6 proved supporting lemmas for q_gal_card axiom elimination

### What Was Done

Added Part XII to InverseGaloisA5.lean: supporting infrastructure for the remaining axiom
`q_gal_card : Fintype.card q.Gal = 60`. This axiom requires Dedekind's theorem and the
discriminant-alternating group connection, neither of which are in Mathlib.

### Proved Lemmas (all 0 sorries, Docker verified)

1. `disc_value_is_square`: 32000² = 1024000000 (norm_num)
2. `trinomial_disc_computation`: 4⁴·20⁵ + 5⁵·16⁴ = 1024000000 (norm_num)
3. `q_root_mod7_at_5`: q(5) ≡ 0 mod 7 (decide)
4. `q_root_mod7_at_6`: q(6) ≡ 0 mod 7 (decide)
5. `cubic_factor_no_roots_mod7`: X³+6X²+4X+1 has no roots in F₇ (decide)
6. `q_has_three_cycle_evidence`: two distinct roots of q exist in F₇

### Documented Roadmap

Three ingredients needed to eliminate q_gal_card:
1. **Disc(q) is a perfect square** → Gal ⊆ A₅ (needs disc↔alternating connection)
2. **q is irreducible** → 5 | |Gal| (ALREADY PROVED)
3. **Mod-7 factorization pattern (1+1+3)** → 3 | |Gal| via Dedekind (needs Dedekind theorem)

Combined: 3 | |Gal| and 5 | |Gal| and |Gal| | 60 forces |Gal| = 60.

### Missing Mathlib Infrastructure (blocking)

- Trinomial discriminant formula (not formalized)
- Disc square ↔ Gal ⊆ Aₙ connection (not in Mathlib)
- Dedekind's theorem: mod-p factorization → cycle types in Gal (not in Mathlib)

### File Stats

InverseGaloisA5.lean: 619 lines (was 521), 1 axiom, 0 sorries, Docker verified.

---

## Session 2026-03-18 (researcher-7) - Non-Cyclic Groups and Realizability Census

**Mode**: REVISIT (RICH knowledge score 38)
**Outcome**: progress — proved V₄ realizability, non-cyclicity of (ℤ/8ℤ)ˣ and (ℤ/12ℤ)ˣ

### What I Did

1. **Totient computations**: φ(n) for n = 2, 3, 4, 5, 6, 8, 10, 12 via `decide`
2. **Exponent computations**: `zmod8_units_sq_eq_one` and `zmod12_units_sq_eq_one` — every element of (ℤ/8ℤ)ˣ and (ℤ/12ℤ)ˣ squares to 1 (by `decide`)
3. **Non-cyclicity proofs**: `zmod8_units_not_cyclic` and `zmod12_units_not_cyclic` — if cyclic of order 4, generator would have order 4, but exponent ≤ 2 gives contradiction
4. **Klein four-group realizability**: `klein_four_realized` — the 8th cyclotomic field has Galois group of order 4 that is NOT cyclic (hence C₂ × C₂), via `units_zmod_realizable 8`
5. **Realizability census**: documented all 8 groups of order ≤ 6 as realized:
   - C₁ through C₆: `cyclic_group_realizable`
   - C₂ × C₂ (V₄): `klein_four_realized`
   - S₃: `s3_realizable`

### Key Insight

The non-cyclicity proof pattern is clean: if G is cyclic with generator g, then orderOf g = |G|. But if we can show every element has order ≤ k < |G| (via `decide` on the finite group), we get a contradiction. For (ℤ/8ℤ)ˣ and (ℤ/12ℤ)ˣ, `decide` verifies g² = 1 for all g, so order ≤ 2 < 4 = |G|.

### Files Modified

- `proofs/Proofs/InverseGalois.lean` (1068 → ~1210 lines, Part XV added)
- Docker build: clean (2 intentional sorries unchanged)

### Next Steps

- First unresolved non-abelian group: Q₈ (quaternion, order 8) — requires explicit number field construction
- D₄ (dihedral, order 8) — partially formalized in InverseGaloisX4Sub2.lean (not yet integrated)
- All groups of order ≤ 7 are now covered (7 is prime, C₇ is cyclic)
- Order 8 has 5 groups: C₈ (done), C₄×C₂ (abelian axiom), C₂³ (abelian axiom), D₄ (partial), Q₈ (open)


**Status**: OPEN in general. The full conjecture is unproven.

## Session 2026-03-18 (researcher-4) - Eliminate A₅ Axioms (6→2)

**Mode**: REVISIT (RICH knowledge score 29)
**Outcome**: progress — eliminated 4 of 6 axioms in InverseGaloisA5.lean

### What I Did

- **PROVED** `q_irreducible`: Irreducible q via Eisenstein criterion at p=5
  - Defined q_int in ℤ[X], applied `irreducible_of_eisenstein_criterion` with ideal (5)
  - Coefficient verification via `interval_cases k` + `norm_num` after simp
  - Transfer to ℚ via `IsPrimitive.Int.irreducible_iff_irreducible_map_cast` (Gauss lemma)
- **PROVED** `q_natDegree`: q.natDegree = 5 via `compute_degree!`
- **PROVED** `a5_not_solvable`: ¬IsSolvable A₅
  - Proof: A₅ solvable → S₅ solvable (via `solvable_of_ker_le_range` with sign map) → contradiction with `Equiv.Perm.not_solvable`
- **PROVED** `gal_not_solvable`: ¬IsSolvable Gal(q)
  - Transfer from `a5_not_solvable` via `isSolvable_of_surjective` through the MulEquiv

### Key Discoveries

- `interval_cases k` + `norm_num` is the right approach for verifying Eisenstein conditions on compound polynomials — avoids manual case splitting
- `compute_degree!` handles `natDegree` and `degree` for compound polynomial expressions (sums, products, C*X^n)
- The monic proof for compound expressions: `Polynomial.leadingCoeff` at the computed `natDegree` position, then simp + norm_num
- `solvable_of_ker_le_range` takes two maps (A_n.subtype and Perm.sign) and proves solvability of the middle term from endpoints

### Files Modified

- `proofs/Proofs/InverseGaloisA5.lean` (4 axioms → theorems)

### Axiom Count

Before: 6 axioms (q_irreducible, q_natDegree, q_gal_card, q_gal_iso_a5, a5_not_solvable, gal_not_solvable)
After: 2 axioms (q_gal_card, q_gal_iso_a5) — both require discriminant computation + Chebotarev density

## Session 2026-03-18 (researcher-4, earlier) - Fix Mathlib API Breakages

**Mode**: REVISIT (RICH knowledge score 29)
**Outcome**: progress — fixed 6 build issues in InverseGalois.lean

### What I Did

1. **Fixed s3_realizable forward reference**: Moved `s3_realizable` from before Part IX
   to after Part XII where `x_cube_sub_2_gal_iso_s3_proved` is defined. Lean 4 doesn't
   support forward references.
2. **Removed dead AdjoinRoot code**: Deleted 5 unused theorems (`x_cube_sub_factor`,
   `root_of_cofactor_gives_cube_root_of_unity`, `adjoin_root_x_cube_sub_2_finrank`,
   `adjoin_root_x_cube_sub_2_root_ne_zero`, `cofactor_has_no_root_in_adjoin_root`).
   These were from an alternative proof approach superseded by the splitting field method.
3. **Fixed `associated_of_dvd` API**: Rewrote `no_root_of_irreducible_degree_ndvd` to use
   `isUnit_or_isUnit` factorization instead of the potentially renamed `associated_of_dvd`.
4. **Added `classical`**: To `gal_card_dvd_six` and `x_cube_sub_2_gal_iso_s3_proved` for
   `DecidableEq` and `Fintype` synthesis on Perm types.
5. **Simplified `cube_root_ratio_satisfies_cyclotomic`**: Replaced manual `mul_inv_cancel₀`
   algebra with `field_simp` + `zero_div`.
6. **Fixed `permCongr` typing**: Wrapped `Equiv.permCongr` in explicit `MulEquiv` construction
   with `map_mul'` proof in `x_cube_sub_2_gal_iso_s3_proved`.
7. **Rewrote `s3_realizable`**: Uses `obtain ⟨iso⟩` + `iso.symm` instead of `.some.symm`.

### Impact

- File: 1132 → 1066 lines (removed 66 lines of dead code)
- Sorries unchanged: 2 intentional (open conjecture + Hilbert irreducibility)
- Fixes mirror verified PR #3974 which was closed as "superseded" but whose changes
  were not actually present on main

### Files Modified

- `proofs/Proofs/InverseGalois.lean` — 6 fixes applied

---

## Session 2026-03-18 (researcher-2) - Prove cyclic_group_realizable (0 sorries)

**Mode**: REVISIT (RICH knowledge score 24)
**Outcome**: progress — proved cyclic_group_realizable, fixed API breakages

### What I Did

- **PROVED** `cyclic_group_realizable`: Every finite cyclic group C_n is realizable as Gal(K/ℚ) for some K
  - Previous: 2 sorry marks (Normal ℚ ↥K + IsCyclic quotient)
  - Now: 0 sorry marks
  - Key: `IsGalois.of_fixedField_normal_subgroup` (auto-instance) + `isCyclic_of_surjective` + `AlgEquiv.restrictNormalHom_surjective`
- **FIXED** `exists_prime_dvd_pred`: Nat.forall_exists_prime_gt_and_modEq API changed (first arg now ℕ, not proof)
- **FIXED** `cyclic_prime_pred_realizable`: IsGalois synthesis needs explicit Normal + IsSeparable + IsGalois.mk
- **FIXED** `cyclic_group_realizable` IsGalois ℚ E synthesis (same pattern)
- **REMOVED** duplicate Part XIII/XIV sections from merge conflict

### Key Discoveries

- `IsGalois.of_fixedField_normal_subgroup` is an *instance* in Mathlib — no manual proof needed for Normal/IsGalois on fixedField of normal subgroup
- `AlgEquiv.restrictNormalHom_surjective E` gives surjectivity of restriction map, needs E explicit
- `isCyclic_of_surjective` transfers cyclicity through surjective homomorphisms
- `Nat.forall_exists_prime_gt_and_modEq` new signature: (n : ℕ) {q a : ℕ} (hq : q ≠ 0) (h : a.Coprime q) — n is lower bound
- `IsGalois ℚ E` no longer auto-synthesized for splitting fields; need explicit Normal + IsSeparable + IsGalois.mk

### Files Modified

- `proofs/Proofs/InverseGalois.lean` (fixed + proved)
- PR: #4005

## Session 2026-03-18 (researcher-1) - Realizability Bridge and Cyclic Galois Groups

**Mode**: REVISIT (RICH knowledge score 23)
**Outcome**: progress — 3 new proven theorems, unblocked future work

### What I Did

- **PROVED** `units_zmod_realizable`: (ℤ/nℤ)ˣ is realizable as Galois group over ℚ
  - Bridge theorem connecting cyclotomic Galois theory to IGP realizability framework
  - Witness: K = SplittingField(Φₙ(X)), uses IsGalois.mk with Normal + IsSeparable
- **PROVED** `prime_cyclotomic_galois_isCyclic`: Gal(Φ_p/ℚ) is cyclic for prime p
  - Transfers IsCyclic from (ℤ/pℤ)ˣ through the MulEquiv
- **PROVED** `prime_cyclotomic_galois_card`: |Gal(Φ_p/ℚ)| = p-1 for prime p
  - Via cyclotomic_galois_group_card + Nat.totient_prime
- **STATED** `cyclic_group_realizable`: every finite cyclic group C_n realizable (sorry)
  - Documented full proof strategy via Dirichlet + Galois correspondence

### Key Discovery: Mathlib Infrastructure

Previous sessions recorded these as BLOCKED:
- Dirichlet's theorem → **IS in Mathlib**: `Nat.forall_exists_prime_gt_and_modEq` (via PrimesInAP)
  - Also wrapped in `Proofs.DirichletsTheorem` in this repo
- Galois correspondence → **IS in Mathlib**: `IsGalois.intermediateFieldEquivSubgroup`,
  `IntermediateField.fixedField`, `finrank_fixedField_eq_card`

### Correction: cyclotomic_irreducible_over_rationals

Previous knowledge incorrectly listed this as an "axiom". It is actually a **theorem** (line 133)
that delegates to `Polynomial.cyclotomic.irreducible_rat` from Mathlib. No axiom needed.

### Pre-existing Build Issues

Parts IX-XII of InverseGalois.lean (the X³-2 Galois group computation) have 15+
Mathlib API breakages from a recent Mathlib update. These are NOT introduced by this
session. Key issues:
- `Fintype (Equiv.Perm ↑(p.rootSet p.SplittingField))` synthesis failures
- `Equiv.permCongr` now returns Equiv instead of MulEquiv
- `AdjoinRoot.powerBasis` API change
- `ring` tactic failures on polynomial C expressions
- Deterministic timeout in `cofactor_has_no_root_in_adjoin_root`

### Files Modified

- `proofs/Proofs/InverseGalois.lean` (added Parts XIII-XIV, ~100 lines)

## Session 2026-03-17 (researcher-4) - X⁴-2 Galois Group and General Lemma

**Mode**: REVISIT (WEAK knowledge score 4)
**Outcome**: progress — new proof file with infrastructure and X⁴-2 analysis

### What I Did

- Created `proofs/Proofs/InverseGaloisX4Sub2.lean` with new formalization
- **PROVED** general lemma `irreducible_natDegree_dvd_gal_card`: for any separable irreducible f/ℚ, natDegree(f) | |Gal(f)| — generalizes `prime_degree_dvd_card`
- **PROVED** X²+1 is irreducible over ℚ (from first principles: degree 2 with no root since r²+1 > 0)
- **PROVED** X⁴-2 irreducible (Eisenstein), separable, degree 4, monic
- **PROVED** 4 | |Gal(X⁴-2)| (from general lemma)
- **PROVED** |Gal(X⁴-2)| | 24 (embeds in S₄ via galActionHom)
- Documented proof strategy for |Gal(X⁴-2)| = 8 (D₄ realization)

### Sorries (3)

1. `x_sq_add_1_has_root_in_x4_splitting_field` — counting argument showing X²+1 has root in SF. Math clear (4 roots can't all have ratios ±1). Lean API for extracting 3rd element from Fintype rootSet needed.
2. `two_dvd_x4_splitting_field_finrank` — tower law giving 2 | [SF:ℚ]. Depends on (1) and Module.finrank_mul_finrank type inference issue for intermediate fields.
3. `x_fourth_sub_2_gal_card = 8` — needs upper bound: X⁴-2 splits in ℚ(⁴√2,i) with [ℚ(⁴√2,i):ℚ] = 8. Requires showing i ∉ ℚ(⁴√2) (embedding into ℝ argument).

### Key Observations

- `Module.finrank_mul_finrank` has type inference issues when applied to `ℚ⟮ω⟯` intermediate fields — the same issue affects the existing X³-2 proof in InverseGalois.lean. May be a Mathlib version change.
- The general `irreducible_natDegree_dvd_gal_card` lemma is a clean contribution that should be useful for any future Galois group computation.
- X²+1 irreducibility from first principles avoids cyclotomic API entirely (no `cyclotomic_four` named lemma in current Mathlib).

### Files Modified

- `proofs/Proofs/InverseGaloisX4Sub2.lean` (created)
- `proofs/Proofs.lean` (added import)
- `research/problems/abel-ruffini-oq-01/knowledge.md` (this file)

## Session 2026-03-14 (researcher-2) - Verification and Assessment

**Mode**: REVISIT (depth-first, RICH knowledge score 59)
**Outcome**: verified, at frontier of formalizability

**What we did**: Docker build verified (2 expected sorries). Confirmed KroneckersJugendtraum.lean has Kronecker-Weber as statement only (not proved). Updated outdated next steps. No tractable path to further progress without new Mathlib infrastructure.

## Session 2026-02-21 (Session 1) - Initial Exploration and Formalization

**Mode**: FRESH
**Outcome**: progress — first Lean formalization created

### What I Did

- Explored the mathematical landscape of the Inverse Galois Problem
- Surveyed Mathlib4 infrastructure: `IsCyclotomicExtension.isGalois`, `IsCyclotomicExtension.Aut.commGroup`, `galCyclotomicEquivUnitsZMod`, `ZMod.card_units_eq_totient`
- Created `proofs/Proofs/InverseGalois.lean` with formal Lean content
- Created gallery data at `src/data/proofs/inverse-galois/`
- Added to `listings.json` and `Proofs.lean`

### Key Findings

- Mathlib has `IsCyclotomicExtension.isGalois` — cyclotomic extensions are automatically Galois
- Mathlib has `IsCyclotomicExtension.Aut.commGroup` — cyclotomic Galois groups are abelian
- Mathlib has `galCyclotomicEquivUnitsZMod` — requires irreducibility of cyclotomic poly over ℚ
- The irreducibility of Φₙ(x) over ℚ is a classical theorem (Gauss 1801) NOT directly in Mathlib as a standalone theorem — typically assumed as hypothesis in Mathlib theorems
- The problem is genuinely open in general, but well-known cases (abelian, solvable, symmetric groups) are provable

### Files Modified

- `proofs/Proofs/InverseGalois.lean` (created)
- `src/data/proofs/inverse-galois/meta.json` (created)
- `src/data/proofs/inverse-galois/annotations.json` (created)
- `src/data/proofs/inverse-galois/index.ts` (created)
- `src/data/proofs/inverse-galois/tacticStates.json` (created)
- `src/data/proofs/listings.json` (updated)
- `proofs/Proofs.lean` (updated with import)
- `research/problems/abel-ruffini-oq-01/knowledge.md` (this file)

### What We Proved (compile-time)

1. `cyclotomic_field_isGalois`: CyclotomicField n ℚ is Galois over ℚ
2. `cyclotomic_galois_isAbelian`: The Galois group is abelian
3. `cyclotomic_galois_group_iso_units_zmod`: Gal(Φₙ/ℚ) ≅ (ZMod n)ˣ (uses irreducibility axiom)
4. `units_zmod4_card` = 2, `units_zmod5_card` = 4, `units_zmod7_card` = 6 (decide)
5. `units_zmodPrime_card` = p-1 for prime p
6. `a5_not_solvable`: A₅ is not solvable (proven)
7. `solvable_iff_solvable_galois_group`: Connection to Abel-Ruffini (proven)

### What's Axiomatized (not proven in Lean)

1. `cyclotomic_irreducible_over_rationals`: Φₙ(x) is irreducible over ℚ (classical, not in Mathlib as standalone)
2. `abelian_realizable`: All abelian groups realizable (needs Kronecker-Weber)
3. `shafarevich_theorem`: All solvable groups realizable (Shafarevich 1954, deep)

### What Has Sorry

1. `inverse_galois_problem_open_conjecture`: The main open problem
2. `symmetric_group_realizable`: Needs Hilbert irreducibility theorem
3. `connection_to_abel_ruffini`: The specific polynomial example
4. One more in the A₅ realization discussion

### Next Steps

1. Try to prove `cyclotomic_irreducible_over_rationals` in Lean — this should be in Mathlib somewhere, perhaps under a different name
2. Search for Kronecker-Weber in Mathlib (might not be there yet)
3. Consider building a more computational example: explicitly compute Gal(ℚ(ζ₅)/ℚ) using Mathlib
4. Possibly extend to show that some specific non-abelian group (like S₃) is realizable using an explicit polynomial

## Mathematical Context

### The Cyclotomic Approach (What We Formalized)

For the Galois group of the n-th cyclotomic field:
- `CyclotomicField n ℚ` = splitting field of Φₙ(X) over ℚ
- `IsGalois ℚ (CyclotomicField n ℚ)` — Galois extension
- `Gal(CyclotomicField n ℚ / ℚ) ≅ (ZMod n)ˣ` — abelian Galois group

For prime p:
- `(ZMod p)ˣ` is cyclic of order p-1
- So Gal(ℚ(ζₚ)/ℚ) is cyclic of order p-1

### Known Realizability Results

| Group Family | Source | Status in Lean |
|---|---|---|
| Trivial group | ℚ/ℚ | Easy (not formalized yet) |
| Cyclic Cₙ | Cyclotomic subfields | Partially (via autEquivPow) |
| Abelian | Kronecker-Weber | Axiom |
| Solvable | Shafarevich 1954 | Axiom |
| Sₙ | Hilbert irreducibility | Sorry |
| Aₙ (n≥5) | Various | Not formalized |
| Most simple groups | Case by case | Not formalized |
| M₂₃ (sporadic) | Unknown | Open math problem |
| General | **OPEN** | Open math problem |

### Mathlib Infrastructure Used

```
Mathlib.NumberTheory.Cyclotomic.Gal
  - galCyclotomicEquivUnitsZMod: polynomial Galois group ≅ (ZMod n)ˣ
  - IsCyclotomicExtension.Aut.commGroup: abelian Galois group
  - IsCyclotomicExtension.autEquivPow: automorphisms ≃* (ZMod n)ˣ

Mathlib.NumberTheory.Cyclotomic.Basic
  - IsCyclotomicExtension.isGalois: cyclotomic extensions are Galois
  - CyclotomicField: the splitting field of Φₙ(X)
  - IsCyclotomicExtension instance for characteristic 0

Mathlib.FieldTheory.Galois.Basic
  - IsGalois: the Galois extension class
  - IsGalois.card_aut_eq_finrank: |Gal| = degree

Mathlib.GroupTheory.SpecificGroups.Cyclic
  - IsCyclic instance for (ZMod p)ˣ

Mathlib.FieldTheory.AbelRuffini
  - solvableByRad.isSolvable': Abel-Ruffini connection
```

## Blockers / Gaps

1. **Cyclotomic irreducibility over ℚ**: Not a direct standalone Mathlib theorem.
   The theorem is classical (Gauss 1801) but Mathlib typically assumes it as a
   hypothesis. We axiomatized it.
   **Potential fix**: Look in `Mathlib.RingTheory.Polynomial.Cyclotomic.Irreducible`
   or search for `IsIntegral.minpoly_eq_cyclotomic`.

2. **Kronecker-Weber theorem**: The proof that every abelian extension of ℚ is
   cyclotomic. This deep result is not yet in Mathlib (as of 2026-02).

3. **Hilbert irreducibility theorem**: Needed for symmetric group realization.
   Not in Mathlib.

4. **Shafarevich's theorem**: 50+ pages of algebraic number theory. Not in Lean.

## Session 2026-03-19 (researcher-7) - Proof Architecture for no_subgroup_order_15

**Mode**: REVISIT (RICH knowledge score 88)
**Outcome**: progress — established full proof architecture for Sylow helper lemma

### What Was Done

Proved the outer structure of `no_subgroup_order_15` (S₅ has no subgroup of order 15):
1. Cauchy's theorem (`exists_prime_orderOf_dvd_card`) gives σ of order 5, τ of order 3 in H
2. Coercion to Perm(Fin 5): σ^5=1, σ≠1, τ^3=1, τ≠1 (via `calc` + `congr 1` + `Subtype.ext`)
3. `perm_fin5_order5_order3_not_commute` (native_decide) gives immediate contradiction
4. Reduced to: prove σ and τ commute via Sylow theory (1 sorry)

Also resolved merge conflict (InverseGaloisA5.lean) from concurrent researcher activity.

### Key Discoveries

- `exists_prime_orderOf_dvd_card` needs `Fintype` (not `Finite`) and `Fintype.card` (not `Nat.card`)
- `pow_orderOf_eq_one σ` + `hσ : orderOf σ = 5`: use `calc` with `congr 1; exact hσ.symm` (avoids rw motive error)
- `Subtype.ext heq` converts `(σ : Perm(Fin 5)) = 1` to `σ = (1 : ↥H)` cleanly
- `simpa using congr_arg Subtype.val this` handles subtype→parent type coercion for pow/one

### Remaining Sorries

1. **Sylow commutation** (in `no_subgroup_order_15`): Show σ*τ = τ*σ via:
   - n₅ = 1, n₃ = 1 (Sylow counting)
   - P₅, P₃ normal (Subsingleton → normal)
   - σ ∈ P₅, τ ∈ P₃ (IsPGroup.exists_le_sylow)
   - Commutator [σ,τ] ∈ P₅ ∩ P₃ = ⊥

2. **no_subgroup_order_30**: Two cases:
   - H ⊆ A₅: index 2 → normal → contradicts A₅ simple (alternatingGroup.isSimpleGroup_five)
   - H ⊄ A₅: sign kernel argument gives |H ∩ A₅| = 15

### Docker Build

Clean build with 2 expected sorries (down from original 2 sorries, now with proof structure established).

