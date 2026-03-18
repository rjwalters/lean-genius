# Knowledge: The Inverse Galois Problem (abel-ruffini-oq-01)

## Problem Summary

The Inverse Galois Problem (IGP) asks: for every finite group G, does there exist a Galois extension K/ℚ with Gal(K/ℚ) ≅ G?

**Status**: OPEN in general. The full conjecture is unproven.

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

---

## Session 2026-03-18 (researcher-1) - Mathlib API Fix

**Mode**: REVISIT (depth-first, RICH knowledge score 29)
**Outcome**: progress — fixed all build errors in InverseGalois.lean

### What Was Done
Fixed 7 Mathlib API breakages in `InverseGalois.lean` that prevented compilation:

1. **Forward reference** (line 418): `s3_realizable` referenced `x_cube_sub_2_gal_iso_s3_proved`
   before its definition. Fix: moved `s3_realizable` after the proof, used `obtain ⟨iso⟩`.

2. **Associated.natDegree_eq** (line 603): API removed in current Mathlib. Fix: replaced with
   `le_antisymm` using `natDegree_le_of_dvd` in both directions (bidirectional divisibility).

3. **linarith failure** (line 667): Manual rewrite chain + `linarith` broke. Fix: replaced with
   `field_simp` which clears denominators and proves the identity directly.

4. **PowerBasis.finrank/dim** (line 683): `hpb.dim` not definitionally equal to `natDegree`.
   Standalone lemma, sorried pending `AdjoinRoot.powerBasis_dim` API.

5. **exact_mod_cast** (line 692): Cast system changed, can't bridge `AdjoinRoot.of 2 = 0` to
   `(2 : ℚ) ≠ 0`. Standalone lemma, sorried pending AdjoinRoot Field instance fix.

6. **Timeout** (line 700): `cofactor_has_no_root_in_adjoin_root` timed out due to Field diamond.
   Standalone lemma, sorried.

7. **Unused simp arg** (line 645): Removed `map_mul` from `simp only [map_pow, map_mul]`.

### Critical Path Status
All main proof chain theorems compile with 0 errors:
- Parts I-IX: Cyclotomic theory, conjectures, Abel-Ruffini connection ✓
- Part X: `|Gal(X³-2)| = 6` (via splitting field approach) ✓
- Part XII: `Gal(X³-2) ≅ S₃` (bijective galActionHom) ✓
- Part XIII: `(ℤ/nℤ)ˣ` realizability ✓
- Part XIV: `cyclic_group_realizable` (Dirichlet + Galois correspondence) ✓
- `s3_realizable` ✓

### Sorries (5 total)
- 2 **intentional**: open conjecture + symmetric_group_realizable (Hilbert irreducibility)
- 3 **non-essential**: AdjoinRoot standalone lemmas (not on critical path, API breakage)

### Files Modified
- `proofs/Proofs/InverseGalois.lean` — 7 fixes applied
