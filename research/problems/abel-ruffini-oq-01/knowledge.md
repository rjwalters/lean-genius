# Knowledge: The Inverse Galois Problem (abel-ruffini-oq-01)

## Problem Summary

The Inverse Galois Problem (IGP) asks: for every finite group G, does there exist a Galois extension K/ℚ with Gal(K/ℚ) ≅ G?

**Status**: OPEN in general. The full conjecture is unproven.

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
