# Inverse Galois Problem: Non-Solvable Frontier (OQ-01)

**Problem**: Does every finite group appear as a Galois group over Q?

**Status**: IN-PROGRESS (structural analysis complete, more group realizations needed)

## Summary

The Inverse Galois Problem (IGP) asks whether every finite group is isomorphic to the Galois group of some Galois extension of Q. This is one of the most important open problems in algebra.

**Key insight**: The problem divides into solvable and non-solvable realms:
- Solvable groups: All realizable by Shafarevich's theorem (axiomatized)
- Non-solvable groups: Require explicit polynomial constructions (A5, S5 done)

## Session 2026-03-24 (Session 1) - Solvability Frontier

**Mode**: FRESH
**Outcome**: progress

### What I Did
- Created `InverseGaloisOQ01.lean` (448 lines, 31 theorems, 0 axioms)
- Proved the complete solvability characterization: Sn is solvable iff n <= 4
- Proved A5 is simple (from Mathlib), not solvable, and perfect ([A5,A5] = A5)
- Proved Galois correspondence degree formulas: [K:K^H] = |H| and [K^H:F] = [G:H]
- Proved Cayley's embedding theorem
- Stated the full Inverse Galois Conjecture formally
- Created gallery entry with metadata

### Key Findings
- The solvability divide at n=5 is the fundamental boundary
- A5 perfection is the core obstruction: the derived series stalls at A5
- The sign homomorphism gives the exact sequence 1 -> An -> Sn -> C2 -> 1
- Galois correspondence provides automatic quotient realizability
- Every quotient of a realized group is realized (via fixed fields)

### Mathlib Gaps
- No `MulAction.toPermHom_injective` (proved manually)
- `IsSimpleGroup` API uses `eq_bot_or_eq_top_of_normal` not `eq_bot_or_eq_top`

### Files Modified
- `proofs/Proofs/InverseGaloisOQ01.lean` (new, 448 lines)
- `src/data/proofs/inverse-galois-oq-01/` (new gallery entry)
- `src/data/research/problems/inverse-galois-oq-01.json` (updated knowledge)

### Next Steps
- Realize PSL(2,7) as Galois group over Q (order 168, second-smallest simple group)
- Realize A6 (order 360) via explicit polynomial
- Prove quotient realizability formally using Mathlib compositum machinery
- Connect S5 realization to the census (import AbelRuffiniOQ04OQ01)

## Session 2026-03-24 (Session 2) - Alternating Group Characterization & Quotient Realizability

**Mode**: REVISIT (rich knowledge, phase ACT)
**Outcome**: progress

### What I Did
- Extended `InverseGaloisOQ01.lean` from 448 → 591 lines, 31 → 39 theorems
- Proved `an_not_solvable_of_ge_five`: Aₙ is not solvable for n ≥ 5 (via exact sequence 1 → Aₙ → Sₙ → C₂ → 1)
- Proved `an_solvable_iff`: Aₙ is solvable iff n ≤ 4 (complete characterization)
- Proved `quotient_is_galois`: K^H/F is Galois when H ◁ Gal(K/F) (via Mathlib instance)
- Defined `quotient_galois_equiv`: the FTGT isomorphism Gal(K/F)/H ≅ Gal(K^H/F)
- Proved `fixed_field_galois_card_eq_index`: |Gal(K^H/F)| = [Gal(K/F) : H]
- Proved `quotient_of_galois_realized`: quotient realizability as existence theorem
- Proved `realizability_closed_under_quotients`: closure under quotients

### Key Findings
- `inferInstance` resolves `IsGalois F (fixedField H)` automatically when H is normal — Mathlib has the instance
- `IsGalois.normalAutEquivQuotient H` is the key Mathlib lemma for FTGT quotient isomorphism
- `Subgroup.index` unfolds to `Nat.card (G ⧸ H)` — needs explicit `unfold` in proofs
- For `an_solvable_iff` backward direction: `interval_cases n <;> infer_instance` works (Mathlib has solvability instances for alternating groups of small n)
- No new Mathlib gaps encountered — all new theorems build cleanly from existing API

### Files Modified
- `proofs/Proofs/InverseGaloisOQ01.lean` (extended, 591 lines)
- `src/data/proofs/inverse-galois-oq-01/meta.json` (updated counts)
- `src/data/research/problems/inverse-galois-oq-01.json` (updated knowledge)

### Next Steps
- Prove PSL(2,7) exists as a group (GL(3,F₂) has order 168) via native_decide
- Formalize direct product realizability via coprime-degree compositum
- Connect S5 realization to census (import InverseGaloisA5)

## Session 2026-03-24 (Session 3) - Commutator Theorem & Census Fix

**Mode**: REVISIT (richest available problem, score 29)
**Outcome**: progress

### What I Did
- Extended `InverseGaloisOQ01.lean` from 591 → 723 lines, 39 → 47 theorems
- **Fixed import collision**: InverseGaloisA5 and AbelRuffiniOQ04OQ01 share top-level `perm_fin5_order5_order3_not_commute`; fixed by adding `private` to duplicates in OQ04OQ01
- **Eliminated 2 census sorries**: `nonsolvable_realized_orders` now sorry-free using `InverseGaloisA5.a5_realizable` (A₅) and `AbelRuffiniOQ04OQ01.gal_card_eq_120` (S₅)
- **Proved [S₅,S₅] = A₅** (`s5_commutator_eq_alternating`): the commutator subgroup of S₅ is exactly A₅
  - Direction 1 (`commutator_le_alternating`): sign hom maps to abelian ℤˣ, so [G,G] ≤ ker(sign) = A₅
  - Direction 2 (`alternating_le_commutator`): A₅ perfect → commutator(↥A₅) = ⊤ → comap + commutator_le + Subgroup.commutator_mono
- Added census integration: `a5_galois_iso`, `s5_galois_iso`, `s5_not_solvable_by_radicals`
- Docker build verified: 0 axioms, 1 sorry (open problem only)

### Key Findings
- `Abelianization.commutator_subset_ker` handles direction 1 cleanly (sign maps [G,G] to 1)
- `Subgroup.commutator_le` + `map_commutatorElement` + `Subgroup.mem_comap`: the clean proof path for direction 2
- `Subgroup.closure_induction` in recent Mathlib uses dependent predicate; use `comap`-based proof instead
- `private` keyword on `native_decide` theorems prevents export collision between files

### Files Modified
- `proofs/Proofs/InverseGaloisOQ01.lean` (extended, 723 lines, 47 theorems)
- `proofs/Proofs/AbelRuffiniOQ04OQ01.lean` (2 theorems made `private` to fix collision)
- `src/data/proofs/inverse-galois-oq-01/meta.json` (updated counts)
- `src/data/research/problems/inverse-galois-oq-01.json` (updated knowledge)

### Next Steps
- Prove Jordan's theorem for S₅: normal subgroups are exactly {⊥, A₅, ⊤}
- Formalize Hilbert irreducibility → all Sₙ realized (axiomatized)
- Add PSL(2,7) characterization and realizability
