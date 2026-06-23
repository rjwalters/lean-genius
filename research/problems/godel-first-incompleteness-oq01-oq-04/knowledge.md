# Knowledge Base: godel-first-incompleteness-oq01-oq-04

## Problem Summary

**Title**: Gödel's Diagonal Lemma: Fixed-Point Theorem Formalization
**Parent**: godel-first-incompleteness-oq01 (companion)
**Goal**: Formalize the Diagonal Lemma as a general principle; derive G's self-reference from it

## Problem Statement

For all φ(x), there exists σ such that F ⊢ σ ↔ φ(⌈σ⌉).

The Diagonal Lemma (Fixed-Point Lemma) states: for any formula with one free variable,
there exists a self-referential sentence σ that provably says of itself that it satisfies φ.

In the context of godel-first-incompleteness-oq01: the G_self_reference axiom is the
instance φ(x) = ¬Prov(x). OQ04 shows this is not a fundamental axiom but a consequence
of the general Diagonal Lemma.

---

## Session 2026-05-03 (Session 1, researcher-3) — COMPLETED

**Mode**: FRESH
**Outcome**: COMPLETED — 5 axioms, 0 sorries, 9 theorems, gallery entry created

### What I Did

- Selected problem from available pool (score 0, EMPTY tier)
- Assessed: clear parent infrastructure in GodelFirstIncompletenessOQ01.lean
- Designed standalone namespace GodelDiagonal with 5-axiom basis
- Created proofs/Proofs/GodelFirstIncompletenessOQ01OQ04.lean (241 lines)
- Created gallery entry src/data/proofs/godel-first-incompleteness-oq01-oq-04/
- Updated Proofs.lean, candidate-pool.json, research problem JSON

### Key Design Decisions

Meta-level vs object-level Diagonal Lemma:
- Meta-level form (implemented): for all ψ, there exists σ such that (⊢σ)↔(⊢ψ(⌈σ⌉)) in Lean
- Object-level form (stronger): for all ψ, there exists σ such that F⊢(σ↔ψ(⌈σ⌉)) as formula in F
- Meta-level suffices for G_not_provable; object-level needed only for neg_G_prov
- neg_G_prov remains an axiom (cannot be derived from meta-level form alone)

Axiom count: same as OQ-01 (5), better structure:
- OQ-01 had G_self_reference as a G-specific axiom + 4 others
- OQ-04 has diagonal_lem (GENERAL) + 4 others
- G_self_reference becomes G_spec (theorem, 1 line)

### 5 Axioms

1. Provable : Formula → Prop (same as OQ-01)
2. d1: if ⊢φ then ⊢Prov(⌈φ⌉) (same as OQ-01)
3. diagonal_lem: for all ψ:N→Formula, there exists σ with (⊢σ)↔(⊢ψ(⌈σ⌉)) [REPLACES G_self_reference]
4. neg_G_prov: ⊢¬G → ⊢Prov(⌈G⌉) (same role as neg_G_prov_G in OQ-01)
5. omega_cons: ¬⊢G → ¬⊢Prov(⌈G⌉) (same as omega_consistency_G in OQ-01)

### 9 Theorems (all 0 sorries)

1. G_spec: (⊢G)↔(⊢¬Prov(⌈G⌉)) — derived from diagonal_lem (was axiom in OQ-01)
2. G_not_provable: clean 3-step proof via D1 + G_spec + Consistent
3. neg_G_not_provable
4. first_incompleteness
5. G_undecidable
6. prov_fixed_point_exists — another instance of diagonal_lem
7. arb_fixed_point_exists — the general statement
8. consistency_sentence_exists — third instance
9. G_self_reference_fwd — forward direction of OQ-01's axiom, derived here

### Status
- Axiom count: 5
- Sorry count: 0 (pending Docker build verification)
- Theorems proved: 9
- Phase: COMPLETED
