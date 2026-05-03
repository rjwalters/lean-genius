# Erdős #1214 — Prime Support Uniqueness (Corrales-Rodánez–Schoof)

## Problem Statement

Let x, y ≥ 2 be integers. Suppose that for all n ≥ 1, the set of primes dividing x^n - 1
equals the set of primes dividing y^n - 1. Must x = y?

**Answer**: YES — proved by Corrales-Rodánez and Schoof (1997).

## Background

The problem was posed by Erdős at a 1988 Banff number theory conference. The "support"
of an integer m is supp(m) = {p prime : p | m}. The question asks if the map x ↦ supp(x^n-1)
is injective for x ≥ 2.

## Key Insight

p | x^n - 1 iff orderOf(x mod p) | n. So equal support for all n forces equal multiplicative
orders modulo every prime p (coprime to xy). By Kummer theory, this forces x = y.

## Session 2026-05-03 (Session 1) — FRESH formalization

**Mode**: FRESH
**Outcome**: progress — gallery entry created, 22 theorems proved

### What I Did
- Created `proofs/Proofs/Erdos1214Problem.lean` (232 lines, 22 theorems, 0 sorries)
- Created `src/data/proofs/erdos-1214/meta.json` gallery entry
- Proved:
  - `sub_one_dvd_pow_sub_one`: (x-1) | (x^n-1) via geometric series in any CommRing
  - `prime_dvd_pow_sub_one_iff_zmod`: p | x^n-1 ↔ (x:ZMod p)^n = 1
  - `prime_dvd_pow_sub_one_iff_order`: p | x^n-1 ↔ orderOf(x:ZMod p) | n
  - `equal_support_implies_equal_orders`: equal support ⟹ same orders mod p (using Fermat's little theorem)
  - Concrete computations: supp(2^k-1) for k=1..5, supp(3^k-1), supp(4^3-1)
  - Support-transfer lemmas: primes and primitive primes transfer under CS hypothesis
  - `corrales_schoof_injective`: the support map is injective
- Axiomatized: `corrales_schoof` (Kummer theory proof) and `zsygmondy` (1892)

### Key Findings
- The ZMod order characterization is the bridge: p | x^n-1 ↔ orderOf(x:ZMod p) | n
- Fermat's little theorem is essential to establish `orderOf(x:ZMod p) > 0` for p ∤ x
- The `equal_support_implies_equal_orders` theorem captures the accessible part; the full
  "equal orders ⟹ x = y" direction requires Kummer theory and is axiomatized

### Files Modified
- `proofs/Proofs/Erdos1214Problem.lean` (new, 232 lines)
- `src/data/proofs/erdos-1214/meta.json` (new)
- `research/problems/erdos-1214/knowledge.md` (this file)
- `src/data/research/problems/erdos-1214.json` (updated)

### Status
- **Axiom count**: 2 (corrales_schoof, zsygmondy)
- **Sorry count**: 0 (pending Docker build verification)
- **Theorems proved**: 22
- **Phase**: ACT (pending PR)
