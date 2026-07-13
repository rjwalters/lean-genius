# Knowledge Base: cube-root-2-irrational-oq-03

Formalize the degree bound: any n-th root of a non-perfect-power is a degree-n algebraic number.

**Status: COMPLETED** — 0 axioms, 0 sorries. File: `proofs/Proofs/CubeRoot2IrrationalOQ03.lean`

---

## Session 2026-04-05 (Session 1) — Degree Bound Proved

**Mode**: FRESH
**Outcome**: completed

### What I Did

1. Generalized the Eisenstein criterion from prime m to any m with a square-free prime factor (p|m, p²∤m)
2. Built `minpoly_nthRoot_eq`: minpoly ℚ (m^(1/n)) = X^n - m using `minpoly.eq_of_irreducible_of_monic`
3. Proved `minpoly_nthRoot_natDegree`: algebraic degree of m^(1/n) is exactly n
4. Proved `adjoin_nthRoot_finrank`: field extension [ℚ(m^(1/n)):ℚ] = n via `IntermediateField.adjoin.finrank`
5. Proved `not_perfect_power_of_sqfree_factor` via p | k + `pow_dvd_pow_of_dvd`
6. Added concrete applications: ∛6, ∛10, ⁵√12, ∜30

### Key Technical Insights

- **`minpoly.eq_of_irreducible_of_monic` arg order**: `(hirr) (haeval) (hmonic)` — from InverseGaloisF20.lean pattern
- **`IntermediateField.adjoin.finrank`**: takes `IsIntegral ℚ α` and gives `finrank ℚ ℚ⟮α⟯ = (minpoly ℚ α).natDegree`
- **`IsIntegral` construction**: `⟨poly, poly.Monic, aeval α poly = 0⟩` — anonymous constructor
- **`pow_dvd_pow_of_dvd`** (without `Nat.` prefix): `a ∣ b → a^n ∣ b^n` for not_perfect_power proof
- **aeval pattern**: same as NthRootIrrationalOQ01 — `simp [map_sub, map_pow, ...] + Real.rpow_mul + simp [hn']`
- **Square-free factor condition**: works for any composite m with a prime factor to the first power, not just primes

### Files Created

- `proofs/Proofs/CubeRoot2IrrationalOQ03.lean` — 204 lines, 0 sorries, 0 axioms
- `src/data/research/problems/cube-root-2-irrational-oq-03.json`
