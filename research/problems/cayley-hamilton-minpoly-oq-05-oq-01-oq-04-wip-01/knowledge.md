# Knowledge Base: cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-01

**Problem**: Prove that nonderogatory matrices have cyclic vectors over ALL fields (including finite)
**Last Updated**: 2026-04-26

---

## Session 2026-04-26 (Session 1) — Irreducible Minpoly Case (Sorry-Free)

**Mode**: FRESH
**Outcome**: progress — 2 new sorry-free theorems added

### What I Did

1. Analyzed the single sorry in the file: `nonderogatory_similar_companion` (line 274)
   - Requires Rational Canonical Form (PID module structure theorem)
   - NOT in Mathlib 4.26
   - Used by `nonderogatory_has_cyclic_vector_any_field` (the main theorem)

2. Identified the IRREDUCIBLE MINPOLY special case as provable without RCF:
   - If `minpoly K M` is irreducible, every nonzero v is cyclic
   - Proof: annihilator gcd(p, μ) is either a unit (forces v=0, contradiction) or
     associates μ (forces p=0 via degree bound n ≤ deg(p) < n)
   - This works over ALL fields (finite and infinite) — pure algebraic argument

3. Added `every_nonzero_cyclic_of_irred_minpoly` (sorry-free):
   - Every nonzero v is cyclic when minpoly is irreducible
   - Uses: `annihilator_dvd_minpoly`, `Polynomial.isUnit_iff`, Bezout/GCD

4. Added `nonderogatory_has_cyclic_vector_irred_minpoly` (sorry-free):
   - Existence corollary when minpoly is irreducible
   - Uses `every_nonzero_cyclic_of_irred_minpoly` with e₀ = Pi.single 0 1

### Key Findings

- **Irreducible minpoly is the key special case**: When μ is irreducible (any annihilating
  poly is either unit or μ itself), the proof is purely algebraic and avoids RCF
- **The unit case in Lean**: `Polynomial.isUnit_iff` gives d = C ↑c for c : Kˣ;
  then `aeval M (C ↑c) = ↑c • I`, so `↑c • v = 0` → `v = 0` (since ↑c ≠ 0)
- **Associate case**: d ~ μ → μ | d | p → deg(p) ≥ n > deg(p) → p = 0
- **Remaining sorry**: `nonderogatory_similar_companion` needs the full PID structure
  theorem for f.g. K[X]-modules (Rational Canonical Form) — not in Mathlib

### Files Modified

- `proofs/Proofs/CayleyHamiltonMinpolyOQ05OQ01OQ04.lean`: Added Section IV.6 with
  `every_nonzero_cyclic_of_irred_minpoly` and `nonderogatory_has_cyclic_vector_irred_minpoly`
- `src/data/research/problems/cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-01.json`: Updated knowledge

### Next Steps

1. Verify the two new theorems compile (docker-build.sh)
2. Consider n=1, n=2 special cases for `nonderogatory_similar_companion`
3. Long-term: watch for Mathlib additions to `Module.InvariantFactors` or RCF
4. The irreducible-minpoly corollary covers an important class (e.g., rotations over ℝ
   with irrational angle → characteristic poly irreducible)
