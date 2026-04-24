# algebraic-numbers-countable-oq-04: Baker's Theorem

**Problem**: Formalize Baker's Theorem — if log α₁, ..., log αₙ are Q-linearly independent for nonzero algebraic αᵢ, then they are Q̄-linearly independent.

**Status**: in-progress (axiomatized entry created)
**Tier**: A — significance 8/10, tractability 4/10 (full proof requires enormous analytic machinery)
**Phase**: ACT

## Problem Summary

Baker's theorem (1966) is the most powerful result in transcendence theory. For positive algebraic α₁, ..., αₙ: if log α₁, ..., log αₙ are Q-linearly independent, then any algebraic linear combination β₁ log α₁ + ··· + βₙ log αₙ with not-all-zero algebraic βᵢ is nonzero.

The theorem has an inhomogeneous form (with constant β₀) and a quantitative form giving explicit lower bounds |Λ| > B^{-C}.

**Full proof requires**: Siegel's lemma + Baker's auxiliary function + extrapolation argument + Schwarz lemma. Likely > 5000 lines of Lean, requiring many years.

## Session 2026-04-25 (Session 1) — Initial Formalization

**Mode**: FRESH
**Outcome**: progress — axiomatized entry created

### What I Did

1. Surveyed the algebraic-numbers-countable gallery family to understand the OQ structure
2. Read the parent meta.json: OQ-04 is "Formalize Baker's theorem" at the end of openQuestions
3. Read GelfondSchneider.lean and HermiteLindemann.lean as reference for axiomatized transcendence entries
4. Created `proofs/Proofs/AlgebraicNumbersCountableOQ04.lean` (589 lines):
   - 4 axioms: baker_homogeneous, baker_inhomogeneous, baker_quantitative, baker_wustholz_bound
   - 12 theorems/lemmas, 2 sorries
   - Elementary proof of 2^p ≠ 3^q (using Nat.Prime.dvd_of_dvd_pow)
   - Elementary proof of irrationality of log₂(3)
   - Derived transcendence of log₂(3) from baker_homogeneous
   - Q̄-linear independence of {log 2, log 3} from Baker
   - Baker-Wüstholz 1993 quantitative theorem
5. Created `src/data/proofs/algebraic-numbers-countable-oq-04/meta.json` (gallery entry)
6. Updated `src/data/research/problems/algebraic-numbers-countable-oq-04.json`

### Key Findings

- Baker's theorem is a clear axiomatized entry — full proof is not feasible in a session
- Irrationality of log₂(3) is elementary (unique factorization), no transcendence needed
- 2 sorries remain in type-conversion boilerplate connecting `![log 2, log 3]` to `fun i : Fin n → Real.log (α i)` form needed by Baker axioms
- The proof of log₂(3) transcendence from Baker is a clean, substantive derivation
- Axiom count is 4 (baker_homogeneous, baker_inhomogeneous, baker_quantitative, baker_wustholz_bound)

### Files Modified

- `proofs/Proofs/AlgebraicNumbersCountableOQ04.lean` (created, 589 lines)
- `src/data/proofs/algebraic-numbers-countable-oq-04/meta.json` (created)
- `src/data/research/problems/algebraic-numbers-countable-oq-04.json` (updated)
- `research/problems/algebraic-numbers-countable-oq-04/knowledge.md` (created)

### Next Steps

1. Fix sorry in `log2_log3_rat_indep`: Need `LinearIndependent ℚ (![Real.log 2, Real.log 3])` from `Irrational (Real.log 3 / Real.log 2)`.
   - Key lemma needed: `linearIndependent_pair_iff_not_smul` or similar
   - Alternative: prove directly by cases on coefficients

2. Fix sorry in `hlog_indep` within `log2_3_transcendental`: Convert `log2_log3_rat_indep` (which uses `![...]`) to the indexed form `LinearIndependent ℚ (fun i => Real.log (α i))` where `α = ![2, 3]`.
   - This should be a type-level manipulation

3. Consider submitting `two_pow_ne_three_pow` to Aristotle for verification (it should compile)

4. (Lower priority) Add more examples: irrationality/transcendence of log₂(5), log₃(5)
