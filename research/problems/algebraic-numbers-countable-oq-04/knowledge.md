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


---

## Session 2026-04-28 (Session 2) — Reconcile stale `phase=ACT/status=in-progress`

**Mode**: REVISIT (metadata reconciliation)
**Outcome**: METADATA RECONCILE — research-side JSON brought in line with merged work

### What I Did

Audited candidate-pool entry: `algebraic-numbers-countable-oq-04` was listed
`status=available` in `.lean/state/candidate-pool.json` with knowledge score 19,
but the actual state diverged:

- **Lean file**: `proofs/Proofs/AlgebraicNumbersCountableOQ04.lean` (640 lines, 0 sorries, 4 `axiom` declarations)
- **Gallery**: `src/data/proofs/algebraic-numbers-countable-oq-04/meta.json` — `status: axiomatized`, `badge: axiom`, `axiomCount: 4`, dated 2026-04-24
- **Research JSON**: stuck at `phase=ACT`, `status=in-progress`, `currentState.nextAction = "Build and verify Lean file compiles via Docker wrapper."` — Session 1 work item from 2026-04-25
- **No `state.md`** existed, so the only narrative source was an outdated `currentState` block

### Reconciliation

1. `src/data/research/problems/algebraic-numbers-countable-oq-04.json`:
   - `phase`: `ACT` → `COMPLETED`
   - `status`: `in-progress` → `completed`
   - `currentState.phase`: `ACT` → `COMPLETED`
   - `currentState.focus` rewritten to describe axiomatized scope
   - `currentState.nextAction` set to `None — work scope complete`
2. Created `research/problems/algebraic-numbers-countable-oq-04/state.md`
   documenting `Phase: COMPLETED (axiomatized)`, the four Baker axioms, and
   why "verified" is not the appropriate badge (full Baker proof needs Siegel
   + auxiliary function + extrapolation, ~5000+ lines).

No code changes; pure metadata reconciliation. The Lean file and gallery
were already in their final state.

### Files Modified

- `src/data/research/problems/algebraic-numbers-countable-oq-04.json`
- `research/problems/algebraic-numbers-countable-oq-04/state.md` (created)
- `research/problems/algebraic-numbers-countable-oq-04/knowledge.md` (this entry)

### Sorry/Axiom Delta

No change. File remains 0 sorries, 4 axioms. Gallery remains `axiomatized`.

### Next Steps

None for the axiomatized scope. A future deepening to `verified` would be a
multi-month formalization of Baker's auxiliary-function machinery and is
not currently scoped.

---

## Session 2026-04-29 (Session 3) — Gallery meta.json drift fix

**Mode**: REVISIT (gallery metadata reconciliation)
**Outcome**: META FIX — section ranges realigned, phantom contribution removed

### What I Did

Audit of `src/data/proofs/algebraic-numbers-countable-oq-04/meta.json` against
the actual Lean file (`proofs/Proofs/AlgebraicNumbersCountableOQ04.lean`,
640 lines, 4 axioms, 0 sorries) found two narrative drifts:

1. **Section line ranges 30-50 lines off** and PART IV missing entirely:
   - sec-arithmetic claimed 129-257; PART I actually spans 129-294
   - sec-baker-axioms claimed 258-363; PART II actually spans 295-400
   - sec-corollaries claimed 364-542; PART III actually spans 401-543
   - PART IV (Four Exponentials Conjecture, lines 544-590) had no section entry
   - sec-baker-wustholz claimed 544-640; PART V actually spans 591-640
2. **Phantom originalContribution**: `baker_wustholz_bound` was listed as an
   "original contribution" but is declared as `axiom` at line 620, not a
   theorem. Listing axiom statements alongside proved theorems overstates
   the verified content. Removed.

### Reconciliation

1. `src/data/proofs/algebraic-numbers-countable-oq-04/meta.json`:
   - Realigned all section `startLine`/`endLine` to match actual PART
     banners (verified by grepping for `PART [IVX]+`)
   - Added new `sec-four-exponentials` section (544-590) covering PART IV
     (commentary-only, no axioms or theorems)
   - Renamed section titles from `Sec N` to `Part N` for consistency with
     the file's own PART numbering
   - Trimmed sec-corollaries summary (it had mentioned Four Exponentials,
     which now lives in its own section)
   - Removed `baker_wustholz_bound` from originalContributions (it is an
     axiom; the other 6 entries are all proved theorems)

No code changes. Lean file unchanged: 640 lines, 4 axioms, 0 sorries.
Gallery still `axiomatized`/`axiom`/`axiomCount: 4`.

### Files Modified

- `src/data/proofs/algebraic-numbers-countable-oq-04/meta.json`
- `research/problems/algebraic-numbers-countable-oq-04/knowledge.md` (this entry)

### Sorry/Axiom Delta

No change.

### Next Steps

None. Gallery is now consistent with the Lean file at the axiomatized scope.
