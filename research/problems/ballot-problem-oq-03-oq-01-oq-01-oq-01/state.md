# Research State: ballot-problem-oq-03-oq-01-oq-01-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-04-24T01:12:29+02:00
**Iteration**: 3

## Current Focus

Proving the Jacobi-Trudi identity via SSYT infrastructure. Two open sorries remain:
- `jdt_weight_sum` (b ≥ 1 branch): JDT bijection ↔ multiset cons/erase identity (~115 lines)
- `jacobi_trudi_ssyt_eq` (k ≥ 3): RSK + algebraic LGV (~300 lines)

## Active Approach

SSYT-based proof, decomposed as follows:
1. `SSYTFin` type defined (entries in Fin n, σ-type domain) ✓
2. `ssytSchurFin` generating function defined ✓
3. `k = 0` base case proved (`schurPolynomial_empty`, `ssytSchurFin_empty`) ✓
4. `k = 1` proved (`ssytSchurFin_one_row` via `List.sortedLE_ofFn_iff` bijection to Sym) ✓
5. `k = 2` proved (`ssytSchurFin_two_row`) modulo `jdt_weight_sum` ✓
6. `jdt_weight_sum` (b ≥ 1) — **open**, decomposition plan in knowledge.md Session 10
7. `jacobi_trudi_ssyt_eq` (k ≥ 3) — **open**, requires RSK + algebraic LGV

## Attempt Count
- Total attempts: 10 (sessions 1-10)
- Current approach attempts: 10
- Approaches tried: 1 (SSYT infrastructure approach)

## Blockers

- **Disk pressure** (1.3 GiB free as of 2026-04-27) blocks Docker build verification.
  Session 10 contributed specification only (no Lean source modifications).
- Pre-existing `BallotProblemOQ03OQ02.lean` upstream issue (fixed in Session 9).

## Next Action (Decomposition from Session 10)

Five-way split of `jdt_weight_sum` (b ≥ 1) into independently submittable lemmas:

1. **`firstViolationIdx`** : `(P, Q) → ¬ColStrictSym → Fin (min a b)` (~15 lines)
2. **`jdt_forward`** : non-col-strict (a, b) → all (a+1, b-1)             (~25 lines)
3. **`jdt_inverse`** : all (a+1, b-1) → non-col-strict (a, b)             (~30 lines)
4. **`jdt_left_inv` + `jdt_right_inv`**                                    (~40 lines)
5. **`jdt_weight_preserve`**                                                 (~6 lines, algebraic)

Total ≈ 115 lines, each piece small enough to submit to Aristotle individually.

## Mathlib API Notes (from Session 10)

- `Sym.cons : α → Sym α n → Sym α n.succ` (line 106 of `Mathlib.Data.Sym.Basic`)
- `Sym.erase : Sym α (n+1) → (a : α) → a ∈ s → Sym α n` (line 203)
- The `Q : Sym n b` ↔ `Sym n ((b-1)+1)` cast uses `Nat.sub_add_cancel hb ▸ Q`
- Weight preservation reduces to `Multiset.prod_cons + Multiset.prod_erase_mul`

## Status of Sub-Approaches

- **JDT bijection** (current path): clear specification, 5-way decomposition ready.
- **Algebraic transfer matrix**: not pursued; would need full RSK for k≥3 anyway.
- **Direct combinatorial inclusion-exclusion**: untried, may avoid bijection but needs invariant.
