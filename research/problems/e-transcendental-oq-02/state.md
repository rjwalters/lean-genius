# Current State

**Phase**: ACT — gallery entry built; 2 axioms tractable, 1 is the main open conjecture
**Since**: 2026-05-04T16:38:18.044Z
**Last Updated**: 2026-05-07
**Iteration**: 2

## Current Focus

Reconciling research metadata with the existing `Proofs/ETranscendentalOQ02.lean`
gallery entry (28 theorems, 3 axioms, 0 sorries, 300 lines). Two axioms are
tractable for future work; the third (`e_absolutely_normal`) is the genuinely
open conjecture this entry is *about*.

## Active Approach

The current Lean entry establishes the framework:
- Definitions: `nthDigit`, `IsNormalInBase`, `IsAbsolutelyNormal`.
- 28 theorems: includes `e_floor`, `e_floor_10..1000000000`, `e_digit1..9`
  (proves first 9 decimal digits 2.718281828 from `Real.exp_one_gt_d9` /
  `Real.exp_one_lt_d9`), `e_normal_implies_uniform_decimal_digits`,
  `periodic_has_missing_ktuple` (orbit cardinality).

Three remaining axioms (per `proofs/Proofs/ETranscendentalOQ02.lean`):
- `rational_digits_eventually_periodic` (line 209) — tractable: rationals have
  eventually periodic base-b digit expansions. Standard pigeonhole proof
  (period divides `φ(q)`); should be provable from Mathlib's `EuclideanDomain`
  or via `Stream'.Periodic` machinery once cast to Fin-b.
- `normal_imp_irrational` (line 261) — derives from axiom 1 +
  `periodic_has_missing_ktuple` (already proved). Discharging axiom 1 first
  then proving 2 is the natural sequence.
- `e_absolutely_normal` (line 271) — the **main open conjecture**. Genuinely
  open as of 2026; will remain axiomatized.

## Blockers

- **Local Lean build unreliable**: Worktree's `proofs/.lake` is a self-cycle
  symlink, so my Docker build attempts hung on `mathlib: cloning` for 14+ min.
  Closing axioms requires careful Mathlib API alignment that's risky without
  fast feedback. Future iterations may need to copy file to main repo and
  build there.

## Next Action

**ACT** — discharge `rational_digits_eventually_periodic`. The proof is
pigeonhole: a rational `p/q` has at most `q` distinct partial remainders
under long-division-by-q, so the digit sequence must repeat with period ≤ q.
The Lean implementation needs:
- Connect `nthDigit b n (p/q : ℝ)` to remainders of `b^n * p mod q`.
- Show `n ↦ b^n * p mod q` factors through `ZMod q`, hence has period
  dividing the multiplicative order of `b` in `(ZMod q)ˣ`.
- Wrap in `eventually` (skip the pre-period).

## Attempt Counts

- Total attempts: 1 (entry built in 2026-05-04 session before research/problems
  was scaffolded; no subsequent attempts on the axioms).
- Current approach attempts: 0
- Approaches tried: 0 (only metadata reconciliation in this session)

## References

- `proofs/Proofs/ETranscendentalOQ02.lean:209` — `rational_digits_eventually_periodic`
- `proofs/Proofs/ETranscendentalOQ02.lean:261` — `normal_imp_irrational`
- `proofs/Proofs/ETranscendentalOQ02.lean:271` — `e_absolutely_normal`
- `src/data/proofs/e-transcendental-oq-02/meta.json` — gallery metadata (correct as of 2026-05-04)
