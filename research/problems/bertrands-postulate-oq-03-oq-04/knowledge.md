# bertrands-postulate-oq-03-oq-04 — Knowledge Base

## Problem Statement

PNT-based asymptotic for prime gaps in short intervals.

For a "short" interval [x, x+h], how many primes does it contain?
The PNT prediction: π(x+h) - π(x) ~ h/ln(x) when h is not too small.

## Status

- **Gallery status**: axiomatized (1 axiom: shortIntervalPNT_rh_conditional)
- **Lean files**: BertrandsPostulateOQ03OQ04.lean (0 sorries, 1 axiom)
- **Aristotle companion**: BertrandsPostulateOQ03OQ04Aristotle.lean (0 sorries after fix)

## Sessions

### Session 2026-04-22 (Session 1) - Aristotle Sorry Resolution

**Mode**: REVISIT
**Outcome**: completed

#### What I Did
- Read the 4 Lean files for this problem family
- Found 2 sorries in BertrandsPostulateOQ03OQ04Aristotle.lean
  - `pnt_1c_logx_tendsto`: needed filter product proof
  - `long_interval_density_from_pnt'`: needed Tendsto.sub algebraic decomposition
- Confirmed both proofs were already written (identically) in BertrandsPostulateOQ03OQ04OQ03.lean
  as `pnt_at_scaled_point` and `pnt_density_long_interval`
- Copied the proofs into the Aristotle file (2→0 sorries)

#### Key Findings
- `pnt_1c_logx_tendsto` = `pnt_at_scaled_point` in OQ03 (identical theorem/proof)
- `long_interval_density_from_pnt'` = `pnt_density_long_interval` in OQ03 (identical)
- The main file (OQ04) and OQ03 file have 0 sorries and were already clean
- Research problem metadata had stale sorryCount: 1 for OQ03 (actual: 0)

#### Files Modified
- proofs/Proofs/BertrandsPostulateOQ03OQ04Aristotle.lean (2→0 sorries)
- src/data/research/problems/bertrands-postulate-oq-03-oq-04.json (updated knowledge)

#### Next Steps
None — all sorries resolved. Problem correctly axiomatized.

### Session 2026-04-28 (Session 2) - Metadata Reconciliation

**Mode**: REVISIT
**Outcome**: completed

#### What I Did
- Verified actual Lean state via `git show HEAD:`:
  - BertrandsPostulateOQ03OQ04.lean: 0 sorries, 1 axiom
  - BertrandsPostulateOQ03OQ04Aristotle.lean: 0 sorries, 0 axioms
  - BertrandsPostulateOQ03OQ04OQ03.lean: 0 sorries (JSON had stale 1)
  - Gallery meta.json: status `axiomatized`, badge `axiom`, sorries 0 — correct
- Reconciled JSON: phase NEW→COMPLETED, status active→completed, sorryCount 1→0 for OQ03 sub-file
- Updated progressSummary, lastUpdate, nextSteps cleared
- No code changes — pool entry was simply stale (`active` despite work done in 2026-04-22 session)

#### Key Findings
- The single remaining axiom `shortIntervalPNT_rh_conditional` encodes RH + von-Koch error term;
  this is a deep result, NOT provable from current Mathlib — keeping as axiom is correct
- Pool sweep value: this is exactly the kind of stale `status: active` flagged in researcher feedback
  memory — high-knowledge problems with completed work but uncleaned pool metadata

#### Files Modified
- src/data/research/problems/bertrands-postulate-oq-03-oq-04.json (phase, status, sorryCount fix)
- research/problems/bertrands-postulate-oq-03-oq-04/knowledge.md (this entry)
