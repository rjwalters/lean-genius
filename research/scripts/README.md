# research/scripts/

Standalone helpers kept next to the research data. The agent-facing Aristotle
pipeline lives in `scripts/aristotle/` (see `research/ARISTOTLE-WORKFLOW.md`);
the three shell scripts here are the older direct-CLI wrappers that
`package.json` and `research/SORRY-CLASSIFICATION.md` still point at.

| File | Role |
|------|------|
| `aristotle-status.sh` | Status of all Aristotle jobs; behind `pnpm aristotle`, `pnpm aristotle:retrieve` (`--retrieve`), `pnpm aristotle:json` (`--json`) |
| `aristotle-submit.sh` | Submit Lean files to Aristotle (cited by `SORRY-CLASSIFICATION.md` pre-submission checklist) |
| `validate-for-aristotle.sh` | Pre-submission validation for Aristotle compatibility |
| `verify_birthday_oq03_*.py` (11 files) | Numeric/symbolic certificates for `birthday-problem-oq-03-…` sessions (gap constant, g1 coefficient, saddle point, Poisson gap, second order) |
| `verify_cbrt3_oq04_s*_convergent.py` (6 files) | Continued-fraction convergent lower bounds for `cbrt3-oq-04` sessions S25–S34 |
| `verify-spherical-dual.py` | Numerical check for `spherical-law-of-cosines-oq-03` |
| `verify_repunit_oq01.py` | Brute-force certificate for `repunit-oq-01` |
| `verify_zsqrtd_neg_two_oq02_scope.py` | ORIENT-phase scope check for `zsqrtd-neg-two-oq-02` |

The `verify_*.py` certificates are referenced from the corresponding
`src/data/research/problems/<slug>.json` entries; each prints `OK` (or the
computed constants) and exits 0 on a clean run.
