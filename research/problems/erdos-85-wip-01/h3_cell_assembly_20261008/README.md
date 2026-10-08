# H3 triple-cell assembly gate

The real `PLAN.json` now binds all 384 independently accepted native parts:
the original 90-part baseline, 288 new sweep parts and six residual parts.
No cell compilation or cell acceptance exists here yet. The source and
object ledger retain the exact producer of every part.

`prepare.py` combines the original five-part sample and 85-part campaign
prefix, checking them against the accepted 90-part baseline, then adds the
completed sweep and residual audits. Each imported part must match the
384-way source manifest, its one exact theorem report and three expected
axioms. Duplicate, overlapping, missing or unresolved residues fail. The
result has exactly one independently accepted object per residue 0–383,
with its producer job and execution commit retained.

The script also verifies retained raw producer evidence and pins the
previously reviewed cell source. It prepares a single bounded cloud compile:
one worker, 2 CPUs, 16 GiB, 90 seconds for Lean and a three-minute outer limit.
The two cell exports must each print exactly the three standard logical
axioms and all 384 native part axioms (387 total). This is assembly only;
it does not repeat any native search. All Lean execution must use the existing
cloud builder.

`run.py` defaults to a read-only preflight and checks all 388 imported objects
(384 native parts plus the four runtime/bridge prerequisites). Execution
requires the exact frozen plan hash. It uses the hash-pinned, already tested
bounded subprocess helper from the residual package and preserves rejected
output separately from the reusable cache. `capture.py` binds the terminal
job and execution commit, checks all committed inputs, both 387-axiom reports,
the fresh cell object and every imported object, and reads object metadata
twice to detect changes during collection. Failed assembly gets no cell credit.

Full cell acceptance will then feed the separately prepared H3 stratum
integration; its old failed-producer gate must be replaced with an explicit
binding to the new cell audit. Neither the source bundle nor historical
receipts should be silently rewritten to imply that the failed first
campaign completed.

Validation: 38 metadata tests cover exact coverage, producer/source/
object/axiom drift, duplicate or missing objects, unresolved parts, incomplete
audits and invalid timeout classification; terminal and preflight collection;
stale, future, changed or missing objects; axiom/command/resource drift; and
pending or failed jobs. The baseline inputs are real accepted audit metadata;
future sweep, residual and assembly outcomes are synthetic fixtures. Tests run
no Lean or finite search. Real cloud preflight and terminal acceptance are
still required.

## Independently accepted preflight

Read-only job `20261008T145222-erdos85__h3-triple-formal-20261007-589730`,
execution pin `9f4301c1a5a4670abe56f4e488fbad189fc9ed3f`, exited zero.
`preflight-evidence1/AUDIT.json` is `CELL_ASSEMBLY_PREFLIGHT_AUDIT_PASS`:
all 384 part objects and four prerequisites checked, source/input pins
unchanged, actual limits two CPUs and 16 GiB, no cell source/object or
attempt directory present. The frozen plan SHA256 is
`1818caee727c64640ad17fde34a57c04a81afee5c723739d9a44f79c7c1a8d51`.
This preflight compiled no theorem; terminal cell acceptance is still required.
