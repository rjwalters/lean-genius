# Changelog: erdos85-drop.9 to erdos85-drop.10

Status-update pass beyond the iteration cap (iteration 10 of `max_iterations: 8`, `metadata.operator_override: true`).
Provenance of the override: `erdos85-drop.9.operator/` (agent-transcribed operator instructions, not a human-authored review).
This pass was edited directly by claude (Claude Opus) in the collaboration room, not by the anvil paper-revise skill, and
claim-reviewed by codex (room messages 53223-53248: corrections in 53226, 53230, 53233; PASS at r4 in 53248).

## Why

v9 described H3, H5 and H7 (t=0) as open in Lean and supported only by reviewed arguments. Since v9:
- H3 and H5 are excluded in Lean (`H3.orderFortyNineStratumExcluded_three`, 411 axioms; `H5.orderFortyNineStratumExcluded_five`).
- The conditional order-49 capstone `Erdos85OrderFortyNineCapstoneH3` was accepted (601/607/604 axioms = 3 standard + 598/604/601
  native_decide; no sorry) and re-validated on the release assembly (`release_assembly_20261011/`, job 20261011T204721, fresh endpoint
  compilation against 891 accepted, hash-pinned dependency objects; not a cold rebuild).
- The H7 (t=0) certificate campaign finished: 28 covers and 377,776 leaves cake_lpr-checked (one leaf via a 256-way split composed by
  `sevenHighT0CanonicalHsbLeafChecked_of_split`); collector `full_campaign_complete = true`, independently re-run by codex.

## What changed

- Abstract, Result A, "What is new", "What is not claimed": the upper side is a Lean theorem conditional on two explicit UNSAT
  hypotheses (H1, H7), each supported by cake_lpr checks outside Lean; no claim of an unconditional Lean theorem.
- §2.2 case split: H9 "no remaining external-evidence hypothesis" with 18 native_decide certificate checks; capstone display, axiom
  counts and audit scope.
- §2.3: H3 (408 native parts), H5 (40 parts + cover checks), H7 t>=1 (certificate files not in the repository; not replayed),
  H7 t=0 Lean reduction (counting by kernel decide, 28 structural cubes, witness-checked symmetry breaking with a soundness theorem,
  cover and leaves) and a new "H7 certificates" paragraph (emitters, three passes, split, retained covers, scoped metrics).
- §3 hexagon comparison and trust paragraph extended to H7; §4 status table rows for H3, H5, H7 (t>=1), H7 (t=0) reduction and
  formulas, upper side; paragraph after the table; §7 reviews paragraph; availability (new Lean, H7 and validation items).
- `\repobase` and availability pinned to release-assembly commit 1d0772cd825462f5230f224c2110231c6483d5e4 (no tag yet; R-LINK).
- Date 11 October 2026.

## Build and gates

- `xelatex`, `bibtex`, then `xelatex` three more times (4 passes); a fifth scratch pass gives a byte-identical `.aux` (fixpoint).
- 0 errors, 0 undefined references or citations (font-shape warnings only), 0 overfull, 6 underfull; `pdftotext` finds 0 `??`.
- 14 pages; references start on p. 12, so the main text is 11 pages (v9: 10).
- Abstract 1,712 rendered characters (limit 1,900, R-V8).
- `scope_lint.py --proofs <release-assembly>/proofs/Proofs`: PASS (39 numbers, 46 Lean names). New refs added to
  `erdos85-drop/refs/` for traceability: H7 collected summary and campaign totals, H7 campaign README, release-assembly README,
  H3-closed capstone README, H5 terminal review README, H3 stratum integration README.
