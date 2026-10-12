# Zenodo deposit plan: Erdős 85 paper

**Status.** DRAFT plan for Robb Walters. Nothing has been uploaded or reserved. The manuscript of record
will be paper v12 (`research/problems/erdos-85-wip-01/manuscript/anvil/erdos85-drop.12/`, 12 October 2026),
copied into `research/problems/erdos-85-wip-01/manuscript/paper/` at release; that directory still holds the
frozen v11 copies today. All paths below are relative to the repository root on branch
`erdos85/paper-v12-final-20261012` (worktree `/Volumes/Stripe/lean-genius/erdos85-paper-v12-final`) unless
stated otherwise. Receipt paths were checked to exist at the pinned release-assembly commit
`fa2b41268df024128ed4738b3bb500637cf1ec12` (v12's current `\repobase`).

## Before depositing

1. Robb's read-through of paper v12 (`manuscript/anvil/erdos85-drop.12/main.pdf`). Its changelog records AI-author
   review and audit passes only; no human read-through is recorded.
2. Copy v12 (`main.tex`, `refs.bib`, `anvil-paper.cls`, `main.pdf`) into `manuscript/paper/` and update
   `manuscript/paper/README.md` to say v12 is the manuscript of record.
3. Create the GitHub release tag (suggested: `erdos85-paper-v1`) on the commit that holds the final paper and receipts.
4. Repin `\repobase` in `main.tex` from `blob/fa2b41268df024128ed4738b3bb500637cf1ec12` to `blob/<release tag>`,
   rebuild with `xelatex main && bibtex main && xelatex main && xelatex main`, and confirm the links resolve.
   In the same pass, align two strings in v12's `main.tex` that do not match the pin: the Availability sentence
   still says "at commit `92ff6248033c`", and `\date` reads 11 October 2026 although the last v12 edit (the
   second rebuild) is dated 12 October 2026.
5. Decide author metadata for the four AI authors (see "Creators" below) and check Zenodo's current guidance on
   non-human creators before submitting.
6. Zenodo account, DOI reservation and upload are done by Robb (see "Steps").

## Files to upload

Three files. Zenodo previews PDFs; keep the source and receipts as zips.

| Upload as | Contents (exact source paths) |
|---|---|
| `erdos85-drop-paper.pdf` | `research/problems/erdos-85-wip-01/manuscript/paper/main.pdf` (v12, after the copy in step 2 and the rebuild in step 4) |
| `erdos85-drop-latex.zip` | `research/problems/erdos-85-wip-01/manuscript/paper/main.tex`<br>`research/problems/erdos-85-wip-01/manuscript/paper/refs.bib`<br>`research/problems/erdos-85-wip-01/manuscript/paper/anvil-paper.cls`<br>`research/problems/erdos-85-wip-01/manuscript/paper/README.md` (build line: xelatex + fontspec, not pdflatex) |
| `erdos85-receipts.zip` (about 46 MB uncompressed at the pin; the H7 receipt tables are already zstd-compressed) | see the list below |

Receipts bundle, preserving directory structure:

```
# H1
research/problems/erdos-85-wip-01/CHECKING.md
research/problems/erdos-85-wip-01/h1_bank_check_20261006/receipts/README.md
research/problems/erdos-85-wip-01/h1_bank_check_20261006/receipts/h1_bank_check_receipts.tsv
research/problems/erdos-85-wip-01/h1_bank_check_20261006/receipts/h1_bank_check_summary.json
research/problems/erdos-85-wip-01/h1_bank_check_20261006/receipts/bank_manifest.jsonl
research/problems/erdos-85-wip-01/h1_cert_full_20261001/receipts/README.md
research/problems/erdos-85-wip-01/h1_cert_full_20261001/receipts/h1_cert_census_receipts.tsv
research/problems/erdos-85-wip-01/h1_cert_full_20261001/receipts/h1_cert_census_summary.json
research/problems/erdos-85-wip-01/h1_cert_full_20261001/receipts/historical96_cake_lpr_receipts.jsonl
research/problems/erdos-85-wip-01/h1_cert_full_20261001/receipts/historical96_receipts.jsonl
research/problems/erdos-85-wip-01/h1_cert_full_20261001/receipts/pilot_h1_81494a_leaf_cake_lpr.jsonl
research/problems/erdos-85-wip-01/h1_cert_full_20261001/receipts/pilot_h1_81494a_leaf_solves.jsonl
research/problems/erdos-85-wip-01/h1_cert_full_20261001/receipts/pilot_h1_81494a_leaf_std_lrat_check.jsonl
research/problems/erdos-85-wip-01/h1_cert_pilot_20261001/H1_COVER_AXIOMS_20261006.txt
research/problems/erdos-85-wip-01/h1_cert_pilot_20261001/COMPOSITION_AXIOMS_20261006.txt
research/problems/erdos-85-wip-01/AXIOM_AUDIT_COLD_20260927/axioms.out
research/problems/erdos-85-wip-01/phase_b_h1_census_20260927/cube-h1_81494a6ef36d3ec9/tree-check.json
research/problems/erdos-85-wip-01/h1_checker_kit/e85-check
research/problems/erdos-85-wip-01/h1_checker_kit/cube_check.py
research/problems/erdos-85-wip-01/h1_checker_kit/ami_setup.sh
proofs/Proofs/Certificates/h1_orbit_inventory.compact
# H7 (t = 0): campaign record, collector, collected receipts (one table per cube, summary.json,
# campaign_totals.json, split specs and pass manifests)
research/problems/erdos-85-wip-01/h7_hsb_campaign_20261008/README.md
research/problems/erdos-85-wip-01/h7_hsb_campaign_20261008/collect_receipts.py
research/problems/erdos-85-wip-01/h7_hsb_campaign_20261008/receipts/collected/
# H7 (t >= 1) packed certificates: manifest and download script (the files themselves stay in S3)
proofs/Proofs/Certificates/strata-lrat.MANIFEST.sha256
proofs/scripts/fetch-h7-certificates.sh
# Cold rebuild of the 893-module project closure (accepted attempt 2, retained failed attempt 1)
research/problems/erdos-85-wip-01/release_cold_build_20261011/README.md
research/problems/erdos-85-wip-01/release_cold_build_20261011/ACCEPTED.md
research/problems/erdos-85-wip-01/release_cold_build_20261011/FAILURE.md
research/problems/erdos-85-wip-01/release_cold_build_20261011/attempt2-evidence/CAPTURE.json
research/problems/erdos-85-wip-01/release_cold_build_20261011/attempt2-evidence/ColdIsolationProbe.lean
research/problems/erdos-85-wip-01/release_cold_build_20261011/attempt2-evidence/RUN.json
research/problems/erdos-85-wip-01/release_cold_build_20261011/attempt2-evidence/full-bundle-manifest.json
research/problems/erdos-85-wip-01/release_cold_build_20261011/attempt2-evidence/instance-state.json
research/problems/erdos-85-wip-01/release_cold_build_20261011/attempt2-evidence/job.exit
research/problems/erdos-85-wip-01/release_cold_build_20261011/attempt2-evidence/job.sha
research/problems/erdos-85-wip-01/release_cold_build_20261011/attempt2-evidence/job.spec
# Second rebuild via the public fetch script (byte-identical objects)
research/problems/erdos-85-wip-01/release_thirdparty_rebuild_20261012/ACCEPTED.md
research/problems/erdos-85-wip-01/release_thirdparty_rebuild_20261012/THIRDPARTY.md
research/problems/erdos-85-wip-01/release_thirdparty_rebuild_20261012/evidence/reproducibility-vs-attempt2.json
# Literature and the order-48 comparison
research/problems/erdos-85-wip-01/manuscript/FIRST_DROP_LITERATURE_CHECK.md
research/problems/erdos-85-wip-01/sat49/BOZA48_NONISOMORPHISM_RECEIPT_20260928.txt
```

Compile logs (`attempt2-evidence/logs/`, `job.log`, `h7_hsb_capstone_review_20261008/stratum.log`) are left out;
they stay in the GitHub release. `FAILURE.md` links files under `release_cold_build_20261011/terminal-evidence/`,
which are also left out of the zip and resolve in the release. Strip the `#` comment lines before passing the
list to `git archive`.

Build it with, e.g. (from the worktree root, after the release commit):

```
git archive --format=zip -o erdos85-receipts.zip HEAD -- <the paths above>
```

`git archive` takes the committed bytes, so the bundle matches the tagged release exactly. Record the zip's sha256
in the deposit description.

Not uploaded (too large, or deliberately unpublished, as the paper's Availability section says): the about 28 TB of
H1 LRAT (bank proofs stay in S3; fresh proofs were discarded and are regenerated by the pinned solver), the H7
(t = 0) leaf and sub-leaf proofs (discarded after the check), the thirteen packed H7 (t ≥ 1) certificate files
(about 2.57 GB, published in S3 and fetched by `fetch-h7-certificates.sh`), the 2.39 GB cold-build output bundle
(kept outside the repository; its per-file hash manifest is in the zip), the rest of the certificate storage, and
the artifact volume with solver logs. The Lean sources are archived through the GitHub release, not duplicated here.

## Metadata

- **Resource type:** Publication / Preprint
- **Title:** A Drop at Forty-Nine in Erdős Problem 85
- **Publication date:** the deposit date (paper v12, 12 October 2026; see step 4 for the `\date` line)
- **Creators** (order as in the paper):
  1. Claude Fable (affiliation: Lean Genius project) [decide: name format and whether to add "Anthropic model"]
  2. GPT Sol (affiliation: Lean Genius project) [decide: "OpenAI model"]
  3. Astra (affiliation: Lean Genius project) [decide: "OpenAI model"]
  4. Claude Opus (affiliation: Lean Genius project) [decide: "Anthropic model"]
  5. Walters, Robb (affiliation: 2AM Logic) [ORCID if available]; mark as contact person
  The paper's byline reads "Lean Genius project, 2AM Logic" for all five. Zenodo's form expects "Family, Given"
  for persons; the AI authors may need to go in as organizational names or as contributors, depending on
  current Zenodo guidance.
- **Description (abstract, verbatim from paper v12, converted to plain text):**

  > For n ≥ 4 let f(n) be the least d such that every simple graph on n vertices with minimum degree at least d
  > contains a four-cycle. Erdős Problem 85 asks whether f is eventually nondecreasing. We report two results.
  >
  > First, f(48) = 8 and f(49) = 7, a strict drop between adjacent orders, as a computational result. The lower
  > sides are explicit graphs checked in Lean 4 through native_decide. For the upper side, Lean refutes one case
  > outright, splits the rest into four strata, excludes two of them, H3 and H5, and reduces H1 and H7 to the
  > unsatisfiability of formulas defined in Lean: 13,351 for H1, and 28 cover and 377,776 leaf formulas for the
  > part of H7 with no triple. The CakeML-verified checker cake_lpr accepted an unsatisfiability proof for every
  > one, directly or, for the two hardest, piece by piece through a split composed in Lean: about 28 TB of LRAT
  > for H1 and 20 TB for H7. Lean thus derives the upper side from two explicit unsatisfiability hypotheses,
  > which the external checks support but which are not admitted into Lean; the derivation prints 598
  > native_decide axioms beyond the three standard ones, and each checked file is tied to its Lean formula by
  > emitters, not a kernel proof. To our knowledge it is the first strict drop of f established on the
  > problem's domain at this level of evidence; one drop is compatible with either answer to the problem.
  >
  > Second, Lean verifies from the standard axioms alone that one proposition, A-REG (for no k ≥ 3 is there a
  > C4-free 2^k-regular graph on 4^k vertices), implies a negative answer to Erdős Problem 85. A-REG is a
  > hypothesis with a stated rival; its q = 4 analogue is false, as Lean exhibits a C4-free 4-regular graph on
  > 16 vertices.

  If the abstract changes after Robb's read-through, copy the final one verbatim at deposit time.

  Append after the abstract: "H1 checker: public AMI ami-05697724475f2e748 (us-east-1); proofs and checker kit in
  the Requester Pays bucket 2am-erdos85-certs (prefixes below); guide CHECKING.md in the receipts bundle. H7
  certificates: the thirteen packed files read by the Lean build are in the same bucket under
  public/erdos85-h7-positive-triple-lrat/ (Requester Pays); proofs/scripts/fetch-h7-certificates.sh downloads
  them and checks them against proofs/Proofs/Certificates/strata-lrat.MANIFEST.sha256. Receipts bundle sha256:
  <fill>."
- **Keywords:** Erdős problems; extremal graph theory; C4-free graphs; minimum degree; Ramsey numbers;
  SAT solving; LRAT; proof certificates; cake_lpr; Lean 4; formal verification; AI-assisted mathematics
- **License:** Creative Commons Attribution 4.0 International (CC-BY-4.0) for the paper and receipts.
  (The repository has no top-level LICENSE file at present; the code license for the GitHub release is a separate
  decision.)
- **Language:** English
- **Version:** v1
- **Related identifiers:**

  | Relation | Identifier | Scheme |
  |---|---|---|
  | is supplemented by | [GitHub release URL, e.g. https://github.com/rjwalters/lean-genius/releases/tag/erdos85-paper-v1] | URL |
  | is supplemented by | https://github.com/rjwalters/lean-genius/blob/<tag>/research/problems/erdos-85-wip-01/CHECKING.md | URL |
  | is supplemented by | s3://2am-erdos85-certs/public/erdos85-h1-checker-kit/ (Requester Pays; checker kit: manifests, orbit tables, receipts, pinned binaries, MANIFEST.sha256) | URL (or put in description if the s3 scheme is rejected) |
  | is supplemented by | s3://2am-erdos85-certs/sat49/campaign-20260825/h1/ (Requester Pays; the 12,094 bank proofs, `<tag>.compact.lrat.gz`) | URL (same caveat) |
  | is supplemented by | s3://2am-erdos85-certs/public/erdos85-h7-positive-triple-lrat/ (Requester Pays; the thirteen packed H7 (t ≥ 1) certificate files, about 2.57 GB, checked against `strata-lrat.MANIFEST.sha256`) | URL (same caveat) |
  | is supplemented by | https://github.com/rjwalters/lean-genius/blob/<tag>/proofs/scripts/fetch-h7-certificates.sh | URL |
  | is documented by | https://rjwalters.info/rooms/erdos-85 (room transcript) | URL |
  | references | arXiv:2409.12770 (Boza, Ramsey numbers of C4 versus a star) | arXiv |
  | references | https://www.erdosproblems.com/85 | URL |

  The AMI has no identifier scheme in Zenodo; give `ami-05697724475f2e748` (us-east-1, name
  `erdos85-h1-checker-20261006`) in the description and in "Additional notes".
- **Additional notes (optional field):** "The H1 proofs and the H7 (t = 0) leaf proofs checked by cake_lpr were
  checked as they streamed and then discarded; only their sha256 and length are kept. With the identical CaDiCaL
  3.0.1 Linux arm64 binary the census proofs reproduce byte for byte. cake_lpr exits with status 0 even when a
  check fails; the success signal is the line `s VERIFIED UNSAT`. The 893-module Lean project closure was
  cold-rebuilt from source and audited (release_cold_build_20261011/ACCEPTED.md; an earlier attempt failed in the
  build runner, FAILURE.md); a second rebuild that obtained the H7 certificate files with the fetch script produced
  byte-identical compiled objects (release_thirdparty_rebuild_20261012/ACCEPTED.md). The fetch script has been
  exercised end to end only with credentials of the bucket owner's account."

## Steps

1. Complete "Before depositing" items 1 to 5.
2. Build the three upload files from the tagged commit; compute and note their sha256.
3. On zenodo.org: New upload. Upload the three files. Click "Reserve DOI" so the DOI is known before publishing.
4. Fill the metadata above. Paste the final abstract verbatim. Set CC-BY-4.0.
5. Put the reserved DOI into: the GitHub release notes; `ARTICLE.md`, `BLOG.md`, `ERDOSPROBLEMS_NOTE.md` and
   `../SF_LEAN_UPDATE_DRAFT.md` ([DOI] placeholders); and, if wanted, a "DOI" line in the paper's Availability
   section (which would need another rebuild and a replaced PDF before publishing the record).
6. Preview the record; check that the PDF opens, the zips list the expected paths, and the related-identifier links
   resolve.
7. Publish. After publishing, files cannot be replaced without a new version, so do the checks in step 6 first.
8. Optional: add an entry to rjwalters.info `src/research/papers/papers.ts` (fields id, title, authors, venue
   "Preprint", year, date, abstract, tags, links {pdf, doi, github}) pointing at the DOI and release.
