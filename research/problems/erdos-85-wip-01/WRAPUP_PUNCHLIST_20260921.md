# Erdős 85 wrap-up punchlist

2026-09-21, claude, at the operator's request. SINGLE-SEAT. Goal: document the
attempt and the evidence for the 48-to-49 drop, publish the paper, then pause
Erdős 85 work for a few months. Board goals #42 and #43 govern. Zero cloud
spend. No new research lanes.

Legend: [ ] open, [~] in progress, [x] done, [R] needs Robb.

## A. Evidence for the drop (the only compute left)

- [x] A1. DONE 2026-09-22 03:20Z: 24/24 UNSAT_CROSSCHECKED. 24-case H1 pilot, reviewed wrapper, 4 workers. Relaunched 2026-09-21
  18:59Z in tmux `e85-pilot` / `e85-monitor`. Output on Stripe:
  `artifacts/erdos85-sat49/h1-verdict-pilot-20260921-claude`. Expect 6–12 h.
- [x] A2. Pilot gate-input audit run 2026-09-22: all checks pass (monitor coverage complete, max 4 solvers, 1.2 GiB peak solver RSS, no swap). Banked as `phase_b_h1_verdict_20260916/PILOT_GATE_INPUT_AUDIT_20260921.json`. No scaling gate is needed (A3).
- [x] A3. Scaling gate: not needed. Robb (2026-09-21, board goal #44) granted the
  single-seat waiver and $200 of AWS. The cloud run uses the reviewed residual
  wrapper with `--case-id` and one worker, which has no gate; `dispatch_scaled.py`
  is not used.
- [x] A4. DONE 2026-09-27. All 1,161 residual roots UNSAT: pilot 24 + pass 1 876 +
  pass 2 242 + pass 3 16 + pass 3b 2 = 1,160 whole-instance two-solver verdicts, plus
  `h1_81494a6ef36d3ec9` by an adaptive cube tree (36 leaves, all two-solver UNSAT,
  checker rc 0). Six spot reclaims restarted rows; actual EC2 cost $235 of the $300
  ceiling. Receipts: `phase_b_h1_census_20260927/` and Stripe
  `artifacts/erdos85-sat49/h1-verdict-cloud-20260921/`, `h1-cube-pass4-20260926/`.
- [x] A5. DONE 2026-09-28: 34/34 outside-frozen slots UNSAT_CROSSCHECKED; gap auditor: 1,191 fresh + 96 inherited + 1 cube slot, 0 incomplete. The 130 gap slots outside the residual queue. The 96 historical rows are
  carried by the reviewed overlay (drat-trim-verified certificates) and reported as
  HISTORICAL_VERIFIED_UNSAT by the summarizer; not re-solved. The 34 outside-frozen
  rows are running on the Mac since 2026-09-27 17:27Z via the reviewed
  `dispatch_capacity34.py` (three four-worker shards, 4 h caps, zero spend), output
  Stripe `artifacts/erdos85-sat49/h1-gap34-20260927/`.
- [x] A6. DECIDED 2026-09-22 (Robb, board #45): second pass at 43,200 s caps for every cap-hit row; rows still open after that are printed as open. Cap-hit policy (original text). Recommendation: no retries, no longer caps. Rows that
  hit the cap are printed as open and the paper uses the "partial evidence"
  wording. Any SAT result stops everything and the drop claim is withdrawn.
- [x] A7. DONE 2026-09-27: `phase_b_h1_census_20260927/h1-census-table.{json,tsv}` from the reviewed summarizer over 1,413 cloud run dirs + the Mac pilot (1,160 UNSAT_CROSSCHECKED, 96 historical, 1 cube row reported separately, 0 disagreements). Receipt-derived H1 census table (auditor 3d263fb913): exact tag and CNF
  joins across the 1,288 gap tags, 96 historical rows, 12,019 certificate rows.
  This table is the only permitted source of counts in the paper and the post.
- [x] A8. 63-to-64 and plane-order campaigns: no further compute. They are
  documented in the paper as open.

## B. The paper

- [x] B1. DONE 2026-09-28 including the capacity-grid row and the §8 reconciliation paragraph. Earlier: DONE 2026-09-27 for the residual roots (abstract, evidence table, §8, cube subsection; no "in progress" phrase remains). Left: the one sentence on the 34 outside-frozen slots once A5 finishes. Fill the H1 row of the evidence table, the abstract sentence and §8 from A7.
- [~] B1a. DRAFTED 2026-09-26 as manuscript subsection "A cheaper route: cube-partitioned certificates (projection)"; update its cube-tree numbers when pass 4 finishes. Cost-to-verify refinement (Robb, 2026-09-26): measure how much of each
  row is trivial. The pass-4 cube split of the hardest row showed 27 of 32 cubes
  refuted by unit propagation in seconds; certificate cost concentrates in a few hard
  cubes, so a cube-partitioned certificate would be far smaller than the priced
  whole-instance replay. Use the pass-4 receipts (and the size distribution of the
  12,019 archived LRATs versus solve time) to revise the cost-to-verify section.
- [x] B2. DONE 2026-09-27: `AXIOM_AUDIT_COLD_20260927/` — output byte-identical to the 2026-09-16 overlay audit; manuscript now cites it. Cold Docker build (fresh build volume `lean-e85-cold-20260927`, pinned image, Mathlib from cache) of the capstone and witness modules, then `AXIOM_AUDIT_COLD_20260927/axioms.lean`. Literal `#print axioms` for every cited Lean statement (two witnesses,
  conditional finite-drop core, Theorem B) from a cold Docker build. The banked
  audit is a preliminary overlay audit.
- [x] B3. DONE 2026-09-27 (single-seat, mechanical): 45 Lean identifiers cited; 40 resolve to declarations in `proofs/Proofs`, 1 is a module name, 2 are the planned names of the not-yet-generated endpoint module (now labelled as such in the text), 2 are notation. A Sol should repeat the semantic half (statement wording vs. Lean statement) when available. Claim-by-claim audit of the manuscript against exact Lean names (goal #40 rule).
- [x] B4. DONE 2026-09-27: `CUTS_LEDGER_DRAFT.md` has rows 1–186; every row cited by the paper (172–186, 174, 175, 176, 180) exists. Room-message and outline-version pointers are transcript references and were left as is. Negative map and cuts ledger: freeze row numbers, check every cross-reference from the paper.
- [x] B5. DONE 2026-09-27: both external URLs resolve (200); every repo-relative file cited in the manuscript exists; F-versus-r convention note in `FIRST_DROP_LITERATURE_CHECK.md` is referenced. References and conventions: Boza arXiv:2409.12770v2, Afzaly–McKay data
  page, erdosproblems.com/85, the F versus r convention note.
- [x] B6. Final PDF 2026-09-28: `manuscript/DRAFT.pdf` (pandoc 3.11 + xelatex, glyph issues fixed by ASCII substitutions). Authorship statement is the existing Contributions section. First PDF builds cleanly with pandoc 3.11 + xelatex (Stripe `artifacts/erdos85-manuscript-build-20260927/DRAFT.pdf`, 158 KB; two glyphs missing in the mono font, to fix in the final pass). Final typeset waits for the 34-slot sentence and the authorship statement. Typeset: Markdown to LaTeX/PDF, title page, AI-authorship and
  contribution statement per the goal #45 ruling.
- [x] B7. DONE 2026-09-28: full read; fixed every passage that still called the census pending (status block, Result A, §5, evidence map, contributions, §8 reconciliation). Final scope-honesty read of the whole paper (claude owns §8).
- [R] B8. Operator read-through. Nothing external before this.

## C. Document the attempt (so a cold reader can resume in months)

- [x] C1. DONE 2026-09-27: `PAUSE_HANDOFF_20260927.md`. `PAUSE_HANDOFF.md`: what is proved, what is computational, what is
  open (A-REG-NONBIP), where every artifact lives, how to resume, what not to
  retry (pointer to the cuts ledger and parked lanes).
- [ ] C2. Closing entry in `FINAL_PROOF_OUTLINE.md`; squad outline publication.
- [x→] C3. DECIDED 2026-09-21 (Robb): clean up the integration branch, tag it as the archive, then cherry-pick the conclusions to `main`. No full merge. Landing strategy (measured 2026-09-21: the merge has ONE conflict,
  `FINAL_PROOF_OUTLINE.md` add/add, but adds 4.4 GB of blobs to `main`,
  including a 92 MB LRAT file and many 50 MB receipt shards, and puts 3,702 new
  Lean files under the `Proofs.*` build glob. Every fleet worktree of `main`
  would grow by 4.4 GB and the default build target would include the
  certificate modules). `erdos85/integration` is 10,232 commits ahead of
  `main` with 3,702 Lean files (about 2.0M lines) that `main` does not have.
  Recommendation: tag the branch (`erdos85-pause-2026-09`), keep it as the
  archive, and land on `main` only the paper, the outline, the handoff, and
  the small Lean core (Theorem B chain, the two witnesses) if it builds
  within the Docker limits. Do not merge the generated certificate modules.
- [ ] C4. Gallery: update `src/data/proofs/erdos-85` and the research problem
  JSON. Status stays `axiomatized`/open. No "verified drop" wording.
- [x] C5. DONE 2026-09-27: README `STRIPE_ARTIFACTS_README_20260927.md`; manifest `artifacts/erdos85-sat49-MANIFEST-20260927.sha256` (194,620 files; regenerate once the 34-slot run finishes, which was still writing) of `artifacts/erdos85-sat49` (830 GB) → `artifacts/erdos85-sat49-MANIFEST-20260927.sha256`; README mapping still to write. Stripe artifacts (933 GB under `artifacts/`): one sha256 manifest, one
  README mapping directories to paper sections.
- [R] C6. S3 bucket `2am-erdos85-certs` (about 6 TB): keep cold, release as
  requester-pays with a manifest, or delete. It costs money every month
  while paused.
- [x] C7. DONE 2026-09-27: PR #43624 closed as superseded (its head is an ancestor of `erdos85/integration`; landing is by tag + cherry-pick).
- [x] C8. `main` checkout strays. Both unpushed local commits are already on
  integration by content. The four untracked erdos-85 files are now banked on
  integration. Two local-only branches with unlanded content were pushed for
  preservation (`archive/erdos85-sol3-integration-…-cleanup-20260910`,
  `feature/erdos85-sol3-normalization`). Remaining: reset the local `main`
  to `origin/main` once Robb agrees (shared checkout, not done by an agent).

## D. Publish

- [R] D1. Venue. Zenodo is the agreed path; arXiv is optional and has its own
  policy on AI authorship.
- [ ] D2. Zenodo deposit: PDF, tagged source snapshot, solver receipts, census
  table. Get the DOI.
- [ ] D3. Fill `[ARCHIVE LINK]` and the counts in
  `manuscript/ERDOSPROBLEMS_POST_DRAFT.md`; choose version A or B.
- [R] D4. Robb posts the comment on erdosproblems.com/85.
- [ ] D5. Optional: herald post on Mathstodon after D4.

## E. Stand down

- [R] E1. AWS. No erdos-85 instance is running. Stopped instances that may
  belong to this project and still carry EBS cost: `deepsix-ondemand`
  (c7i.8xlarge), one unnamed c7i.4xlarge, `repo-remote-repo` (t3.small). The
  account is shared with other projects, so Robb confirms before termination.
- [~] E2. IN PROGRESS 2026-09-27: the 115 non-worktree folders are being moved (not deleted) to Stripe `attic/home-scratch-20260927/` (list in `MOVED-FROM-HOME.txt`); the two registered worktrees (`a3-bank`, `h1-pilot-consume`) are removed after their loose files are confirmed banked. Host scratch: 117 `~/lean-genius-*` folders, 70 GB. First bank the two
  loose items (a3-bank untracked files, one freight tarball), then delete the
  small review folders, then move or delete the raw sweep folders per Robb.
- [ ] E3. Worktrees and branches: 16 erdos-85 worktrees. Check `.lake` symlinks
  before removing any. Prune merged branches.
- [ ] E4. Docker: remove erdos-85 volumes and the generator containers only.
  Other projects share the daemon.
- [ ] E5. Kill tmux sessions, retire `~/lean-genius-remote-staging`.
- [ ] E6. Squad: close goals #15, #23, #37, #38, #41, #42, #43 with final notes,
  release claims, agents leave. Memory note with the resume pointer.

## AWS option for A4 (quota checked 2026-09-21, nothing launched)

us-east-1 spot quota is 300 standard vCPUs with 0 in use; on-demand is 128
with 80 in use by other projects. us-east-2 has 5, us-west-2 has 32 spot.
Spot now: c7a.16xlarge $1.03/h (64 real cores), c7g.16xlarge $0.64/h,
c8g.16xlarge $0.71/h. Work is about 1,137 roots × (Kissat ≈ 1.25 h + CaDiCaL
≈ 1.4 h) ≈ 3,000 core-hours plus the cap tail. Four 64-core spot hosts finish
in roughly 14–20 h for about $45–85 total, inside the $100/day ceiling, versus
3–5 days on the Mac. Needs: CNFs generated and hashed on the Mac then uploaded
(no Lean image in the cloud), the same pinned Kissat 4.0.4 and CaDiCaL 3.0.1
builds, verdict-only, no proof logging, receipts in the Phase B schema so the
reviewed auditor reads them unchanged. Per goal #42 this needs Robb's explicit
nod with a declared figure before any launch.

## Order of work

A1 runs now. B2, B4, B5, C1, C5 and C8 do not depend on the census and can be
done while solvers run. A3 is the first blocking decision. Critical path:
A1 → A2 → A3 → A4/A5 → A7 → B1 → B7 → B8 → D2 → D4 → E.
