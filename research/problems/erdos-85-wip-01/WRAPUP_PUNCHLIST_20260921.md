# Erdős 85 wrap-up punchlist

2026-09-21, claude, at the operator's request. SINGLE-SEAT. Goal: document the
attempt and the evidence for the 48-to-49 drop, publish the paper, then pause
Erdős 85 work for a few months. Board goals #42 and #43 govern. Zero cloud
spend. No new research lanes.

Legend: [ ] open, [~] in progress, [x] done, [R] needs Robb.

## A. Evidence for the drop (the only compute left)

- [~] A1. 24-case H1 pilot, reviewed wrapper, 4 workers. Relaunched 2026-09-21
  18:59Z in tmux `e85-pilot` / `e85-monitor`. Output on Stripe:
  `artifacts/erdos85-sat49/h1-verdict-pilot-20260921-claude`. Expect 6–12 h.
- [ ] A2. Run `audit_pilot_gate_inputs.py` on the finished pilot; bank the report.
- [R] A3. Scaling gate. `dispatch_scaled.py` fails closed until a reviewed gate
  SHA is pinned in source. Either wait for a Sol seat, or Robb waives the
  second seat and claude pins it after A2.
- [ ] A4. Full run: the other 1,137 residual roots, up to 24 workers, Kissat then
  CaDiCaL, 4 h cap each. Estimate 3–5 days on the host.
- [ ] A5. The 130 gap slots outside the residual queue: 96-historical route
  (54b7f7035b) and 34-outside-frozen route (4366cedadb).
- [R] A6. Cap-hit policy. Recommendation: no retries, no longer caps. Rows that
  hit the cap are printed as open and the paper uses the "partial evidence"
  wording. Any SAT result stops everything and the drop claim is withdrawn.
- [ ] A7. Receipt-derived H1 census table (auditor 3d263fb913): exact tag and CNF
  joins across the 1,288 gap tags, 96 historical rows, 12,019 certificate rows.
  This table is the only permitted source of counts in the paper and the post.
- [x] A8. 63-to-64 and plane-order campaigns: no further compute. They are
  documented in the paper as open.

## B. The paper

- [ ] B1. Fill the H1 row of the evidence table, the abstract sentence and §8
  from A7. Remove every "in progress" phrase (DRAFT.md lines 20, 131, 560, 702).
- [ ] B2. Literal `#print axioms` for every cited Lean statement (two witnesses,
  conditional finite-drop core, Theorem B) from a cold Docker build. The banked
  audit is a preliminary overlay audit.
- [ ] B3. Claim-by-claim audit of the manuscript against exact Lean names
  (goal #40 rule). Sol-1's job; single-seat if the Sols are still away.
- [ ] B4. Negative map and cuts ledger: freeze row numbers, check every
  cross-reference from the paper.
- [ ] B5. References and conventions: Boza arXiv:2409.12770v2, Afzaly–McKay data
  page, erdosproblems.com/85, the F versus r convention note.
- [ ] B6. Typeset: Markdown to LaTeX/PDF, title page, AI-authorship and
  contribution statement per the goal #45 ruling.
- [ ] B7. Final scope-honesty read of the whole paper (claude owns §8).
- [R] B8. Operator read-through. Nothing external before this.

## C. Document the attempt (so a cold reader can resume in months)

- [ ] C1. `PAUSE_HANDOFF.md`: what is proved, what is computational, what is
  open (A-REG-NONBIP), where every artifact lives, how to resume, what not to
  retry (pointer to the cuts ledger and parked lanes).
- [ ] C2. Closing entry in `FINAL_PROOF_OUTLINE.md`; squad outline publication.
- [R] C3. Landing strategy. `erdos85/integration` is 10,232 commits ahead of
  `main` with 3,702 Lean files (about 2.0M lines) that `main` does not have.
  Recommendation: tag the branch (`erdos85-pause-2026-09`), keep it as the
  archive, and land on `main` only the paper, the outline, the handoff, and
  the small Lean core (Theorem B chain, the two witnesses) if it builds
  within the Docker limits. Do not merge the generated certificate modules.
- [ ] C4. Gallery: update `src/data/proofs/erdos-85` and the research problem
  JSON. Status stays `axiomatized`/open. No "verified drop" wording.
- [ ] C5. Stripe artifacts (933 GB under `artifacts/`): one sha256 manifest, one
  README mapping directories to paper sections.
- [R] C6. S3 bucket `2am-erdos85-certs` (about 6 TB): keep cold, release as
  requester-pays with a manifest, or delete. It costs money every month
  while paused.
- [ ] C7. PR #43624 (open since 2026-08-04): merge or close with a note.
- [ ] C8. `main` checkout: two unpushed local commits and four untracked
  erdos-85 paths. Bank or drop each one.

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
- [ ] E2. Host scratch: 117 `~/lean-genius-*` folders, 70 GB. First bank the two
  loose items (a3-bank untracked files, one freight tarball), then delete the
  small review folders, then move or delete the raw sweep folders per Robb.
- [ ] E3. Worktrees and branches: 16 erdos-85 worktrees. Check `.lake` symlinks
  before removing any. Prune merged branches.
- [ ] E4. Docker: remove erdos-85 volumes and the generator containers only.
  Other projects share the daemon.
- [ ] E5. Kill tmux sessions, retire `~/lean-genius-remote-staging`.
- [ ] E6. Squad: close goals #15, #23, #37, #38, #41, #42, #43 with final notes,
  release claims, agents leave. Memory note with the resume pointer.

## Order of work

A1 runs now. B2, B4, B5, C1, C5 and C8 do not depend on the census and can be
done while solvers run. A3 is the first blocking decision. Critical path:
A1 → A2 → A3 → A4/A5 → A7 → B1 → B7 → B8 → D2 → D4 → E.
