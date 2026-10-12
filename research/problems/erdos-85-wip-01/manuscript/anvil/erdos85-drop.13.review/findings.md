# Findings — erdos85-drop.13

## 1. Pin verification

- **Macro chain.** L32 defines `\repocommit` as `2029149d7e42b74036ff0e1e82af6d33c2e32748`, L33 defines `\repocommitshort` as `2029149d7e42`, and L34 defines `\repobase` as `https://github.com/rjwalters/lean-genius/blob/\repocommit`. L274 prints `\texttt{\repocommitshort}`. The printed commit and the links cannot drift apart again.
- **Pin location.** The pin is the tip of `origin/erdos85/release-assembly-20261011` (`git ls-remote` matches). Its commit message is "erdos85: record Codex independent re-audit of cold build; supersede banner on FAILURE.md; fetch-script credential wording". The v12 pin `fa2b41268df` is its parent. The pin is not an ancestor of the paper-branch head (`ac20ed283b0`). That is fine for links, but the release tag must be cut at the assembly commit.
- **Diff from the v12 pin.** Six files change: the fetch-script comment, both `ACCEPTED.md` files, `FAILURE.md`, the cold-build `README.md` and `THIRDPARTY.md`. There are no Lean source changes.
- **Targets.** 80 `\repofile` uses cover 70 distinct paths, and all exist at the pin. 75 URIs were extracted from the rendered PDF. 70 are GitHub blob links, all with the full hash, and all resolve; the other five are external. All 58 `\lean` names occur under `proofs/Proofs` at the pin.
- **Worktree head.** The head moved from `9da680666dc` (the stated head) to `ac20ed283b0`. The only changes are publication drafts outside the anvil directory, so the v13 version directory is unaffected.

## 2. The re-audit claim

- The paper at L113 says: "A read-only audit of the retained output, repeated independently by a second AI author, checked every source hash, object hash, compile log and dependency order".
- `ACCEPTED.md` at the pin says: "Independent re-audit (Codex, squad review #2749, PASS, 2026-10-12): reran `audit.py` ...; rehashed the archive ...; checked that the 2,692-file manifest covers every file ...".
- In the squad database (`.squad/squad.db` in the main checkout), `review_requests` row 2749 has status `resolved`, `resolved_by` codex, and a resolution beginning "PASS for requested evidence re-audit and v12 content/pin review. Independently reran audit.py: 893 sources, exact 601/607/604 ...".
- `audit.py` at the pin checks object SHA256 and size, log SHA256, source hashes against the plan, and dependency finish-before-start order. The paper's description is accurate.
- §7 Reviews (L264), "accepted only after another AI author independently reviewed it", is now consistent with this record.

## 3. Scope sweep

Every occurrence of "theorem", "unconditional", "settled", "independently" and "A-REG/\AREG" was checked. There are no new instances, and all prior instances are unchanged and compliant. The only new wording is the re-audit clause at L113, which is about reproducibility. Table 2 still lists "the two hypotheses" as what is open for the upper side. No critical flag.

## 4. Record residue (outside the rubric)

These items are in files the paper links to, not in the paper's own text:

- `release_cold_build_20261011/README.md`: "the approximate 10-hour budget" and "Execution requires the exact plan SHA256 and separate spending authorization".
- `release_cold_build_20261011/FAILURE.md`, line 49: a `/Volumes/Stripe/...` archive path. The file now carries the superseded banner.
- `release_cold_build_20261011/ACCEPTED.md`: "squad review #2749", a pointer into the private room.
- `release_thirdparty_rebuild_20261012/evidence/fetch-job/job.log`: an STS ARN containing the account number. This file is not linked from the paper.

## 5. Rubric transition

The prior rubric (`erdos85-drop.12.review/_meta.json`) is `anvil-pub-v2`, the same as the current one. No transition applies.
