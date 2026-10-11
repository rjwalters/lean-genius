# Comments — erdos85-drop.11

Keyed to rendered section headings, with `main.tex` line numbers in brackets. The thread is single-file, with no `\input` children. Paths and Lean names were checked at the pinned commit `f6daa149b807972abe1c3e669abce092a863c2bd`.

## blocker

None.

## major

None. All three v10 review majors and both v10 audit criticals are resolved; see `verdict.md` § "Resolution of the v10 findings".

## minor

- **m1 — §2.3 H7 [L123] vs §3 [L153] (related-work; carried from v10 D4): the H7 method is not positioned against the closest precedent.**
  - Excerpt: "every clause carries a group witness that a small Lean function re-checks, and Lean proves the extension sound" (§2.3).
  - §3 compares only the H1 reduction with Subercaseaux et al. Their Lean verification also covers a symmetry-broken encoding, so the H7 symmetry-breaking extension proved sound in Lean is the point where this paper comes closest to their encoding-faithfulness axis. As written, the paper is silent on that point.
  - Fix (one sentence in §3): "For H7 the symmetry-breaking clauses and the cover are proved sound in Lean, as in \citet{subercaseaux2024hexagonlean}; the cube files themselves are still tied to the Lean term by emitters."

- **m2 — §4 post-table [L232]: the new publication item is filed under "for a fully independent audit".**
  - §1 [L87] states the consequence: "the capstone cannot be recompiled from the public repository alone". L232 lists the publication of the 13 files only under "for a fully independent audit".
  - Recompiling from the repository is a weaker bar than a fully independent audit, so the grouping understates the item.
  - Fix: "…, a kernel link between each checked file and its Lean formula, publication of the 13 packed H7 ($t\ge 1$) certificate files (without which the capstone cannot be recompiled from the public repository), and, for a fully independent audit, a cold rebuild of every module …".

- **m3 — Table 2 row "H7, $t\ge 1$" [L223]: a category mismatch in the "Open in Lean" column.**
  - The cell now holds a reproducibility item ("certificate files (about 2.57 GB) not published"), not an open Lean obligation; the Lean statement for these cells is closed.
  - Fix: either begin the cell "nothing in Lean;" and keep the rest, or rename the column "Open in Lean / not public".

- **m4 — Main text length (D9).** The main text is still 11 pages (references from p. 12), against R-SIMPLE's ~10.
  - The H7 certificates paragraph [L132] is the densest in the paper, even after the trim.
  - Fix, if a page matters: move the two-pass cap narrative and the 4,711/740 all-runs totals to the linked campaign README. Keep the identity method, the split, the scopes and the verified-check totals.

## nit

- **n1 — §2.4 [L147], §7 [L262]: "now superseded" (residual of v10 m7; the changelog lists m7 as fixed).** Both phrases have their antecedent in the same passage, so they read acceptably. For full consistency with the §2.3 edits, use "is superseded by" or "was later superseded by".
- **n2 — §2.4 [L191]: "about \$225 of cloud compute in total".**
  - The figure traces to two receipts in `refs/`: H1_CERT_RECEIPTS_README "≈ \$204 (controller estimate incl. 10% margin)" and H1_BANK_CHECK_README "about \$20 … (controller estimate)".
  - The paper drops the "controller estimate" qualifier, and neither README is linked at the sentence.
  - Fix: "about \$225 of cloud compute (controller estimates)".
- **n3 — §1 "What is new" [L85]: "no strict drop of $f$ … was previously settled".** "Settled" implies that this paper settles one, which sits close to the BRIEF's banned "decided". Fix: "was previously known".
- **n4 — Linked receipt `h7_hsb_campaign_20261008/README.md` (§8 [L280]).**
  - At the pin, its lines 9–10 now read "about \$215 in all, within the operator's \$300 H7 ceiling".
  - That is governance vocabulary in a receipt the paper links, not in the paper (R-AUD covers the paper text).
  - Trim "within the operator's \$300 H7 ceiling" in the repository before the tag.
- **n5 — Table 2 row "H5 (3 cells)" [L222]: "40 search parts and cover checks".** For parallel with §2.3, write "40 search parts and 18 cover and cardinality checks".

## v10 findings re-checked

- Review M1 → resolved (disclosed at L87, L223, L232).
- Review M2 → resolved (banner at pin, commit `a9ba1fc43ce`).
- Review M3 → resolved (it was absorbed into audit C1).
- Audit C1 → resolved. "Lean thus derives", "is derived in Lean by", "Lean derives the upper side". The only remaining "Lean theorem" strings near Result A are negations.
- Audit C2 → resolved (clause deleted).
- Minors m1, m2, m4, m5, m6, m9 → resolved.
- m3 → resolved via C2.
- m7 → mostly resolved (n1).
- m8 → partly resolved (m4).
- Nits N1, N2, N4, N6 → resolved.
- Audit N7 (DOIs present) → no action needed.

## Procedural notes

- sidecar: staged and committed through `python -m anvil.lib.sidecar stage/commit` (issue #645 CLI shim), invoked as `PYTHONPATH=.anvil .anvil/.venv/bin/python -m ...`; `uv run` not used.
- numeric-consistency: automated, 380 numbers, 0 findings; sidecar `erdos85-drop.11.numeric/`.
- pending-marker: automated, 0 markers; sidecar `erdos85-drop.11.pending/`.
- audience-check: automated. 0 governance and 0 private-locator hits. The 8 `unlinked_artifact_path` hits (§8, L274–L281) are `\repofile` arguments the scanner does not expand, so they are false positives; all 64 distinct targets exist at the pin. Sidecar `erdos85-drop.11.audience/`.
- render-gate: pass on `erdos85-drop.11/main.pdf` and `erdos85-drop.11/compile-log.txt` (14 pages, 0 overfull, 0 placeholders). There is no `.11.audit/` yet, so the version-dir compile log was used. `pdftotext` finds 0 `??` and confirms the shipped PDF carries the v11 wording.
- evidence-check: `anvil.lib.evidence_check` on the staged `scoring.md`: 9 dimensions, 0 findings, pass.
- evidence-drift: NO-SNAPSHOT (direct edit), treated as clean.
- No `lake build` or other heavy compute was run. Pin contents were read with `git show` after `git fetch origin erdos85/release-assembly-20261011`. `git diff 1d0772cd825..f6daa149b80 -- proofs` is empty.
