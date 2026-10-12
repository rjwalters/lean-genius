# Revision: erdos85-drop.12 to erdos85-drop.13

Prepared by Claude (Opus), an AI author, as a direct edit addressing the v12 review
(`erdos85-drop.12.review/`, 41/44, advance) and author audit (`erdos85-drop.12.audit/`,
BLOCK on one critical flag). Not a human read-through.

| Source | Finding | Resolution |
|---|---|---|
| v12 audit C1 / review M1 | Availability named commit `92ff6248033c`, which lacks the rebuild records | `\repocommit` macro holds the pin; `\repobase` and the Availability sentence both use it. Pin now release assembly `2029149d7e42` (all 70 link targets exist there). |
| v12 audit M1 / review m4 | Independent check of the cold-build acceptance not recorded at the pin | Codex's re-audit (squad review #2749, PASS) recorded in `release_cold_build_20261011/ACCEPTED.md` at the pin; the build sentence now says the audit was repeated independently by a second AI author. |
| review m1 | Fetch-script comment "any AWS credentials work" | Script comment at the pin now says authenticated credentials, tested only with the bucket owner's account. |
| review m2 | FAILURE.md read as current; private path and account number in records | Superseded banner on FAILURE.md; ACCEPTED/THIRDPARTY records drop the local path and account number; README drops operator wording. |
| review m3 | Reproducibility in Table 2's "Open in Lean" column | Moved to "How it is checked" for H7 t>=1; removed from the upper-side "Open" cell. |
| review m5 | Labels with spaces rendered without spaces | Filename/directory labels. |
| review m6 | "cold rebuild"/"cold audit" ambiguous | Witness-axiom sentence, Table 2 and the Theorem B sentence name the September 2026 cold axiom audit. |
| audit minor | "second cold rebuild" was the third attempt | "A further cold rebuild". |
| audit minor | Output bundle publication status | "retained outside the repository and is not published". |
| nits | Date; compile rerun warning | Dated 12 October 2026; compiled to a fixpoint (no rerun warning). |
| review m7 / economy | ~12 pages vs ~10 target | Not addressed in this pass. |
