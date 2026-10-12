# Editable revision: erdos85-drop.11 to erdos85-drop.12

Status: revise in progress. Prepared by codex, an AI author, under the user's
ongoing request to finalize the paper following publication of the H7 inputs.
This is a direct editing pass beyond the historical iteration cap, not an
independent human read-through or an operator critic. The version stays
editable until the cold-build result is retained, audited and reconciled.
No READY/AUDITED or publication decision is recorded here.

| Source | Note | Resolution |
|---|---|---|
| Squad review 2747 (Claude, PASS at a992868f51e) | Explain why the H7 leaf was split | States that the leaf exceeded the solver time cap; detailed pass caps remain in the linked campaign record. This review covers the settled prose and supporting documents, not final build acceptance. |
| .11.review (generic m1) | Position H7 against the empty-hexagon precedent | Added the source-checked comparison: symmetry-breaking soundness and composition of cover/leaf UNSAT hypotheses. The cover UNSAT hypothesis itself is not called a proved result. |
| .11.review (generic m2) / .11.audit (M1 disclosure) | Publication versus cold reproducibility | Updated publication status across introduction, H7, status table and availability. Separated formal gaps from replay validation. Added script, manifest and build-recipe links. Cold-build acceptance remains pending. |
| .11.review (generic m3) | Artifact availability in Open in Lean column | H7 positive-triple row starts “nothing; not standard-axiom-only,” with prior replay scope stated separately. |
| .11.review (generic m4) | Dense campaign paragraph / approximate ten-page target | Removed pass caps, timeout counts and all-runs totals from the paragraph, retaining the split, identity method and verified-check totals. Detailed totals remain in the linked campaign record. Final page count to be checked after all edits. |
| .11.review (generic n1) | Two “now superseded” phrases | Removed “now”; made the chronology explicit where appropriate. |
| .11.review (generic n2) | $225 estimate qualifier and sources | Added “controller estimates” and linked both source receipts. |
| .11.review (generic n3) | “Previously settled” | Changed to “previously known”; novelty remains qualified. |
| .11.review (generic n4) | Operator-ceiling clause in linked H7 README | Removed from the supporting receipt on this draft branch; final artifact re-pin remains outstanding. |
| .11.review (generic n5) | H5 table check count | States 40 search parts and 18 cover/cardinality checks. |
| .11.review (BRIEF advisory) | Stale historical claim | Updated the BRIEF current claim and factual amendment; manuscript README now records v11 review/audit and distinguishes editable v12 from the manuscript of record. |
| .11.audit (citation limits) | Ten sources unverified locally, three partial | Follow-up reads of eight existing sources are recorded in citation-followup.md, with abstract-only and retention limits explicit. Removed the unsupported generalization “too large to keep.” Bibliography unchanged; final audit still outstanding. |
| .11.numeric / .11.pending / .11.audience | Existing deterministic checks | Prior clean numeric/pending results are not reused as new results. Prior audience hits were verified macro-expansion false positives. The new draft contains an intentional pending cold-build marker. |

The initial artifact pin is published commit
92ff6248033c6e6a16acd372120a056df759c9f4, containing the relative input paths,
fetch script, SHA256 manifest, full owner-profile fetch log and cold-build
procedure. This is an interim artifact pin; the final version must link the
terminal result and reviewed integration snapshot. Download success from a
separate AWS account has not been tested.

Remaining work: terminal cold-build evidence/audit; final pin; complete
render, link, numeric, claim, peer review
and author audit checks. A successful source rebuild would not discharge
the explicit H1/H7 UNSAT hypotheses, the emitter identity gap or the
native_decide trust assumptions.

Initial draft preflight: three XeLaTeX passes with BibTeX reached an aux
fixpoint, 14 pages, zero overfull boxes or final-pass unresolved/rerun
warnings. All 67 artifact-link targets exist at the interim pin; all 17
citation keys resolve. The pending-marker tool exits 1 for the real
outstanding cold-build dependency. Main-text length remains an advisory
item; no final review score or audit acceptance is inferred.

Publication follow-up: unauthenticated HTTPS downloads of the pinned fetch
script and manifest match their Git blobs. S3 configuration confirms the
public GetObject grant includes the H7 positive-triple prefix, Requester
Pays is enabled, and no bucket/account public-policy restriction or explicit
bucket-policy deny blocks that grant. This is configuration evidence, not
a separate-account download test; see publication-check.json. The fetch
script's credential comment now states the required S3 permissions, with
no executable behavior change.
