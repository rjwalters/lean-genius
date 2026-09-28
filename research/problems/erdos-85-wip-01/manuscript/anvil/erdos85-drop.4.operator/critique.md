# Operator critique of erdos85-drop.4 (read-through, 2026-09-28)

Two defects the lifecycle did not catch (filed upstream as rjwalters/anvil#1322). Both are now hard rules in BRIEF.md (R-AUD, R-LINK) and are critical flags for v5.

## F1 — governance and authorization notes addressed to the operator, not the reader (R-AUD)

Examples in v4 (not exhaustive; apply the rule to the whole text):
- §4.4 "No replay wave is authorized by this estimate."
- §4.4 and §7 "subject to the operator's publication gate"
- Appendix A "all 20 authorized solver attempts ended UNKNOWN"
- Appendix B: "Operator goal #25 made the outline the allocation instrument", "reopened by goal #38", "Goal #39 required a pre-fire manifest", "Goal #36 imposed a stuck test", "goal #39 authorized the certificate campaign ...; goal #40 commissioned this manuscript", "nothing goes external before operator review (messages 31965, 31970)", "the operator cancelled certificate production and replay for this paper"
- Appendix B and §1: room-message numbers ("message 31994", "messages 31868--31874", …), "outline v2.64 entry 2.61", and §1's "the appendices carry transcript pointers into the campaign record"
- §1 contributions: keep the transcript-true contribution statement, but "The human operator set compute policy, research priorities, authorship, scope, and the final read-through gate" reads as governance; reduce to what a reader needs.

Fix: delete or rewrite as the reader-relevant fact. Appendix B keeps only technical lessons (verification asymmetry, the 80/88-owner case study, the adversarial-diversity examples, the structure–compute exchange rate, silence-is-not-success) written without goal numbers, authorizations or message numbers; the "Persistence" and "The human role" paragraphs go; "Methods" stays as pointers.

## F2 — repo-relative paths and private locators instead of public links (R-LINK)

§7 names ~30 files as bare repo-relative paths with one \url to the repository root; Appendix A names ledger files the same way; §4.2 and §3.2 name Lean modules; §7 names the S3 bucket and the artifact volume path. Fix: `\repobase` + `\repofile{path}{label}` hyperlinks for everything public (see BRIEF R-LINK for the canonical paths); one sentence for what is not public.

## Carry-overs from .4.audit (minors) to fix in the same pass
m1 "one for each of its canonical cells with a positive triple" → representatives; m2 "complement completion for eleven of the twelve a = 7 roots" → "where required (three roots)"; m3 1,412 preparations concern the 1,137 cloud-dispatched rows (24 pilot rows on the Mac); m4 §2 "compiler-generated axioms that we list" → scoped to the witnesses; n1 use one vocabulary for the native_decide axioms; n2 "pilot plus four cloud passes".
