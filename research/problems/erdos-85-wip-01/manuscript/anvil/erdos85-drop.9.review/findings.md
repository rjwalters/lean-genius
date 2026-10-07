# Findings — erdos85-drop.9

## 1. H3/H5/H7 sentence-by-sentence check against `refs/H3_EVIDENCE_AUDIT_20261007.md`

| Location | Text (abridged) | Ref says | Match |
|---|---|---|---|
| Abstract L66 | "only one part has certificates, checked inside Lean (H7, $t\ge1$)" | certificate-checked strata are H1 (external) and H7 $t\ge1$ (inside Lean) | yes |
| Abstract L66 | "reviewed arguments with independently **replayed** computation (H3, H5; H7, $t=0$)" | "reviewed arguments with independently **checked** computation" | **no — M1** (H3 yes; H5, H7 $t=0$ over-stated) |
| Abstract L66 | "the H3, H5 and H7 ($t=0$) exclusions are open in Lean" | cell exclusions undischarged hypotheses; H5 premises; H7 capstone | yes |
| Result A L78 | "certificate-checked computation for H1 and for H7 with $t\ge1$ ... independently **replayed** computation for H3, H5 and H7 with $t=0$" | as above | H1/H7 scope yes; "replayed" **no — M1** |
| §1 L87 | "exclusions of H3, H5 and H7 ($t=0$) rest on reviewed arguments rather than on certificates or Lean proofs" | same | yes |
| §2.3 L110 | two cells $t=1$ / $t=0$ with $b\in\{0,1\}$ matching | Q7 note: triple profile / pair profile, matching with b=0 or 1 | yes |
| §2.3 L110 | `threeHighCanonicalGraphCover_all` proves the cover; `..._three_of_representativeExclusions` reduces to two exclusions | "graph normalization/cover is proved"; Q7 names the conditional theorem | yes (verified in source L530/L537) |
| §2.3 L110 | "no SAT verdict or LRAT proof exists for either cell formula ... undischarged hypotheses" | verbatim substance | yes |
| §2.3 L110 | 3,337 / 972 / 3,600; independent review; $t=0$ replays unchanged-source, no time limit, exact agreement | Q7 table and replay sentence | yes |
| §2.3 L112 | H5 "reviewed reductions with independently checked finite computation ... No SAT certificate ... three Boolean-exclusion premises" | "v8's wording ... is accurate" | yes |
| §2.3 L114 | H7 $t\ge1$ LRAT certificates checked inside Lean by `native_decide`; `Lean.ofReduceBool` | H7 $t\ge1$ certificate-checked inside Lean | yes |
| §2.3 L116 | H7 $t=0$ reviewed ledger; one enumeration audited not replayed; capstone uninstantiated | H7 $t=0$ under reviewed arguments | yes |
| Table 2 L205–L208 | H3 "independently replayed ... no certificates", "two cell-exclusion premises"; H5/H7 $t=0$ "independently checked" | as above | yes |
| §4 L214 | "H3 could instead be closed by a certificate for each of its two cell formulas, but neither has been produced" | "Closing H3 in Lean needs either two `LRAT.check` facts ... or four `Unsat` facts" | yes (m3 optional context) |
| §8 L257 | links `STRATA_AND_SMALL_ORDERS_20260928.md` | "Source of the error ... Corrected in place 2026-10-07" — correction not on `erdos85/integration` | **receipt stale — M2** |

## 2. "Certificate-checked" scope

Occurrences in v9: abstract (H1), Result A (H1; H7 $t\ge1$), §2.3 L110 (negated, for H3). "Formally verified checker" appears only in §1 L85 for H1 (cake_lpr), and "the formally verified empty-hexagon theorem" for the precedent. The old title, the only unscoped use, was replaced mid-review by R-TITLE, and the new title does not contain the term. No use extends the term to H3, H5 or H7 $t=0$.

## 3. Cross-section observations

- The status discipline holds: Table 2 is the single list of open items, and the abstract, §1 and §3.4 refer to it with short mandated restatements.
- The v9 changes are confined to what the changelog states. A diff against v8 shows edits only in the abstract, Result A, §1, §2.3 H3, §2.4 (`native_decide` note), §3 opening, §3.2 (two paragraphs), §3.4, Table 2, post-table, and §8, plus 3 `refs.bib` title-capital fixes. The title line was changed later by the operator.
- `main.pdf` predates the operator's title edit and must be rebuilt.
- The BRIEF frontmatter `claim` (corrected 2026-10-07) and the abstract now agree in substance. The only wording gap is "checked" vs. "replayed" (M1).

(No rubric version transition: the prior review `erdos85-drop.8.review/` was scored against `anvil-pub-v2`, the same rubric.)
