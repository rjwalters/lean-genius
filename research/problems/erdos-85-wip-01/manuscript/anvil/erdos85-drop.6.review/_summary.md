# Review summary

```json
{
 "critic": "review",
 "for_version": 6,
 "rubric": {
  "id": "anvil-pub-v2",
  "total": 44,
  "advance_threshold": 35,
  "dimensions": 9,
  "prior_rubric_id": "anvil-pub-v2"
 },
 "total": 34,
 "threshold": 35,
 "advance": false,
 "ready": false,
 "critical_flags": [
  "scope_overclaim_h1_certificate_check"
 ],
 "dimensions": [
  {
   "id": "1_rigor",
   "score": 5,
   "max": 6
  },
  {
   "id": "2_evidence",
   "score": 4,
   "max": 6
  },
  {
   "id": "3_contribution_clarity",
   "score": 4,
   "max": 5
  },
  {
   "id": "4_related_work",
   "score": 4,
   "max": 5
  },
  {
   "id": "5_reproducibility",
   "score": 4,
   "max": 5
  },
  {
   "id": "6_figures_tables",
   "score": 3,
   "max": 4
  },
  {
   "id": "7_prose_structure",
   "score": 3,
   "max": 4
  },
  {
   "id": "8_citation_hygiene",
   "score": 4,
   "max": 5
  },
  {
   "id": "9_rhetorical_economy",
   "score": 3,
   "max": 4
  }
 ],
 "render_gate": {
  "pass": true,
  "pages": 23,
  "overfull_boxes": 0,
  "placeholders": 0
 },
 "numeric_consistency": {
  "pass": true,
  "numbers_extracted": 935,
  "claims_checked": 1,
  "findings": 0
 },
 "pending_marker": {
  "pass": true,
  "outstanding_sources": []
 },
 "audience_check": {
  "advisory": true,
  "governance_vocabulary": 0,
  "private_locator": 0,
  "unlinked_artifact_path": 14,
  "note": "all 14 are \\repofile false positives"
 },
 "evidence_drift": {
  "status": "CLEAN",
  "changed_paths": []
 },
 "evidence_check": {
  "pass": true,
  "dimensions_checked": 9,
  "findings": 0
 },
 "scope_lint": "PASS (58 numbers, 57 Lean names)",
 "prior_review": {
  "version": 5,
  "total": 38
 },
 "prior_operator_critic": {
  "version": 5,
  "verdict": "BLOCK",
  "critical_flags_resolved": [
   "brief_amendment (R-CERT) - resolved in form; reframing introduced scope_overclaim_h1_certificate_check",
   "operator_defect a (Lean.ofReduceBool S3.1)",
   "operator_defect b (App. B thirteen hashes; abstract native_decide)"
  ]
 },
 "iteration": {
  "current": 6,
  "max": 6,
  "operator_override": true
 },
 "termination_reason": "BLOCKED_CRITICAL_FLAG"
}
```
