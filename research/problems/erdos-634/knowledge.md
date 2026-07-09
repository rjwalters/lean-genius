# Knowledge Base: erdos-634 (Triangle Dissection into Congruent Pieces)

## Session 2026-07-08 (researcher-2) — SURVEY: formalization-integrity defects, no PR

Claimed the PARENT `erdos-634` (research DB status = "completed", knowledge empty).
Inspection of `proofs/Proofs/Erdos634Problem.lean` (331 L, 3 axioms, **6 sorries**) found
it is NOT a sound research target — it has modeling defects that make honest sorry-filling
either vacuous or impossible. Flagging for Mechanic/Auditor rather than forcing a PR.

### Defect 1 — `Dissection` is area-only ⇒ positives vacuous, negatives unsound
`structure Dissection T n` (line 101) requires ONLY `∑ᵢ (pieces i).area = T.area`; no
disjointness/coverage. So `IsDissectable n` (∃ T, ∃ area-matching n congruent pieces) is
trivially TRUE for every n ≥ 1: take n identical copies of any triangle P (pairwise congruent)
and let T be P scaled by √n (area n·area(P) = ∑). This means:
- the positive sorries (`squares_dissectable` k², `two/three/six_squares_dissectable`,
  `sum_squares_dissectable`) are provable only *vacuously* — but their docstrings promise the
  real "explicit subdivision map", so a trivial identical-pieces fill would misrepresent them;
- the axioms `seven_not_dissectable`, `eleven_not_dissectable` (¬IsDissectable 7/11) are
  UNSOUND relative to this weak definition (area-IsDissectable 7 is actually true). No `False`
  is currently derivable because no positive theorem targets 7 or 11 (7,11 ∉ {k²,2n²,3n²,6n²,
  n²+m²}), but the model cannot distinguish the genuine (open) geometry.

### Defect 2 — `congruent_implies_similar` (line 79) is FALSE as stated
`Congruent` = multiset-equality of the side list; `Similar` = *componentwise* scaling
(∃k, T₂.a=k·T₁.a ∧ …). Counterexample: T₁=(3,4,5), T₂=(4,3,5) are congruent (same multiset)
but no k makes them componentwise-proportional. The sorry at line 81 cannot be honestly filled;
the lemma is unused downstream. Correct replacements would be `Congruent → equal area`
(Heron is symmetric in the side multiset) or a permutation-aware `Similar`.

### Recommendation
Route to Mechanic: either (a) strengthen `Dissection` with disjointness+coverage (>1000 L
geometry, BLOCKED-scale) or (b) reframe the entry honestly as an *area-level* proxy and fix/
remove the false `congruent_implies_similar`. Reconcile the DB "completed" status with the 6
remaining sorries. The three OQ children (medial-congruence / medial-covering, all 0-sorry/
0-axiom) are the sound active research surface; the parent needs integrity repair, not new
theorems on top of a degenerate model.
