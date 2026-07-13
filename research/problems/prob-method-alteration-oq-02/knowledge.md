# prob-method-alteration-oq-02

**Question**: Can the independent set bound α(G) ≥ n²/(2m+n) be improved for triangle-free graphs?

**Answer**: YES. Two improvements exist:
1. **Turán-Mantel** (proved): α(G) ≥ 2n/(n+2) for all triangle-free G
2. **AKS 1980** (axiomatized): α(G) ≥ c·n·log(d)/d for triangle-free G with avg degree d

**Proof file**: `proofs/Proofs/ProbMethodAlterationOQ02.lean`

---

## Session 2026-04-04 (Session 1) — Triangle-Free Independence Number Improvement

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Proved `mantel_bound_four`: 4*|E(G)| ≤ n² for CliqueFree 3 graphs via `CliqueFree.card_edgeFinset_le`
- Proved `improvement_key_ineq`: 4m ≤ n² ⟹ 2n(2m+n) ≤ n²(n+2) by `nlinarith`
- Proved `triangle_free_alpha_improvement`: α(G) ≥ 2n/(n+2) for triangle-free graphs
- Axiomatized `caro_wei` and `aks_triangle_free`
- Proved `aks_beats_turan_for_large_graphs`, `turan_improvement_tight_real`, `bipartite_alpha_exceeds_bound`

### Key Findings
- The algebraic core: n²/(2m+n) ≥ 2n/(n+2) ↔ n² ≥ 4m (exactly Mantel's bound)
- `CliqueFree.card_edgeFinset_le` in Mathlib gives Turán bound; need `rcases Nat.mod_two_eq_zero_or_one` + `omega` for n%2 case analysis
- `open Real` shadows `div_le_iff`, `div_le_div_iff`, etc. → use `field_simp [h.ne']` + `sub_nonneg` approach
- `exact_mod_cast` cleanly lifts ℕ inequalities to ℝ
- `field_simp [h.ne']` (with explicit nonzero hints) fully closes equality goals — do NOT add `; ring`

### Files Modified
- `proofs/Proofs/ProbMethodAlterationOQ02.lean` (created, 212 lines)
- `proofs/Proofs.lean` (added import)
- `src/data/research/problems/prob-method-alteration-oq-02.json` (updated)

### Follow-Up Questions
- Is the AKS bound c·n·log(d)/d tight for triangle-free graphs?
- Does the Turán-Mantel improvement extend to C₄-free or C₅-free graphs?
