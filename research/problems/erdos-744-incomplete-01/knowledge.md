# Erdős #744 (incomplete-01: complete `bipartitionNumber` definition) — Knowledge Base

## Session 2026-07-08 (researcher-1) — PHANTOM-COMPLETE + tautological-axiom integrity finding

**The `bipartitionNumber` definition-sorry this slug targets is already resolved.**
problem.md describes a `sorry` in a `Nat.find` witness for `bipartitionNumber`, but the
definition was rewritten intrinsically (PR #27334, "complete bipartitionNumber definition;
un-bit-rot") as
`bipartitionNumber G := (univ : Finset (V→Bool)).inf' univ_nonempty (monochromaticEdges G)`
— total, no `Nat.find`, no sorry, no axiom. PR #35148 later cut the chromaticNumber axiom
(2→1). Current `Erdos744Problem.lean`: 0 sorries, 1 axiom, 11 theorems. So the served task
is DONE — no code change made.

## ★Integrity finding (for mechanic / peer-reviewer): the remaining axiom is a TAUTOLOGY

The sole remaining axiom is
`axiom rodl_tuza_theorem (k) (hk : k ≥ 3) : ∃ N₀, ∀ n ≥ N₀, f k n = (k-1)*(k-2)/2`.
But `f` is DEFINED as a hardcoded closed form, independent of n:
```
def f (k n : ℕ) : ℕ := if k < 3 then 0 else if k = 3 then 1 else (k-1)*(k-2)/2
```
For every k ≥ 3 and EVERY n, `f k n = (k-1)*(k-2)/2` (k=3: 1 = 2·1/2; k≥4: by def). So
`rodl_tuza_theorem` is trivially provable with N₀ = 0 (`refine ⟨0, fun n _ => ?_⟩; unfold f;
split_ifs <;> [omega; (subst ..; decide); rfl]`). It captures NONE of the genuine
Rödl–Tuza content — `f` is defined to equal the answer, not as
`min { bipartitionNumber G : G is k-critical on n vertices }`.

**Why I did NOT convert it.** Converting the axiom to a theorem would make the file
0-axiom/0-sorry ⇒ the gallery would mechanically read `verified`, badly OVERCLAIMING: the
entry would appear to machine-prove Erdős #744 while formalizing only a definitional
placeholder. Per CLAUDE.md ("when in doubt, axiomatized; overclaiming verified damages
credibility") the honest fix is NOT a trivial conversion.

**Genuine fix (BLOCKED, > 1000 LOC).** Redefine `f k n` as the true extremal minimum over
k-critical graphs on n vertices, then either prove the Rödl–Tuza asymptotic (deep research
theorem, not in Mathlib) or keep it as an honest STATEMENT axiom about the REAL `f`. Either
way needs k-critical-graph machinery Mathlib lacks. Recommend the mechanic/peer-reviewer
decide between (a) redefining `f` properly, or (b) at minimum relabeling the current
tautological "axiom" and documenting that `f` is a hardcoded placeholder.
