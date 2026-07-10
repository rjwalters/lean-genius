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

## Session 2026-07-09 (researcher-2) — 3 structural bipartitionNumber lemmas (axiom-free)

The served definition-sorry remains phantom-complete (confirmed prior finding). Rather
than touch the tautological `rodl_tuza_theorem` axiom (which would overclaim — see prior
session), added genuine axiom-free structural machinery about the intrinsic
`bipartitionNumber` definition (Erdos744Problem.lean, VERIFIED 0-sorry / 1-axiom-unchanged):

- `monochromaticEdges_mono`: if `G.Adj ⊆ H.Adj` then `monochromaticEdges G c ≤ monochromaticEdges H c`
  for every 2-colouring `c` (Finset.card_le_card on the filter subset).
- `bipartitionNumber_mono`: **bipartition number is monotone under edge addition** —
  `bipartitionNumber G ≤ bipartitionNumber H`. Take H's minimiser `c` via
  `Finset.exists_mem_eq_inf'`, then `inf'_le` + `monochromaticEdges_mono`. This is exactly
  the property Erdős's (disproved) original intuition concerned: he expected f_k to grow
  with the graph; monotonicity holds, but the *critical-graph minimum* f_k does not grow.
- `edgeCount` def + `bipartitionNumber_le_edgeCount`: `bipartitionNumber G ≤ edgeCount G`
  (the all-`true` colouring makes every edge monochromatic, so its count = edgeCount, and
  the inf can only do better). Records the trivial "delete every edge" upper bound.

Counts: leanFile/meta 407→467 lines, 11→14 thm, 13→14 def, axiomCount 1 unchanged,
status stays `axiomatized` (the honest Rödl–Tuza statement axiom remains).

## Session 2026-07-09 (researcher-2) — Max-cut / min-uncut complementarity (DEEP DIVE, PROGRESS)

The served definition-sorry remains phantom-complete and the tautological `rodl_tuza_theorem`
axiom was left untouched (converting it overclaims — see prior integrity finding). Added a
genuine, load-bearing structural layer on the intrinsic `bipartitionNumber` engine, distinct
from the earlier-today monotonicity/edgeCount lemmas (VERIFIED axiom-free, axiomCount unchanged):

- `bichromaticEdges G c` (def) — dual of `monochromaticEdges`: edges whose endpoints get
  *different* colors (the edges cut by `c`).
- `monochromaticEdges_add_bichromaticEdges` — per-coloring edge conservation:
  `monochromaticEdges G c + bichromaticEdges G c = edgeCount G`. Proof: rewrite both filters as
  `(edge-base-set).filter (c = c)` / `.filter (¬ c = c)` via `Finset.filter_filter`, then
  `Finset.filter_card_add_filter_neg_card_eq_card`; close `s.card = edgeCount` by `rfl` (defeq).
- `maxCut G` (def) — `sup'` of `bichromaticEdges` over all colorings.
- **`bipartitionNumber_add_maxCut`** — the headline: `bipartitionNumber G + maxCut G = edgeCount G`.
  The min-uncut (`bipartitionNumber`) and max-cut are complementary and realized by the *same*
  optimal coloring. Proof by `le_antisymm`: each direction picks the extremal coloring
  (`exists_mem_eq_sup'` / `exists_mem_eq_inf'`), applies the per-coloring conservation identity,
  and finishes by `omega` (using `bipartitionNumber_le` / `Finset.le_sup'`).
- `maxCut_eq_edgeCount_iff` — `maxCut G = edgeCount G ↔ G bipartite` (∃ proper 2-coloring), from
  the complementarity + `bipartitionNumber_eq_zero_iff`, via `omega` on the iff.

**Why not scaffolding.** This is the standard max-cut ↔ min-uncut duality, the natural companion
to the file's `bipartitionNumber` = min-monochromatic-edges definition, and it does NOT sit on the
tautological axiom (`#print axioms` on all three theorems = `[propext, Classical.choice, Quot.sound]`
only). It is orthogonal structural graph theory, not a step toward the (disproved) Erdős #744
conjecture, whose status is unchanged.

**Verification (docker DOWN).** Containerd meta.db + content-store blob `input/output error` at
image build (operator-level, NOT disk — 157Gi free). Verified by direct `lean` elaboration against
the repo's pinned Mathlib v4.26.0 oleans: **exit 0**, only two PRE-EXISTING `unused variable`
warnings in the untouched `f_*` theorems. `#print axioms` clean (above).

**Counts.** Erdos744Problem.lean → 578 lines, 20 thm, 15 def, 1 axiom (unchanged), 0 sorry;
src/data/proofs/erdos-744/meta.json synced.

## Session 2026-07-09 (researcher-3) — max-cut ≤ edgeCount + edgeless zero-case (VERIFIED)

The `bipartitionNumber`/`maxCut` engine already had complementarity
(`bipartitionNumber_add_maxCut`), `bipartitionNumber_le_edgeCount`, and the saturated-case
`maxCut_eq_edgeCount_iff`. Added the two missing companions (both axiom-free):

- `maxCut_le_edgeCount`: the dual of `bipartitionNumber_le_edgeCount` — one-line `omega`
  off the complementarity identity.
- `maxCut_eq_zero_iff`: `maxCut G = 0 ↔ edgeCount G = 0` (max-cut vanishes iff `G` edgeless),
  the zero-case dual of `maxCut_eq_edgeCount_iff`. Forward direction is a construction: if
  `edgeCount > 0` pick an edge `p` (`Finset.card_pos`), the isolating coloring
  `c = fun w => decide (w = p.1)` cuts it (`c p.1 = true ≠ false = c p.2` since `p.2 ≠ p.1`
  from `p.1 < p.2`), so `bichromaticEdges G c ≥ 1 ≤ maxCut` contradicts `maxCut = 0`; reverse
  is `omega` off `maxCut_le_edgeCount`. Membership discharge mirrors `monochromaticEdges_eq_zero_iff`
  (`filter_eq_empty_iff` + `⟨hlt, hadj, by simp only [hc]; simp [hne_uv]⟩`).

The tautological `rodl_tuza_theorem` axiom is untouched (converting it overclaims — prior
integrity finding); axiomCount unchanged, status stays `axiomatized`.

VERIFIED green via direct lean-elab vs pinned Mathlib v4.26.0 (docker containerd blob I/O down):
exit 0, no errors; `#print axioms` on both = `[propext, Classical.choice, Quot.sound]`.
Gallery meta erdos-744: lineCount 578→614, leanFile.theoremCount 20→22 (top-level curated
theoremCount 14 left as-is — different convention).

## Session 2026-07-10 (researcher-3) — fourth corner of the max-cut/min-uncut square (VERIFIED)

**Mode**: REVISIT (MODERATE) · **Outcome**: progress (1 theorem, 0 new axioms), **VERIFIED**
via direct `lake env lean` single-file elaboration against pinned Mathlib v4.26.0 oleans
(docker image build still hits containerd meta.db I/O error; single-file elab is exit 0, only
two pre-existing `unused variable` warnings in the untouched `f_*` theorems).

**Contribution.** Added `bipartitionNumber_eq_edgeCount_iff : bipartitionNumber G = edgeCount G ↔ edgeCount G = 0`
— the fourth and final "corner" of the max-cut / min-uncut characterization square, the exact
dual of the existing `maxCut_eq_edgeCount_iff`:

| quantity | `= 0` | `= edgeCount` |
|----------|-------|---------------|
| `maxCut` | edgeless (`maxCut_eq_zero_iff`) | bipartite (`maxCut_eq_edgeCount_iff`) |
| `bipartitionNumber` | bipartite (`bipartitionNumber_eq_zero_iff`) | **edgeless (this lemma)** |

Proof mirrors `maxCut_eq_edgeCount_iff` exactly: `rw [← maxCut_eq_zero_iff]; have h := bipartitionNumber_add_maxCut G; omega`.
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (does NOT touch `rodl_tuza_theorem`).

**File state:** 1 axiom (`rodl_tuza_theorem`, tautological/untouched — converting overclaims,
prior integrity finding), 0 sorries. 614→634 lines. meta.lineCount synced 614→634; curated
meta.theoremCount left at 14 (per prior-session convention: curated headline count, not raw).

**No follow-up questions:** engine is saturated (all four extremal corners now present); the
Erdős #744 conjecture status is unchanged (disproved), remaining directions are the untouched
tautological axiom and the f_k(n) table.

**Verification path (REUSABLE):** docker down but `cd proofs && ./bin/lake env lean Proofs/<File>.lean`
works — `lake env` is allowed by the safety wrapper (only `lake build` is blocked), and Mathlib
oleans are present at `.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean`. Single-file
elaboration does not rebuild Mathlib, so it is safe and fast (~exit 0 in seconds).
