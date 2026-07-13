# Knowledge Base: erdos-1092-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

## Session 2026-07-09 (researcher-5) — fThreshold well-definedness + parent build-repair

**Mode**: BUILD/ACT. **Outcome**: VERIFIED (docker [7744/7744], 0 sorry, 0 axiom) —
new file `Erdos1092OQ02.lean` (+ repaired the build-broken parent).

### New file `Erdos1092OQ02.lean`
Answers the OQ-02 question of whether `fThreshold`'s `sSup` (parent
`Erdos1092Problem.lean`) is a *genuine finite maximum* or the degenerate `sSup ℕ = 0`
artifact. Proved: **yes, in the non-degenerate regime `1 ≤ r ∧ r + 2 ≤ n`.**
- `SGraph.completeGraph` + `completeGraph_not_hasColoring` — `K_n` not `r`-colorable for
  `r < n` (pigeonhole `Fintype.card_le_of_injective`).
- `canReduce_removeAll` — deleting all `n*n` edges makes any graph `r`-colorable (`r ≥ 1`).
- `fThresholdSet` + `fThresholdSet_downClosed` — defining set is downward closed
  (via parent's `CanReduceChromatic_mono_k`).
- `fThresholdSet_bddAbove` — bounded above by `n*n` (K_n witness) in the regime.
- `fThreshold_le_sq` — `fThreshold r n ≤ n*n` (`csSup_le'`, no nonemptiness needed).

### Key mathematical finding
The problem has **two** degeneracies, not one:
- *Upper* (documented in parent): `r + 1 ≥ n` ⇒ every graph is `(r+1)`-colorable ⇒
  defining set = `ℕ` ⇒ `sSup = 0`.
- *Lower* (surfaced here): `r = 0` ⇒ reducing to `0` colors is impossible on `n ≥ 1`
  vertices ⇒ the antecedent `∀S CanReduce(·,k,0)` is always false ⇒ implication vacuous
  ⇒ defining set = `ℕ` ⇒ `sSup = 0`.
So the precise non-degenerate regime is `1 ≤ r ∧ r + 2 ≤ n`.

### Parent build-repair (was broken on main vs Mathlib 4.26)
- `SGraph.edgeCount`: `DecidablePred` synth failed on Prop-valued `G.adj` → `open scoped
  Classical`.
- `SGraph.chromaticNum`: malformed `Nat.find` (predicate unspecified, `Fin.elim0` witness
  only valid at `n=0`) → `sInf {r | G.hasColoring r}`.
- `SGraph.hasColoring_mono`: `Fin.val` elaborated at wrong `Fin` type → rewrote via
  `Fin.castLE` + `Fin.castLE_injective`.

### Gotchas
- `exact hmem (mem_univ _)` gives `False`, but the coloring goal is `c u ≠ c v` → use
  `absurd (mem_univ _) hmem`.
- `csSup_le'` (for `ConditionallyCompleteLinearOrderBot`) needs only an upper-bound
  membership, NOT nonemptiness — clean for `sSup`-of-possibly-empty ℕ sets.
- Persistent fleet SIGBUS-135 at olean-*write* (`[7744/7744]`, deps "Completed
  successfully"): elaboration is clean; only the write is killed. Also several corrupted
  Mathlib cache artifacts (`.ir`/`.trace` "invalid header"/"unexpected end of input") —
  `rm` the named file and rebuild. Needed ~15 build attempts to catch a clean write.
