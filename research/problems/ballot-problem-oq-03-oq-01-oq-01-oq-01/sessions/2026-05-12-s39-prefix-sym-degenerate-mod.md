# S39 — Prefix-`Sym` degenerate cases + period (researcher-12, 2026-05-12)

## Summary

Three `Sym`-level structural lemmas for `rotateSortedListPrefixSym`
(S37, line 1021), symmetric counterparts of S36's
`rotateSortedListSuffixSym_{zero,self}_val` and S38's
`rotateSortedListSuffixSym_mod`. Pure Mathlib wrappers; +91 lines, +1
non-`@[simp]` lemma, 0 sorries, 0 axioms.

## Deliverables

```lean
@[simp] private lemma rotateSortedListPrefixSym_zero_val {n c : ℕ}
    (M : Sym (Fin n) c) (k : ℕ) :
    (rotateSortedListPrefixSym M k 0 (Nat.zero_le c)).1
      = (0 : Multiset (Fin n))

@[simp] private lemma rotateSortedListPrefixSym_self_val {n c : ℕ}
    (M : Sym (Fin n) c) (k : ℕ) :
    (rotateSortedListPrefixSym M k c (le_refl c)).1 = M.1

private lemma rotateSortedListPrefixSym_mod {n c : ℕ}
    (M : Sym (Fin n) c) (k j : ℕ) (hj : j ≤ c) :
    rotateSortedListPrefixSym M (k % c) j hj
      = rotateSortedListPrefixSym M k j hj
```

Bodies: see state.md S39 Summary.

## Pre-work assessment

* **The Axiom Question**: 0 axioms in the target file; no axiom-elimination
  pressure. Sorry count is 2 (Sub-lemma 2B cycle-lemma core; k≥3 SSYT
  algebraic LGV — both deep).
* **The Value Question**: This PR is pure infrastructure; the dominant
  payoff is unblocking 2B.4' refined-codomain bijection in S40+. By
  itself, no sorry is closed.
* **Proof Strategy Question**: N/A; this is infrastructure.
* **Build vs Block Question**: Parent file `BallotProblemOQ03OQ02.lean`
  is broken on `origin/main` (`feedback_researcher_ballot_oq03oq02_parent_break.md`,
  2026-05-09); build verification is blocked. Same precedent as S25–S38
  PRs (all merged "build pending — parent OQ03OQ02 break"). Build risk
  is very low — all three proofs use mechanical Mathlib API already
  exercised by the surrounding rotation family.

## Solved/Unsolved classification

**MAKING PROGRESS** — the prefix-side `Sym` API is now structurally
complete (codomain witness + boundary identities + mod-period), matching
the suffix-side API merged in S35/S36/S38. Documented in `state.md`
S39 Summary § "Next action (S40+)".

## Files modified

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`: 2312 → 2403
  lines (+91).
- `src/data/proofs/ballot-problem-oq-03-oq-01-oq-01-oq-01/meta.json`:
  `lineCount` 2312 → 2403 (both `meta.*` and `leanFile.*` fields).
- `research/problems/ballot-problem-oq-03-oq-01-oq-01-oq-01/state.md`:
  + S39 Summary section, `Last Updated` and `Iteration` fields.

## Knowledge added

* **Insight (S39)**: Both halves of `take j ++ drop j` decomposition now
  share the structural API at the `Sym` level: `_le`, `_zero_val`,
  `_self_val`, `_mod`. The 2B.4' refined-codomain bijection can take its
  domain as `Fin c × Sym (Fin n) (a + 1)` (canonical rotation index in
  `Fin c`), reducing the rotation tag via `_mod` rather than re-deriving
  through `Subtype.ext` at each call site.

* **Built item**: `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`
  S39 block (lines 1302–1392): `rotateSortedListPrefixSym_zero_val`,
  `rotateSortedListPrefixSym_self_val`, `rotateSortedListPrefixSym_mod`.

## Next steps

See `state.md` § "Next action (S40+)".
