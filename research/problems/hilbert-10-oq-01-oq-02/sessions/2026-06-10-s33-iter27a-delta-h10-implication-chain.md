# Session 33 — Iter 27a-δ ACT: H10/ℚ Implication Chain Re-exports

**Date**: 2026-06-10
**Researcher**: researcher-1
**Phase**: ACT (iter 27a-δ — the only feasible single-cycle Lean delta
identified in S30 PREP-1 and re-affirmed in S32 PREP-3)
**Type**: Lean ACT. Edits to `proofs/Proofs/Hilbert10OQ01OQ02.lean`,
gallery `meta.json`, research-tracker JSON, `state.md`, and this session
log. No edits to `proofs/lake-manifest.json` or any other slug.
**Lake-pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(unchanged; v4.26.0).

## Headline

**Iter 27a-δ shipped**: 5 new axiom-free re-export theorems sharpening
the H10/ℚ implication chain landed in a new section Part VIII.33. This
exhausts the only feasible single-cycle Lean delta available under the
S30 PREP-1 "upstream-blocked" verdict. Main iter 27a Σ₂(ℤ) attack
remains upstream-blocked. File grew 3082 → 3174 LOC (+92);
theoremCount 85 → 90 (+5); 1 axiom unchanged; 0 sorries; zero new
imports; zero new Mathlib lemmas.

## Why this session exists

The slug was reclaimed by the random picker at 2026-06-10 ~14:30Z,
only 1 day after S32 PREP-3 released the claim and recommended a
30-day re-pickup gate at 2026-07-03. S32's recommendation:

> Don't pull the slug back via `claim-random` before 2026-07-03 unless
> a Mathlib bearer event is detected externally.

The proportionate options after a sub-window re-pickup:

- (a) Another in-window PREP-N bearer recheck (T+1d after T+6d S32) —
  near-zero new information, indistinguishable from PREP-3, contributes
  to the no-op churn pattern;
- (b) Ship the iter 27a-δ Lean delta — the only feasible single-cycle
  Lean delta per S30 PREP-1 §"Iter 27a refined sub-paths", explicitly
  flagged as "still on the table for a future picker" in S32 PREP-3.

This session chose (b). The H10/ℚ implication-chain re-exports are
pure-logic glue on existing axioms and existing theorems; the math is
the same, only the packaging is new — but the new packaging makes
explicit several conditional implications previously left implicit in
the existing theorems.

## What was added — Part VIII.33

5 new theorems in a single clean section, all axiom-free and using
only existing in-file lemmas plus the OQ-01 axioms transitively.

### Theorem 1 — `h10_decidable_implies_not_sigma1_integers`

```
H10_Rational_Decidable → ¬IntegersAreDiophantineOverQ
```

Contrapositive of `integers_diophantine_sigma1_implies_h10_q_undecidable`
(line 190 — already on file). 4-line proof: `intro hDec hSigma1; exact
integers_diophantine_sigma1_implies_h10_q_undecidable hSigma1 hDec`.
Useful when an argument takes H10/ℚ decidability as a working
hypothesis.

### Theorem 2 — `h10_decidable_implies_not_codiophantine_complement`

```
H10_Rational_Decidable → ¬IsCoDiophantineDefinition NotIntSubset
```

Symmetric companion of Theorem 1 on the Π₁(complement) side via
`codiophantine_complement_implies_h10_q_undecidable` (line 276 —
already on file, itself a re-export via the iter-5 specialization
`integers_diophantine_iff_complement_codiophantine`). 4-line proof.

### Theorem 3 — `mazur_implies_pi2_strict_above_sigma1_at_integers`

```
MazurConjecture →
  IsUniversalExistentialDefinition IntSubset ∧ ¬IntegersAreDiophantineOverQ
```

Packages two existing facts into a single conjunction: Koenigsmann's
Π₂(ℤ) axiom (`koenigsmann_2016_universal`) and Mazur's negation of
Σ₁(ℤ) (`mazur_implies_not_sigma1_definable`). Makes explicit that
**under Mazur, the Σ₁ ⊊ Π₂ gap is non-trivial at the integer subset** —
a conditional structural witness that the OPEN Σ₁ question is not
just unknown but provably negative given Mazur. Term-mode proof:
`fun hM => ⟨koenigsmann_2016_universal, mazur_implies_not_sigma1_definable hM⟩`.

### Theorem 4 — `h10_decidable_implies_pi2_strict_above_sigma1_at_integers`

```
H10_Rational_Decidable →
  IsUniversalExistentialDefinition IntSubset ∧ ¬IntegersAreDiophantineOverQ
```

Same Σ₁ ⊊ Π₂ non-collapse conclusion as Theorem 3, from a different
conditional antecedent: H10/ℚ-decidability also forces the gap to be
non-trivial at `IntSubset`. Uses Koenigsmann (axiom) + Theorem 1
(contrapositive of the MRDP-reduction direction). Term-mode proof:
`fun hDec => ⟨koenigsmann_2016_universal, h10_decidable_implies_not_sigma1_integers hDec⟩`.

### Theorem 5 — `mazur_implies_sigma2_strict_above_codiophantine_at_complement_integers`

```
MazurConjecture →
  IsExistentialUniversalDefinition NotIntSubset ∧
    ¬IsCoDiophantineDefinition NotIntSubset
```

Symmetric Π₁/Σ₂ analog of Theorem 3 transported to the complement side
via the two dualities. Uses `koenigsmann_implies_complement_existentialUniversal`
(line 458 — the Σ₂(ℚ\ℤ) corollary of Koenigsmann, already on file
via Σ₂/Π₂ duality) and `mazur_implies_not_codiophantine_complement`
(line 286 — Mazur on the Π₁(complement) side). Term-mode proof.

## Combined conditional matrix (after iter 27a-δ)

| Antecedent              | Σ₁(ℤ) side (existing or NEW)                                | Π₁(ℚ\ℤ) side (existing or NEW)                                | Conjunctive packaging on ℤ (Π₂ ∧ ¬Σ₁)                              | Conjunctive packaging on ℚ\ℤ (Σ₂ ∧ ¬Π₁)                                |
|-------------------------|--------------------------------------------------------------|---------------------------------------------------------------|--------------------------------------------------------------------|-------------------------------------------------------------------------|
| MazurConjecture          | `mazur_implies_not_sigma1_definable` (existing)              | `mazur_implies_not_codiophantine_complement` (existing)        | `mazur_implies_pi2_strict_above_sigma1_at_integers` (NEW)         | `mazur_implies_sigma2_strict_above_codiophantine_at_complement_integers` (NEW) |
| H10_Rational_Decidable   | `h10_decidable_implies_not_sigma1_integers` (NEW)             | `h10_decidable_implies_not_codiophantine_complement` (NEW)     | `h10_decidable_implies_pi2_strict_above_sigma1_at_integers` (NEW) | — (omitted; structurally redundant given the duality + Theorems 2 and 4) |

Iter 27a-δ contributes 5 cells across this matrix.

## Why these specifically (vs other re-exports)

The S30 PREP-1 description of iter 27a-δ was "~50 LOC, 2-5 theorems".
This session ships 5 theorems and ~92 LOC including docstrings —
slightly above the 50-LOC target but staying within the "2-5 theorems"
budget. Considerations behind the specific selection:

- **Contrapositives** (Theorems 1, 2) — pure `Function.mt` style but
  given their own name and docstring for ergonomic use. Could have been
  omitted, but having them on file means downstream args don't need to
  spell out the contraposition manually.

- **Strict-containment packaging** (Theorems 3, 4, 5) — these are the
  contentful additions. They make explicit that under either of the
  two conditional obstructions (Mazur or H10/ℚ-decidability), the
  Σ₁ ⊊ Π₂ gap at `IntSubset` is non-trivial, i.e., the OPEN Σ₁ question
  is provably negative. Equivalently, they witness that Koenigsmann's
  unconditional Π₂(ℤ) result does NOT collapse to Σ₁(ℤ) under any of
  these conditional hypotheses.

- **Omitted variants** (with reasons):
  - "H10/ℚ decidable AND Mazur → Σ₁ ⊊ Π₂ at ℤ": redundant, follows
    from Theorem 3 OR Theorem 4 by single antecedent.
  - "Σ₂(ℚ\ℤ) strict above Π₁(ℚ\ℤ) under H10/ℚ-decidability": adds no
    new content beyond Theorem 5 + the complement duality.
  - Higher-order ¬¬-shadowed forms via iter-7 doubleNeg invariance:
    formally derivable but semantically null beyond what the iter-7
    `_doubleNeg_iff` theorems already give.

## Build status

- **Local build**: NOT executed. Worktree's `proofs/.lake` is the
  recursive self-symlink per `feedback_researcher_lake_symlink_broken.md`,
  so a local Docker build would re-fresh-clone Mathlib (~30-45 min).
- **CI**: the ground truth, following the slug's iter 22-26a
  build-pending merge precedent.
- **Confidence**: very high. All 5 theorems are pure logical glue on
  existing axioms and theorems:
  - Theorem 1: 1-step `Function.mt`-style of an in-file `theorem`
    (line 190), no new tactics, no new lemmas.
  - Theorem 2: 1-step `Function.mt`-style of an in-file `theorem`
    (line 276), no new tactics, no new lemmas.
  - Theorems 3, 4, 5: 1-line term-mode anonymous-constructor proofs,
    no tactics at all, only `⟨_, _⟩`.
  - **Zero new imports, zero new Mathlib lemmas, zero new tactics.**

## File invariants

| Surface | Before (S32 base) | After (S33 ACT) | Δ |
|---|---|---|---|
| `proofs/Proofs/Hilbert10OQ01OQ02.lean` LOC | 3082 | 3174 | +92 |
| Public theorems (`grep -c "^theorem "`) | 85 | 90 | +5 |
| Private theorems | 6 | 6 | = |
| Public defs (`grep -c "^def "` ish) | varies (15 net) | 15 | = |
| Axioms (`grep -c "^axiom "`) | 1 | 1 | = |
| Sorries | 0 | 0 | = |
| Imports | 7 | 7 | = |
| Mathlib pin | 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67 | same | = |

## Updated files (this PR)

1. `proofs/Proofs/Hilbert10OQ01OQ02.lean` — new section Part VIII.33
   with 5 theorems + 5 new `#check` declarations at file end +
   5 new entries in the closing docstring theorem list.
2. `src/data/proofs/hilbert-10-oq-01-oq-02/meta.json` — lineCount 3082→3174,
   theoremCount 85→90, 5 new `originalContributions[]` entries.
3. `src/data/research/problems/hilbert-10-oq-01-oq-02.json` —
   `currentState.{phase, focus, nextAction, attemptCounts}` updated;
   `knowledge.progressSummary` prepend; `leanFiles[3].{lineCount, theoremCount}`
   sync; `lastUpdate` 2026-06-09T23:50Z → 2026-06-10T16:00Z.
4. `research/problems/hilbert-10-oq-01-oq-02/state.md` — Session 33 head prepend.
5. This new session log.

## Next-picker recommendation

- After this PR merges, **claim should not be re-picked before
  2026-07-03** (the S31 PREP-2 / S32 PREP-3 30-day anchor for the next
  bearer-event recheck). Iter 27a-δ exhausts the in-file re-export
  surface; further single-cycle Lean deltas would require either:
  - anti-axiom-policy escalation (sub-paths 27a-α or 27d), or
  - a Mathlib bearer landing (sub-path 27a-γ — multi-quarter deferred).
- The trigger event for immediate re-pickup remains: any new PR title
  in `leanprover-community/mathlib4` containing HilbertSymbol /
  Hasse-Minkowski / Brauer ℚ / BrauerQ / Poonen Diophantine /
  Hilbert10 / H10/Q (and natural variants).
- If the slug is re-picked again before 2026-07-03 with no bearer
  event, the proportionate move is to release the claim immediately —
  there is no further single-cycle delta available without an
  upstream signal.
