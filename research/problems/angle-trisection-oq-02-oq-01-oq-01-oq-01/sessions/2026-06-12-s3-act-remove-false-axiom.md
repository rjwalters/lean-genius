# S3 ACT — remove the false axiom `insep_gal_trivial` (axiom-free)

**Date**: 2026-06-12
**Researcher**: researcher-2
**Mode**: ACT (Lean bodies change; Docker build-verified)
**Phase**: S3 ACT
**Branch**: `research/erdos-735-oq-04-s6a-tetrahedron-<ts>` (this session bundled two slugs;
see also the erdos-735-oq-04 S6a scaffold commit)

## Problem

`proofs/Proofs/AngleTrisectionOQ02OQ01OQ01OQ01.lean` carried **1 axiom**,
`insep_gal_trivial` ("char p, inseparable irreducible ⇒ |Gal| = 1"), which is
**mathematically FALSE**: the OQ-01 descendant
(`AngleTrisectionOQ02OQ01OQ01OQ01OQ01.lean`) refutes it with `f = X⁴ + X² + a`
over `F₂(a)` — irreducible, inseparable, yet `|Gal(f)| = 2` via the
Artin–Schreier automorphism `α^{1/2} ↦ α^{1/2} + 1`. The axiom had been retained
as a placeholder so the consequence `natDeg_notDvd_gal_of_insep` type-checked.
The S2 STATE-SYNC (2026-06-09) flagged this and named the removal as the next ACT.

## What this iteration did

Deleted the false axiom and its false-axiom-backed consequence, and replaced them
with the honest, axiom-free obstruction — **ported** from the descendant (which
imports this file and so cannot be imported back without a cycle):

| Declaration | Role |
|---|---|
| `sub_pow_char_pow_eq` | char-`p` Frobenius identity `(a-b)^(p^n)=a^(p^n)-b^(p^n)` |
| `algEquiv_eq_refl_of_isPurelyInseparable` | every `σ : K ≃ₐ[F] K` over a purely inseparable `K` is `refl` |
| `gal_card_one_of_purelyInseparable_splitting` | purely-inseparable splitting field ⇒ `|Gal| = 1` |
| `natDeg_notDvd_gal_of_purelyInseparable_splitting` | honest non-divisibility for degree > 1 |

The correct hypothesis is **purely-inseparable splitting field**, not mere
inseparability of `f` — exactly the distinction the descendant's counterexample
forces.

## Verification

- `./proofs/scripts/docker-build.sh Proofs.AngleTrisectionOQ02OQ01OQ01OQ01` →
  clean, **7745 jobs**, 0 warnings.
- `./proofs/scripts/docker-build.sh Proofs.AngleTrisectionOQ02OQ01OQ01OQ01OQ01`
  (the importing descendant) → clean, **7746 jobs**; only pre-existing
  `unusedSimpArgs` linter warnings (not introduced here). No regression.
- Confirmed no other file references the deleted symbols in code
  (`grep` for `insep_gal_trivial` / `natDeg_notDvd_gal_of_insep` → only this file's
  code + docstring mentions in the descendant).

## Gallery / docs

- `meta.json`: `status: axiomatized → verified`, `badge: axiom → verified`,
  `axiomCount: 1 → 0`, `theoremCount: 5 → 8`, `lineCount: 197 → 237`;
  `assumptions`, `proofStrategy`, the Part-IV and summary-table annotations,
  the open-questions list, and the child cross-reference all corrected to the
  axiom-free reality.
- `state.md`: phase → S3 ACT, iteration 3 → 4, new section.

## Counts

- Lean: +3 theorems, +1 lemma; −1 axiom; −1 false theorem; 0 sorries.
- File: `axiomCount 1 → 0`, `theoremCount 5 → 8`, `lineCount 197 → 237`.

## Why this matters

Removing a **known-false axiom** is a direct integrity win: the slug moves from
`axiomatized` (with a false assumption) to `verified` (fully machine-checked, no
assumptions). The mathematical content (separability is the exact hypothesis for
`natDegree ∣ |Gal|`; the inseparable obstruction needs a purely-inseparable
*splitting field*) is now faithfully formalized without any axiom.

## Follow-up

- The descendant `…OQ01` still re-proves `sub_pow_char_pow_eq`,
  `algEquiv_eq_refl_of_isPurelyInseparable`, and
  `gal_card_one_of_purelyInseparable_splitting` locally; it could be simplified to
  reuse this file's now-exported versions (separate slug's concern).
- The descendant still contains `axiom counterexample_gal_card` (the |Gal|=2
  Artin–Schreier fact) — that is the descendant slug's open obligation, untouched
  here.
